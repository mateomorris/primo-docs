function noop() { }
const identity = x => x;
function assign(tar, src) {
    // @ts-ignore
    for (const k in src)
        tar[k] = src[k];
    return tar;
}
// Adapted from https://github.com/then/is-promise/blob/master/index.js
// Distributed under MIT License https://github.com/then/is-promise/blob/master/LICENSE
function is_promise(value) {
    return !!value && (typeof value === 'object' || typeof value === 'function') && typeof value.then === 'function';
}
function run(fn) {
    return fn();
}
function blank_object() {
    return Object.create(null);
}
function run_all(fns) {
    fns.forEach(run);
}
function is_function(thing) {
    return typeof thing === 'function';
}
function safe_not_equal(a, b) {
    return a != a ? b == b : a !== b || ((a && typeof a === 'object') || typeof a === 'function');
}
let src_url_equal_anchor;
function src_url_equal(element_src, url) {
    if (!src_url_equal_anchor) {
        src_url_equal_anchor = document.createElement('a');
    }
    src_url_equal_anchor.href = url;
    return element_src === src_url_equal_anchor.href;
}
function is_empty(obj) {
    return Object.keys(obj).length === 0;
}
function exclude_internal_props(props) {
    const result = {};
    for (const k in props)
        if (k[0] !== '$')
            result[k] = props[k];
    return result;
}
function null_to_empty(value) {
    return value == null ? '' : value;
}

const is_client = typeof window !== 'undefined';
let now = is_client
    ? () => window.performance.now()
    : () => Date.now();
let raf = is_client ? cb => requestAnimationFrame(cb) : noop;

const tasks = new Set();
function run_tasks(now) {
    tasks.forEach(task => {
        if (!task.c(now)) {
            tasks.delete(task);
            task.f();
        }
    });
    if (tasks.size !== 0)
        raf(run_tasks);
}
/**
 * Creates a new task that runs on each raf frame
 * until it returns a falsy value or is aborted
 */
function loop(callback) {
    let task;
    if (tasks.size === 0)
        raf(run_tasks);
    return {
        promise: new Promise(fulfill => {
            tasks.add(task = { c: callback, f: fulfill });
        }),
        abort() {
            tasks.delete(task);
        }
    };
}

// Track which nodes are claimed during hydration. Unclaimed nodes can then be removed from the DOM
// at the end of hydration without touching the remaining nodes.
let is_hydrating = false;
function start_hydrating() {
    is_hydrating = true;
}
function end_hydrating() {
    is_hydrating = false;
}
function upper_bound(low, high, key, value) {
    // Return first index of value larger than input value in the range [low, high)
    while (low < high) {
        const mid = low + ((high - low) >> 1);
        if (key(mid) <= value) {
            low = mid + 1;
        }
        else {
            high = mid;
        }
    }
    return low;
}
function init_hydrate(target) {
    if (target.hydrate_init)
        return;
    target.hydrate_init = true;
    // We know that all children have claim_order values since the unclaimed have been detached if target is not <head>
    let children = target.childNodes;
    // If target is <head>, there may be children without claim_order
    if (target.nodeName === 'HEAD') {
        const myChildren = [];
        for (let i = 0; i < children.length; i++) {
            const node = children[i];
            if (node.claim_order !== undefined) {
                myChildren.push(node);
            }
        }
        children = myChildren;
    }
    /*
    * Reorder claimed children optimally.
    * We can reorder claimed children optimally by finding the longest subsequence of
    * nodes that are already claimed in order and only moving the rest. The longest
    * subsequence of nodes that are claimed in order can be found by
    * computing the longest increasing subsequence of .claim_order values.
    *
    * This algorithm is optimal in generating the least amount of reorder operations
    * possible.
    *
    * Proof:
    * We know that, given a set of reordering operations, the nodes that do not move
    * always form an increasing subsequence, since they do not move among each other
    * meaning that they must be already ordered among each other. Thus, the maximal
    * set of nodes that do not move form a longest increasing subsequence.
    */
    // Compute longest increasing subsequence
    // m: subsequence length j => index k of smallest value that ends an increasing subsequence of length j
    const m = new Int32Array(children.length + 1);
    // Predecessor indices + 1
    const p = new Int32Array(children.length);
    m[0] = -1;
    let longest = 0;
    for (let i = 0; i < children.length; i++) {
        const current = children[i].claim_order;
        // Find the largest subsequence length such that it ends in a value less than our current value
        // upper_bound returns first greater value, so we subtract one
        // with fast path for when we are on the current longest subsequence
        const seqLen = ((longest > 0 && children[m[longest]].claim_order <= current) ? longest + 1 : upper_bound(1, longest, idx => children[m[idx]].claim_order, current)) - 1;
        p[i] = m[seqLen] + 1;
        const newLen = seqLen + 1;
        // We can guarantee that current is the smallest value. Otherwise, we would have generated a longer sequence.
        m[newLen] = i;
        longest = Math.max(newLen, longest);
    }
    // The longest increasing subsequence of nodes (initially reversed)
    const lis = [];
    // The rest of the nodes, nodes that will be moved
    const toMove = [];
    let last = children.length - 1;
    for (let cur = m[longest] + 1; cur != 0; cur = p[cur - 1]) {
        lis.push(children[cur - 1]);
        for (; last >= cur; last--) {
            toMove.push(children[last]);
        }
        last--;
    }
    for (; last >= 0; last--) {
        toMove.push(children[last]);
    }
    lis.reverse();
    // We sort the nodes being moved to guarantee that their insertion order matches the claim order
    toMove.sort((a, b) => a.claim_order - b.claim_order);
    // Finally, we move the nodes
    for (let i = 0, j = 0; i < toMove.length; i++) {
        while (j < lis.length && toMove[i].claim_order >= lis[j].claim_order) {
            j++;
        }
        const anchor = j < lis.length ? lis[j] : null;
        target.insertBefore(toMove[i], anchor);
    }
}
function append(target, node) {
    target.appendChild(node);
}
function get_root_for_style(node) {
    if (!node)
        return document;
    const root = node.getRootNode ? node.getRootNode() : node.ownerDocument;
    if (root && root.host) {
        return root;
    }
    return node.ownerDocument;
}
function append_empty_stylesheet(node) {
    const style_element = element('style');
    append_stylesheet(get_root_for_style(node), style_element);
    return style_element.sheet;
}
function append_stylesheet(node, style) {
    append(node.head || node, style);
    return style.sheet;
}
function append_hydration(target, node) {
    if (is_hydrating) {
        init_hydrate(target);
        if ((target.actual_end_child === undefined) || ((target.actual_end_child !== null) && (target.actual_end_child.parentNode !== target))) {
            target.actual_end_child = target.firstChild;
        }
        // Skip nodes of undefined ordering
        while ((target.actual_end_child !== null) && (target.actual_end_child.claim_order === undefined)) {
            target.actual_end_child = target.actual_end_child.nextSibling;
        }
        if (node !== target.actual_end_child) {
            // We only insert if the ordering of this node should be modified or the parent node is not target
            if (node.claim_order !== undefined || node.parentNode !== target) {
                target.insertBefore(node, target.actual_end_child);
            }
        }
        else {
            target.actual_end_child = node.nextSibling;
        }
    }
    else if (node.parentNode !== target || node.nextSibling !== null) {
        target.appendChild(node);
    }
}
function insert(target, node, anchor) {
    target.insertBefore(node, anchor || null);
}
function insert_hydration(target, node, anchor) {
    if (is_hydrating && !anchor) {
        append_hydration(target, node);
    }
    else if (node.parentNode !== target || node.nextSibling != anchor) {
        target.insertBefore(node, anchor || null);
    }
}
function detach(node) {
    if (node.parentNode) {
        node.parentNode.removeChild(node);
    }
}
function destroy_each(iterations, detaching) {
    for (let i = 0; i < iterations.length; i += 1) {
        if (iterations[i])
            iterations[i].d(detaching);
    }
}
function element(name) {
    return document.createElement(name);
}
function svg_element(name) {
    return document.createElementNS('http://www.w3.org/2000/svg', name);
}
function text(data) {
    return document.createTextNode(data);
}
function space() {
    return text(' ');
}
function empty() {
    return text('');
}
function listen(node, event, handler, options) {
    node.addEventListener(event, handler, options);
    return () => node.removeEventListener(event, handler, options);
}
function attr(node, attribute, value) {
    if (value == null)
        node.removeAttribute(attribute);
    else if (node.getAttribute(attribute) !== value)
        node.setAttribute(attribute, value);
}
/**
 * List of attributes that should always be set through the attr method,
 * because updating them through the property setter doesn't work reliably.
 * In the example of `width`/`height`, the problem is that the setter only
 * accepts numeric values, but the attribute can also be set to a string like `50%`.
 * If this list becomes too big, rethink this approach.
 */
const always_set_through_set_attribute = ['width', 'height'];
function set_attributes(node, attributes) {
    // @ts-ignore
    const descriptors = Object.getOwnPropertyDescriptors(node.__proto__);
    for (const key in attributes) {
        if (attributes[key] == null) {
            node.removeAttribute(key);
        }
        else if (key === 'style') {
            node.style.cssText = attributes[key];
        }
        else if (key === '__value') {
            node.value = node[key] = attributes[key];
        }
        else if (descriptors[key] && descriptors[key].set && always_set_through_set_attribute.indexOf(key) === -1) {
            node[key] = attributes[key];
        }
        else {
            attr(node, key, attributes[key]);
        }
    }
}
function set_svg_attributes(node, attributes) {
    for (const key in attributes) {
        attr(node, key, attributes[key]);
    }
}
function children(element) {
    return Array.from(element.childNodes);
}
function init_claim_info(nodes) {
    if (nodes.claim_info === undefined) {
        nodes.claim_info = { last_index: 0, total_claimed: 0 };
    }
}
function claim_node(nodes, predicate, processNode, createNode, dontUpdateLastIndex = false) {
    // Try to find nodes in an order such that we lengthen the longest increasing subsequence
    init_claim_info(nodes);
    const resultNode = (() => {
        // We first try to find an element after the previous one
        for (let i = nodes.claim_info.last_index; i < nodes.length; i++) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                return node;
            }
        }
        // Otherwise, we try to find one before
        // We iterate in reverse so that we don't go too far back
        for (let i = nodes.claim_info.last_index - 1; i >= 0; i--) {
            const node = nodes[i];
            if (predicate(node)) {
                const replacement = processNode(node);
                if (replacement === undefined) {
                    nodes.splice(i, 1);
                }
                else {
                    nodes[i] = replacement;
                }
                if (!dontUpdateLastIndex) {
                    nodes.claim_info.last_index = i;
                }
                else if (replacement === undefined) {
                    // Since we spliced before the last_index, we decrease it
                    nodes.claim_info.last_index--;
                }
                return node;
            }
        }
        // If we can't find any matching node, we create a new one
        return createNode();
    })();
    resultNode.claim_order = nodes.claim_info.total_claimed;
    nodes.claim_info.total_claimed += 1;
    return resultNode;
}
function claim_element_base(nodes, name, attributes, create_element) {
    return claim_node(nodes, (node) => node.nodeName === name, (node) => {
        const remove = [];
        for (let j = 0; j < node.attributes.length; j++) {
            const attribute = node.attributes[j];
            if (!attributes[attribute.name]) {
                remove.push(attribute.name);
            }
        }
        remove.forEach(v => node.removeAttribute(v));
        return undefined;
    }, () => create_element(name));
}
function claim_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, element);
}
function claim_svg_element(nodes, name, attributes) {
    return claim_element_base(nodes, name, attributes, svg_element);
}
function claim_text(nodes, data) {
    return claim_node(nodes, (node) => node.nodeType === 3, (node) => {
        const dataStr = '' + data;
        if (node.data.startsWith(dataStr)) {
            if (node.data.length !== dataStr.length) {
                return node.splitText(dataStr.length);
            }
        }
        else {
            node.data = dataStr;
        }
    }, () => text(data), true // Text nodes should not update last index since it is likely not worth it to eliminate an increasing subsequence of actual elements
    );
}
function claim_space(nodes) {
    return claim_text(nodes, ' ');
}
function find_comment(nodes, text, start) {
    for (let i = start; i < nodes.length; i += 1) {
        const node = nodes[i];
        if (node.nodeType === 8 /* comment node */ && node.textContent.trim() === text) {
            return i;
        }
    }
    return nodes.length;
}
function claim_html_tag(nodes, is_svg) {
    // find html opening tag
    const start_index = find_comment(nodes, 'HTML_TAG_START', 0);
    const end_index = find_comment(nodes, 'HTML_TAG_END', start_index);
    if (start_index === end_index) {
        return new HtmlTagHydration(undefined, is_svg);
    }
    init_claim_info(nodes);
    const html_tag_nodes = nodes.splice(start_index, end_index - start_index + 1);
    detach(html_tag_nodes[0]);
    detach(html_tag_nodes[html_tag_nodes.length - 1]);
    const claimed_nodes = html_tag_nodes.slice(1, html_tag_nodes.length - 1);
    for (const n of claimed_nodes) {
        n.claim_order = nodes.claim_info.total_claimed;
        nodes.claim_info.total_claimed += 1;
    }
    return new HtmlTagHydration(claimed_nodes, is_svg);
}
function set_data(text, data) {
    data = '' + data;
    if (text.data === data)
        return;
    text.data = data;
}
function toggle_class(element, name, toggle) {
    element.classList[toggle ? 'add' : 'remove'](name);
}
function custom_event(type, detail, { bubbles = false, cancelable = false } = {}) {
    const e = document.createEvent('CustomEvent');
    e.initCustomEvent(type, bubbles, cancelable, detail);
    return e;
}
function head_selector(nodeId, head) {
    const result = [];
    let started = 0;
    for (const node of head.childNodes) {
        if (node.nodeType === 8 /* comment node */) {
            const comment = node.textContent.trim();
            if (comment === `HEAD_${nodeId}_END`) {
                started -= 1;
                result.push(node);
            }
            else if (comment === `HEAD_${nodeId}_START`) {
                started += 1;
                result.push(node);
            }
        }
        else if (started > 0) {
            result.push(node);
        }
    }
    return result;
}
class HtmlTag {
    constructor(is_svg = false) {
        this.is_svg = false;
        this.is_svg = is_svg;
        this.e = this.n = null;
    }
    c(html) {
        this.h(html);
    }
    m(html, target, anchor = null) {
        if (!this.e) {
            if (this.is_svg)
                this.e = svg_element(target.nodeName);
            /** #7364  target for <template> may be provided as #document-fragment(11) */
            else
                this.e = element((target.nodeType === 11 ? 'TEMPLATE' : target.nodeName));
            this.t = target.tagName !== 'TEMPLATE' ? target : target.content;
            this.c(html);
        }
        this.i(anchor);
    }
    h(html) {
        this.e.innerHTML = html;
        this.n = Array.from(this.e.nodeName === 'TEMPLATE' ? this.e.content.childNodes : this.e.childNodes);
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert(this.t, this.n[i], anchor);
        }
    }
    p(html) {
        this.d();
        this.h(html);
        this.i(this.a);
    }
    d() {
        this.n.forEach(detach);
    }
}
class HtmlTagHydration extends HtmlTag {
    constructor(claimed_nodes, is_svg = false) {
        super(is_svg);
        this.e = this.n = null;
        this.l = claimed_nodes;
    }
    c(html) {
        if (this.l) {
            this.n = this.l;
        }
        else {
            super.c(html);
        }
    }
    i(anchor) {
        for (let i = 0; i < this.n.length; i += 1) {
            insert_hydration(this.t, this.n[i], anchor);
        }
    }
}

// we need to store the information for multiple documents because a Svelte application could also contain iframes
// https://github.com/sveltejs/svelte/issues/3624
const managed_styles = new Map();
let active = 0;
// https://github.com/darkskyapp/string-hash/blob/master/index.js
function hash(str) {
    let hash = 5381;
    let i = str.length;
    while (i--)
        hash = ((hash << 5) - hash) ^ str.charCodeAt(i);
    return hash >>> 0;
}
function create_style_information(doc, node) {
    const info = { stylesheet: append_empty_stylesheet(node), rules: {} };
    managed_styles.set(doc, info);
    return info;
}
function create_rule(node, a, b, duration, delay, ease, fn, uid = 0) {
    const step = 16.666 / duration;
    let keyframes = '{\n';
    for (let p = 0; p <= 1; p += step) {
        const t = a + (b - a) * ease(p);
        keyframes += p * 100 + `%{${fn(t, 1 - t)}}\n`;
    }
    const rule = keyframes + `100% {${fn(b, 1 - b)}}\n}`;
    const name = `__svelte_${hash(rule)}_${uid}`;
    const doc = get_root_for_style(node);
    const { stylesheet, rules } = managed_styles.get(doc) || create_style_information(doc, node);
    if (!rules[name]) {
        rules[name] = true;
        stylesheet.insertRule(`@keyframes ${name} ${rule}`, stylesheet.cssRules.length);
    }
    const animation = node.style.animation || '';
    node.style.animation = `${animation ? `${animation}, ` : ''}${name} ${duration}ms linear ${delay}ms 1 both`;
    active += 1;
    return name;
}
function delete_rule(node, name) {
    const previous = (node.style.animation || '').split(', ');
    const next = previous.filter(name
        ? anim => anim.indexOf(name) < 0 // remove specific animation
        : anim => anim.indexOf('__svelte') === -1 // remove all Svelte animations
    );
    const deleted = previous.length - next.length;
    if (deleted) {
        node.style.animation = next.join(', ');
        active -= deleted;
        if (!active)
            clear_rules();
    }
}
function clear_rules() {
    raf(() => {
        if (active)
            return;
        managed_styles.forEach(info => {
            const { ownerNode } = info.stylesheet;
            // there is no ownerNode if it runs on jsdom.
            if (ownerNode)
                detach(ownerNode);
        });
        managed_styles.clear();
    });
}

let current_component;
function set_current_component(component) {
    current_component = component;
}
function get_current_component() {
    if (!current_component)
        throw new Error('Function called outside component initialization');
    return current_component;
}
/**
 * The `onMount` function schedules a callback to run as soon as the component has been mounted to the DOM.
 * It must be called during the component's initialisation (but doesn't need to live *inside* the component;
 * it can be called from an external module).
 *
 * `onMount` does not run inside a [server-side component](/docs#run-time-server-side-component-api).
 *
 * https://svelte.dev/docs#run-time-svelte-onmount
 */
function onMount(fn) {
    get_current_component().$$.on_mount.push(fn);
}
/**
 * Schedules a callback to run immediately before the component is unmounted.
 *
 * Out of `onMount`, `beforeUpdate`, `afterUpdate` and `onDestroy`, this is the
 * only one that runs inside a server-side component.
 *
 * https://svelte.dev/docs#run-time-svelte-ondestroy
 */
function onDestroy(fn) {
    get_current_component().$$.on_destroy.push(fn);
}
/**
 * Creates an event dispatcher that can be used to dispatch [component events](/docs#template-syntax-component-directives-on-eventname).
 * Event dispatchers are functions that can take two arguments: `name` and `detail`.
 *
 * Component events created with `createEventDispatcher` create a
 * [CustomEvent](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent).
 * These events do not [bubble](https://developer.mozilla.org/en-US/docs/Learn/JavaScript/Building_blocks/Events#Event_bubbling_and_capture).
 * The `detail` argument corresponds to the [CustomEvent.detail](https://developer.mozilla.org/en-US/docs/Web/API/CustomEvent/detail)
 * property and can contain any type of data.
 *
 * https://svelte.dev/docs#run-time-svelte-createeventdispatcher
 */
function createEventDispatcher() {
    const component = get_current_component();
    return (type, detail, { cancelable = false } = {}) => {
        const callbacks = component.$$.callbacks[type];
        if (callbacks) {
            // TODO are there situations where events could be dispatched
            // in a server (non-DOM) environment?
            const event = custom_event(type, detail, { cancelable });
            callbacks.slice().forEach(fn => {
                fn.call(component, event);
            });
            return !event.defaultPrevented;
        }
        return true;
    };
}

const dirty_components = [];
const binding_callbacks = [];
let render_callbacks = [];
const flush_callbacks = [];
const resolved_promise = /* @__PURE__ */ Promise.resolve();
let update_scheduled = false;
function schedule_update() {
    if (!update_scheduled) {
        update_scheduled = true;
        resolved_promise.then(flush);
    }
}
function tick() {
    schedule_update();
    return resolved_promise;
}
function add_render_callback(fn) {
    render_callbacks.push(fn);
}
// flush() calls callbacks in this order:
// 1. All beforeUpdate callbacks, in order: parents before children
// 2. All bind:this callbacks, in reverse order: children before parents.
// 3. All afterUpdate callbacks, in order: parents before children. EXCEPT
//    for afterUpdates called during the initial onMount, which are called in
//    reverse order: children before parents.
// Since callbacks might update component values, which could trigger another
// call to flush(), the following steps guard against this:
// 1. During beforeUpdate, any updated components will be added to the
//    dirty_components array and will cause a reentrant call to flush(). Because
//    the flush index is kept outside the function, the reentrant call will pick
//    up where the earlier call left off and go through all dirty components. The
//    current_component value is saved and restored so that the reentrant call will
//    not interfere with the "parent" flush() call.
// 2. bind:this callbacks cannot trigger new flush() calls.
// 3. During afterUpdate, any updated components will NOT have their afterUpdate
//    callback called a second time; the seen_callbacks set, outside the flush()
//    function, guarantees this behavior.
const seen_callbacks = new Set();
let flushidx = 0; // Do *not* move this inside the flush() function
function flush() {
    // Do not reenter flush while dirty components are updated, as this can
    // result in an infinite loop. Instead, let the inner flush handle it.
    // Reentrancy is ok afterwards for bindings etc.
    if (flushidx !== 0) {
        return;
    }
    const saved_component = current_component;
    do {
        // first, call beforeUpdate functions
        // and update components
        try {
            while (flushidx < dirty_components.length) {
                const component = dirty_components[flushidx];
                flushidx++;
                set_current_component(component);
                update(component.$$);
            }
        }
        catch (e) {
            // reset dirty state to not end up in a deadlocked state and then rethrow
            dirty_components.length = 0;
            flushidx = 0;
            throw e;
        }
        set_current_component(null);
        dirty_components.length = 0;
        flushidx = 0;
        while (binding_callbacks.length)
            binding_callbacks.pop()();
        // then, once components are updated, call
        // afterUpdate functions. This may cause
        // subsequent updates...
        for (let i = 0; i < render_callbacks.length; i += 1) {
            const callback = render_callbacks[i];
            if (!seen_callbacks.has(callback)) {
                // ...so guard against infinite loops
                seen_callbacks.add(callback);
                callback();
            }
        }
        render_callbacks.length = 0;
    } while (dirty_components.length);
    while (flush_callbacks.length) {
        flush_callbacks.pop()();
    }
    update_scheduled = false;
    seen_callbacks.clear();
    set_current_component(saved_component);
}
function update($$) {
    if ($$.fragment !== null) {
        $$.update();
        run_all($$.before_update);
        const dirty = $$.dirty;
        $$.dirty = [-1];
        $$.fragment && $$.fragment.p($$.ctx, dirty);
        $$.after_update.forEach(add_render_callback);
    }
}
/**
 * Useful for example to execute remaining `afterUpdate` callbacks before executing `destroy`.
 */
function flush_render_callbacks(fns) {
    const filtered = [];
    const targets = [];
    render_callbacks.forEach((c) => fns.indexOf(c) === -1 ? filtered.push(c) : targets.push(c));
    targets.forEach((c) => c());
    render_callbacks = filtered;
}

let promise;
function wait() {
    if (!promise) {
        promise = Promise.resolve();
        promise.then(() => {
            promise = null;
        });
    }
    return promise;
}
function dispatch(node, direction, kind) {
    node.dispatchEvent(custom_event(`${direction ? 'intro' : 'outro'}${kind}`));
}
const outroing = new Set();
let outros;
function group_outros() {
    outros = {
        r: 0,
        c: [],
        p: outros // parent group
    };
}
function check_outros() {
    if (!outros.r) {
        run_all(outros.c);
    }
    outros = outros.p;
}
function transition_in(block, local) {
    if (block && block.i) {
        outroing.delete(block);
        block.i(local);
    }
}
function transition_out(block, local, detach, callback) {
    if (block && block.o) {
        if (outroing.has(block))
            return;
        outroing.add(block);
        outros.c.push(() => {
            outroing.delete(block);
            if (callback) {
                if (detach)
                    block.d(1);
                callback();
            }
        });
        block.o(local);
    }
    else if (callback) {
        callback();
    }
}
const null_transition = { duration: 0 };
function create_bidirectional_transition(node, fn, params, intro) {
    const options = { direction: 'both' };
    let config = fn(node, params, options);
    let t = intro ? 0 : 1;
    let running_program = null;
    let pending_program = null;
    let animation_name = null;
    function clear_animation() {
        if (animation_name)
            delete_rule(node, animation_name);
    }
    function init(program, duration) {
        const d = (program.b - t);
        duration *= Math.abs(d);
        return {
            a: t,
            b: program.b,
            d,
            duration,
            start: program.start,
            end: program.start + duration,
            group: program.group
        };
    }
    function go(b) {
        const { delay = 0, duration = 300, easing = identity, tick = noop, css } = config || null_transition;
        const program = {
            start: now() + delay,
            b
        };
        if (!b) {
            // @ts-ignore todo: improve typings
            program.group = outros;
            outros.r += 1;
        }
        if (running_program || pending_program) {
            pending_program = program;
        }
        else {
            // if this is an intro, and there's a delay, we need to do
            // an initial tick and/or apply CSS animation immediately
            if (css) {
                clear_animation();
                animation_name = create_rule(node, t, b, duration, delay, easing, css);
            }
            if (b)
                tick(0, 1);
            running_program = init(program, duration);
            add_render_callback(() => dispatch(node, b, 'start'));
            loop(now => {
                if (pending_program && now > pending_program.start) {
                    running_program = init(pending_program, duration);
                    pending_program = null;
                    dispatch(node, running_program.b, 'start');
                    if (css) {
                        clear_animation();
                        animation_name = create_rule(node, t, running_program.b, running_program.duration, 0, easing, config.css);
                    }
                }
                if (running_program) {
                    if (now >= running_program.end) {
                        tick(t = running_program.b, 1 - t);
                        dispatch(node, running_program.b, 'end');
                        if (!pending_program) {
                            // we're done
                            if (running_program.b) {
                                // intro — we can tidy up immediately
                                clear_animation();
                            }
                            else {
                                // outro — needs to be coordinated
                                if (!--running_program.group.r)
                                    run_all(running_program.group.c);
                            }
                        }
                        running_program = null;
                    }
                    else if (now >= running_program.start) {
                        const p = now - running_program.start;
                        t = running_program.a + running_program.d * easing(p / running_program.duration);
                        tick(t, 1 - t);
                    }
                }
                return !!(running_program || pending_program);
            });
        }
    }
    return {
        run(b) {
            if (is_function(config)) {
                wait().then(() => {
                    // @ts-ignore
                    config = config(options);
                    go(b);
                });
            }
            else {
                go(b);
            }
        },
        end() {
            clear_animation();
            running_program = pending_program = null;
        }
    };
}

function handle_promise(promise, info) {
    const token = info.token = {};
    function update(type, index, key, value) {
        if (info.token !== token)
            return;
        info.resolved = value;
        let child_ctx = info.ctx;
        if (key !== undefined) {
            child_ctx = child_ctx.slice();
            child_ctx[key] = value;
        }
        const block = type && (info.current = type)(child_ctx);
        let needs_flush = false;
        if (info.block) {
            if (info.blocks) {
                info.blocks.forEach((block, i) => {
                    if (i !== index && block) {
                        group_outros();
                        transition_out(block, 1, 1, () => {
                            if (info.blocks[i] === block) {
                                info.blocks[i] = null;
                            }
                        });
                        check_outros();
                    }
                });
            }
            else {
                info.block.d(1);
            }
            block.c();
            transition_in(block, 1);
            block.m(info.mount(), info.anchor);
            needs_flush = true;
        }
        info.block = block;
        if (info.blocks)
            info.blocks[index] = block;
        if (needs_flush) {
            flush();
        }
    }
    if (is_promise(promise)) {
        const current_component = get_current_component();
        promise.then(value => {
            set_current_component(current_component);
            update(info.then, 1, info.value, value);
            set_current_component(null);
        }, error => {
            set_current_component(current_component);
            update(info.catch, 2, info.error, error);
            set_current_component(null);
            if (!info.hasCatch) {
                throw error;
            }
        });
        // if we previously had a then/catch block, destroy it
        if (info.current !== info.pending) {
            update(info.pending, 0);
            return true;
        }
    }
    else {
        if (info.current !== info.then) {
            update(info.then, 1, info.value, promise);
            return true;
        }
        info.resolved = promise;
    }
}
function update_await_block_branch(info, ctx, dirty) {
    const child_ctx = ctx.slice();
    const { resolved } = info;
    if (info.current === info.then) {
        child_ctx[info.value] = resolved;
    }
    if (info.current === info.catch) {
        child_ctx[info.error] = resolved;
    }
    info.block.p(child_ctx, dirty);
}

function get_spread_update(levels, updates) {
    const update = {};
    const to_null_out = {};
    const accounted_for = { $$scope: 1 };
    let i = levels.length;
    while (i--) {
        const o = levels[i];
        const n = updates[i];
        if (n) {
            for (const key in o) {
                if (!(key in n))
                    to_null_out[key] = 1;
            }
            for (const key in n) {
                if (!accounted_for[key]) {
                    update[key] = n[key];
                    accounted_for[key] = 1;
                }
            }
            levels[i] = n;
        }
        else {
            for (const key in o) {
                accounted_for[key] = 1;
            }
        }
    }
    for (const key in to_null_out) {
        if (!(key in update))
            update[key] = undefined;
    }
    return update;
}
function create_component(block) {
    block && block.c();
}
function claim_component(block, parent_nodes) {
    block && block.l(parent_nodes);
}
function mount_component(component, target, anchor, customElement) {
    const { fragment, after_update } = component.$$;
    fragment && fragment.m(target, anchor);
    if (!customElement) {
        // onMount happens before the initial afterUpdate
        add_render_callback(() => {
            const new_on_destroy = component.$$.on_mount.map(run).filter(is_function);
            // if the component was destroyed immediately
            // it will update the `$$.on_destroy` reference to `null`.
            // the destructured on_destroy may still reference to the old array
            if (component.$$.on_destroy) {
                component.$$.on_destroy.push(...new_on_destroy);
            }
            else {
                // Edge case - component was destroyed immediately,
                // most likely as a result of a binding initialising
                run_all(new_on_destroy);
            }
            component.$$.on_mount = [];
        });
    }
    after_update.forEach(add_render_callback);
}
function destroy_component(component, detaching) {
    const $$ = component.$$;
    if ($$.fragment !== null) {
        flush_render_callbacks($$.after_update);
        run_all($$.on_destroy);
        $$.fragment && $$.fragment.d(detaching);
        // TODO null out other refs, including component.$$ (but need to
        // preserve final state?)
        $$.on_destroy = $$.fragment = null;
        $$.ctx = [];
    }
}
function make_dirty(component, i) {
    if (component.$$.dirty[0] === -1) {
        dirty_components.push(component);
        schedule_update();
        component.$$.dirty.fill(0);
    }
    component.$$.dirty[(i / 31) | 0] |= (1 << (i % 31));
}
function init(component, options, instance, create_fragment, not_equal, props, append_styles, dirty = [-1]) {
    const parent_component = current_component;
    set_current_component(component);
    const $$ = component.$$ = {
        fragment: null,
        ctx: [],
        // state
        props,
        update: noop,
        not_equal,
        bound: blank_object(),
        // lifecycle
        on_mount: [],
        on_destroy: [],
        on_disconnect: [],
        before_update: [],
        after_update: [],
        context: new Map(options.context || (parent_component ? parent_component.$$.context : [])),
        // everything else
        callbacks: blank_object(),
        dirty,
        skip_bound: false,
        root: options.target || parent_component.$$.root
    };
    append_styles && append_styles($$.root);
    let ready = false;
    $$.ctx = instance
        ? instance(component, options.props || {}, (i, ret, ...rest) => {
            const value = rest.length ? rest[0] : ret;
            if ($$.ctx && not_equal($$.ctx[i], $$.ctx[i] = value)) {
                if (!$$.skip_bound && $$.bound[i])
                    $$.bound[i](value);
                if (ready)
                    make_dirty(component, i);
            }
            return ret;
        })
        : [];
    $$.update();
    ready = true;
    run_all($$.before_update);
    // `false` as a special case of no DOM component
    $$.fragment = create_fragment ? create_fragment($$.ctx) : false;
    if (options.target) {
        if (options.hydrate) {
            start_hydrating();
            const nodes = children(options.target);
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.l(nodes);
            nodes.forEach(detach);
        }
        else {
            // eslint-disable-next-line @typescript-eslint/no-non-null-assertion
            $$.fragment && $$.fragment.c();
        }
        if (options.intro)
            transition_in(component.$$.fragment);
        mount_component(component, options.target, options.anchor, options.customElement);
        end_hydrating();
        flush();
    }
    set_current_component(parent_component);
}
/**
 * Base class for Svelte components. Used when dev=false.
 */
class SvelteComponent {
    $destroy() {
        destroy_component(this, 1);
        this.$destroy = noop;
    }
    $on(type, callback) {
        if (!is_function(callback)) {
            return noop;
        }
        const callbacks = (this.$$.callbacks[type] || (this.$$.callbacks[type] = []));
        callbacks.push(callback);
        return () => {
            const index = callbacks.indexOf(callback);
            if (index !== -1)
                callbacks.splice(index, 1);
        };
    }
    $set($$props) {
        if (this.$$set && !is_empty($$props)) {
            this.$$.skip_bound = true;
            this.$$set($$props);
            this.$$.skip_bound = false;
        }
    }
}

/* generated by Svelte v3.58.0 */

function create_fragment(ctx) {
	let meta0;
	let meta1;
	let link;
	let title_value;
	let meta2;
	let style;
	let t;
	document.title = title_value = /*title*/ ctx[0];

	return {
		c() {
			meta0 = element("meta");
			meta1 = element("meta");
			link = element("link");
			meta2 = element("meta");
			style = element("style");
			t = text("@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n@import url(https://fonts.bunny.net/css?family=archivo:200,300,300i,400,400i,500,500i,600,600i,700,700i|inter:300,400,500,600,700,800);\n\nhtml {\n  /* Colors */\n  --color-accent: #35d994;\n\n  /* Default property values */\n  --background: #111;\n  --color: #c2c2c2;\n  --padding: 2rem;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --max-width: 1200px;\n  --border-color: #333;\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color, var(--transition-time) border-color,\n    var(--transition-time) text-decoration-color,\n    var(--transition-time) box-shadow, var(--transtion-time) transform;\n}\n\n#page {\n  font-family: \"Inter\", sans-serif;\n  color: var(--color);\n  line-height: 1.6;\n  font-size: 1rem;\n  background: #111;\n  font-weight: 300;\n}\n\n.content {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding: var(--padding);\n\n  /*   pre {\n    padding: 2rem;\n    background: #222;\n    border-radius: 0.25rem;\n    margin-bottom: 2rem;\n    margin-top: 1em;\n  } */\n}\n\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n    color: var(--color);\n  }\n\n.content strong {\n    font-weight: 500;\n    color: white;\n  }\n\n.content a {\n    text-decoration: underline;\n  }\n\n.content h1 {\n    line-height: 1.2;\n    font-size: 2.25rem;\n    font-weight: 500;\n    margin-bottom: 0.5rem;\n    color: white;\n  }\n\n.content h2 {\n    font-size: 1.75rem;\n    font-weight: 500;\n    margin-bottom: 0.5rem;\n    margin-top: 2rem;\n    color: white;\n  }\n\n.content h3 {\n    font-size: 1.5rem;\n    font-weight: 500;\n    margin-bottom: 0.25rem;\n    margin-top: 1rem;\n    color: white;\n  }\n\n.content h4 {\n    font-size: 1.15rem;\n    font-weight: 500;\n    margin-bottom: 0.25rem;\n    margin-top: 1rem;\n    color: white;\n  }\n\n.content h5 {\n    font-size: 1rem;\n    font-weight: 500;\n    margin-bottom: 0.25rem;\n    margin-top: 1rem;\n    color: white;\n  }\n\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.content blockquote {\n    border: 1px solid #222;\n    margin: 1rem 0;\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section-container {\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: 3rem var(--padding, 1rem);\n}\n\n.heading {\n  font-size: 3rem;\n  line-height: 1;\n  font-weight: 500;\n  margin: 0;\n}\n\n.button {\n  color: white;\n  background: var(--color-accent);\n  border-radius: 5px;\n  padding: 8px 20px;\n  transition: var(--transition);\n}\n\n.button:hover {\n    box-shadow: 0 0 10px 5px rgba(0, 0, 0, 0.1);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent);\n    border: 2px solid var(--color-accent);\n  }");
			this.h();
		},
		l(nodes) {
			const head_nodes = head_selector('svelte-178vttq', document.head);
			meta0 = claim_element(head_nodes, "META", { name: true, content: true });
			meta1 = claim_element(head_nodes, "META", { charset: true });
			link = claim_element(head_nodes, "LINK", { rel: true, type: true, href: true });
			meta2 = claim_element(head_nodes, "META", { name: true, content: true });
			style = claim_element(head_nodes, "STYLE", {});
			var style_nodes = children(style);
			t = claim_text(style_nodes, "@import url(\"https://unpkg.com/@primo-app/primo@1.3.64/reset.css\");\n@import url(https://fonts.bunny.net/css?family=archivo:200,300,300i,400,400i,500,500i,600,600i,700,700i|inter:300,400,500,600,700,800);\n\nhtml {\n  /* Colors */\n  --color-accent: #35d994;\n\n  /* Default property values */\n  --background: #111;\n  --color: #c2c2c2;\n  --padding: 2rem;\n  --box-shadow: 0px 4px 30px rgba(0, 0, 0, 0.2);\n  --border-radius: 8px;\n  --max-width: 1200px;\n  --border-color: #333;\n  --transition-time: 0.1s;\n  --transition: var(--transition-time) color,\n    var(--transition-time) background-color, var(--transition-time) border-color,\n    var(--transition-time) text-decoration-color,\n    var(--transition-time) box-shadow, var(--transtion-time) transform;\n}\n\n#page {\n  font-family: \"Inter\", sans-serif;\n  color: var(--color);\n  line-height: 1.6;\n  font-size: 1rem;\n  background: #111;\n  font-weight: 300;\n}\n\n.content {\n  max-width: var(--max-width);\n  margin: 0 auto;\n  padding: var(--padding);\n\n  /*   pre {\n    padding: 2rem;\n    background: #222;\n    border-radius: 0.25rem;\n    margin-bottom: 2rem;\n    margin-top: 1em;\n  } */\n}\n\n.content img {\n    width: 100%;\n    margin: 2rem 0;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.content p {\n    padding: 0.25rem 0;\n    line-height: 1.5;\n    color: var(--color);\n  }\n\n.content strong {\n    font-weight: 500;\n    color: white;\n  }\n\n.content a {\n    text-decoration: underline;\n  }\n\n.content h1 {\n    line-height: 1.2;\n    font-size: 2.25rem;\n    font-weight: 500;\n    margin-bottom: 0.5rem;\n    color: white;\n  }\n\n.content h2 {\n    font-size: 1.75rem;\n    font-weight: 500;\n    margin-bottom: 0.5rem;\n    margin-top: 2rem;\n    color: white;\n  }\n\n.content h3 {\n    font-size: 1.5rem;\n    font-weight: 500;\n    margin-bottom: 0.25rem;\n    margin-top: 1rem;\n    color: white;\n  }\n\n.content h4 {\n    font-size: 1.15rem;\n    font-weight: 500;\n    margin-bottom: 0.25rem;\n    margin-top: 1rem;\n    color: white;\n  }\n\n.content h5 {\n    font-size: 1rem;\n    font-weight: 500;\n    margin-bottom: 0.25rem;\n    margin-top: 1rem;\n    color: white;\n  }\n\n.content ul {\n    list-style: disc;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.content ol {\n    list-style: decimal;\n    padding: 0.5rem 0;\n    padding-left: 1.25rem;\n  }\n\n.content blockquote {\n    border: 1px solid #222;\n    margin: 1rem 0;\n    padding: 2rem;\n    box-shadow: var(--box-shadow);\n    border-radius: var(--border-radius);\n  }\n\n.section-container {\n  max-width: var(--max-width, 1200px);\n  margin: 0 auto;\n  padding: 3rem var(--padding, 1rem);\n}\n\n.heading {\n  font-size: 3rem;\n  line-height: 1;\n  font-weight: 500;\n  margin: 0;\n}\n\n.button {\n  color: white;\n  background: var(--color-accent);\n  border-radius: 5px;\n  padding: 8px 20px;\n  transition: var(--transition);\n}\n\n.button:hover {\n    box-shadow: 0 0 10px 5px rgba(0, 0, 0, 0.1);\n  }\n\n.button.inverted {\n    background: transparent;\n    color: var(--color-accent);\n    border: 2px solid var(--color-accent);\n  }");
			style_nodes.forEach(detach);
			head_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(meta0, "name", "viewport");
			attr(meta0, "content", "width=device-width, initial-scale=1.0");
			attr(meta1, "charset", "UTF-8");
			attr(link, "rel", "shortcut icon");
			attr(link, "type", "image/png");
			attr(link, "href", "https://res.cloudinary.com/primoaf/image/upload/v1659676914/favicon_roaxv0.png");
			attr(meta2, "name", "description");
			attr(meta2, "content", /*description*/ ctx[1]);
		},
		m(target, anchor) {
			append_hydration(document.head, meta0);
			append_hydration(document.head, meta1);
			append_hydration(document.head, link);
			append_hydration(document.head, meta2);
			append_hydration(document.head, style);
			append_hydration(style, t);
		},
		p(ctx, [dirty]) {
			if (dirty & /*title*/ 1 && title_value !== (title_value = /*title*/ ctx[0])) {
				document.title = title_value;
			}

			if (dirty & /*description*/ 2) {
				attr(meta2, "content", /*description*/ ctx[1]);
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			detach(meta0);
			detach(meta1);
			detach(link);
			detach(meta2);
			detach(style);
		}
	};
}

function instance($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('description' in $$props) $$invalidate(1, description = $$props.description);
	};

	return [title, description];
}

class Component extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance, create_fragment, safe_not_equal, { title: 0, description: 1 });
	}
}

var global$1 = typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : {};
function bind(fn, thisArg) {
  return function wrap() {
    return fn.apply(thisArg, arguments);
  };
}
const {toString} = Object.prototype;
const {getPrototypeOf} = Object;
const kindOf = ((cache) => (thing) => {
  const str = toString.call(thing);
  return cache[str] || (cache[str] = str.slice(8, -1).toLowerCase());
})(Object.create(null));
const kindOfTest = (type) => {
  type = type.toLowerCase();
  return (thing) => kindOf(thing) === type;
};
const typeOfTest = (type) => (thing) => typeof thing === type;
const {isArray} = Array;
const isUndefined = typeOfTest("undefined");
function isBuffer(val) {
  return val !== null && !isUndefined(val) && val.constructor !== null && !isUndefined(val.constructor) && isFunction(val.constructor.isBuffer) && val.constructor.isBuffer(val);
}
const isArrayBuffer = kindOfTest("ArrayBuffer");
function isArrayBufferView(val) {
  let result;
  if (typeof ArrayBuffer !== "undefined" && ArrayBuffer.isView) {
    result = ArrayBuffer.isView(val);
  } else {
    result = val && val.buffer && isArrayBuffer(val.buffer);
  }
  return result;
}
const isString = typeOfTest("string");
const isFunction = typeOfTest("function");
const isNumber = typeOfTest("number");
const isObject = (thing) => thing !== null && typeof thing === "object";
const isBoolean = (thing) => thing === true || thing === false;
const isPlainObject = (val) => {
  if (kindOf(val) !== "object") {
    return false;
  }
  const prototype = getPrototypeOf(val);
  return (prototype === null || prototype === Object.prototype || Object.getPrototypeOf(prototype) === null) && !(Symbol.toStringTag in val) && !(Symbol.iterator in val);
};
const isDate = kindOfTest("Date");
const isFile = kindOfTest("File");
const isBlob = kindOfTest("Blob");
const isFileList = kindOfTest("FileList");
const isStream = (val) => isObject(val) && isFunction(val.pipe);
const isFormData = (thing) => {
  let kind;
  return thing && (typeof FormData === "function" && thing instanceof FormData || isFunction(thing.append) && ((kind = kindOf(thing)) === "formdata" || kind === "object" && isFunction(thing.toString) && thing.toString() === "[object FormData]"));
};
const isURLSearchParams = kindOfTest("URLSearchParams");
const trim = (str) => str.trim ? str.trim() : str.replace(/^[\s\uFEFF\xA0]+|[\s\uFEFF\xA0]+$/g, "");
function forEach(obj, fn, {allOwnKeys = false} = {}) {
  if (obj === null || typeof obj === "undefined") {
    return;
  }
  let i;
  let l;
  if (typeof obj !== "object") {
    obj = [obj];
  }
  if (isArray(obj)) {
    for (i = 0, l = obj.length; i < l; i++) {
      fn.call(null, obj[i], i, obj);
    }
  } else {
    const keys = allOwnKeys ? Object.getOwnPropertyNames(obj) : Object.keys(obj);
    const len = keys.length;
    let key;
    for (i = 0; i < len; i++) {
      key = keys[i];
      fn.call(null, obj[key], key, obj);
    }
  }
}
function findKey(obj, key) {
  key = key.toLowerCase();
  const keys = Object.keys(obj);
  let i = keys.length;
  let _key;
  while (i-- > 0) {
    _key = keys[i];
    if (key === _key.toLowerCase()) {
      return _key;
    }
  }
  return null;
}
const _global = (() => {
  if (typeof globalThis !== "undefined")
    return globalThis;
  return typeof self !== "undefined" ? self : typeof window !== "undefined" ? window : global$1;
})();
const isContextDefined = (context) => !isUndefined(context) && context !== _global;
function merge() {
  const {caseless} = isContextDefined(this) && this || {};
  const result = {};
  const assignValue = (val, key) => {
    const targetKey = caseless && findKey(result, key) || key;
    if (isPlainObject(result[targetKey]) && isPlainObject(val)) {
      result[targetKey] = merge(result[targetKey], val);
    } else if (isPlainObject(val)) {
      result[targetKey] = merge({}, val);
    } else if (isArray(val)) {
      result[targetKey] = val.slice();
    } else {
      result[targetKey] = val;
    }
  };
  for (let i = 0, l = arguments.length; i < l; i++) {
    arguments[i] && forEach(arguments[i], assignValue);
  }
  return result;
}
const extend = (a, b, thisArg, {allOwnKeys} = {}) => {
  forEach(b, (val, key) => {
    if (thisArg && isFunction(val)) {
      a[key] = bind(val, thisArg);
    } else {
      a[key] = val;
    }
  }, {allOwnKeys});
  return a;
};
const stripBOM = (content) => {
  if (content.charCodeAt(0) === 65279) {
    content = content.slice(1);
  }
  return content;
};
const inherits = (constructor, superConstructor, props, descriptors) => {
  constructor.prototype = Object.create(superConstructor.prototype, descriptors);
  constructor.prototype.constructor = constructor;
  Object.defineProperty(constructor, "super", {
    value: superConstructor.prototype
  });
  props && Object.assign(constructor.prototype, props);
};
const toFlatObject = (sourceObj, destObj, filter, propFilter) => {
  let props;
  let i;
  let prop;
  const merged = {};
  destObj = destObj || {};
  if (sourceObj == null)
    return destObj;
  do {
    props = Object.getOwnPropertyNames(sourceObj);
    i = props.length;
    while (i-- > 0) {
      prop = props[i];
      if ((!propFilter || propFilter(prop, sourceObj, destObj)) && !merged[prop]) {
        destObj[prop] = sourceObj[prop];
        merged[prop] = true;
      }
    }
    sourceObj = filter !== false && getPrototypeOf(sourceObj);
  } while (sourceObj && (!filter || filter(sourceObj, destObj)) && sourceObj !== Object.prototype);
  return destObj;
};
const endsWith = (str, searchString, position) => {
  str = String(str);
  if (position === void 0 || position > str.length) {
    position = str.length;
  }
  position -= searchString.length;
  const lastIndex = str.indexOf(searchString, position);
  return lastIndex !== -1 && lastIndex === position;
};
const toArray = (thing) => {
  if (!thing)
    return null;
  if (isArray(thing))
    return thing;
  let i = thing.length;
  if (!isNumber(i))
    return null;
  const arr = new Array(i);
  while (i-- > 0) {
    arr[i] = thing[i];
  }
  return arr;
};
const isTypedArray = ((TypedArray) => {
  return (thing) => {
    return TypedArray && thing instanceof TypedArray;
  };
})(typeof Uint8Array !== "undefined" && getPrototypeOf(Uint8Array));
const forEachEntry = (obj, fn) => {
  const generator = obj && obj[Symbol.iterator];
  const iterator = generator.call(obj);
  let result;
  while ((result = iterator.next()) && !result.done) {
    const pair = result.value;
    fn.call(obj, pair[0], pair[1]);
  }
};
const matchAll = (regExp, str) => {
  let matches;
  const arr = [];
  while ((matches = regExp.exec(str)) !== null) {
    arr.push(matches);
  }
  return arr;
};
const isHTMLForm = kindOfTest("HTMLFormElement");
const toCamelCase = (str) => {
  return str.toLowerCase().replace(/[-_\s]([a-z\d])(\w*)/g, function replacer(m, p1, p2) {
    return p1.toUpperCase() + p2;
  });
};
const hasOwnProperty = (({hasOwnProperty: hasOwnProperty2}) => (obj, prop) => hasOwnProperty2.call(obj, prop))(Object.prototype);
const isRegExp = kindOfTest("RegExp");
const reduceDescriptors = (obj, reducer) => {
  const descriptors = Object.getOwnPropertyDescriptors(obj);
  const reducedDescriptors = {};
  forEach(descriptors, (descriptor, name) => {
    if (reducer(descriptor, name, obj) !== false) {
      reducedDescriptors[name] = descriptor;
    }
  });
  Object.defineProperties(obj, reducedDescriptors);
};
const freezeMethods = (obj) => {
  reduceDescriptors(obj, (descriptor, name) => {
    if (isFunction(obj) && ["arguments", "caller", "callee"].indexOf(name) !== -1) {
      return false;
    }
    const value = obj[name];
    if (!isFunction(value))
      return;
    descriptor.enumerable = false;
    if ("writable" in descriptor) {
      descriptor.writable = false;
      return;
    }
    if (!descriptor.set) {
      descriptor.set = () => {
        throw Error("Can not rewrite read-only method '" + name + "'");
      };
    }
  });
};
const toObjectSet = (arrayOrString, delimiter) => {
  const obj = {};
  const define = (arr) => {
    arr.forEach((value) => {
      obj[value] = true;
    });
  };
  isArray(arrayOrString) ? define(arrayOrString) : define(String(arrayOrString).split(delimiter));
  return obj;
};
const noop$1 = () => {
};
const toFiniteNumber = (value, defaultValue) => {
  value = +value;
  return Number.isFinite(value) ? value : defaultValue;
};
const ALPHA = "abcdefghijklmnopqrstuvwxyz";
const DIGIT = "0123456789";
const ALPHABET = {
  DIGIT,
  ALPHA,
  ALPHA_DIGIT: ALPHA + ALPHA.toUpperCase() + DIGIT
};
const generateString = (size = 16, alphabet = ALPHABET.ALPHA_DIGIT) => {
  let str = "";
  const {length} = alphabet;
  while (size--) {
    str += alphabet[Math.random() * length | 0];
  }
  return str;
};
function isSpecCompliantForm(thing) {
  return !!(thing && isFunction(thing.append) && thing[Symbol.toStringTag] === "FormData" && thing[Symbol.iterator]);
}
const toJSONObject = (obj) => {
  const stack = new Array(10);
  const visit = (source, i) => {
    if (isObject(source)) {
      if (stack.indexOf(source) >= 0) {
        return;
      }
      if (!("toJSON" in source)) {
        stack[i] = source;
        const target = isArray(source) ? [] : {};
        forEach(source, (value, key) => {
          const reducedValue = visit(value, i + 1);
          !isUndefined(reducedValue) && (target[key] = reducedValue);
        });
        stack[i] = void 0;
        return target;
      }
    }
    return source;
  };
  return visit(obj, 0);
};
const isAsyncFn = kindOfTest("AsyncFunction");
const isThenable = (thing) => thing && (isObject(thing) || isFunction(thing)) && isFunction(thing.then) && isFunction(thing.catch);
var utils = {
  isArray,
  isArrayBuffer,
  isBuffer,
  isFormData,
  isArrayBufferView,
  isString,
  isNumber,
  isBoolean,
  isObject,
  isPlainObject,
  isUndefined,
  isDate,
  isFile,
  isBlob,
  isRegExp,
  isFunction,
  isStream,
  isURLSearchParams,
  isTypedArray,
  isFileList,
  forEach,
  merge,
  extend,
  trim,
  stripBOM,
  inherits,
  toFlatObject,
  kindOf,
  kindOfTest,
  endsWith,
  toArray,
  forEachEntry,
  matchAll,
  isHTMLForm,
  hasOwnProperty,
  hasOwnProp: hasOwnProperty,
  reduceDescriptors,
  freezeMethods,
  toObjectSet,
  toCamelCase,
  noop: noop$1,
  toFiniteNumber,
  findKey,
  global: _global,
  isContextDefined,
  ALPHABET,
  generateString,
  isSpecCompliantForm,
  toJSONObject,
  isAsyncFn,
  isThenable
};

function AxiosError(message, code, config, request, response) {
  Error.call(this);
  if (Error.captureStackTrace) {
    Error.captureStackTrace(this, this.constructor);
  } else {
    this.stack = new Error().stack;
  }
  this.message = message;
  this.name = "AxiosError";
  code && (this.code = code);
  config && (this.config = config);
  request && (this.request = request);
  response && (this.response = response);
}
utils.inherits(AxiosError, Error, {
  toJSON: function toJSON() {
    return {
      message: this.message,
      name: this.name,
      description: this.description,
      number: this.number,
      fileName: this.fileName,
      lineNumber: this.lineNumber,
      columnNumber: this.columnNumber,
      stack: this.stack,
      config: utils.toJSONObject(this.config),
      code: this.code,
      status: this.response && this.response.status ? this.response.status : null
    };
  }
});
const prototype = AxiosError.prototype;
const descriptors = {};
[
  "ERR_BAD_OPTION_VALUE",
  "ERR_BAD_OPTION",
  "ECONNABORTED",
  "ETIMEDOUT",
  "ERR_NETWORK",
  "ERR_FR_TOO_MANY_REDIRECTS",
  "ERR_DEPRECATED",
  "ERR_BAD_RESPONSE",
  "ERR_BAD_REQUEST",
  "ERR_CANCELED",
  "ERR_NOT_SUPPORT",
  "ERR_INVALID_URL"
].forEach((code) => {
  descriptors[code] = {value: code};
});
Object.defineProperties(AxiosError, descriptors);
Object.defineProperty(prototype, "isAxiosError", {value: true});
AxiosError.from = (error, code, config, request, response, customProps) => {
  const axiosError = Object.create(prototype);
  utils.toFlatObject(error, axiosError, function filter(obj) {
    return obj !== Error.prototype;
  }, (prop) => {
    return prop !== "isAxiosError";
  });
  AxiosError.call(axiosError, error.message, code, config, request, response);
  axiosError.cause = error;
  axiosError.name = error.name;
  customProps && Object.assign(axiosError, customProps);
  return axiosError;
};

var lookup = [];
var revLookup = [];
var Arr = typeof Uint8Array !== "undefined" ? Uint8Array : Array;
var inited = false;
function init$1() {
  inited = true;
  var code = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";
  for (var i = 0, len = code.length; i < len; ++i) {
    lookup[i] = code[i];
    revLookup[code.charCodeAt(i)] = i;
  }
  revLookup["-".charCodeAt(0)] = 62;
  revLookup["_".charCodeAt(0)] = 63;
}
function toByteArray(b64) {
  if (!inited) {
    init$1();
  }
  var i, j, l, tmp, placeHolders, arr;
  var len = b64.length;
  if (len % 4 > 0) {
    throw new Error("Invalid string. Length must be a multiple of 4");
  }
  placeHolders = b64[len - 2] === "=" ? 2 : b64[len - 1] === "=" ? 1 : 0;
  arr = new Arr(len * 3 / 4 - placeHolders);
  l = placeHolders > 0 ? len - 4 : len;
  var L = 0;
  for (i = 0, j = 0; i < l; i += 4, j += 3) {
    tmp = revLookup[b64.charCodeAt(i)] << 18 | revLookup[b64.charCodeAt(i + 1)] << 12 | revLookup[b64.charCodeAt(i + 2)] << 6 | revLookup[b64.charCodeAt(i + 3)];
    arr[L++] = tmp >> 16 & 255;
    arr[L++] = tmp >> 8 & 255;
    arr[L++] = tmp & 255;
  }
  if (placeHolders === 2) {
    tmp = revLookup[b64.charCodeAt(i)] << 2 | revLookup[b64.charCodeAt(i + 1)] >> 4;
    arr[L++] = tmp & 255;
  } else if (placeHolders === 1) {
    tmp = revLookup[b64.charCodeAt(i)] << 10 | revLookup[b64.charCodeAt(i + 1)] << 4 | revLookup[b64.charCodeAt(i + 2)] >> 2;
    arr[L++] = tmp >> 8 & 255;
    arr[L++] = tmp & 255;
  }
  return arr;
}
function tripletToBase64(num) {
  return lookup[num >> 18 & 63] + lookup[num >> 12 & 63] + lookup[num >> 6 & 63] + lookup[num & 63];
}
function encodeChunk(uint8, start, end) {
  var tmp;
  var output = [];
  for (var i = start; i < end; i += 3) {
    tmp = (uint8[i] << 16) + (uint8[i + 1] << 8) + uint8[i + 2];
    output.push(tripletToBase64(tmp));
  }
  return output.join("");
}
function fromByteArray(uint8) {
  if (!inited) {
    init$1();
  }
  var tmp;
  var len = uint8.length;
  var extraBytes = len % 3;
  var output = "";
  var parts = [];
  var maxChunkLength = 16383;
  for (var i = 0, len2 = len - extraBytes; i < len2; i += maxChunkLength) {
    parts.push(encodeChunk(uint8, i, i + maxChunkLength > len2 ? len2 : i + maxChunkLength));
  }
  if (extraBytes === 1) {
    tmp = uint8[len - 1];
    output += lookup[tmp >> 2];
    output += lookup[tmp << 4 & 63];
    output += "==";
  } else if (extraBytes === 2) {
    tmp = (uint8[len - 2] << 8) + uint8[len - 1];
    output += lookup[tmp >> 10];
    output += lookup[tmp >> 4 & 63];
    output += lookup[tmp << 2 & 63];
    output += "=";
  }
  parts.push(output);
  return parts.join("");
}
function read(buffer, offset, isLE, mLen, nBytes) {
  var e, m;
  var eLen = nBytes * 8 - mLen - 1;
  var eMax = (1 << eLen) - 1;
  var eBias = eMax >> 1;
  var nBits = -7;
  var i = isLE ? nBytes - 1 : 0;
  var d = isLE ? -1 : 1;
  var s = buffer[offset + i];
  i += d;
  e = s & (1 << -nBits) - 1;
  s >>= -nBits;
  nBits += eLen;
  for (; nBits > 0; e = e * 256 + buffer[offset + i], i += d, nBits -= 8) {
  }
  m = e & (1 << -nBits) - 1;
  e >>= -nBits;
  nBits += mLen;
  for (; nBits > 0; m = m * 256 + buffer[offset + i], i += d, nBits -= 8) {
  }
  if (e === 0) {
    e = 1 - eBias;
  } else if (e === eMax) {
    return m ? NaN : (s ? -1 : 1) * Infinity;
  } else {
    m = m + Math.pow(2, mLen);
    e = e - eBias;
  }
  return (s ? -1 : 1) * m * Math.pow(2, e - mLen);
}
function write(buffer, value, offset, isLE, mLen, nBytes) {
  var e, m, c;
  var eLen = nBytes * 8 - mLen - 1;
  var eMax = (1 << eLen) - 1;
  var eBias = eMax >> 1;
  var rt = mLen === 23 ? Math.pow(2, -24) - Math.pow(2, -77) : 0;
  var i = isLE ? 0 : nBytes - 1;
  var d = isLE ? 1 : -1;
  var s = value < 0 || value === 0 && 1 / value < 0 ? 1 : 0;
  value = Math.abs(value);
  if (isNaN(value) || value === Infinity) {
    m = isNaN(value) ? 1 : 0;
    e = eMax;
  } else {
    e = Math.floor(Math.log(value) / Math.LN2);
    if (value * (c = Math.pow(2, -e)) < 1) {
      e--;
      c *= 2;
    }
    if (e + eBias >= 1) {
      value += rt / c;
    } else {
      value += rt * Math.pow(2, 1 - eBias);
    }
    if (value * c >= 2) {
      e++;
      c /= 2;
    }
    if (e + eBias >= eMax) {
      m = 0;
      e = eMax;
    } else if (e + eBias >= 1) {
      m = (value * c - 1) * Math.pow(2, mLen);
      e = e + eBias;
    } else {
      m = value * Math.pow(2, eBias - 1) * Math.pow(2, mLen);
      e = 0;
    }
  }
  for (; mLen >= 8; buffer[offset + i] = m & 255, i += d, m /= 256, mLen -= 8) {
  }
  e = e << mLen | m;
  eLen += mLen;
  for (; eLen > 0; buffer[offset + i] = e & 255, i += d, e /= 256, eLen -= 8) {
  }
  buffer[offset + i - d] |= s * 128;
}
var toString$1 = {}.toString;
var isArray$1 = Array.isArray || function(arr) {
  return toString$1.call(arr) == "[object Array]";
};
/*!
 * The buffer module from node.js, for the browser.
 *
 * @author   Feross Aboukhadijeh <feross@feross.org> <http://feross.org>
 * @license  MIT
 */
var INSPECT_MAX_BYTES = 50;
Buffer.TYPED_ARRAY_SUPPORT = global$1.TYPED_ARRAY_SUPPORT !== void 0 ? global$1.TYPED_ARRAY_SUPPORT : true;
function kMaxLength() {
  return Buffer.TYPED_ARRAY_SUPPORT ? 2147483647 : 1073741823;
}
function createBuffer(that, length) {
  if (kMaxLength() < length) {
    throw new RangeError("Invalid typed array length");
  }
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    that = new Uint8Array(length);
    that.__proto__ = Buffer.prototype;
  } else {
    if (that === null) {
      that = new Buffer(length);
    }
    that.length = length;
  }
  return that;
}
function Buffer(arg, encodingOrOffset, length) {
  if (!Buffer.TYPED_ARRAY_SUPPORT && !(this instanceof Buffer)) {
    return new Buffer(arg, encodingOrOffset, length);
  }
  if (typeof arg === "number") {
    if (typeof encodingOrOffset === "string") {
      throw new Error("If encoding is specified then the first argument must be a string");
    }
    return allocUnsafe(this, arg);
  }
  return from(this, arg, encodingOrOffset, length);
}
Buffer.poolSize = 8192;
Buffer._augment = function(arr) {
  arr.__proto__ = Buffer.prototype;
  return arr;
};
function from(that, value, encodingOrOffset, length) {
  if (typeof value === "number") {
    throw new TypeError('"value" argument must not be a number');
  }
  if (typeof ArrayBuffer !== "undefined" && value instanceof ArrayBuffer) {
    return fromArrayBuffer(that, value, encodingOrOffset, length);
  }
  if (typeof value === "string") {
    return fromString(that, value, encodingOrOffset);
  }
  return fromObject(that, value);
}
Buffer.from = function(value, encodingOrOffset, length) {
  return from(null, value, encodingOrOffset, length);
};
if (Buffer.TYPED_ARRAY_SUPPORT) {
  Buffer.prototype.__proto__ = Uint8Array.prototype;
  Buffer.__proto__ = Uint8Array;
}
function assertSize(size) {
  if (typeof size !== "number") {
    throw new TypeError('"size" argument must be a number');
  } else if (size < 0) {
    throw new RangeError('"size" argument must not be negative');
  }
}
function alloc(that, size, fill2, encoding) {
  assertSize(size);
  if (size <= 0) {
    return createBuffer(that, size);
  }
  if (fill2 !== void 0) {
    return typeof encoding === "string" ? createBuffer(that, size).fill(fill2, encoding) : createBuffer(that, size).fill(fill2);
  }
  return createBuffer(that, size);
}
Buffer.alloc = function(size, fill2, encoding) {
  return alloc(null, size, fill2, encoding);
};
function allocUnsafe(that, size) {
  assertSize(size);
  that = createBuffer(that, size < 0 ? 0 : checked(size) | 0);
  if (!Buffer.TYPED_ARRAY_SUPPORT) {
    for (var i = 0; i < size; ++i) {
      that[i] = 0;
    }
  }
  return that;
}
Buffer.allocUnsafe = function(size) {
  return allocUnsafe(null, size);
};
Buffer.allocUnsafeSlow = function(size) {
  return allocUnsafe(null, size);
};
function fromString(that, string, encoding) {
  if (typeof encoding !== "string" || encoding === "") {
    encoding = "utf8";
  }
  if (!Buffer.isEncoding(encoding)) {
    throw new TypeError('"encoding" must be a valid string encoding');
  }
  var length = byteLength(string, encoding) | 0;
  that = createBuffer(that, length);
  var actual = that.write(string, encoding);
  if (actual !== length) {
    that = that.slice(0, actual);
  }
  return that;
}
function fromArrayLike(that, array) {
  var length = array.length < 0 ? 0 : checked(array.length) | 0;
  that = createBuffer(that, length);
  for (var i = 0; i < length; i += 1) {
    that[i] = array[i] & 255;
  }
  return that;
}
function fromArrayBuffer(that, array, byteOffset, length) {
  array.byteLength;
  if (byteOffset < 0 || array.byteLength < byteOffset) {
    throw new RangeError("'offset' is out of bounds");
  }
  if (array.byteLength < byteOffset + (length || 0)) {
    throw new RangeError("'length' is out of bounds");
  }
  if (byteOffset === void 0 && length === void 0) {
    array = new Uint8Array(array);
  } else if (length === void 0) {
    array = new Uint8Array(array, byteOffset);
  } else {
    array = new Uint8Array(array, byteOffset, length);
  }
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    that = array;
    that.__proto__ = Buffer.prototype;
  } else {
    that = fromArrayLike(that, array);
  }
  return that;
}
function fromObject(that, obj) {
  if (internalIsBuffer(obj)) {
    var len = checked(obj.length) | 0;
    that = createBuffer(that, len);
    if (that.length === 0) {
      return that;
    }
    obj.copy(that, 0, 0, len);
    return that;
  }
  if (obj) {
    if (typeof ArrayBuffer !== "undefined" && obj.buffer instanceof ArrayBuffer || "length" in obj) {
      if (typeof obj.length !== "number" || isnan(obj.length)) {
        return createBuffer(that, 0);
      }
      return fromArrayLike(that, obj);
    }
    if (obj.type === "Buffer" && isArray$1(obj.data)) {
      return fromArrayLike(that, obj.data);
    }
  }
  throw new TypeError("First argument must be a string, Buffer, ArrayBuffer, Array, or array-like object.");
}
function checked(length) {
  if (length >= kMaxLength()) {
    throw new RangeError("Attempt to allocate Buffer larger than maximum size: 0x" + kMaxLength().toString(16) + " bytes");
  }
  return length | 0;
}
Buffer.isBuffer = isBuffer$1;
function internalIsBuffer(b) {
  return !!(b != null && b._isBuffer);
}
Buffer.compare = function compare(a, b) {
  if (!internalIsBuffer(a) || !internalIsBuffer(b)) {
    throw new TypeError("Arguments must be Buffers");
  }
  if (a === b)
    return 0;
  var x = a.length;
  var y = b.length;
  for (var i = 0, len = Math.min(x, y); i < len; ++i) {
    if (a[i] !== b[i]) {
      x = a[i];
      y = b[i];
      break;
    }
  }
  if (x < y)
    return -1;
  if (y < x)
    return 1;
  return 0;
};
Buffer.isEncoding = function isEncoding(encoding) {
  switch (String(encoding).toLowerCase()) {
    case "hex":
    case "utf8":
    case "utf-8":
    case "ascii":
    case "latin1":
    case "binary":
    case "base64":
    case "ucs2":
    case "ucs-2":
    case "utf16le":
    case "utf-16le":
      return true;
    default:
      return false;
  }
};
Buffer.concat = function concat(list, length) {
  if (!isArray$1(list)) {
    throw new TypeError('"list" argument must be an Array of Buffers');
  }
  if (list.length === 0) {
    return Buffer.alloc(0);
  }
  var i;
  if (length === void 0) {
    length = 0;
    for (i = 0; i < list.length; ++i) {
      length += list[i].length;
    }
  }
  var buffer = Buffer.allocUnsafe(length);
  var pos = 0;
  for (i = 0; i < list.length; ++i) {
    var buf = list[i];
    if (!internalIsBuffer(buf)) {
      throw new TypeError('"list" argument must be an Array of Buffers');
    }
    buf.copy(buffer, pos);
    pos += buf.length;
  }
  return buffer;
};
function byteLength(string, encoding) {
  if (internalIsBuffer(string)) {
    return string.length;
  }
  if (typeof ArrayBuffer !== "undefined" && typeof ArrayBuffer.isView === "function" && (ArrayBuffer.isView(string) || string instanceof ArrayBuffer)) {
    return string.byteLength;
  }
  if (typeof string !== "string") {
    string = "" + string;
  }
  var len = string.length;
  if (len === 0)
    return 0;
  var loweredCase = false;
  for (; ; ) {
    switch (encoding) {
      case "ascii":
      case "latin1":
      case "binary":
        return len;
      case "utf8":
      case "utf-8":
      case void 0:
        return utf8ToBytes(string).length;
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return len * 2;
      case "hex":
        return len >>> 1;
      case "base64":
        return base64ToBytes(string).length;
      default:
        if (loweredCase)
          return utf8ToBytes(string).length;
        encoding = ("" + encoding).toLowerCase();
        loweredCase = true;
    }
  }
}
Buffer.byteLength = byteLength;
function slowToString(encoding, start, end) {
  var loweredCase = false;
  if (start === void 0 || start < 0) {
    start = 0;
  }
  if (start > this.length) {
    return "";
  }
  if (end === void 0 || end > this.length) {
    end = this.length;
  }
  if (end <= 0) {
    return "";
  }
  end >>>= 0;
  start >>>= 0;
  if (end <= start) {
    return "";
  }
  if (!encoding)
    encoding = "utf8";
  while (true) {
    switch (encoding) {
      case "hex":
        return hexSlice(this, start, end);
      case "utf8":
      case "utf-8":
        return utf8Slice(this, start, end);
      case "ascii":
        return asciiSlice(this, start, end);
      case "latin1":
      case "binary":
        return latin1Slice(this, start, end);
      case "base64":
        return base64Slice(this, start, end);
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return utf16leSlice(this, start, end);
      default:
        if (loweredCase)
          throw new TypeError("Unknown encoding: " + encoding);
        encoding = (encoding + "").toLowerCase();
        loweredCase = true;
    }
  }
}
Buffer.prototype._isBuffer = true;
function swap(b, n, m) {
  var i = b[n];
  b[n] = b[m];
  b[m] = i;
}
Buffer.prototype.swap16 = function swap16() {
  var len = this.length;
  if (len % 2 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 16-bits");
  }
  for (var i = 0; i < len; i += 2) {
    swap(this, i, i + 1);
  }
  return this;
};
Buffer.prototype.swap32 = function swap32() {
  var len = this.length;
  if (len % 4 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 32-bits");
  }
  for (var i = 0; i < len; i += 4) {
    swap(this, i, i + 3);
    swap(this, i + 1, i + 2);
  }
  return this;
};
Buffer.prototype.swap64 = function swap64() {
  var len = this.length;
  if (len % 8 !== 0) {
    throw new RangeError("Buffer size must be a multiple of 64-bits");
  }
  for (var i = 0; i < len; i += 8) {
    swap(this, i, i + 7);
    swap(this, i + 1, i + 6);
    swap(this, i + 2, i + 5);
    swap(this, i + 3, i + 4);
  }
  return this;
};
Buffer.prototype.toString = function toString2() {
  var length = this.length | 0;
  if (length === 0)
    return "";
  if (arguments.length === 0)
    return utf8Slice(this, 0, length);
  return slowToString.apply(this, arguments);
};
Buffer.prototype.equals = function equals(b) {
  if (!internalIsBuffer(b))
    throw new TypeError("Argument must be a Buffer");
  if (this === b)
    return true;
  return Buffer.compare(this, b) === 0;
};
Buffer.prototype.inspect = function inspect() {
  var str = "";
  var max = INSPECT_MAX_BYTES;
  if (this.length > 0) {
    str = this.toString("hex", 0, max).match(/.{2}/g).join(" ");
    if (this.length > max)
      str += " ... ";
  }
  return "<Buffer " + str + ">";
};
Buffer.prototype.compare = function compare2(target, start, end, thisStart, thisEnd) {
  if (!internalIsBuffer(target)) {
    throw new TypeError("Argument must be a Buffer");
  }
  if (start === void 0) {
    start = 0;
  }
  if (end === void 0) {
    end = target ? target.length : 0;
  }
  if (thisStart === void 0) {
    thisStart = 0;
  }
  if (thisEnd === void 0) {
    thisEnd = this.length;
  }
  if (start < 0 || end > target.length || thisStart < 0 || thisEnd > this.length) {
    throw new RangeError("out of range index");
  }
  if (thisStart >= thisEnd && start >= end) {
    return 0;
  }
  if (thisStart >= thisEnd) {
    return -1;
  }
  if (start >= end) {
    return 1;
  }
  start >>>= 0;
  end >>>= 0;
  thisStart >>>= 0;
  thisEnd >>>= 0;
  if (this === target)
    return 0;
  var x = thisEnd - thisStart;
  var y = end - start;
  var len = Math.min(x, y);
  var thisCopy = this.slice(thisStart, thisEnd);
  var targetCopy = target.slice(start, end);
  for (var i = 0; i < len; ++i) {
    if (thisCopy[i] !== targetCopy[i]) {
      x = thisCopy[i];
      y = targetCopy[i];
      break;
    }
  }
  if (x < y)
    return -1;
  if (y < x)
    return 1;
  return 0;
};
function bidirectionalIndexOf(buffer, val, byteOffset, encoding, dir) {
  if (buffer.length === 0)
    return -1;
  if (typeof byteOffset === "string") {
    encoding = byteOffset;
    byteOffset = 0;
  } else if (byteOffset > 2147483647) {
    byteOffset = 2147483647;
  } else if (byteOffset < -2147483648) {
    byteOffset = -2147483648;
  }
  byteOffset = +byteOffset;
  if (isNaN(byteOffset)) {
    byteOffset = dir ? 0 : buffer.length - 1;
  }
  if (byteOffset < 0)
    byteOffset = buffer.length + byteOffset;
  if (byteOffset >= buffer.length) {
    if (dir)
      return -1;
    else
      byteOffset = buffer.length - 1;
  } else if (byteOffset < 0) {
    if (dir)
      byteOffset = 0;
    else
      return -1;
  }
  if (typeof val === "string") {
    val = Buffer.from(val, encoding);
  }
  if (internalIsBuffer(val)) {
    if (val.length === 0) {
      return -1;
    }
    return arrayIndexOf(buffer, val, byteOffset, encoding, dir);
  } else if (typeof val === "number") {
    val = val & 255;
    if (Buffer.TYPED_ARRAY_SUPPORT && typeof Uint8Array.prototype.indexOf === "function") {
      if (dir) {
        return Uint8Array.prototype.indexOf.call(buffer, val, byteOffset);
      } else {
        return Uint8Array.prototype.lastIndexOf.call(buffer, val, byteOffset);
      }
    }
    return arrayIndexOf(buffer, [val], byteOffset, encoding, dir);
  }
  throw new TypeError("val must be string, number or Buffer");
}
function arrayIndexOf(arr, val, byteOffset, encoding, dir) {
  var indexSize = 1;
  var arrLength = arr.length;
  var valLength = val.length;
  if (encoding !== void 0) {
    encoding = String(encoding).toLowerCase();
    if (encoding === "ucs2" || encoding === "ucs-2" || encoding === "utf16le" || encoding === "utf-16le") {
      if (arr.length < 2 || val.length < 2) {
        return -1;
      }
      indexSize = 2;
      arrLength /= 2;
      valLength /= 2;
      byteOffset /= 2;
    }
  }
  function read2(buf, i2) {
    if (indexSize === 1) {
      return buf[i2];
    } else {
      return buf.readUInt16BE(i2 * indexSize);
    }
  }
  var i;
  if (dir) {
    var foundIndex = -1;
    for (i = byteOffset; i < arrLength; i++) {
      if (read2(arr, i) === read2(val, foundIndex === -1 ? 0 : i - foundIndex)) {
        if (foundIndex === -1)
          foundIndex = i;
        if (i - foundIndex + 1 === valLength)
          return foundIndex * indexSize;
      } else {
        if (foundIndex !== -1)
          i -= i - foundIndex;
        foundIndex = -1;
      }
    }
  } else {
    if (byteOffset + valLength > arrLength)
      byteOffset = arrLength - valLength;
    for (i = byteOffset; i >= 0; i--) {
      var found = true;
      for (var j = 0; j < valLength; j++) {
        if (read2(arr, i + j) !== read2(val, j)) {
          found = false;
          break;
        }
      }
      if (found)
        return i;
    }
  }
  return -1;
}
Buffer.prototype.includes = function includes(val, byteOffset, encoding) {
  return this.indexOf(val, byteOffset, encoding) !== -1;
};
Buffer.prototype.indexOf = function indexOf(val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, true);
};
Buffer.prototype.lastIndexOf = function lastIndexOf(val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, false);
};
function hexWrite(buf, string, offset, length) {
  offset = Number(offset) || 0;
  var remaining = buf.length - offset;
  if (!length) {
    length = remaining;
  } else {
    length = Number(length);
    if (length > remaining) {
      length = remaining;
    }
  }
  var strLen = string.length;
  if (strLen % 2 !== 0)
    throw new TypeError("Invalid hex string");
  if (length > strLen / 2) {
    length = strLen / 2;
  }
  for (var i = 0; i < length; ++i) {
    var parsed = parseInt(string.substr(i * 2, 2), 16);
    if (isNaN(parsed))
      return i;
    buf[offset + i] = parsed;
  }
  return i;
}
function utf8Write(buf, string, offset, length) {
  return blitBuffer(utf8ToBytes(string, buf.length - offset), buf, offset, length);
}
function asciiWrite(buf, string, offset, length) {
  return blitBuffer(asciiToBytes(string), buf, offset, length);
}
function latin1Write(buf, string, offset, length) {
  return asciiWrite(buf, string, offset, length);
}
function base64Write(buf, string, offset, length) {
  return blitBuffer(base64ToBytes(string), buf, offset, length);
}
function ucs2Write(buf, string, offset, length) {
  return blitBuffer(utf16leToBytes(string, buf.length - offset), buf, offset, length);
}
Buffer.prototype.write = function write2(string, offset, length, encoding) {
  if (offset === void 0) {
    encoding = "utf8";
    length = this.length;
    offset = 0;
  } else if (length === void 0 && typeof offset === "string") {
    encoding = offset;
    length = this.length;
    offset = 0;
  } else if (isFinite(offset)) {
    offset = offset | 0;
    if (isFinite(length)) {
      length = length | 0;
      if (encoding === void 0)
        encoding = "utf8";
    } else {
      encoding = length;
      length = void 0;
    }
  } else {
    throw new Error("Buffer.write(string, encoding, offset[, length]) is no longer supported");
  }
  var remaining = this.length - offset;
  if (length === void 0 || length > remaining)
    length = remaining;
  if (string.length > 0 && (length < 0 || offset < 0) || offset > this.length) {
    throw new RangeError("Attempt to write outside buffer bounds");
  }
  if (!encoding)
    encoding = "utf8";
  var loweredCase = false;
  for (; ; ) {
    switch (encoding) {
      case "hex":
        return hexWrite(this, string, offset, length);
      case "utf8":
      case "utf-8":
        return utf8Write(this, string, offset, length);
      case "ascii":
        return asciiWrite(this, string, offset, length);
      case "latin1":
      case "binary":
        return latin1Write(this, string, offset, length);
      case "base64":
        return base64Write(this, string, offset, length);
      case "ucs2":
      case "ucs-2":
      case "utf16le":
      case "utf-16le":
        return ucs2Write(this, string, offset, length);
      default:
        if (loweredCase)
          throw new TypeError("Unknown encoding: " + encoding);
        encoding = ("" + encoding).toLowerCase();
        loweredCase = true;
    }
  }
};
Buffer.prototype.toJSON = function toJSON() {
  return {
    type: "Buffer",
    data: Array.prototype.slice.call(this._arr || this, 0)
  };
};
function base64Slice(buf, start, end) {
  if (start === 0 && end === buf.length) {
    return fromByteArray(buf);
  } else {
    return fromByteArray(buf.slice(start, end));
  }
}
function utf8Slice(buf, start, end) {
  end = Math.min(buf.length, end);
  var res = [];
  var i = start;
  while (i < end) {
    var firstByte = buf[i];
    var codePoint = null;
    var bytesPerSequence = firstByte > 239 ? 4 : firstByte > 223 ? 3 : firstByte > 191 ? 2 : 1;
    if (i + bytesPerSequence <= end) {
      var secondByte, thirdByte, fourthByte, tempCodePoint;
      switch (bytesPerSequence) {
        case 1:
          if (firstByte < 128) {
            codePoint = firstByte;
          }
          break;
        case 2:
          secondByte = buf[i + 1];
          if ((secondByte & 192) === 128) {
            tempCodePoint = (firstByte & 31) << 6 | secondByte & 63;
            if (tempCodePoint > 127) {
              codePoint = tempCodePoint;
            }
          }
          break;
        case 3:
          secondByte = buf[i + 1];
          thirdByte = buf[i + 2];
          if ((secondByte & 192) === 128 && (thirdByte & 192) === 128) {
            tempCodePoint = (firstByte & 15) << 12 | (secondByte & 63) << 6 | thirdByte & 63;
            if (tempCodePoint > 2047 && (tempCodePoint < 55296 || tempCodePoint > 57343)) {
              codePoint = tempCodePoint;
            }
          }
          break;
        case 4:
          secondByte = buf[i + 1];
          thirdByte = buf[i + 2];
          fourthByte = buf[i + 3];
          if ((secondByte & 192) === 128 && (thirdByte & 192) === 128 && (fourthByte & 192) === 128) {
            tempCodePoint = (firstByte & 15) << 18 | (secondByte & 63) << 12 | (thirdByte & 63) << 6 | fourthByte & 63;
            if (tempCodePoint > 65535 && tempCodePoint < 1114112) {
              codePoint = tempCodePoint;
            }
          }
      }
    }
    if (codePoint === null) {
      codePoint = 65533;
      bytesPerSequence = 1;
    } else if (codePoint > 65535) {
      codePoint -= 65536;
      res.push(codePoint >>> 10 & 1023 | 55296);
      codePoint = 56320 | codePoint & 1023;
    }
    res.push(codePoint);
    i += bytesPerSequence;
  }
  return decodeCodePointsArray(res);
}
var MAX_ARGUMENTS_LENGTH = 4096;
function decodeCodePointsArray(codePoints) {
  var len = codePoints.length;
  if (len <= MAX_ARGUMENTS_LENGTH) {
    return String.fromCharCode.apply(String, codePoints);
  }
  var res = "";
  var i = 0;
  while (i < len) {
    res += String.fromCharCode.apply(String, codePoints.slice(i, i += MAX_ARGUMENTS_LENGTH));
  }
  return res;
}
function asciiSlice(buf, start, end) {
  var ret = "";
  end = Math.min(buf.length, end);
  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i] & 127);
  }
  return ret;
}
function latin1Slice(buf, start, end) {
  var ret = "";
  end = Math.min(buf.length, end);
  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i]);
  }
  return ret;
}
function hexSlice(buf, start, end) {
  var len = buf.length;
  if (!start || start < 0)
    start = 0;
  if (!end || end < 0 || end > len)
    end = len;
  var out = "";
  for (var i = start; i < end; ++i) {
    out += toHex(buf[i]);
  }
  return out;
}
function utf16leSlice(buf, start, end) {
  var bytes = buf.slice(start, end);
  var res = "";
  for (var i = 0; i < bytes.length; i += 2) {
    res += String.fromCharCode(bytes[i] + bytes[i + 1] * 256);
  }
  return res;
}
Buffer.prototype.slice = function slice(start, end) {
  var len = this.length;
  start = ~~start;
  end = end === void 0 ? len : ~~end;
  if (start < 0) {
    start += len;
    if (start < 0)
      start = 0;
  } else if (start > len) {
    start = len;
  }
  if (end < 0) {
    end += len;
    if (end < 0)
      end = 0;
  } else if (end > len) {
    end = len;
  }
  if (end < start)
    end = start;
  var newBuf;
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    newBuf = this.subarray(start, end);
    newBuf.__proto__ = Buffer.prototype;
  } else {
    var sliceLen = end - start;
    newBuf = new Buffer(sliceLen, void 0);
    for (var i = 0; i < sliceLen; ++i) {
      newBuf[i] = this[i + start];
    }
  }
  return newBuf;
};
function checkOffset(offset, ext, length) {
  if (offset % 1 !== 0 || offset < 0)
    throw new RangeError("offset is not uint");
  if (offset + ext > length)
    throw new RangeError("Trying to access beyond buffer length");
}
Buffer.prototype.readUIntLE = function readUIntLE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var val = this[offset];
  var mul = 1;
  var i = 0;
  while (++i < byteLength2 && (mul *= 256)) {
    val += this[offset + i] * mul;
  }
  return val;
};
Buffer.prototype.readUIntBE = function readUIntBE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    checkOffset(offset, byteLength2, this.length);
  }
  var val = this[offset + --byteLength2];
  var mul = 1;
  while (byteLength2 > 0 && (mul *= 256)) {
    val += this[offset + --byteLength2] * mul;
  }
  return val;
};
Buffer.prototype.readUInt8 = function readUInt8(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 1, this.length);
  return this[offset];
};
Buffer.prototype.readUInt16LE = function readUInt16LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  return this[offset] | this[offset + 1] << 8;
};
Buffer.prototype.readUInt16BE = function readUInt16BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  return this[offset] << 8 | this[offset + 1];
};
Buffer.prototype.readUInt32LE = function readUInt32LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return (this[offset] | this[offset + 1] << 8 | this[offset + 2] << 16) + this[offset + 3] * 16777216;
};
Buffer.prototype.readUInt32BE = function readUInt32BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] * 16777216 + (this[offset + 1] << 16 | this[offset + 2] << 8 | this[offset + 3]);
};
Buffer.prototype.readIntLE = function readIntLE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var val = this[offset];
  var mul = 1;
  var i = 0;
  while (++i < byteLength2 && (mul *= 256)) {
    val += this[offset + i] * mul;
  }
  mul *= 128;
  if (val >= mul)
    val -= Math.pow(2, 8 * byteLength2);
  return val;
};
Buffer.prototype.readIntBE = function readIntBE(offset, byteLength2, noAssert) {
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert)
    checkOffset(offset, byteLength2, this.length);
  var i = byteLength2;
  var mul = 1;
  var val = this[offset + --i];
  while (i > 0 && (mul *= 256)) {
    val += this[offset + --i] * mul;
  }
  mul *= 128;
  if (val >= mul)
    val -= Math.pow(2, 8 * byteLength2);
  return val;
};
Buffer.prototype.readInt8 = function readInt8(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 1, this.length);
  if (!(this[offset] & 128))
    return this[offset];
  return (255 - this[offset] + 1) * -1;
};
Buffer.prototype.readInt16LE = function readInt16LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  var val = this[offset] | this[offset + 1] << 8;
  return val & 32768 ? val | 4294901760 : val;
};
Buffer.prototype.readInt16BE = function readInt16BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 2, this.length);
  var val = this[offset + 1] | this[offset] << 8;
  return val & 32768 ? val | 4294901760 : val;
};
Buffer.prototype.readInt32LE = function readInt32LE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] | this[offset + 1] << 8 | this[offset + 2] << 16 | this[offset + 3] << 24;
};
Buffer.prototype.readInt32BE = function readInt32BE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return this[offset] << 24 | this[offset + 1] << 16 | this[offset + 2] << 8 | this[offset + 3];
};
Buffer.prototype.readFloatLE = function readFloatLE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return read(this, offset, true, 23, 4);
};
Buffer.prototype.readFloatBE = function readFloatBE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 4, this.length);
  return read(this, offset, false, 23, 4);
};
Buffer.prototype.readDoubleLE = function readDoubleLE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 8, this.length);
  return read(this, offset, true, 52, 8);
};
Buffer.prototype.readDoubleBE = function readDoubleBE(offset, noAssert) {
  if (!noAssert)
    checkOffset(offset, 8, this.length);
  return read(this, offset, false, 52, 8);
};
function checkInt(buf, value, offset, ext, max, min) {
  if (!internalIsBuffer(buf))
    throw new TypeError('"buffer" argument must be a Buffer instance');
  if (value > max || value < min)
    throw new RangeError('"value" argument is out of bounds');
  if (offset + ext > buf.length)
    throw new RangeError("Index out of range");
}
Buffer.prototype.writeUIntLE = function writeUIntLE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength2) - 1;
    checkInt(this, value, offset, byteLength2, maxBytes, 0);
  }
  var mul = 1;
  var i = 0;
  this[offset] = value & 255;
  while (++i < byteLength2 && (mul *= 256)) {
    this[offset + i] = value / mul & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeUIntBE = function writeUIntBE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  byteLength2 = byteLength2 | 0;
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength2) - 1;
    checkInt(this, value, offset, byteLength2, maxBytes, 0);
  }
  var i = byteLength2 - 1;
  var mul = 1;
  this[offset + i] = value & 255;
  while (--i >= 0 && (mul *= 256)) {
    this[offset + i] = value / mul & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeUInt8 = function writeUInt8(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 1, 255, 0);
  if (!Buffer.TYPED_ARRAY_SUPPORT)
    value = Math.floor(value);
  this[offset] = value & 255;
  return offset + 1;
};
function objectWriteUInt16(buf, value, offset, littleEndian) {
  if (value < 0)
    value = 65535 + value + 1;
  for (var i = 0, j = Math.min(buf.length - offset, 2); i < j; ++i) {
    buf[offset + i] = (value & 255 << 8 * (littleEndian ? i : 1 - i)) >>> (littleEndian ? i : 1 - i) * 8;
  }
}
Buffer.prototype.writeUInt16LE = function writeUInt16LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 65535, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
  } else {
    objectWriteUInt16(this, value, offset, true);
  }
  return offset + 2;
};
Buffer.prototype.writeUInt16BE = function writeUInt16BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 65535, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 8;
    this[offset + 1] = value & 255;
  } else {
    objectWriteUInt16(this, value, offset, false);
  }
  return offset + 2;
};
function objectWriteUInt32(buf, value, offset, littleEndian) {
  if (value < 0)
    value = 4294967295 + value + 1;
  for (var i = 0, j = Math.min(buf.length - offset, 4); i < j; ++i) {
    buf[offset + i] = value >>> (littleEndian ? i : 3 - i) * 8 & 255;
  }
}
Buffer.prototype.writeUInt32LE = function writeUInt32LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 4294967295, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset + 3] = value >>> 24;
    this[offset + 2] = value >>> 16;
    this[offset + 1] = value >>> 8;
    this[offset] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, true);
  }
  return offset + 4;
};
Buffer.prototype.writeUInt32BE = function writeUInt32BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 4294967295, 0);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 24;
    this[offset + 1] = value >>> 16;
    this[offset + 2] = value >>> 8;
    this[offset + 3] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, false);
  }
  return offset + 4;
};
Buffer.prototype.writeIntLE = function writeIntLE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert) {
    var limit = Math.pow(2, 8 * byteLength2 - 1);
    checkInt(this, value, offset, byteLength2, limit - 1, -limit);
  }
  var i = 0;
  var mul = 1;
  var sub = 0;
  this[offset] = value & 255;
  while (++i < byteLength2 && (mul *= 256)) {
    if (value < 0 && sub === 0 && this[offset + i - 1] !== 0) {
      sub = 1;
    }
    this[offset + i] = (value / mul >> 0) - sub & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeIntBE = function writeIntBE(value, offset, byteLength2, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert) {
    var limit = Math.pow(2, 8 * byteLength2 - 1);
    checkInt(this, value, offset, byteLength2, limit - 1, -limit);
  }
  var i = byteLength2 - 1;
  var mul = 1;
  var sub = 0;
  this[offset + i] = value & 255;
  while (--i >= 0 && (mul *= 256)) {
    if (value < 0 && sub === 0 && this[offset + i + 1] !== 0) {
      sub = 1;
    }
    this[offset + i] = (value / mul >> 0) - sub & 255;
  }
  return offset + byteLength2;
};
Buffer.prototype.writeInt8 = function writeInt8(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 1, 127, -128);
  if (!Buffer.TYPED_ARRAY_SUPPORT)
    value = Math.floor(value);
  if (value < 0)
    value = 255 + value + 1;
  this[offset] = value & 255;
  return offset + 1;
};
Buffer.prototype.writeInt16LE = function writeInt16LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 32767, -32768);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
  } else {
    objectWriteUInt16(this, value, offset, true);
  }
  return offset + 2;
};
Buffer.prototype.writeInt16BE = function writeInt16BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 2, 32767, -32768);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 8;
    this[offset + 1] = value & 255;
  } else {
    objectWriteUInt16(this, value, offset, false);
  }
  return offset + 2;
};
Buffer.prototype.writeInt32LE = function writeInt32LE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 2147483647, -2147483648);
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value & 255;
    this[offset + 1] = value >>> 8;
    this[offset + 2] = value >>> 16;
    this[offset + 3] = value >>> 24;
  } else {
    objectWriteUInt32(this, value, offset, true);
  }
  return offset + 4;
};
Buffer.prototype.writeInt32BE = function writeInt32BE(value, offset, noAssert) {
  value = +value;
  offset = offset | 0;
  if (!noAssert)
    checkInt(this, value, offset, 4, 2147483647, -2147483648);
  if (value < 0)
    value = 4294967295 + value + 1;
  if (Buffer.TYPED_ARRAY_SUPPORT) {
    this[offset] = value >>> 24;
    this[offset + 1] = value >>> 16;
    this[offset + 2] = value >>> 8;
    this[offset + 3] = value & 255;
  } else {
    objectWriteUInt32(this, value, offset, false);
  }
  return offset + 4;
};
function checkIEEE754(buf, value, offset, ext, max, min) {
  if (offset + ext > buf.length)
    throw new RangeError("Index out of range");
  if (offset < 0)
    throw new RangeError("Index out of range");
}
function writeFloat(buf, value, offset, littleEndian, noAssert) {
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 4);
  }
  write(buf, value, offset, littleEndian, 23, 4);
  return offset + 4;
}
Buffer.prototype.writeFloatLE = function writeFloatLE(value, offset, noAssert) {
  return writeFloat(this, value, offset, true, noAssert);
};
Buffer.prototype.writeFloatBE = function writeFloatBE(value, offset, noAssert) {
  return writeFloat(this, value, offset, false, noAssert);
};
function writeDouble(buf, value, offset, littleEndian, noAssert) {
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 8);
  }
  write(buf, value, offset, littleEndian, 52, 8);
  return offset + 8;
}
Buffer.prototype.writeDoubleLE = function writeDoubleLE(value, offset, noAssert) {
  return writeDouble(this, value, offset, true, noAssert);
};
Buffer.prototype.writeDoubleBE = function writeDoubleBE(value, offset, noAssert) {
  return writeDouble(this, value, offset, false, noAssert);
};
Buffer.prototype.copy = function copy(target, targetStart, start, end) {
  if (!start)
    start = 0;
  if (!end && end !== 0)
    end = this.length;
  if (targetStart >= target.length)
    targetStart = target.length;
  if (!targetStart)
    targetStart = 0;
  if (end > 0 && end < start)
    end = start;
  if (end === start)
    return 0;
  if (target.length === 0 || this.length === 0)
    return 0;
  if (targetStart < 0) {
    throw new RangeError("targetStart out of bounds");
  }
  if (start < 0 || start >= this.length)
    throw new RangeError("sourceStart out of bounds");
  if (end < 0)
    throw new RangeError("sourceEnd out of bounds");
  if (end > this.length)
    end = this.length;
  if (target.length - targetStart < end - start) {
    end = target.length - targetStart + start;
  }
  var len = end - start;
  var i;
  if (this === target && start < targetStart && targetStart < end) {
    for (i = len - 1; i >= 0; --i) {
      target[i + targetStart] = this[i + start];
    }
  } else if (len < 1e3 || !Buffer.TYPED_ARRAY_SUPPORT) {
    for (i = 0; i < len; ++i) {
      target[i + targetStart] = this[i + start];
    }
  } else {
    Uint8Array.prototype.set.call(target, this.subarray(start, start + len), targetStart);
  }
  return len;
};
Buffer.prototype.fill = function fill(val, start, end, encoding) {
  if (typeof val === "string") {
    if (typeof start === "string") {
      encoding = start;
      start = 0;
      end = this.length;
    } else if (typeof end === "string") {
      encoding = end;
      end = this.length;
    }
    if (val.length === 1) {
      var code = val.charCodeAt(0);
      if (code < 256) {
        val = code;
      }
    }
    if (encoding !== void 0 && typeof encoding !== "string") {
      throw new TypeError("encoding must be a string");
    }
    if (typeof encoding === "string" && !Buffer.isEncoding(encoding)) {
      throw new TypeError("Unknown encoding: " + encoding);
    }
  } else if (typeof val === "number") {
    val = val & 255;
  }
  if (start < 0 || this.length < start || this.length < end) {
    throw new RangeError("Out of range index");
  }
  if (end <= start) {
    return this;
  }
  start = start >>> 0;
  end = end === void 0 ? this.length : end >>> 0;
  if (!val)
    val = 0;
  var i;
  if (typeof val === "number") {
    for (i = start; i < end; ++i) {
      this[i] = val;
    }
  } else {
    var bytes = internalIsBuffer(val) ? val : utf8ToBytes(new Buffer(val, encoding).toString());
    var len = bytes.length;
    for (i = 0; i < end - start; ++i) {
      this[i + start] = bytes[i % len];
    }
  }
  return this;
};
var INVALID_BASE64_RE = /[^+\/0-9A-Za-z-_]/g;
function base64clean(str) {
  str = stringtrim(str).replace(INVALID_BASE64_RE, "");
  if (str.length < 2)
    return "";
  while (str.length % 4 !== 0) {
    str = str + "=";
  }
  return str;
}
function stringtrim(str) {
  if (str.trim)
    return str.trim();
  return str.replace(/^\s+|\s+$/g, "");
}
function toHex(n) {
  if (n < 16)
    return "0" + n.toString(16);
  return n.toString(16);
}
function utf8ToBytes(string, units) {
  units = units || Infinity;
  var codePoint;
  var length = string.length;
  var leadSurrogate = null;
  var bytes = [];
  for (var i = 0; i < length; ++i) {
    codePoint = string.charCodeAt(i);
    if (codePoint > 55295 && codePoint < 57344) {
      if (!leadSurrogate) {
        if (codePoint > 56319) {
          if ((units -= 3) > -1)
            bytes.push(239, 191, 189);
          continue;
        } else if (i + 1 === length) {
          if ((units -= 3) > -1)
            bytes.push(239, 191, 189);
          continue;
        }
        leadSurrogate = codePoint;
        continue;
      }
      if (codePoint < 56320) {
        if ((units -= 3) > -1)
          bytes.push(239, 191, 189);
        leadSurrogate = codePoint;
        continue;
      }
      codePoint = (leadSurrogate - 55296 << 10 | codePoint - 56320) + 65536;
    } else if (leadSurrogate) {
      if ((units -= 3) > -1)
        bytes.push(239, 191, 189);
    }
    leadSurrogate = null;
    if (codePoint < 128) {
      if ((units -= 1) < 0)
        break;
      bytes.push(codePoint);
    } else if (codePoint < 2048) {
      if ((units -= 2) < 0)
        break;
      bytes.push(codePoint >> 6 | 192, codePoint & 63 | 128);
    } else if (codePoint < 65536) {
      if ((units -= 3) < 0)
        break;
      bytes.push(codePoint >> 12 | 224, codePoint >> 6 & 63 | 128, codePoint & 63 | 128);
    } else if (codePoint < 1114112) {
      if ((units -= 4) < 0)
        break;
      bytes.push(codePoint >> 18 | 240, codePoint >> 12 & 63 | 128, codePoint >> 6 & 63 | 128, codePoint & 63 | 128);
    } else {
      throw new Error("Invalid code point");
    }
  }
  return bytes;
}
function asciiToBytes(str) {
  var byteArray = [];
  for (var i = 0; i < str.length; ++i) {
    byteArray.push(str.charCodeAt(i) & 255);
  }
  return byteArray;
}
function utf16leToBytes(str, units) {
  var c, hi, lo;
  var byteArray = [];
  for (var i = 0; i < str.length; ++i) {
    if ((units -= 2) < 0)
      break;
    c = str.charCodeAt(i);
    hi = c >> 8;
    lo = c % 256;
    byteArray.push(lo);
    byteArray.push(hi);
  }
  return byteArray;
}
function base64ToBytes(str) {
  return toByteArray(base64clean(str));
}
function blitBuffer(src, dst, offset, length) {
  for (var i = 0; i < length; ++i) {
    if (i + offset >= dst.length || i >= src.length)
      break;
    dst[i + offset] = src[i];
  }
  return i;
}
function isnan(val) {
  return val !== val;
}
function isBuffer$1(obj) {
  return obj != null && (!!obj._isBuffer || isFastBuffer(obj) || isSlowBuffer(obj));
}
function isFastBuffer(obj) {
  return !!obj.constructor && typeof obj.constructor.isBuffer === "function" && obj.constructor.isBuffer(obj);
}
function isSlowBuffer(obj) {
  return typeof obj.readFloatLE === "function" && typeof obj.slice === "function" && isFastBuffer(obj.slice(0, 0));
}
function isVisitable(thing) {
  return utils.isPlainObject(thing) || utils.isArray(thing);
}
function removeBrackets(key) {
  return utils.endsWith(key, "[]") ? key.slice(0, -2) : key;
}
function renderKey(path, key, dots) {
  if (!path)
    return key;
  return path.concat(key).map(function each(token, i) {
    token = removeBrackets(token);
    return !dots && i ? "[" + token + "]" : token;
  }).join(dots ? "." : "");
}
function isFlatArray(arr) {
  return utils.isArray(arr) && !arr.some(isVisitable);
}
const predicates = utils.toFlatObject(utils, {}, null, function filter(prop) {
  return /^is[A-Z]/.test(prop);
});
function toFormData(obj, formData, options) {
  if (!utils.isObject(obj)) {
    throw new TypeError("target must be an object");
  }
  formData = formData || new FormData();
  options = utils.toFlatObject(options, {
    metaTokens: true,
    dots: false,
    indexes: false
  }, false, function defined(option, source) {
    return !utils.isUndefined(source[option]);
  });
  const metaTokens = options.metaTokens;
  const visitor = options.visitor || defaultVisitor;
  const dots = options.dots;
  const indexes = options.indexes;
  const _Blob = options.Blob || typeof Blob !== "undefined" && Blob;
  const useBlob = _Blob && utils.isSpecCompliantForm(formData);
  if (!utils.isFunction(visitor)) {
    throw new TypeError("visitor must be a function");
  }
  function convertValue(value) {
    if (value === null)
      return "";
    if (utils.isDate(value)) {
      return value.toISOString();
    }
    if (!useBlob && utils.isBlob(value)) {
      throw new AxiosError("Blob is not supported. Use a Buffer instead.");
    }
    if (utils.isArrayBuffer(value) || utils.isTypedArray(value)) {
      return useBlob && typeof Blob === "function" ? new Blob([value]) : Buffer.from(value);
    }
    return value;
  }
  function defaultVisitor(value, key, path) {
    let arr = value;
    if (value && !path && typeof value === "object") {
      if (utils.endsWith(key, "{}")) {
        key = metaTokens ? key : key.slice(0, -2);
        value = JSON.stringify(value);
      } else if (utils.isArray(value) && isFlatArray(value) || (utils.isFileList(value) || utils.endsWith(key, "[]")) && (arr = utils.toArray(value))) {
        key = removeBrackets(key);
        arr.forEach(function each(el, index) {
          !(utils.isUndefined(el) || el === null) && formData.append(indexes === true ? renderKey([key], index, dots) : indexes === null ? key : key + "[]", convertValue(el));
        });
        return false;
      }
    }
    if (isVisitable(value)) {
      return true;
    }
    formData.append(renderKey(path, key, dots), convertValue(value));
    return false;
  }
  const stack = [];
  const exposedHelpers = Object.assign(predicates, {
    defaultVisitor,
    convertValue,
    isVisitable
  });
  function build(value, path) {
    if (utils.isUndefined(value))
      return;
    if (stack.indexOf(value) !== -1) {
      throw Error("Circular reference detected in " + path.join("."));
    }
    stack.push(value);
    utils.forEach(value, function each(el, key) {
      const result = !(utils.isUndefined(el) || el === null) && visitor.call(formData, el, utils.isString(key) ? key.trim() : key, path, exposedHelpers);
      if (result === true) {
        build(el, path ? path.concat(key) : [key]);
      }
    });
    stack.pop();
  }
  if (!utils.isObject(obj)) {
    throw new TypeError("data must be an object");
  }
  build(obj);
  return formData;
}
function encode(str) {
  const charMap = {
    "!": "%21",
    "'": "%27",
    "(": "%28",
    ")": "%29",
    "~": "%7E",
    "%20": "+",
    "%00": "\0"
  };
  return encodeURIComponent(str).replace(/[!'()~]|%20|%00/g, function replacer(match) {
    return charMap[match];
  });
}
function AxiosURLSearchParams(params, options) {
  this._pairs = [];
  params && toFormData(params, this, options);
}
const prototype$1 = AxiosURLSearchParams.prototype;
prototype$1.append = function append(name, value) {
  this._pairs.push([name, value]);
};
prototype$1.toString = function toString3(encoder) {
  const _encode = encoder ? function(value) {
    return encoder.call(this, value, encode);
  } : encode;
  return this._pairs.map(function each(pair) {
    return _encode(pair[0]) + "=" + _encode(pair[1]);
  }, "").join("&");
};
function encode$1(val) {
  return encodeURIComponent(val).replace(/%3A/gi, ":").replace(/%24/g, "$").replace(/%2C/gi, ",").replace(/%20/g, "+").replace(/%5B/gi, "[").replace(/%5D/gi, "]");
}
function buildURL(url, params, options) {
  if (!params) {
    return url;
  }
  const _encode = options && options.encode || encode$1;
  const serializeFn = options && options.serialize;
  let serializedParams;
  if (serializeFn) {
    serializedParams = serializeFn(params, options);
  } else {
    serializedParams = utils.isURLSearchParams(params) ? params.toString() : new AxiosURLSearchParams(params, options).toString(_encode);
  }
  if (serializedParams) {
    const hashmarkIndex = url.indexOf("#");
    if (hashmarkIndex !== -1) {
      url = url.slice(0, hashmarkIndex);
    }
    url += (url.indexOf("?") === -1 ? "?" : "&") + serializedParams;
  }
  return url;
}

function settle(resolve, reject, response) {
  const validateStatus = response.config.validateStatus;
  if (!response.status || !validateStatus || validateStatus(response.status)) {
    resolve(response);
  } else {
    reject(new AxiosError("Request failed with status code " + response.status, [AxiosError.ERR_BAD_REQUEST, AxiosError.ERR_BAD_RESPONSE][Math.floor(response.status / 100) - 4], response.config, response.request, response));
  }
}

function isAbsoluteURL(url) {
  return /^([a-z][a-z\d+\-.]*:)?\/\//i.test(url);
}

function combineURLs(baseURL, relativeURL) {
  return relativeURL ? baseURL.replace(/\/+$/, "") + "/" + relativeURL.replace(/^\/+/, "") : baseURL;
}

function buildFullPath(baseURL, requestedURL) {
  if (baseURL && !isAbsoluteURL(requestedURL)) {
    return combineURLs(baseURL, requestedURL);
  }
  return requestedURL;
}

var transitionalDefaults = {
  silentJSONParsing: true,
  forcedJSONParsing: true,
  clarifyTimeoutError: false
};
var URLSearchParams$1 = typeof URLSearchParams !== "undefined" ? URLSearchParams : AxiosURLSearchParams;
var FormData$1 = typeof FormData !== "undefined" ? FormData : null;
var Blob$1 = typeof Blob !== "undefined" ? Blob : null;
const isStandardBrowserEnv = (() => {
  let product;
  if (typeof navigator !== "undefined" && ((product = navigator.product) === "ReactNative" || product === "NativeScript" || product === "NS")) {
    return false;
  }
  return typeof window !== "undefined" && typeof document !== "undefined";
})();
const isStandardBrowserWebWorkerEnv = (() => {
  return typeof WorkerGlobalScope !== "undefined" && self instanceof WorkerGlobalScope && typeof self.importScripts === "function";
})();
var platform = {
  isBrowser: true,
  classes: {
    URLSearchParams: URLSearchParams$1,
    FormData: FormData$1,
    Blob: Blob$1
  },
  isStandardBrowserEnv,
  isStandardBrowserWebWorkerEnv,
  protocols: ["http", "https", "file", "blob", "url", "data"]
};
const ignoreDuplicateOf = utils.toObjectSet([
  "age",
  "authorization",
  "content-length",
  "content-type",
  "etag",
  "expires",
  "from",
  "host",
  "if-modified-since",
  "if-unmodified-since",
  "last-modified",
  "location",
  "max-forwards",
  "proxy-authorization",
  "referer",
  "retry-after",
  "user-agent"
]);
var parseHeaders = (rawHeaders) => {
  const parsed = {};
  let key;
  let val;
  let i;
  rawHeaders && rawHeaders.split("\n").forEach(function parser(line) {
    i = line.indexOf(":");
    key = line.substring(0, i).trim().toLowerCase();
    val = line.substring(i + 1).trim();
    if (!key || parsed[key] && ignoreDuplicateOf[key]) {
      return;
    }
    if (key === "set-cookie") {
      if (parsed[key]) {
        parsed[key].push(val);
      } else {
        parsed[key] = [val];
      }
    } else {
      parsed[key] = parsed[key] ? parsed[key] + ", " + val : val;
    }
  });
  return parsed;
};
const $internals = Symbol("internals");
function normalizeHeader(header) {
  return header && String(header).trim().toLowerCase();
}
function normalizeValue(value) {
  if (value === false || value == null) {
    return value;
  }
  return utils.isArray(value) ? value.map(normalizeValue) : String(value);
}
function parseTokens(str) {
  const tokens = Object.create(null);
  const tokensRE = /([^\s,;=]+)\s*(?:=\s*([^,;]+))?/g;
  let match;
  while (match = tokensRE.exec(str)) {
    tokens[match[1]] = match[2];
  }
  return tokens;
}
const isValidHeaderName = (str) => /^[-_a-zA-Z0-9^`|~,!#$%&'*+.]+$/.test(str.trim());
function matchHeaderValue(context, value, header, filter, isHeaderNameFilter) {
  if (utils.isFunction(filter)) {
    return filter.call(this, value, header);
  }
  if (isHeaderNameFilter) {
    value = header;
  }
  if (!utils.isString(value))
    return;
  if (utils.isString(filter)) {
    return value.indexOf(filter) !== -1;
  }
  if (utils.isRegExp(filter)) {
    return filter.test(value);
  }
}
function formatHeader(header) {
  return header.trim().toLowerCase().replace(/([a-z\d])(\w*)/g, (w, char, str) => {
    return char.toUpperCase() + str;
  });
}
function buildAccessors(obj, header) {
  const accessorName = utils.toCamelCase(" " + header);
  ["get", "set", "has"].forEach((methodName) => {
    Object.defineProperty(obj, methodName + accessorName, {
      value: function(arg1, arg2, arg3) {
        return this[methodName].call(this, header, arg1, arg2, arg3);
      },
      configurable: true
    });
  });
}
class AxiosHeaders {
  constructor(headers) {
    headers && this.set(headers);
  }
  set(header, valueOrRewrite, rewrite) {
    const self2 = this;
    function setHeader(_value, _header, _rewrite) {
      const lHeader = normalizeHeader(_header);
      if (!lHeader) {
        throw new Error("header name must be a non-empty string");
      }
      const key = utils.findKey(self2, lHeader);
      if (!key || self2[key] === void 0 || _rewrite === true || _rewrite === void 0 && self2[key] !== false) {
        self2[key || _header] = normalizeValue(_value);
      }
    }
    const setHeaders = (headers, _rewrite) => utils.forEach(headers, (_value, _header) => setHeader(_value, _header, _rewrite));
    if (utils.isPlainObject(header) || header instanceof this.constructor) {
      setHeaders(header, valueOrRewrite);
    } else if (utils.isString(header) && (header = header.trim()) && !isValidHeaderName(header)) {
      setHeaders(parseHeaders(header), valueOrRewrite);
    } else {
      header != null && setHeader(valueOrRewrite, header, rewrite);
    }
    return this;
  }
  get(header, parser) {
    header = normalizeHeader(header);
    if (header) {
      const key = utils.findKey(this, header);
      if (key) {
        const value = this[key];
        if (!parser) {
          return value;
        }
        if (parser === true) {
          return parseTokens(value);
        }
        if (utils.isFunction(parser)) {
          return parser.call(this, value, key);
        }
        if (utils.isRegExp(parser)) {
          return parser.exec(value);
        }
        throw new TypeError("parser must be boolean|regexp|function");
      }
    }
  }
  has(header, matcher) {
    header = normalizeHeader(header);
    if (header) {
      const key = utils.findKey(this, header);
      return !!(key && this[key] !== void 0 && (!matcher || matchHeaderValue(this, this[key], key, matcher)));
    }
    return false;
  }
  delete(header, matcher) {
    const self2 = this;
    let deleted = false;
    function deleteHeader(_header) {
      _header = normalizeHeader(_header);
      if (_header) {
        const key = utils.findKey(self2, _header);
        if (key && (!matcher || matchHeaderValue(self2, self2[key], key, matcher))) {
          delete self2[key];
          deleted = true;
        }
      }
    }
    if (utils.isArray(header)) {
      header.forEach(deleteHeader);
    } else {
      deleteHeader(header);
    }
    return deleted;
  }
  clear(matcher) {
    const keys = Object.keys(this);
    let i = keys.length;
    let deleted = false;
    while (i--) {
      const key = keys[i];
      if (!matcher || matchHeaderValue(this, this[key], key, matcher, true)) {
        delete this[key];
        deleted = true;
      }
    }
    return deleted;
  }
  normalize(format) {
    const self2 = this;
    const headers = {};
    utils.forEach(this, (value, header) => {
      const key = utils.findKey(headers, header);
      if (key) {
        self2[key] = normalizeValue(value);
        delete self2[header];
        return;
      }
      const normalized = format ? formatHeader(header) : String(header).trim();
      if (normalized !== header) {
        delete self2[header];
      }
      self2[normalized] = normalizeValue(value);
      headers[normalized] = true;
    });
    return this;
  }
  concat(...targets) {
    return this.constructor.concat(this, ...targets);
  }
  toJSON(asStrings) {
    const obj = Object.create(null);
    utils.forEach(this, (value, header) => {
      value != null && value !== false && (obj[header] = asStrings && utils.isArray(value) ? value.join(", ") : value);
    });
    return obj;
  }
  [Symbol.iterator]() {
    return Object.entries(this.toJSON())[Symbol.iterator]();
  }
  toString() {
    return Object.entries(this.toJSON()).map(([header, value]) => header + ": " + value).join("\n");
  }
  get [Symbol.toStringTag]() {
    return "AxiosHeaders";
  }
  static from(thing) {
    return thing instanceof this ? thing : new this(thing);
  }
  static concat(first, ...targets) {
    const computed = new this(first);
    targets.forEach((target) => computed.set(target));
    return computed;
  }
  static accessor(header) {
    const internals = this[$internals] = this[$internals] = {
      accessors: {}
    };
    const accessors = internals.accessors;
    const prototype = this.prototype;
    function defineAccessor(_header) {
      const lHeader = normalizeHeader(_header);
      if (!accessors[lHeader]) {
        buildAccessors(prototype, _header);
        accessors[lHeader] = true;
      }
    }
    utils.isArray(header) ? header.forEach(defineAccessor) : defineAccessor(header);
    return this;
  }
}
AxiosHeaders.accessor(["Content-Type", "Content-Length", "Accept", "Accept-Encoding", "User-Agent", "Authorization"]);
utils.freezeMethods(AxiosHeaders.prototype);
utils.freezeMethods(AxiosHeaders);
function CanceledError(message, config, request) {
  AxiosError.call(this, message == null ? "canceled" : message, AxiosError.ERR_CANCELED, config, request);
  this.name = "CanceledError";
}
utils.inherits(CanceledError, AxiosError, {
  __CANCEL__: true
});
var cookies = platform.isStandardBrowserEnv ? function standardBrowserEnv() {
  return {
    write: function write(name, value, expires, path, domain, secure) {
      const cookie = [];
      cookie.push(name + "=" + encodeURIComponent(value));
      if (utils.isNumber(expires)) {
        cookie.push("expires=" + new Date(expires).toGMTString());
      }
      if (utils.isString(path)) {
        cookie.push("path=" + path);
      }
      if (utils.isString(domain)) {
        cookie.push("domain=" + domain);
      }
      if (secure === true) {
        cookie.push("secure");
      }
      document.cookie = cookie.join("; ");
    },
    read: function read(name) {
      const match = document.cookie.match(new RegExp("(^|;\\s*)(" + name + ")=([^;]*)"));
      return match ? decodeURIComponent(match[3]) : null;
    },
    remove: function remove(name) {
      this.write(name, "", Date.now() - 864e5);
    }
  };
}() : function nonStandardBrowserEnv() {
  return {
    write: function write() {
    },
    read: function read() {
      return null;
    },
    remove: function remove() {
    }
  };
}();
var isURLSameOrigin = platform.isStandardBrowserEnv ? function standardBrowserEnv2() {
  const msie = /(msie|trident)/i.test(navigator.userAgent);
  const urlParsingNode = document.createElement("a");
  let originURL;
  function resolveURL(url) {
    let href = url;
    if (msie) {
      urlParsingNode.setAttribute("href", href);
      href = urlParsingNode.href;
    }
    urlParsingNode.setAttribute("href", href);
    return {
      href: urlParsingNode.href,
      protocol: urlParsingNode.protocol ? urlParsingNode.protocol.replace(/:$/, "") : "",
      host: urlParsingNode.host,
      search: urlParsingNode.search ? urlParsingNode.search.replace(/^\?/, "") : "",
      hash: urlParsingNode.hash ? urlParsingNode.hash.replace(/^#/, "") : "",
      hostname: urlParsingNode.hostname,
      port: urlParsingNode.port,
      pathname: urlParsingNode.pathname.charAt(0) === "/" ? urlParsingNode.pathname : "/" + urlParsingNode.pathname
    };
  }
  originURL = resolveURL(window.location.href);
  return function isURLSameOrigin2(requestURL) {
    const parsed = utils.isString(requestURL) ? resolveURL(requestURL) : requestURL;
    return parsed.protocol === originURL.protocol && parsed.host === originURL.host;
  };
}() : function nonStandardBrowserEnv2() {
  return function isURLSameOrigin2() {
    return true;
  };
}();
function parseProtocol(url) {
  const match = /^([-+\w]{1,25})(:?\/\/|:)/.exec(url);
  return match && match[1] || "";
}
function speedometer(samplesCount, min) {
  samplesCount = samplesCount || 10;
  const bytes = new Array(samplesCount);
  const timestamps = new Array(samplesCount);
  let head = 0;
  let tail = 0;
  let firstSampleTS;
  min = min !== void 0 ? min : 1e3;
  return function push(chunkLength) {
    const now = Date.now();
    const startedAt = timestamps[tail];
    if (!firstSampleTS) {
      firstSampleTS = now;
    }
    bytes[head] = chunkLength;
    timestamps[head] = now;
    let i = tail;
    let bytesCount = 0;
    while (i !== head) {
      bytesCount += bytes[i++];
      i = i % samplesCount;
    }
    head = (head + 1) % samplesCount;
    if (head === tail) {
      tail = (tail + 1) % samplesCount;
    }
    if (now - firstSampleTS < min) {
      return;
    }
    const passed = startedAt && now - startedAt;
    return passed ? Math.round(bytesCount * 1e3 / passed) : void 0;
  };
}
function progressEventReducer(listener, isDownloadStream) {
  let bytesNotified = 0;
  const _speedometer = speedometer(50, 250);
  return (e) => {
    const loaded = e.loaded;
    const total = e.lengthComputable ? e.total : void 0;
    const progressBytes = loaded - bytesNotified;
    const rate = _speedometer(progressBytes);
    const inRange = loaded <= total;
    bytesNotified = loaded;
    const data = {
      loaded,
      total,
      progress: total ? loaded / total : void 0,
      bytes: progressBytes,
      rate: rate ? rate : void 0,
      estimated: rate && total && inRange ? (total - loaded) / rate : void 0,
      event: e
    };
    data[isDownloadStream ? "download" : "upload"] = true;
    listener(data);
  };
}
const isXHRAdapterSupported = typeof XMLHttpRequest !== "undefined";
var xhrAdapter = isXHRAdapterSupported && function(config) {
  return new Promise(function dispatchXhrRequest(resolve, reject) {
    let requestData = config.data;
    const requestHeaders = AxiosHeaders.from(config.headers).normalize();
    const responseType = config.responseType;
    let onCanceled;
    function done() {
      if (config.cancelToken) {
        config.cancelToken.unsubscribe(onCanceled);
      }
      if (config.signal) {
        config.signal.removeEventListener("abort", onCanceled);
      }
    }
    if (utils.isFormData(requestData)) {
      if (platform.isStandardBrowserEnv || platform.isStandardBrowserWebWorkerEnv) {
        requestHeaders.setContentType(false);
      } else {
        requestHeaders.setContentType("multipart/form-data;", false);
      }
    }
    let request = new XMLHttpRequest();
    if (config.auth) {
      const username = config.auth.username || "";
      const password = config.auth.password ? unescape(encodeURIComponent(config.auth.password)) : "";
      requestHeaders.set("Authorization", "Basic " + btoa(username + ":" + password));
    }
    const fullPath = buildFullPath(config.baseURL, config.url);
    request.open(config.method.toUpperCase(), buildURL(fullPath, config.params, config.paramsSerializer), true);
    request.timeout = config.timeout;
    function onloadend() {
      if (!request) {
        return;
      }
      const responseHeaders = AxiosHeaders.from("getAllResponseHeaders" in request && request.getAllResponseHeaders());
      const responseData = !responseType || responseType === "text" || responseType === "json" ? request.responseText : request.response;
      const response = {
        data: responseData,
        status: request.status,
        statusText: request.statusText,
        headers: responseHeaders,
        config,
        request
      };
      settle(function _resolve(value) {
        resolve(value);
        done();
      }, function _reject(err) {
        reject(err);
        done();
      }, response);
      request = null;
    }
    if ("onloadend" in request) {
      request.onloadend = onloadend;
    } else {
      request.onreadystatechange = function handleLoad() {
        if (!request || request.readyState !== 4) {
          return;
        }
        if (request.status === 0 && !(request.responseURL && request.responseURL.indexOf("file:") === 0)) {
          return;
        }
        setTimeout(onloadend);
      };
    }
    request.onabort = function handleAbort() {
      if (!request) {
        return;
      }
      reject(new AxiosError("Request aborted", AxiosError.ECONNABORTED, config, request));
      request = null;
    };
    request.onerror = function handleError() {
      reject(new AxiosError("Network Error", AxiosError.ERR_NETWORK, config, request));
      request = null;
    };
    request.ontimeout = function handleTimeout() {
      let timeoutErrorMessage = config.timeout ? "timeout of " + config.timeout + "ms exceeded" : "timeout exceeded";
      const transitional = config.transitional || transitionalDefaults;
      if (config.timeoutErrorMessage) {
        timeoutErrorMessage = config.timeoutErrorMessage;
      }
      reject(new AxiosError(timeoutErrorMessage, transitional.clarifyTimeoutError ? AxiosError.ETIMEDOUT : AxiosError.ECONNABORTED, config, request));
      request = null;
    };
    if (platform.isStandardBrowserEnv) {
      const xsrfValue = (config.withCredentials || isURLSameOrigin(fullPath)) && config.xsrfCookieName && cookies.read(config.xsrfCookieName);
      if (xsrfValue) {
        requestHeaders.set(config.xsrfHeaderName, xsrfValue);
      }
    }
    requestData === void 0 && requestHeaders.setContentType(null);
    if ("setRequestHeader" in request) {
      utils.forEach(requestHeaders.toJSON(), function setRequestHeader(val, key) {
        request.setRequestHeader(key, val);
      });
    }
    if (!utils.isUndefined(config.withCredentials)) {
      request.withCredentials = !!config.withCredentials;
    }
    if (responseType && responseType !== "json") {
      request.responseType = config.responseType;
    }
    if (typeof config.onDownloadProgress === "function") {
      request.addEventListener("progress", progressEventReducer(config.onDownloadProgress, true));
    }
    if (typeof config.onUploadProgress === "function" && request.upload) {
      request.upload.addEventListener("progress", progressEventReducer(config.onUploadProgress));
    }
    if (config.cancelToken || config.signal) {
      onCanceled = (cancel) => {
        if (!request) {
          return;
        }
        reject(!cancel || cancel.type ? new CanceledError(null, config, request) : cancel);
        request.abort();
        request = null;
      };
      config.cancelToken && config.cancelToken.subscribe(onCanceled);
      if (config.signal) {
        config.signal.aborted ? onCanceled() : config.signal.addEventListener("abort", onCanceled);
      }
    }
    const protocol = parseProtocol(fullPath);
    if (protocol && platform.protocols.indexOf(protocol) === -1) {
      reject(new AxiosError("Unsupported protocol " + protocol + ":", AxiosError.ERR_BAD_REQUEST, config));
      return;
    }
    request.send(requestData || null);
  });
};

var httpAdapter = null;

class InterceptorManager {
  constructor() {
    this.handlers = [];
  }
  use(fulfilled, rejected, options) {
    this.handlers.push({
      fulfilled,
      rejected,
      synchronous: options ? options.synchronous : false,
      runWhen: options ? options.runWhen : null
    });
    return this.handlers.length - 1;
  }
  eject(id) {
    if (this.handlers[id]) {
      this.handlers[id] = null;
    }
  }
  clear() {
    if (this.handlers) {
      this.handlers = [];
    }
  }
  forEach(fn) {
    utils.forEach(this.handlers, function forEachHandler(h) {
      if (h !== null) {
        fn(h);
      }
    });
  }
}
function toURLEncodedForm(data, options) {
  return toFormData(data, new platform.classes.URLSearchParams(), Object.assign({
    visitor: function(value, key, path, helpers) {
      return helpers.defaultVisitor.apply(this, arguments);
    }
  }, options));
}
function parsePropPath(name) {
  return utils.matchAll(/\w+|\[(\w*)]/g, name).map((match) => {
    return match[0] === "[]" ? "" : match[1] || match[0];
  });
}
function arrayToObject(arr) {
  const obj = {};
  const keys = Object.keys(arr);
  let i;
  const len = keys.length;
  let key;
  for (i = 0; i < len; i++) {
    key = keys[i];
    obj[key] = arr[key];
  }
  return obj;
}
function formDataToJSON(formData) {
  function buildPath(path, value, target, index) {
    let name = path[index++];
    const isNumericKey = Number.isFinite(+name);
    const isLast = index >= path.length;
    name = !name && utils.isArray(target) ? target.length : name;
    if (isLast) {
      if (utils.hasOwnProp(target, name)) {
        target[name] = [target[name], value];
      } else {
        target[name] = value;
      }
      return !isNumericKey;
    }
    if (!target[name] || !utils.isObject(target[name])) {
      target[name] = [];
    }
    const result = buildPath(path, value, target[name], index);
    if (result && utils.isArray(target[name])) {
      target[name] = arrayToObject(target[name]);
    }
    return !isNumericKey;
  }
  if (utils.isFormData(formData) && utils.isFunction(formData.entries)) {
    const obj = {};
    utils.forEachEntry(formData, (name, value) => {
      buildPath(parsePropPath(name), value, obj, 0);
    });
    return obj;
  }
  return null;
}
const DEFAULT_CONTENT_TYPE = {
  "Content-Type": void 0
};
function stringifySafely(rawValue, parser, encoder) {
  if (utils.isString(rawValue)) {
    try {
      (parser || JSON.parse)(rawValue);
      return utils.trim(rawValue);
    } catch (e) {
      if (e.name !== "SyntaxError") {
        throw e;
      }
    }
  }
  return (encoder || JSON.stringify)(rawValue);
}
const defaults = {
  transitional: transitionalDefaults,
  adapter: ["xhr", "http"],
  transformRequest: [function transformRequest(data, headers) {
    const contentType = headers.getContentType() || "";
    const hasJSONContentType = contentType.indexOf("application/json") > -1;
    const isObjectPayload = utils.isObject(data);
    if (isObjectPayload && utils.isHTMLForm(data)) {
      data = new FormData(data);
    }
    const isFormData = utils.isFormData(data);
    if (isFormData) {
      if (!hasJSONContentType) {
        return data;
      }
      return hasJSONContentType ? JSON.stringify(formDataToJSON(data)) : data;
    }
    if (utils.isArrayBuffer(data) || utils.isBuffer(data) || utils.isStream(data) || utils.isFile(data) || utils.isBlob(data)) {
      return data;
    }
    if (utils.isArrayBufferView(data)) {
      return data.buffer;
    }
    if (utils.isURLSearchParams(data)) {
      headers.setContentType("application/x-www-form-urlencoded;charset=utf-8", false);
      return data.toString();
    }
    let isFileList;
    if (isObjectPayload) {
      if (contentType.indexOf("application/x-www-form-urlencoded") > -1) {
        return toURLEncodedForm(data, this.formSerializer).toString();
      }
      if ((isFileList = utils.isFileList(data)) || contentType.indexOf("multipart/form-data") > -1) {
        const _FormData = this.env && this.env.FormData;
        return toFormData(isFileList ? {"files[]": data} : data, _FormData && new _FormData(), this.formSerializer);
      }
    }
    if (isObjectPayload || hasJSONContentType) {
      headers.setContentType("application/json", false);
      return stringifySafely(data);
    }
    return data;
  }],
  transformResponse: [function transformResponse(data) {
    const transitional2 = this.transitional || defaults.transitional;
    const forcedJSONParsing = transitional2 && transitional2.forcedJSONParsing;
    const JSONRequested = this.responseType === "json";
    if (data && utils.isString(data) && (forcedJSONParsing && !this.responseType || JSONRequested)) {
      const silentJSONParsing = transitional2 && transitional2.silentJSONParsing;
      const strictJSONParsing = !silentJSONParsing && JSONRequested;
      try {
        return JSON.parse(data);
      } catch (e) {
        if (strictJSONParsing) {
          if (e.name === "SyntaxError") {
            throw AxiosError.from(e, AxiosError.ERR_BAD_RESPONSE, this, null, this.response);
          }
          throw e;
        }
      }
    }
    return data;
  }],
  timeout: 0,
  xsrfCookieName: "XSRF-TOKEN",
  xsrfHeaderName: "X-XSRF-TOKEN",
  maxContentLength: -1,
  maxBodyLength: -1,
  env: {
    FormData: platform.classes.FormData,
    Blob: platform.classes.Blob
  },
  validateStatus: function validateStatus(status) {
    return status >= 200 && status < 300;
  },
  headers: {
    common: {
      Accept: "application/json, text/plain, */*"
    }
  }
};
utils.forEach(["delete", "get", "head"], function forEachMethodNoData(method) {
  defaults.headers[method] = {};
});
utils.forEach(["post", "put", "patch"], function forEachMethodWithData(method) {
  defaults.headers[method] = utils.merge(DEFAULT_CONTENT_TYPE);
});
function transformData(fns, response) {
  const config = this || defaults;
  const context = response || config;
  const headers = AxiosHeaders.from(context.headers);
  let data = context.data;
  utils.forEach(fns, function transform(fn) {
    data = fn.call(config, data, headers.normalize(), response ? response.status : void 0);
  });
  headers.normalize();
  return data;
}
function isCancel(value) {
  return !!(value && value.__CANCEL__);
}
const knownAdapters = {
  http: httpAdapter,
  xhr: xhrAdapter
};
utils.forEach(knownAdapters, (fn, value) => {
  if (fn) {
    try {
      Object.defineProperty(fn, "name", {value});
    } catch (e) {
    }
    Object.defineProperty(fn, "adapterName", {value});
  }
});
var adapters = {
  getAdapter: (adapters2) => {
    adapters2 = utils.isArray(adapters2) ? adapters2 : [adapters2];
    const {length} = adapters2;
    let nameOrAdapter;
    let adapter;
    for (let i = 0; i < length; i++) {
      nameOrAdapter = adapters2[i];
      if (adapter = utils.isString(nameOrAdapter) ? knownAdapters[nameOrAdapter.toLowerCase()] : nameOrAdapter) {
        break;
      }
    }
    if (!adapter) {
      if (adapter === false) {
        throw new AxiosError(`Adapter ${nameOrAdapter} is not supported by the environment`, "ERR_NOT_SUPPORT");
      }
      throw new Error(utils.hasOwnProp(knownAdapters, nameOrAdapter) ? `Adapter '${nameOrAdapter}' is not available in the build` : `Unknown adapter '${nameOrAdapter}'`);
    }
    if (!utils.isFunction(adapter)) {
      throw new TypeError("adapter is not a function");
    }
    return adapter;
  },
  adapters: knownAdapters
};
function throwIfCancellationRequested(config) {
  if (config.cancelToken) {
    config.cancelToken.throwIfRequested();
  }
  if (config.signal && config.signal.aborted) {
    throw new CanceledError(null, config);
  }
}
function dispatchRequest(config) {
  throwIfCancellationRequested(config);
  config.headers = AxiosHeaders.from(config.headers);
  config.data = transformData.call(config, config.transformRequest);
  if (["post", "put", "patch"].indexOf(config.method) !== -1) {
    config.headers.setContentType("application/x-www-form-urlencoded", false);
  }
  const adapter = adapters.getAdapter(config.adapter || defaults.adapter);
  return adapter(config).then(function onAdapterResolution(response) {
    throwIfCancellationRequested(config);
    response.data = transformData.call(config, config.transformResponse, response);
    response.headers = AxiosHeaders.from(response.headers);
    return response;
  }, function onAdapterRejection(reason) {
    if (!isCancel(reason)) {
      throwIfCancellationRequested(config);
      if (reason && reason.response) {
        reason.response.data = transformData.call(config, config.transformResponse, reason.response);
        reason.response.headers = AxiosHeaders.from(reason.response.headers);
      }
    }
    return Promise.reject(reason);
  });
}
const headersToObject = (thing) => thing instanceof AxiosHeaders ? thing.toJSON() : thing;
function mergeConfig(config1, config2) {
  config2 = config2 || {};
  const config = {};
  function getMergedValue(target, source, caseless) {
    if (utils.isPlainObject(target) && utils.isPlainObject(source)) {
      return utils.merge.call({caseless}, target, source);
    } else if (utils.isPlainObject(source)) {
      return utils.merge({}, source);
    } else if (utils.isArray(source)) {
      return source.slice();
    }
    return source;
  }
  function mergeDeepProperties(a, b, caseless) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(a, b, caseless);
    } else if (!utils.isUndefined(a)) {
      return getMergedValue(void 0, a, caseless);
    }
  }
  function valueFromConfig2(a, b) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(void 0, b);
    }
  }
  function defaultToConfig2(a, b) {
    if (!utils.isUndefined(b)) {
      return getMergedValue(void 0, b);
    } else if (!utils.isUndefined(a)) {
      return getMergedValue(void 0, a);
    }
  }
  function mergeDirectKeys(a, b, prop) {
    if (prop in config2) {
      return getMergedValue(a, b);
    } else if (prop in config1) {
      return getMergedValue(void 0, a);
    }
  }
  const mergeMap = {
    url: valueFromConfig2,
    method: valueFromConfig2,
    data: valueFromConfig2,
    baseURL: defaultToConfig2,
    transformRequest: defaultToConfig2,
    transformResponse: defaultToConfig2,
    paramsSerializer: defaultToConfig2,
    timeout: defaultToConfig2,
    timeoutMessage: defaultToConfig2,
    withCredentials: defaultToConfig2,
    adapter: defaultToConfig2,
    responseType: defaultToConfig2,
    xsrfCookieName: defaultToConfig2,
    xsrfHeaderName: defaultToConfig2,
    onUploadProgress: defaultToConfig2,
    onDownloadProgress: defaultToConfig2,
    decompress: defaultToConfig2,
    maxContentLength: defaultToConfig2,
    maxBodyLength: defaultToConfig2,
    beforeRedirect: defaultToConfig2,
    transport: defaultToConfig2,
    httpAgent: defaultToConfig2,
    httpsAgent: defaultToConfig2,
    cancelToken: defaultToConfig2,
    socketPath: defaultToConfig2,
    responseEncoding: defaultToConfig2,
    validateStatus: mergeDirectKeys,
    headers: (a, b) => mergeDeepProperties(headersToObject(a), headersToObject(b), true)
  };
  utils.forEach(Object.keys(Object.assign({}, config1, config2)), function computeConfigValue(prop) {
    const merge = mergeMap[prop] || mergeDeepProperties;
    const configValue = merge(config1[prop], config2[prop], prop);
    utils.isUndefined(configValue) && merge !== mergeDirectKeys || (config[prop] = configValue);
  });
  return config;
}
const VERSION = "1.4.0";
const validators = {};
["object", "boolean", "number", "function", "string", "symbol"].forEach((type, i) => {
  validators[type] = function validator2(thing) {
    return typeof thing === type || "a" + (i < 1 ? "n " : " ") + type;
  };
});
const deprecatedWarnings = {};
validators.transitional = function transitional(validator2, version, message) {
  function formatMessage(opt, desc) {
    return "[Axios v" + VERSION + "] Transitional option '" + opt + "'" + desc + (message ? ". " + message : "");
  }
  return (value, opt, opts) => {
    if (validator2 === false) {
      throw new AxiosError(formatMessage(opt, " has been removed" + (version ? " in " + version : "")), AxiosError.ERR_DEPRECATED);
    }
    if (version && !deprecatedWarnings[opt]) {
      deprecatedWarnings[opt] = true;
      console.warn(formatMessage(opt, " has been deprecated since v" + version + " and will be removed in the near future"));
    }
    return validator2 ? validator2(value, opt, opts) : true;
  };
};
function assertOptions(options, schema, allowUnknown) {
  if (typeof options !== "object") {
    throw new AxiosError("options must be an object", AxiosError.ERR_BAD_OPTION_VALUE);
  }
  const keys = Object.keys(options);
  let i = keys.length;
  while (i-- > 0) {
    const opt = keys[i];
    const validator2 = schema[opt];
    if (validator2) {
      const value = options[opt];
      const result = value === void 0 || validator2(value, opt, options);
      if (result !== true) {
        throw new AxiosError("option " + opt + " must be " + result, AxiosError.ERR_BAD_OPTION_VALUE);
      }
      continue;
    }
    if (allowUnknown !== true) {
      throw new AxiosError("Unknown option " + opt, AxiosError.ERR_BAD_OPTION);
    }
  }
}
var validator = {
  assertOptions,
  validators
};
const validators$1 = validator.validators;
class Axios {
  constructor(instanceConfig) {
    this.defaults = instanceConfig;
    this.interceptors = {
      request: new InterceptorManager(),
      response: new InterceptorManager()
    };
  }
  request(configOrUrl, config) {
    if (typeof configOrUrl === "string") {
      config = config || {};
      config.url = configOrUrl;
    } else {
      config = configOrUrl || {};
    }
    config = mergeConfig(this.defaults, config);
    const {transitional: transitional2, paramsSerializer, headers} = config;
    if (transitional2 !== void 0) {
      validator.assertOptions(transitional2, {
        silentJSONParsing: validators$1.transitional(validators$1.boolean),
        forcedJSONParsing: validators$1.transitional(validators$1.boolean),
        clarifyTimeoutError: validators$1.transitional(validators$1.boolean)
      }, false);
    }
    if (paramsSerializer != null) {
      if (utils.isFunction(paramsSerializer)) {
        config.paramsSerializer = {
          serialize: paramsSerializer
        };
      } else {
        validator.assertOptions(paramsSerializer, {
          encode: validators$1.function,
          serialize: validators$1.function
        }, true);
      }
    }
    config.method = (config.method || this.defaults.method || "get").toLowerCase();
    let contextHeaders;
    contextHeaders = headers && utils.merge(headers.common, headers[config.method]);
    contextHeaders && utils.forEach(["delete", "get", "head", "post", "put", "patch", "common"], (method) => {
      delete headers[method];
    });
    config.headers = AxiosHeaders.concat(contextHeaders, headers);
    const requestInterceptorChain = [];
    let synchronousRequestInterceptors = true;
    this.interceptors.request.forEach(function unshiftRequestInterceptors(interceptor) {
      if (typeof interceptor.runWhen === "function" && interceptor.runWhen(config) === false) {
        return;
      }
      synchronousRequestInterceptors = synchronousRequestInterceptors && interceptor.synchronous;
      requestInterceptorChain.unshift(interceptor.fulfilled, interceptor.rejected);
    });
    const responseInterceptorChain = [];
    this.interceptors.response.forEach(function pushResponseInterceptors(interceptor) {
      responseInterceptorChain.push(interceptor.fulfilled, interceptor.rejected);
    });
    let promise;
    let i = 0;
    let len;
    if (!synchronousRequestInterceptors) {
      const chain = [dispatchRequest.bind(this), void 0];
      chain.unshift.apply(chain, requestInterceptorChain);
      chain.push.apply(chain, responseInterceptorChain);
      len = chain.length;
      promise = Promise.resolve(config);
      while (i < len) {
        promise = promise.then(chain[i++], chain[i++]);
      }
      return promise;
    }
    len = requestInterceptorChain.length;
    let newConfig = config;
    i = 0;
    while (i < len) {
      const onFulfilled = requestInterceptorChain[i++];
      const onRejected = requestInterceptorChain[i++];
      try {
        newConfig = onFulfilled(newConfig);
      } catch (error) {
        onRejected.call(this, error);
        break;
      }
    }
    try {
      promise = dispatchRequest.call(this, newConfig);
    } catch (error) {
      return Promise.reject(error);
    }
    i = 0;
    len = responseInterceptorChain.length;
    while (i < len) {
      promise = promise.then(responseInterceptorChain[i++], responseInterceptorChain[i++]);
    }
    return promise;
  }
  getUri(config) {
    config = mergeConfig(this.defaults, config);
    const fullPath = buildFullPath(config.baseURL, config.url);
    return buildURL(fullPath, config.params, config.paramsSerializer);
  }
}
utils.forEach(["delete", "get", "head", "options"], function forEachMethodNoData2(method) {
  Axios.prototype[method] = function(url, config) {
    return this.request(mergeConfig(config || {}, {
      method,
      url,
      data: (config || {}).data
    }));
  };
});
utils.forEach(["post", "put", "patch"], function forEachMethodWithData2(method) {
  function generateHTTPMethod(isForm) {
    return function httpMethod(url, data, config) {
      return this.request(mergeConfig(config || {}, {
        method,
        headers: isForm ? {
          "Content-Type": "multipart/form-data"
        } : {},
        url,
        data
      }));
    };
  }
  Axios.prototype[method] = generateHTTPMethod();
  Axios.prototype[method + "Form"] = generateHTTPMethod(true);
});
class CancelToken {
  constructor(executor) {
    if (typeof executor !== "function") {
      throw new TypeError("executor must be a function.");
    }
    let resolvePromise;
    this.promise = new Promise(function promiseExecutor(resolve) {
      resolvePromise = resolve;
    });
    const token = this;
    this.promise.then((cancel) => {
      if (!token._listeners)
        return;
      let i = token._listeners.length;
      while (i-- > 0) {
        token._listeners[i](cancel);
      }
      token._listeners = null;
    });
    this.promise.then = (onfulfilled) => {
      let _resolve;
      const promise = new Promise((resolve) => {
        token.subscribe(resolve);
        _resolve = resolve;
      }).then(onfulfilled);
      promise.cancel = function reject() {
        token.unsubscribe(_resolve);
      };
      return promise;
    };
    executor(function cancel(message, config, request) {
      if (token.reason) {
        return;
      }
      token.reason = new CanceledError(message, config, request);
      resolvePromise(token.reason);
    });
  }
  throwIfRequested() {
    if (this.reason) {
      throw this.reason;
    }
  }
  subscribe(listener) {
    if (this.reason) {
      listener(this.reason);
      return;
    }
    if (this._listeners) {
      this._listeners.push(listener);
    } else {
      this._listeners = [listener];
    }
  }
  unsubscribe(listener) {
    if (!this._listeners) {
      return;
    }
    const index = this._listeners.indexOf(listener);
    if (index !== -1) {
      this._listeners.splice(index, 1);
    }
  }
  static source() {
    let cancel;
    const token = new CancelToken(function executor(c) {
      cancel = c;
    });
    return {
      token,
      cancel
    };
  }
}
function spread(callback) {
  return function wrap(arr) {
    return callback.apply(null, arr);
  };
}
function isAxiosError(payload) {
  return utils.isObject(payload) && payload.isAxiosError === true;
}
const HttpStatusCode = {
  Continue: 100,
  SwitchingProtocols: 101,
  Processing: 102,
  EarlyHints: 103,
  Ok: 200,
  Created: 201,
  Accepted: 202,
  NonAuthoritativeInformation: 203,
  NoContent: 204,
  ResetContent: 205,
  PartialContent: 206,
  MultiStatus: 207,
  AlreadyReported: 208,
  ImUsed: 226,
  MultipleChoices: 300,
  MovedPermanently: 301,
  Found: 302,
  SeeOther: 303,
  NotModified: 304,
  UseProxy: 305,
  Unused: 306,
  TemporaryRedirect: 307,
  PermanentRedirect: 308,
  BadRequest: 400,
  Unauthorized: 401,
  PaymentRequired: 402,
  Forbidden: 403,
  NotFound: 404,
  MethodNotAllowed: 405,
  NotAcceptable: 406,
  ProxyAuthenticationRequired: 407,
  RequestTimeout: 408,
  Conflict: 409,
  Gone: 410,
  LengthRequired: 411,
  PreconditionFailed: 412,
  PayloadTooLarge: 413,
  UriTooLong: 414,
  UnsupportedMediaType: 415,
  RangeNotSatisfiable: 416,
  ExpectationFailed: 417,
  ImATeapot: 418,
  MisdirectedRequest: 421,
  UnprocessableEntity: 422,
  Locked: 423,
  FailedDependency: 424,
  TooEarly: 425,
  UpgradeRequired: 426,
  PreconditionRequired: 428,
  TooManyRequests: 429,
  RequestHeaderFieldsTooLarge: 431,
  UnavailableForLegalReasons: 451,
  InternalServerError: 500,
  NotImplemented: 501,
  BadGateway: 502,
  ServiceUnavailable: 503,
  GatewayTimeout: 504,
  HttpVersionNotSupported: 505,
  VariantAlsoNegotiates: 506,
  InsufficientStorage: 507,
  LoopDetected: 508,
  NotExtended: 510,
  NetworkAuthenticationRequired: 511
};
Object.entries(HttpStatusCode).forEach(([key, value]) => {
  HttpStatusCode[value] = key;
});
function createInstance(defaultConfig) {
  const context = new Axios(defaultConfig);
  const instance = bind(Axios.prototype.request, context);
  utils.extend(instance, Axios.prototype, context, {allOwnKeys: true});
  utils.extend(instance, context, null, {allOwnKeys: true});
  instance.create = function create(instanceConfig) {
    return createInstance(mergeConfig(defaultConfig, instanceConfig));
  };
  return instance;
}
const axios = createInstance(defaults);
axios.Axios = Axios;
axios.CanceledError = CanceledError;
axios.CancelToken = CancelToken;
axios.isCancel = isCancel;
axios.VERSION = VERSION;
axios.toFormData = toFormData;
axios.AxiosError = AxiosError;
axios.Cancel = axios.CanceledError;
axios.all = function all(promises) {
  return Promise.all(promises);
};
axios.spread = spread;
axios.isAxiosError = isAxiosError;
axios.mergeConfig = mergeConfig;
axios.AxiosHeaders = AxiosHeaders;
axios.formToJSON = (thing) => formDataToJSON(utils.isHTMLForm(thing) ? new FormData(thing) : thing);
axios.HttpStatusCode = HttpStatusCode;
axios.default = axios;

const matchIconName = /^[a-z0-9]+(-[a-z0-9]+)*$/;
const stringToIcon = (value, validate, allowSimpleName, provider = "") => {
  const colonSeparated = value.split(":");
  if (value.slice(0, 1) === "@") {
    if (colonSeparated.length < 2 || colonSeparated.length > 3) {
      return null;
    }
    provider = colonSeparated.shift().slice(1);
  }
  if (colonSeparated.length > 3 || !colonSeparated.length) {
    return null;
  }
  if (colonSeparated.length > 1) {
    const name2 = colonSeparated.pop();
    const prefix = colonSeparated.pop();
    const result = {
      provider: colonSeparated.length > 0 ? colonSeparated[0] : provider,
      prefix,
      name: name2
    };
    return validate && !validateIconName(result) ? null : result;
  }
  const name = colonSeparated[0];
  const dashSeparated = name.split("-");
  if (dashSeparated.length > 1) {
    const result = {
      provider,
      prefix: dashSeparated.shift(),
      name: dashSeparated.join("-")
    };
    return validate && !validateIconName(result) ? null : result;
  }
  if (allowSimpleName && provider === "") {
    const result = {
      provider,
      prefix: "",
      name
    };
    return validate && !validateIconName(result, allowSimpleName) ? null : result;
  }
  return null;
};
const validateIconName = (icon, allowSimpleName) => {
  if (!icon) {
    return false;
  }
  return !!((icon.provider === "" || icon.provider.match(matchIconName)) && (allowSimpleName && icon.prefix === "" || icon.prefix.match(matchIconName)) && icon.name.match(matchIconName));
};
const defaultIconDimensions = Object.freeze({
  left: 0,
  top: 0,
  width: 16,
  height: 16
});
const defaultIconTransformations = Object.freeze({
  rotate: 0,
  vFlip: false,
  hFlip: false
});
const defaultIconProps = Object.freeze({
  ...defaultIconDimensions,
  ...defaultIconTransformations
});
const defaultExtendedIconProps = Object.freeze({
  ...defaultIconProps,
  body: "",
  hidden: false
});
function mergeIconTransformations(obj1, obj2) {
  const result = {};
  if (!obj1.hFlip !== !obj2.hFlip) {
    result.hFlip = true;
  }
  if (!obj1.vFlip !== !obj2.vFlip) {
    result.vFlip = true;
  }
  const rotate = ((obj1.rotate || 0) + (obj2.rotate || 0)) % 4;
  if (rotate) {
    result.rotate = rotate;
  }
  return result;
}
function mergeIconData(parent, child) {
  const result = mergeIconTransformations(parent, child);
  for (const key in defaultExtendedIconProps) {
    if (key in defaultIconTransformations) {
      if (key in parent && !(key in result)) {
        result[key] = defaultIconTransformations[key];
      }
    } else if (key in child) {
      result[key] = child[key];
    } else if (key in parent) {
      result[key] = parent[key];
    }
  }
  return result;
}
function getIconsTree(data, names) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  const resolved = /* @__PURE__ */ Object.create(null);
  function resolve(name) {
    if (icons[name]) {
      return resolved[name] = [];
    }
    if (!(name in resolved)) {
      resolved[name] = null;
      const parent = aliases[name] && aliases[name].parent;
      const value = parent && resolve(parent);
      if (value) {
        resolved[name] = [parent].concat(value);
      }
    }
    return resolved[name];
  }
  (names || Object.keys(icons).concat(Object.keys(aliases))).forEach(resolve);
  return resolved;
}
function internalGetIconData(data, name, tree) {
  const icons = data.icons;
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  let currentProps = {};
  function parse(name2) {
    currentProps = mergeIconData(icons[name2] || aliases[name2], currentProps);
  }
  parse(name);
  tree.forEach(parse);
  return mergeIconData(data, currentProps);
}
function parseIconSet(data, callback) {
  const names = [];
  if (typeof data !== "object" || typeof data.icons !== "object") {
    return names;
  }
  if (data.not_found instanceof Array) {
    data.not_found.forEach((name) => {
      callback(name, null);
      names.push(name);
    });
  }
  const tree = getIconsTree(data);
  for (const name in tree) {
    const item = tree[name];
    if (item) {
      callback(name, internalGetIconData(data, name, item));
      names.push(name);
    }
  }
  return names;
}
const optionalPropertyDefaults = {
  provider: "",
  aliases: {},
  not_found: {},
  ...defaultIconDimensions
};
function checkOptionalProps(item, defaults) {
  for (const prop in defaults) {
    if (prop in item && typeof item[prop] !== typeof defaults[prop]) {
      return false;
    }
  }
  return true;
}
function quicklyValidateIconSet(obj) {
  if (typeof obj !== "object" || obj === null) {
    return null;
  }
  const data = obj;
  if (typeof data.prefix !== "string" || !obj.icons || typeof obj.icons !== "object") {
    return null;
  }
  if (!checkOptionalProps(obj, optionalPropertyDefaults)) {
    return null;
  }
  const icons = data.icons;
  for (const name in icons) {
    const icon = icons[name];
    if (!name.match(matchIconName) || typeof icon.body !== "string" || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  const aliases = data.aliases || /* @__PURE__ */ Object.create(null);
  for (const name in aliases) {
    const icon = aliases[name];
    const parent = icon.parent;
    if (!name.match(matchIconName) || typeof parent !== "string" || !icons[parent] && !aliases[parent] || !checkOptionalProps(icon, defaultExtendedIconProps)) {
      return null;
    }
  }
  return data;
}
const dataStorage = /* @__PURE__ */ Object.create(null);
function newStorage(provider, prefix) {
  return {
    provider,
    prefix,
    icons: /* @__PURE__ */ Object.create(null),
    missing: /* @__PURE__ */ new Set()
  };
}
function getStorage(provider, prefix) {
  const providerStorage = dataStorage[provider] || (dataStorage[provider] = /* @__PURE__ */ Object.create(null));
  return providerStorage[prefix] || (providerStorage[prefix] = newStorage(provider, prefix));
}
function addIconSet(storage2, data) {
  if (!quicklyValidateIconSet(data)) {
    return [];
  }
  return parseIconSet(data, (name, icon) => {
    if (icon) {
      storage2.icons[name] = icon;
    } else {
      storage2.missing.add(name);
    }
  });
}
function addIconToStorage(storage2, name, icon) {
  try {
    if (typeof icon.body === "string") {
      storage2.icons[name] = {...icon};
      return true;
    }
  } catch (err) {
  }
  return false;
}
let simpleNames = false;
function allowSimpleNames(allow) {
  if (typeof allow === "boolean") {
    simpleNames = allow;
  }
  return simpleNames;
}
function getIconData(name) {
  const icon = typeof name === "string" ? stringToIcon(name, true, simpleNames) : name;
  if (icon) {
    const storage2 = getStorage(icon.provider, icon.prefix);
    const iconName = icon.name;
    return storage2.icons[iconName] || (storage2.missing.has(iconName) ? null : void 0);
  }
}
function addIcon(name, data) {
  const icon = stringToIcon(name, true, simpleNames);
  if (!icon) {
    return false;
  }
  const storage2 = getStorage(icon.provider, icon.prefix);
  return addIconToStorage(storage2, icon.name, data);
}
function addCollection(data, provider) {
  if (typeof data !== "object") {
    return false;
  }
  if (typeof provider !== "string") {
    provider = data.provider || "";
  }
  if (simpleNames && !provider && !data.prefix) {
    let added = false;
    if (quicklyValidateIconSet(data)) {
      data.prefix = "";
      parseIconSet(data, (name, icon) => {
        if (icon && addIcon(name, icon)) {
          added = true;
        }
      });
    }
    return added;
  }
  const prefix = data.prefix;
  if (!validateIconName({
    provider,
    prefix,
    name: "a"
  })) {
    return false;
  }
  const storage2 = getStorage(provider, prefix);
  return !!addIconSet(storage2, data);
}
const defaultIconSizeCustomisations = Object.freeze({
  width: null,
  height: null
});
const defaultIconCustomisations = Object.freeze({
  ...defaultIconSizeCustomisations,
  ...defaultIconTransformations
});
const unitsSplit = /(-?[0-9.]*[0-9]+[0-9.]*)/g;
const unitsTest = /^-?[0-9.]*[0-9]+[0-9.]*$/g;
function calculateSize(size, ratio, precision) {
  if (ratio === 1) {
    return size;
  }
  precision = precision || 100;
  if (typeof size === "number") {
    return Math.ceil(size * ratio * precision) / precision;
  }
  if (typeof size !== "string") {
    return size;
  }
  const oldParts = size.split(unitsSplit);
  if (oldParts === null || !oldParts.length) {
    return size;
  }
  const newParts = [];
  let code = oldParts.shift();
  let isNumber = unitsTest.test(code);
  while (true) {
    if (isNumber) {
      const num = parseFloat(code);
      if (isNaN(num)) {
        newParts.push(code);
      } else {
        newParts.push(Math.ceil(num * ratio * precision) / precision);
      }
    } else {
      newParts.push(code);
    }
    code = oldParts.shift();
    if (code === void 0) {
      return newParts.join("");
    }
    isNumber = !isNumber;
  }
}
const isUnsetKeyword = (value) => value === "unset" || value === "undefined" || value === "none";
function iconToSVG(icon, customisations) {
  const fullIcon = {
    ...defaultIconProps,
    ...icon
  };
  const fullCustomisations = {
    ...defaultIconCustomisations,
    ...customisations
  };
  const box = {
    left: fullIcon.left,
    top: fullIcon.top,
    width: fullIcon.width,
    height: fullIcon.height
  };
  let body = fullIcon.body;
  [fullIcon, fullCustomisations].forEach((props) => {
    const transformations = [];
    const hFlip = props.hFlip;
    const vFlip = props.vFlip;
    let rotation = props.rotate;
    if (hFlip) {
      if (vFlip) {
        rotation += 2;
      } else {
        transformations.push("translate(" + (box.width + box.left).toString() + " " + (0 - box.top).toString() + ")");
        transformations.push("scale(-1 1)");
        box.top = box.left = 0;
      }
    } else if (vFlip) {
      transformations.push("translate(" + (0 - box.left).toString() + " " + (box.height + box.top).toString() + ")");
      transformations.push("scale(1 -1)");
      box.top = box.left = 0;
    }
    let tempValue;
    if (rotation < 0) {
      rotation -= Math.floor(rotation / 4) * 4;
    }
    rotation = rotation % 4;
    switch (rotation) {
      case 1:
        tempValue = box.height / 2 + box.top;
        transformations.unshift("rotate(90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
      case 2:
        transformations.unshift("rotate(180 " + (box.width / 2 + box.left).toString() + " " + (box.height / 2 + box.top).toString() + ")");
        break;
      case 3:
        tempValue = box.width / 2 + box.left;
        transformations.unshift("rotate(-90 " + tempValue.toString() + " " + tempValue.toString() + ")");
        break;
    }
    if (rotation % 2 === 1) {
      if (box.left !== box.top) {
        tempValue = box.left;
        box.left = box.top;
        box.top = tempValue;
      }
      if (box.width !== box.height) {
        tempValue = box.width;
        box.width = box.height;
        box.height = tempValue;
      }
    }
    if (transformations.length) {
      body = '<g transform="' + transformations.join(" ") + '">' + body + "</g>";
    }
  });
  const customisationsWidth = fullCustomisations.width;
  const customisationsHeight = fullCustomisations.height;
  const boxWidth = box.width;
  const boxHeight = box.height;
  let width;
  let height;
  if (customisationsWidth === null) {
    height = customisationsHeight === null ? "1em" : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
    width = calculateSize(height, boxWidth / boxHeight);
  } else {
    width = customisationsWidth === "auto" ? boxWidth : customisationsWidth;
    height = customisationsHeight === null ? calculateSize(width, boxHeight / boxWidth) : customisationsHeight === "auto" ? boxHeight : customisationsHeight;
  }
  const attributes = {};
  const setAttr = (prop, value) => {
    if (!isUnsetKeyword(value)) {
      attributes[prop] = value.toString();
    }
  };
  setAttr("width", width);
  setAttr("height", height);
  attributes.viewBox = box.left.toString() + " " + box.top.toString() + " " + boxWidth.toString() + " " + boxHeight.toString();
  return {
    attributes,
    body
  };
}
const regex = /\sid="(\S+)"/g;
const randomPrefix = "IconifyId" + Date.now().toString(16) + (Math.random() * 16777216 | 0).toString(16);
let counter = 0;
function replaceIDs(body, prefix = randomPrefix) {
  const ids = [];
  let match;
  while (match = regex.exec(body)) {
    ids.push(match[1]);
  }
  if (!ids.length) {
    return body;
  }
  const suffix = "suffix" + (Math.random() * 16777216 | Date.now()).toString(16);
  ids.forEach((id) => {
    const newID = typeof prefix === "function" ? prefix(id) : prefix + (counter++).toString();
    const escapedID = id.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
    body = body.replace(new RegExp('([#;"])(' + escapedID + ')([")]|\\.[a-z])', "g"), "$1" + newID + suffix + "$3");
  });
  body = body.replace(new RegExp(suffix, "g"), "");
  return body;
}
const storage = /* @__PURE__ */ Object.create(null);
function setAPIModule(provider, item) {
  storage[provider] = item;
}
function getAPIModule(provider) {
  return storage[provider] || storage[""];
}
function createAPIConfig(source) {
  let resources;
  if (typeof source.resources === "string") {
    resources = [source.resources];
  } else {
    resources = source.resources;
    if (!(resources instanceof Array) || !resources.length) {
      return null;
    }
  }
  const result = {
    resources,
    path: source.path || "/",
    maxURL: source.maxURL || 500,
    rotate: source.rotate || 750,
    timeout: source.timeout || 5e3,
    random: source.random === true,
    index: source.index || 0,
    dataAfterTimeout: source.dataAfterTimeout !== false
  };
  return result;
}
const configStorage = /* @__PURE__ */ Object.create(null);
const fallBackAPISources = [
  "https://api.simplesvg.com",
  "https://api.unisvg.com"
];
const fallBackAPI = [];
while (fallBackAPISources.length > 0) {
  if (fallBackAPISources.length === 1) {
    fallBackAPI.push(fallBackAPISources.shift());
  } else {
    if (Math.random() > 0.5) {
      fallBackAPI.push(fallBackAPISources.shift());
    } else {
      fallBackAPI.push(fallBackAPISources.pop());
    }
  }
}
configStorage[""] = createAPIConfig({
  resources: ["https://api.iconify.design"].concat(fallBackAPI)
});
function addAPIProvider(provider, customConfig) {
  const config = createAPIConfig(customConfig);
  if (config === null) {
    return false;
  }
  configStorage[provider] = config;
  return true;
}
function getAPIConfig(provider) {
  return configStorage[provider];
}
const detectFetch = () => {
  let callback;
  try {
    callback = fetch;
    if (typeof callback === "function") {
      return callback;
    }
  } catch (err) {
  }
};
let fetchModule = detectFetch();
function calculateMaxLength(provider, prefix) {
  const config = getAPIConfig(provider);
  if (!config) {
    return 0;
  }
  let result;
  if (!config.maxURL) {
    result = 0;
  } else {
    let maxHostLength = 0;
    config.resources.forEach((item) => {
      const host = item;
      maxHostLength = Math.max(maxHostLength, host.length);
    });
    const url = prefix + ".json?icons=";
    result = config.maxURL - maxHostLength - config.path.length - url.length;
  }
  return result;
}
function shouldAbort(status) {
  return status === 404;
}
const prepare = (provider, prefix, icons) => {
  const results = [];
  const maxLength = calculateMaxLength(provider, prefix);
  const type = "icons";
  let item = {
    type,
    provider,
    prefix,
    icons: []
  };
  let length = 0;
  icons.forEach((name, index) => {
    length += name.length + 1;
    if (length >= maxLength && index > 0) {
      results.push(item);
      item = {
        type,
        provider,
        prefix,
        icons: []
      };
      length = name.length;
    }
    item.icons.push(name);
  });
  results.push(item);
  return results;
};
function getPath(provider) {
  if (typeof provider === "string") {
    const config = getAPIConfig(provider);
    if (config) {
      return config.path;
    }
  }
  return "/";
}
const send = (host, params, callback) => {
  if (!fetchModule) {
    callback("abort", 424);
    return;
  }
  let path = getPath(params.provider);
  switch (params.type) {
    case "icons": {
      const prefix = params.prefix;
      const icons = params.icons;
      const iconsList = icons.join(",");
      const urlParams = new URLSearchParams({
        icons: iconsList
      });
      path += prefix + ".json?" + urlParams.toString();
      break;
    }
    case "custom": {
      const uri = params.uri;
      path += uri.slice(0, 1) === "/" ? uri.slice(1) : uri;
      break;
    }
    default:
      callback("abort", 400);
      return;
  }
  let defaultError = 503;
  fetchModule(host + path).then((response) => {
    const status = response.status;
    if (status !== 200) {
      setTimeout(() => {
        callback(shouldAbort(status) ? "abort" : "next", status);
      });
      return;
    }
    defaultError = 501;
    return response.json();
  }).then((data) => {
    if (typeof data !== "object" || data === null) {
      setTimeout(() => {
        if (data === 404) {
          callback("abort", data);
        } else {
          callback("next", defaultError);
        }
      });
      return;
    }
    setTimeout(() => {
      callback("success", data);
    });
  }).catch(() => {
    callback("next", defaultError);
  });
};
const fetchAPIModule = {
  prepare,
  send
};
function sortIcons(icons) {
  const result = {
    loaded: [],
    missing: [],
    pending: []
  };
  const storage2 = /* @__PURE__ */ Object.create(null);
  icons.sort((a, b) => {
    if (a.provider !== b.provider) {
      return a.provider.localeCompare(b.provider);
    }
    if (a.prefix !== b.prefix) {
      return a.prefix.localeCompare(b.prefix);
    }
    return a.name.localeCompare(b.name);
  });
  let lastIcon = {
    provider: "",
    prefix: "",
    name: ""
  };
  icons.forEach((icon) => {
    if (lastIcon.name === icon.name && lastIcon.prefix === icon.prefix && lastIcon.provider === icon.provider) {
      return;
    }
    lastIcon = icon;
    const provider = icon.provider;
    const prefix = icon.prefix;
    const name = icon.name;
    const providerStorage = storage2[provider] || (storage2[provider] = /* @__PURE__ */ Object.create(null));
    const localStorage = providerStorage[prefix] || (providerStorage[prefix] = getStorage(provider, prefix));
    let list;
    if (name in localStorage.icons) {
      list = result.loaded;
    } else if (prefix === "" || localStorage.missing.has(name)) {
      list = result.missing;
    } else {
      list = result.pending;
    }
    const item = {
      provider,
      prefix,
      name
    };
    list.push(item);
  });
  return result;
}
function removeCallback(storages, id) {
  storages.forEach((storage2) => {
    const items = storage2.loaderCallbacks;
    if (items) {
      storage2.loaderCallbacks = items.filter((row) => row.id !== id);
    }
  });
}
function updateCallbacks(storage2) {
  if (!storage2.pendingCallbacksFlag) {
    storage2.pendingCallbacksFlag = true;
    setTimeout(() => {
      storage2.pendingCallbacksFlag = false;
      const items = storage2.loaderCallbacks ? storage2.loaderCallbacks.slice(0) : [];
      if (!items.length) {
        return;
      }
      let hasPending = false;
      const provider = storage2.provider;
      const prefix = storage2.prefix;
      items.forEach((item) => {
        const icons = item.icons;
        const oldLength = icons.pending.length;
        icons.pending = icons.pending.filter((icon) => {
          if (icon.prefix !== prefix) {
            return true;
          }
          const name = icon.name;
          if (storage2.icons[name]) {
            icons.loaded.push({
              provider,
              prefix,
              name
            });
          } else if (storage2.missing.has(name)) {
            icons.missing.push({
              provider,
              prefix,
              name
            });
          } else {
            hasPending = true;
            return true;
          }
          return false;
        });
        if (icons.pending.length !== oldLength) {
          if (!hasPending) {
            removeCallback([storage2], item.id);
          }
          item.callback(icons.loaded.slice(0), icons.missing.slice(0), icons.pending.slice(0), item.abort);
        }
      });
    });
  }
}
let idCounter = 0;
function storeCallback(callback, icons, pendingSources) {
  const id = idCounter++;
  const abort = removeCallback.bind(null, pendingSources, id);
  if (!icons.pending.length) {
    return abort;
  }
  const item = {
    id,
    icons,
    callback,
    abort
  };
  pendingSources.forEach((storage2) => {
    (storage2.loaderCallbacks || (storage2.loaderCallbacks = [])).push(item);
  });
  return abort;
}
function listToIcons(list, validate = true, simpleNames2 = false) {
  const result = [];
  list.forEach((item) => {
    const icon = typeof item === "string" ? stringToIcon(item, validate, simpleNames2) : item;
    if (icon) {
      result.push(icon);
    }
  });
  return result;
}
var defaultConfig = {
  resources: [],
  index: 0,
  timeout: 2e3,
  rotate: 750,
  random: false,
  dataAfterTimeout: false
};
function sendQuery(config, payload, query, done) {
  const resourcesCount = config.resources.length;
  const startIndex = config.random ? Math.floor(Math.random() * resourcesCount) : config.index;
  let resources;
  if (config.random) {
    let list = config.resources.slice(0);
    resources = [];
    while (list.length > 1) {
      const nextIndex = Math.floor(Math.random() * list.length);
      resources.push(list[nextIndex]);
      list = list.slice(0, nextIndex).concat(list.slice(nextIndex + 1));
    }
    resources = resources.concat(list);
  } else {
    resources = config.resources.slice(startIndex).concat(config.resources.slice(0, startIndex));
  }
  const startTime = Date.now();
  let status = "pending";
  let queriesSent = 0;
  let lastError;
  let timer = null;
  let queue = [];
  let doneCallbacks = [];
  if (typeof done === "function") {
    doneCallbacks.push(done);
  }
  function resetTimer() {
    if (timer) {
      clearTimeout(timer);
      timer = null;
    }
  }
  function abort() {
    if (status === "pending") {
      status = "aborted";
    }
    resetTimer();
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function subscribe(callback, overwrite) {
    if (overwrite) {
      doneCallbacks = [];
    }
    if (typeof callback === "function") {
      doneCallbacks.push(callback);
    }
  }
  function getQueryStatus() {
    return {
      startTime,
      payload,
      status,
      queriesSent,
      queriesPending: queue.length,
      subscribe,
      abort
    };
  }
  function failQuery() {
    status = "failed";
    doneCallbacks.forEach((callback) => {
      callback(void 0, lastError);
    });
  }
  function clearQueue() {
    queue.forEach((item) => {
      if (item.status === "pending") {
        item.status = "aborted";
      }
    });
    queue = [];
  }
  function moduleResponse(item, response, data) {
    const isError = response !== "success";
    queue = queue.filter((queued) => queued !== item);
    switch (status) {
      case "pending":
        break;
      case "failed":
        if (isError || !config.dataAfterTimeout) {
          return;
        }
        break;
      default:
        return;
    }
    if (response === "abort") {
      lastError = data;
      failQuery();
      return;
    }
    if (isError) {
      lastError = data;
      if (!queue.length) {
        if (!resources.length) {
          failQuery();
        } else {
          execNext();
        }
      }
      return;
    }
    resetTimer();
    clearQueue();
    if (!config.random) {
      const index = config.resources.indexOf(item.resource);
      if (index !== -1 && index !== config.index) {
        config.index = index;
      }
    }
    status = "completed";
    doneCallbacks.forEach((callback) => {
      callback(data);
    });
  }
  function execNext() {
    if (status !== "pending") {
      return;
    }
    resetTimer();
    const resource = resources.shift();
    if (resource === void 0) {
      if (queue.length) {
        timer = setTimeout(() => {
          resetTimer();
          if (status === "pending") {
            clearQueue();
            failQuery();
          }
        }, config.timeout);
        return;
      }
      failQuery();
      return;
    }
    const item = {
      status: "pending",
      resource,
      callback: (status2, data) => {
        moduleResponse(item, status2, data);
      }
    };
    queue.push(item);
    queriesSent++;
    timer = setTimeout(execNext, config.rotate);
    query(resource, payload, item.callback);
  }
  setTimeout(execNext);
  return getQueryStatus;
}
function initRedundancy(cfg) {
  const config = {
    ...defaultConfig,
    ...cfg
  };
  let queries = [];
  function cleanup() {
    queries = queries.filter((item) => item().status === "pending");
  }
  function query(payload, queryCallback, doneCallback) {
    const query2 = sendQuery(config, payload, queryCallback, (data, error) => {
      cleanup();
      if (doneCallback) {
        doneCallback(data, error);
      }
    });
    queries.push(query2);
    return query2;
  }
  function find(callback) {
    return queries.find((value) => {
      return callback(value);
    }) || null;
  }
  const instance = {
    query,
    find,
    setIndex: (index) => {
      config.index = index;
    },
    getIndex: () => config.index,
    cleanup
  };
  return instance;
}
function emptyCallback$1() {
}
const redundancyCache = /* @__PURE__ */ Object.create(null);
function getRedundancyCache(provider) {
  if (!redundancyCache[provider]) {
    const config = getAPIConfig(provider);
    if (!config) {
      return;
    }
    const redundancy = initRedundancy(config);
    const cachedReundancy = {
      config,
      redundancy
    };
    redundancyCache[provider] = cachedReundancy;
  }
  return redundancyCache[provider];
}
function sendAPIQuery(target, query, callback) {
  let redundancy;
  let send2;
  if (typeof target === "string") {
    const api = getAPIModule(target);
    if (!api) {
      callback(void 0, 424);
      return emptyCallback$1;
    }
    send2 = api.send;
    const cached = getRedundancyCache(target);
    if (cached) {
      redundancy = cached.redundancy;
    }
  } else {
    const config = createAPIConfig(target);
    if (config) {
      redundancy = initRedundancy(config);
      const moduleKey = target.resources ? target.resources[0] : "";
      const api = getAPIModule(moduleKey);
      if (api) {
        send2 = api.send;
      }
    }
  }
  if (!redundancy || !send2) {
    callback(void 0, 424);
    return emptyCallback$1;
  }
  return redundancy.query(query, send2, callback)().abort;
}
const browserCacheVersion = "iconify2";
const browserCachePrefix = "iconify";
const browserCacheCountKey = browserCachePrefix + "-count";
const browserCacheVersionKey = browserCachePrefix + "-version";
const browserStorageHour = 36e5;
const browserStorageCacheExpiration = 168;
function getStoredItem(func, key) {
  try {
    return func.getItem(key);
  } catch (err) {
  }
}
function setStoredItem(func, key, value) {
  try {
    func.setItem(key, value);
    return true;
  } catch (err) {
  }
}
function removeStoredItem(func, key) {
  try {
    func.removeItem(key);
  } catch (err) {
  }
}
function setBrowserStorageItemsCount(storage2, value) {
  return setStoredItem(storage2, browserCacheCountKey, value.toString());
}
function getBrowserStorageItemsCount(storage2) {
  return parseInt(getStoredItem(storage2, browserCacheCountKey)) || 0;
}
const browserStorageConfig = {
  local: true,
  session: true
};
const browserStorageEmptyItems = {
  local: /* @__PURE__ */ new Set(),
  session: /* @__PURE__ */ new Set()
};
let browserStorageStatus = false;
function setBrowserStorageStatus(status) {
  browserStorageStatus = status;
}
let _window = typeof window === "undefined" ? {} : window;
function getBrowserStorage(key) {
  const attr = key + "Storage";
  try {
    if (_window && _window[attr] && typeof _window[attr].length === "number") {
      return _window[attr];
    }
  } catch (err) {
  }
  browserStorageConfig[key] = false;
}
function iterateBrowserStorage(key, callback) {
  const func = getBrowserStorage(key);
  if (!func) {
    return;
  }
  const version = getStoredItem(func, browserCacheVersionKey);
  if (version !== browserCacheVersion) {
    if (version) {
      const total2 = getBrowserStorageItemsCount(func);
      for (let i = 0; i < total2; i++) {
        removeStoredItem(func, browserCachePrefix + i.toString());
      }
    }
    setStoredItem(func, browserCacheVersionKey, browserCacheVersion);
    setBrowserStorageItemsCount(func, 0);
    return;
  }
  const minTime = Math.floor(Date.now() / browserStorageHour) - browserStorageCacheExpiration;
  const parseItem = (index) => {
    const name = browserCachePrefix + index.toString();
    const item = getStoredItem(func, name);
    if (typeof item !== "string") {
      return;
    }
    try {
      const data = JSON.parse(item);
      if (typeof data === "object" && typeof data.cached === "number" && data.cached > minTime && typeof data.provider === "string" && typeof data.data === "object" && typeof data.data.prefix === "string" && callback(data, index)) {
        return true;
      }
    } catch (err) {
    }
    removeStoredItem(func, name);
  };
  let total = getBrowserStorageItemsCount(func);
  for (let i = total - 1; i >= 0; i--) {
    if (!parseItem(i)) {
      if (i === total - 1) {
        total--;
        setBrowserStorageItemsCount(func, total);
      } else {
        browserStorageEmptyItems[key].add(i);
      }
    }
  }
}
function initBrowserStorage() {
  if (browserStorageStatus) {
    return;
  }
  setBrowserStorageStatus(true);
  for (const key in browserStorageConfig) {
    iterateBrowserStorage(key, (item) => {
      const iconSet = item.data;
      const provider = item.provider;
      const prefix = iconSet.prefix;
      const storage2 = getStorage(provider, prefix);
      if (!addIconSet(storage2, iconSet).length) {
        return false;
      }
      const lastModified = iconSet.lastModified || -1;
      storage2.lastModifiedCached = storage2.lastModifiedCached ? Math.min(storage2.lastModifiedCached, lastModified) : lastModified;
      return true;
    });
  }
}
function updateLastModified(storage2, lastModified) {
  const lastValue = storage2.lastModifiedCached;
  if (lastValue && lastValue >= lastModified) {
    return lastValue === lastModified;
  }
  storage2.lastModifiedCached = lastModified;
  if (lastValue) {
    for (const key in browserStorageConfig) {
      iterateBrowserStorage(key, (item) => {
        const iconSet = item.data;
        return item.provider !== storage2.provider || iconSet.prefix !== storage2.prefix || iconSet.lastModified === lastModified;
      });
    }
  }
  return true;
}
function storeInBrowserStorage(storage2, data) {
  if (!browserStorageStatus) {
    initBrowserStorage();
  }
  function store(key) {
    let func;
    if (!browserStorageConfig[key] || !(func = getBrowserStorage(key))) {
      return;
    }
    const set = browserStorageEmptyItems[key];
    let index;
    if (set.size) {
      set.delete(index = Array.from(set).shift());
    } else {
      index = getBrowserStorageItemsCount(func);
      if (!setBrowserStorageItemsCount(func, index + 1)) {
        return;
      }
    }
    const item = {
      cached: Math.floor(Date.now() / browserStorageHour),
      provider: storage2.provider,
      data
    };
    return setStoredItem(func, browserCachePrefix + index.toString(), JSON.stringify(item));
  }
  if (data.lastModified && !updateLastModified(storage2, data.lastModified)) {
    return;
  }
  if (!Object.keys(data.icons).length) {
    return;
  }
  if (data.not_found) {
    data = Object.assign({}, data);
    delete data.not_found;
  }
  if (!store("local")) {
    store("session");
  }
}
function emptyCallback() {
}
function loadedNewIcons(storage2) {
  if (!storage2.iconsLoaderFlag) {
    storage2.iconsLoaderFlag = true;
    setTimeout(() => {
      storage2.iconsLoaderFlag = false;
      updateCallbacks(storage2);
    });
  }
}
function loadNewIcons(storage2, icons) {
  if (!storage2.iconsToLoad) {
    storage2.iconsToLoad = icons;
  } else {
    storage2.iconsToLoad = storage2.iconsToLoad.concat(icons).sort();
  }
  if (!storage2.iconsQueueFlag) {
    storage2.iconsQueueFlag = true;
    setTimeout(() => {
      storage2.iconsQueueFlag = false;
      const {provider, prefix} = storage2;
      const icons2 = storage2.iconsToLoad;
      delete storage2.iconsToLoad;
      let api;
      if (!icons2 || !(api = getAPIModule(provider))) {
        return;
      }
      const params = api.prepare(provider, prefix, icons2);
      params.forEach((item) => {
        sendAPIQuery(provider, item, (data) => {
          if (typeof data !== "object") {
            item.icons.forEach((name) => {
              storage2.missing.add(name);
            });
          } else {
            try {
              const parsed = addIconSet(storage2, data);
              if (!parsed.length) {
                return;
              }
              const pending = storage2.pendingIcons;
              if (pending) {
                parsed.forEach((name) => {
                  pending.delete(name);
                });
              }
              storeInBrowserStorage(storage2, data);
            } catch (err) {
              console.error(err);
            }
          }
          loadedNewIcons(storage2);
        });
      });
    });
  }
}
const loadIcons = (icons, callback) => {
  const cleanedIcons = listToIcons(icons, true, allowSimpleNames());
  const sortedIcons = sortIcons(cleanedIcons);
  if (!sortedIcons.pending.length) {
    let callCallback = true;
    if (callback) {
      setTimeout(() => {
        if (callCallback) {
          callback(sortedIcons.loaded, sortedIcons.missing, sortedIcons.pending, emptyCallback);
        }
      });
    }
    return () => {
      callCallback = false;
    };
  }
  const newIcons = /* @__PURE__ */ Object.create(null);
  const sources = [];
  let lastProvider, lastPrefix;
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix} = icon;
    if (prefix === lastPrefix && provider === lastProvider) {
      return;
    }
    lastProvider = provider;
    lastPrefix = prefix;
    sources.push(getStorage(provider, prefix));
    const providerNewIcons = newIcons[provider] || (newIcons[provider] = /* @__PURE__ */ Object.create(null));
    if (!providerNewIcons[prefix]) {
      providerNewIcons[prefix] = [];
    }
  });
  sortedIcons.pending.forEach((icon) => {
    const {provider, prefix, name} = icon;
    const storage2 = getStorage(provider, prefix);
    const pendingQueue = storage2.pendingIcons || (storage2.pendingIcons = /* @__PURE__ */ new Set());
    if (!pendingQueue.has(name)) {
      pendingQueue.add(name);
      newIcons[provider][prefix].push(name);
    }
  });
  sources.forEach((storage2) => {
    const {provider, prefix} = storage2;
    if (newIcons[provider][prefix].length) {
      loadNewIcons(storage2, newIcons[provider][prefix]);
    }
  });
  return callback ? storeCallback(callback, sortedIcons, sources) : emptyCallback;
};
function mergeCustomisations(defaults, item) {
  const result = {
    ...defaults
  };
  for (const key in item) {
    const value = item[key];
    const valueType = typeof value;
    if (key in defaultIconSizeCustomisations) {
      if (value === null || value && (valueType === "string" || valueType === "number")) {
        result[key] = value;
      }
    } else if (valueType === typeof result[key]) {
      result[key] = key === "rotate" ? value % 4 : value;
    }
  }
  return result;
}
const separator = /[\s,]+/;
function flipFromString(custom, flip) {
  flip.split(separator).forEach((str) => {
    const value = str.trim();
    switch (value) {
      case "horizontal":
        custom.hFlip = true;
        break;
      case "vertical":
        custom.vFlip = true;
        break;
    }
  });
}
function rotateFromString(value, defaultValue = 0) {
  const units = value.replace(/^-?[0-9.]*/, "");
  function cleanup(value2) {
    while (value2 < 0) {
      value2 += 4;
    }
    return value2 % 4;
  }
  if (units === "") {
    const num = parseInt(value);
    return isNaN(num) ? 0 : cleanup(num);
  } else if (units !== value) {
    let split = 0;
    switch (units) {
      case "%":
        split = 25;
        break;
      case "deg":
        split = 90;
    }
    if (split) {
      let num = parseFloat(value.slice(0, value.length - units.length));
      if (isNaN(num)) {
        return 0;
      }
      num = num / split;
      return num % 1 === 0 ? cleanup(num) : 0;
    }
  }
  return defaultValue;
}
function iconToHTML(body, attributes) {
  let renderAttribsHTML = body.indexOf("xlink:") === -1 ? "" : ' xmlns:xlink="http://www.w3.org/1999/xlink"';
  for (const attr in attributes) {
    renderAttribsHTML += " " + attr + '="' + attributes[attr] + '"';
  }
  return '<svg xmlns="http://www.w3.org/2000/svg"' + renderAttribsHTML + ">" + body + "</svg>";
}
function encodeSVGforURL(svg) {
  return svg.replace(/"/g, "'").replace(/%/g, "%25").replace(/#/g, "%23").replace(/</g, "%3C").replace(/>/g, "%3E").replace(/\s+/g, " ");
}
function svgToData(svg) {
  return "data:image/svg+xml," + encodeSVGforURL(svg);
}
function svgToURL(svg) {
  return 'url("' + svgToData(svg) + '")';
}
const defaultExtendedIconCustomisations = {
  ...defaultIconCustomisations,
  inline: false
};
const svgDefaults = {
  xmlns: "http://www.w3.org/2000/svg",
  "xmlns:xlink": "http://www.w3.org/1999/xlink",
  "aria-hidden": true,
  role: "img"
};
const commonProps = {
  display: "inline-block"
};
const monotoneProps = {
  "background-color": "currentColor"
};
const coloredProps = {
  "background-color": "transparent"
};
const propsToAdd = {
  image: "var(--svg)",
  repeat: "no-repeat",
  size: "100% 100%"
};
const propsToAddTo = {
  "-webkit-mask": monotoneProps,
  mask: monotoneProps,
  background: coloredProps
};
for (const prefix in propsToAddTo) {
  const list = propsToAddTo[prefix];
  for (const prop in propsToAdd) {
    list[prefix + "-" + prop] = propsToAdd[prop];
  }
}
function fixSize(value) {
  return value + (value.match(/^[-0-9.]+$/) ? "px" : "");
}
function render(icon, props) {
  const customisations = mergeCustomisations(defaultExtendedIconCustomisations, props);
  const mode = props.mode || "svg";
  const componentProps = mode === "svg" ? {...svgDefaults} : {};
  if (icon.body.indexOf("xlink:") === -1) {
    delete componentProps["xmlns:xlink"];
  }
  let style = typeof props.style === "string" ? props.style : "";
  for (let key in props) {
    const value = props[key];
    if (value === void 0) {
      continue;
    }
    switch (key) {
      case "icon":
      case "style":
      case "onLoad":
      case "mode":
        break;
      case "inline":
      case "hFlip":
      case "vFlip":
        customisations[key] = value === true || value === "true" || value === 1;
        break;
      case "flip":
        if (typeof value === "string") {
          flipFromString(customisations, value);
        }
        break;
      case "color":
        style = style + (style.length > 0 && style.trim().slice(-1) !== ";" ? ";" : "") + "color: " + value + "; ";
        break;
      case "rotate":
        if (typeof value === "string") {
          customisations[key] = rotateFromString(value);
        } else if (typeof value === "number") {
          customisations[key] = value;
        }
        break;
      case "ariaHidden":
      case "aria-hidden":
        if (value !== true && value !== "true") {
          delete componentProps["aria-hidden"];
        }
        break;
      default:
        if (key.slice(0, 3) === "on:") {
          break;
        }
        if (defaultExtendedIconCustomisations[key] === void 0) {
          componentProps[key] = value;
        }
    }
  }
  const item = iconToSVG(icon, customisations);
  const renderAttribs = item.attributes;
  if (customisations.inline) {
    style = "vertical-align: -0.125em; " + style;
  }
  if (mode === "svg") {
    Object.assign(componentProps, renderAttribs);
    if (style !== "") {
      componentProps.style = style;
    }
    let localCounter = 0;
    let id = props.id;
    if (typeof id === "string") {
      id = id.replace(/-/g, "_");
    }
    return {
      svg: true,
      attributes: componentProps,
      body: replaceIDs(item.body, id ? () => id + "ID" + localCounter++ : "iconifySvelte")
    };
  }
  const {body, width, height} = icon;
  const useMask = mode === "mask" || (mode === "bg" ? false : body.indexOf("currentColor") !== -1);
  const html = iconToHTML(body, {
    ...renderAttribs,
    width: width + "",
    height: height + ""
  });
  const url = svgToURL(html);
  const styles = {
    "--svg": url
  };
  const size = (prop) => {
    const value = renderAttribs[prop];
    if (value) {
      styles[prop] = fixSize(value);
    }
  };
  size("width");
  size("height");
  Object.assign(styles, commonProps, useMask ? monotoneProps : coloredProps);
  let customStyle = "";
  for (const key in styles) {
    customStyle += key + ": " + styles[key] + ";";
  }
  componentProps.style = customStyle + style;
  return {
    svg: false,
    attributes: componentProps
  };
}
allowSimpleNames(true);
setAPIModule("", fetchAPIModule);
if (typeof document !== "undefined" && typeof window !== "undefined") {
  initBrowserStorage();
  const _window2 = window;
  if (_window2.IconifyPreload !== void 0) {
    const preload = _window2.IconifyPreload;
    const err = "Invalid IconifyPreload syntax.";
    if (typeof preload === "object" && preload !== null) {
      (preload instanceof Array ? preload : [preload]).forEach((item) => {
        try {
          if (typeof item !== "object" || item === null || item instanceof Array || typeof item.icons !== "object" || typeof item.prefix !== "string" || !addCollection(item)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      });
    }
  }
  if (_window2.IconifyProviders !== void 0) {
    const providers = _window2.IconifyProviders;
    if (typeof providers === "object" && providers !== null) {
      for (let key in providers) {
        const err = "IconifyProviders[" + key + "] is invalid.";
        try {
          const value = providers[key];
          if (typeof value !== "object" || !value || value.resources === void 0) {
            continue;
          }
          if (!addAPIProvider(key, value)) {
            console.error(err);
          }
        } catch (e) {
          console.error(err);
        }
      }
    }
  }
}
function checkIconState(icon, state, mounted, callback, onload) {
  function abortLoading() {
    if (state.loading) {
      state.loading.abort();
      state.loading = null;
    }
  }
  if (typeof icon === "object" && icon !== null && typeof icon.body === "string") {
    state.name = "";
    abortLoading();
    return {data: {...defaultIconProps, ...icon}};
  }
  let iconName;
  if (typeof icon !== "string" || (iconName = stringToIcon(icon, false, true)) === null) {
    abortLoading();
    return null;
  }
  const data = getIconData(iconName);
  if (!data) {
    if (mounted && (!state.loading || state.loading.name !== icon)) {
      abortLoading();
      state.name = "";
      state.loading = {
        name: icon,
        abort: loadIcons([iconName], callback)
      };
    }
    return null;
  }
  abortLoading();
  if (state.name !== icon) {
    state.name = icon;
    if (onload && !state.destroyed) {
      onload(icon);
    }
  }
  const classes = ["iconify"];
  if (iconName.prefix !== "") {
    classes.push("iconify--" + iconName.prefix);
  }
  if (iconName.provider !== "") {
    classes.push("iconify--" + iconName.provider);
  }
  return {data, classes};
}
function generateIcon(icon, props) {
  return icon ? render({
    ...defaultIconProps,
    ...icon
  }, props) : null;
}
var checkIconState_1 = checkIconState;
var generateIcon_1 = generateIcon;

/* generated by Svelte v3.58.0 */

function create_if_block(ctx) {
	let if_block_anchor;

	function select_block_type(ctx, dirty) {
		if (/*data*/ ctx[0].svg) return create_if_block_1;
		return create_else_block;
	}

	let current_block_type = select_block_type(ctx);
	let if_block = current_block_type(ctx);

	return {
		c() {
			if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, dirty) {
			if (current_block_type === (current_block_type = select_block_type(ctx)) && if_block) {
				if_block.p(ctx, dirty);
			} else {
				if_block.d(1);
				if_block = current_block_type(ctx);

				if (if_block) {
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			}
		},
		d(detaching) {
			if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

// (113:1) {:else}
function create_else_block(ctx) {
	let span;
	let span_levels = [/*data*/ ctx[0].attributes];
	let span_data = {};

	for (let i = 0; i < span_levels.length; i += 1) {
		span_data = assign(span_data, span_levels[i]);
	}

	return {
		c() {
			span = element("span");
			this.h();
		},
		l(nodes) {
			span = claim_element(nodes, "SPAN", {});
			children(span).forEach(detach);
			this.h();
		},
		h() {
			set_attributes(span, span_data);
		},
		m(target, anchor) {
			insert_hydration(target, span, anchor);
		},
		p(ctx, dirty) {
			set_attributes(span, span_data = get_spread_update(span_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(span);
		}
	};
}

// (109:1) {#if data.svg}
function create_if_block_1(ctx) {
	let svg;
	let raw_value = /*data*/ ctx[0].body + "";
	let svg_levels = [/*data*/ ctx[0].attributes];
	let svg_data = {};

	for (let i = 0; i < svg_levels.length; i += 1) {
		svg_data = assign(svg_data, svg_levels[i]);
	}

	return {
		c() {
			svg = svg_element("svg");
			this.h();
		},
		l(nodes) {
			svg = claim_svg_element(nodes, "svg", {});
			var svg_nodes = children(svg);
			svg_nodes.forEach(detach);
			this.h();
		},
		h() {
			set_svg_attributes(svg, svg_data);
		},
		m(target, anchor) {
			insert_hydration(target, svg, anchor);
			svg.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			if (dirty & /*data*/ 1 && raw_value !== (raw_value = /*data*/ ctx[0].body + "")) svg.innerHTML = raw_value;			set_svg_attributes(svg, svg_data = get_spread_update(svg_levels, [dirty & /*data*/ 1 && /*data*/ ctx[0].attributes]));
		},
		d(detaching) {
			if (detaching) detach(svg);
		}
	};
}

function create_fragment$1(ctx) {
	let if_block_anchor;
	let if_block = /*data*/ ctx[0] && create_if_block(ctx);

	return {
		c() {
			if (if_block) if_block.c();
			if_block_anchor = empty();
		},
		l(nodes) {
			if (if_block) if_block.l(nodes);
			if_block_anchor = empty();
		},
		m(target, anchor) {
			if (if_block) if_block.m(target, anchor);
			insert_hydration(target, if_block_anchor, anchor);
		},
		p(ctx, [dirty]) {
			if (/*data*/ ctx[0]) {
				if (if_block) {
					if_block.p(ctx, dirty);
				} else {
					if_block = create_if_block(ctx);
					if_block.c();
					if_block.m(if_block_anchor.parentNode, if_block_anchor);
				}
			} else if (if_block) {
				if_block.d(1);
				if_block = null;
			}
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (if_block) if_block.d(detaching);
			if (detaching) detach(if_block_anchor);
		}
	};
}

function instance$1($$self, $$props, $$invalidate) {
	const state = {
		// Last icon name
		name: '',
		// Loading status
		loading: null,
		// Destroyed status
		destroyed: false
	};

	// Mounted status
	let mounted = false;

	// Callback counter
	let counter = 0;

	// Generated data
	let data;

	const onLoad = icon => {
		// Legacy onLoad property
		if (typeof $$props.onLoad === 'function') {
			$$props.onLoad(icon);
		}

		// on:load event
		const dispatch = createEventDispatcher();

		dispatch('load', { icon });
	};

	// Increase counter when loaded to force re-calculation of data
	function loaded() {
		$$invalidate(3, counter++, counter);
	}

	// Force re-render
	onMount(() => {
		$$invalidate(2, mounted = true);
	});

	// Abort loading when component is destroyed
	onDestroy(() => {
		$$invalidate(1, state.destroyed = true, state);

		if (state.loading) {
			state.loading.abort();
			$$invalidate(1, state.loading = null, state);
		}
	});

	$$self.$$set = $$new_props => {
		$$invalidate(6, $$props = assign(assign({}, $$props), exclude_internal_props($$new_props)));
	};

	$$self.$$.update = () => {
		 {
			const iconData = checkIconState_1($$props.icon, state, mounted, loaded, onLoad);
			$$invalidate(0, data = iconData ? generateIcon_1(iconData.data, $$props) : null);

			if (data && iconData.classes) {
				// Add classes
				$$invalidate(
					0,
					data.attributes['class'] = (typeof $$props['class'] === 'string'
					? $$props['class'] + ' '
					: '') + iconData.classes.join(' '),
					data
				);
			}
		}
	};

	$$props = exclude_internal_props($$props);
	return [data, state, mounted, counter];
}

class Component$1 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$1, create_fragment$1, safe_not_equal, {});
	}
}

function fade(node, { delay = 0, duration = 400, easing = identity } = {}) {
    const o = +getComputedStyle(node).opacity;
    return {
        delay,
        duration,
        easing,
        css: t => `opacity: ${t * o}`
    };
}

/* generated by Svelte v3.58.0 */

function get_each_context(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[11] = list[i].link;
	return child_ctx;
}

function get_each_context_1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[15] = list[i];
	return child_ctx;
}

function get_each_context_2(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[11] = list[i].link;
	return child_ctx;
}

function get_then_context_1(ctx) {
	const constants_0 = /*footer*/ ctx[20].content.en;
	ctx[21] = constants_0.social;
}

function get_each_context_3(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[22] = list[i].icon;
	child_ctx[11] = list[i].link;
	return child_ctx;
}

function get_then_context(ctx) {
	const constants_0 = /*header*/ ctx[25].content.en;
	ctx[26] = constants_0.logo;
}

// (1:0)            <script>                         export let title; export let description; export let secondary_logo; export let nav;               import axios from "axios"; import Icon from "@iconify/svelte/dist/Icon.svelte"; import { fade }
function create_catch_block_2(ctx) {
	return {
		c: noop,
		l: noop,
		m: noop,
		p: noop,
		d: noop
	};
}

// (295:77)        {@const { logo }
function create_then_block_2(ctx) {
	get_then_context(ctx);
	let a;
	let raw_value = /*logo*/ ctx[26].svg + "";

	return {
		c() {
			a = element("a");
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", {
				href: true,
				class: true,
				"aria-label": true
			});

			var a_nodes = children(a);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", "https://primocms.org");
			attr(a, "class", "logo svelte-2f98hs");
			attr(a, "aria-label", "Primo main site");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			a.innerHTML = raw_value;
		},
		p(ctx, dirty) {
			get_then_context(ctx);
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (1:0)            <script>                         export let title; export let description; export let secondary_logo; export let nav;               import axios from "axios"; import Icon from "@iconify/svelte/dist/Icon.svelte"; import { fade }
function create_pending_block_2(ctx) {
	return {
		c: noop,
		l: noop,
		m: noop,
		p: noop,
		d: noop
	};
}

// (1:0)            <script>                         export let title; export let description; export let secondary_logo; export let nav;               import axios from "axios"; import Icon from "@iconify/svelte/dist/Icon.svelte"; import { fade }
function create_catch_block_1(ctx) {
	return {
		c: noop,
		l: noop,
		m: noop,
		p: noop,
		i: noop,
		o: noop,
		d: noop
	};
}

// (302:70)          {@const { social }
function create_then_block_1(ctx) {
	get_then_context_1(ctx);
	let each_1_anchor;
	let current;
	let each_value_3 = /*social*/ ctx[21];
	let each_blocks = [];

	for (let i = 0; i < each_value_3.length; i += 1) {
		each_blocks[i] = create_each_block_3(get_each_context_3(ctx, each_value_3, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	return {
		c() {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			each_1_anchor = empty();
		},
		l(nodes) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nodes);
			}

			each_1_anchor = empty();
		},
		m(target, anchor) {
			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(target, anchor);
				}
			}

			insert_hydration(target, each_1_anchor, anchor);
			current = true;
		},
		p(ctx, dirty) {
			get_then_context_1(ctx);

			if (dirty & /*parent_href, main_site*/ 64) {
				each_value_3 = /*social*/ ctx[21];
				let i;

				for (i = 0; i < each_value_3.length; i += 1) {
					const child_ctx = get_each_context_3(ctx, each_value_3, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block_3(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(each_1_anchor.parentNode, each_1_anchor);
					}
				}

				group_outros();

				for (i = each_value_3.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value_3.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			current = false;
		},
		d(detaching) {
			destroy_each(each_blocks, detaching);
			if (detaching) detach(each_1_anchor);
		}
	};
}

// (304:8) {#each social as { icon, link }}
function create_each_block_3(ctx) {
	let a;
	let icon;
	let t;
	let a_href_value;
	let current;
	icon = new Component$1({ props: { icon: /*icon*/ ctx[22] } });

	return {
		c() {
			a = element("a");
			create_component(icon.$$.fragment);
			t = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			t = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = parent_href(/*link*/ ctx[11]));
			attr(a, "class", "svelte-2f98hs");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			mount_component(icon, a, null);
			append_hydration(a, t);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

// (1:0)            <script>                         export let title; export let description; export let secondary_logo; export let nav;               import axios from "axios"; import Icon from "@iconify/svelte/dist/Icon.svelte"; import { fade }
function create_pending_block_1(ctx) {
	return {
		c: noop,
		l: noop,
		m: noop,
		p: noop,
		i: noop,
		o: noop,
		d: noop
	};
}

// (318:8) {#each nav as { link }}
function create_each_block_2(ctx) {
	let a;
	let t_value = /*link*/ ctx[11].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[11].url);
			attr(a, "class", "link svelte-2f98hs");
			toggle_class(a, "active", window.location.pathname === /*link*/ ctx[11].url);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 1 && t_value !== (t_value = /*link*/ ctx[11].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[11].url)) {
				attr(a, "href", a_href_value);
			}

			if (dirty & /*window, nav*/ 1) {
				toggle_class(a, "active", window.location.pathname === /*link*/ ctx[11].url);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

// (1:0)            <script>                         export let title; export let description; export let secondary_logo; export let nav;               import axios from "axios"; import Icon from "@iconify/svelte/dist/Icon.svelte"; import { fade }
function create_catch_block(ctx) {
	return {
		c: noop,
		l: noop,
		m: noop,
		p: noop,
		d: noop
	};
}

// (332:120)              <ul>               {#each guides as guide}
function create_then_block(ctx) {
	let ul;
	let each_value_1 = /*guides*/ ctx[14];
	let each_blocks = [];

	for (let i = 0; i < each_value_1.length; i += 1) {
		each_blocks[i] = create_each_block_1(get_each_context_1(ctx, each_value_1, i));
	}

	return {
		c() {
			ul = element("ul");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			this.h();
		},
		l(nodes) {
			ul = claim_element(nodes, "UL", { class: true });
			var ul_nodes = children(ul);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(ul_nodes);
			}

			ul_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(ul, "class", "svelte-2f98hs");
		},
		m(target, anchor) {
			insert_hydration(target, ul, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(ul, null);
				}
			}
		},
		p(ctx, dirty) {
			if (dirty & /*Site*/ 32) {
				each_value_1 = /*guides*/ ctx[14];
				let i;

				for (i = 0; i < each_value_1.length; i += 1) {
					const child_ctx = get_each_context_1(ctx, each_value_1, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_1(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(ul, null);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_1.length;
			}
		},
		d(detaching) {
			if (detaching) detach(ul);
			destroy_each(each_blocks, detaching);
		}
	};
}

// (334:14) {#each guides as guide}
function create_each_block_1(ctx) {
	let li;
	let a;
	let t0_value = /*guide*/ ctx[15].name + "";
	let t0;
	let a_href_value;
	let t1;

	return {
		c() {
			li = element("li");
			a = element("a");
			t0 = text(t0_value);
			t1 = space();
			this.h();
		},
		l(nodes) {
			li = claim_element(nodes, "LI", {});
			var li_nodes = children(li);
			a = claim_element(li_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t0 = claim_text(a_nodes, t0_value);
			a_nodes.forEach(detach);
			t1 = claim_space(li_nodes);
			li_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = "/guides/" + /*guide*/ ctx[15].url);
			attr(a, "class", "svelte-2f98hs");
		},
		m(target, anchor) {
			insert_hydration(target, li, anchor);
			append_hydration(li, a);
			append_hydration(a, t0);
			append_hydration(li, t1);
		},
		p: noop,
		d(detaching) {
			if (detaching) detach(li);
		}
	};
}

// (1:0)            <script>                         export let title; export let description; export let secondary_logo; export let nav;               import axios from "axios"; import Icon from "@iconify/svelte/dist/Icon.svelte"; import { fade }
function create_pending_block(ctx) {
	return {
		c: noop,
		l: noop,
		m: noop,
		p: noop,
		d: noop
	};
}

// (349:4) {#if mobileNavOpen}
function create_if_block$1(ctx) {
	let nav_1;
	let t;
	let button;
	let icon;
	let nav_1_transition;
	let current;
	let mounted;
	let dispose;
	let each_value = /*nav*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block(get_each_context(ctx, each_value, i));
	}

	icon = new Component$1({
			props: {
				height: "30",
				icon: "material-symbols:close"
			}
		});

	return {
		c() {
			nav_1 = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t = space();
			button = element("button");
			create_component(icon.$$.fragment);
			this.h();
		},
		l(nodes) {
			nav_1 = claim_element(nodes, "NAV", { id: true, class: true });
			var nav_1_nodes = children(nav_1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_1_nodes);
			}

			t = claim_space(nav_1_nodes);

			button = claim_element(nav_1_nodes, "BUTTON", {
				id: true,
				"aria-label": true,
				class: true
			});

			var button_nodes = children(button);
			claim_component(icon.$$.fragment, button_nodes);
			button_nodes.forEach(detach);
			nav_1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(button, "id", "close");
			attr(button, "aria-label", "Close Navigation");
			attr(button, "class", "svelte-2f98hs");
			attr(nav_1, "id", "mobile-nav");
			attr(nav_1, "class", "svelte-2f98hs");
		},
		m(target, anchor) {
			insert_hydration(target, nav_1, anchor);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav_1, null);
				}
			}

			append_hydration(nav_1, t);
			append_hydration(nav_1, button);
			mount_component(icon, button, null);
			current = true;

			if (!mounted) {
				dispose = listen(button, "click", /*toggleMobileNav*/ ctx[4]);
				mounted = true;
			}
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 1) {
				each_value = /*nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav_1, t);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value.length;
			}
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);

			add_render_callback(() => {
				if (!current) return;
				if (!nav_1_transition) nav_1_transition = create_bidirectional_transition(nav_1, fade, { duration: 200 }, true);
				nav_1_transition.run(1);
			});

			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			if (!nav_1_transition) nav_1_transition = create_bidirectional_transition(nav_1, fade, { duration: 200 }, false);
			nav_1_transition.run(0);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(nav_1);
			destroy_each(each_blocks, detaching);
			destroy_component(icon);
			if (detaching && nav_1_transition) nav_1_transition.end();
			mounted = false;
			dispose();
		}
	};
}

// (351:8) {#each nav as { link }}
function create_each_block(ctx) {
	let a;
	let t_value = /*link*/ ctx[11].label + "";
	let t;
	let a_href_value;

	return {
		c() {
			a = element("a");
			t = text(t_value);
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t = claim_text(a_nodes, t_value);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(a, "href", a_href_value = /*link*/ ctx[11].url);
			attr(a, "class", "link svelte-2f98hs");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, t);
		},
		p(ctx, dirty) {
			if (dirty & /*nav*/ 1 && t_value !== (t_value = /*link*/ ctx[11].label + "")) set_data(t, t_value);

			if (dirty & /*nav*/ 1 && a_href_value !== (a_href_value = /*link*/ ctx[11].url)) {
				attr(a, "href", a_href_value);
			}
		},
		d(detaching) {
			if (detaching) detach(a);
		}
	};
}

function create_fragment$2(ctx) {
	let div6;
	let header;
	let div0;
	let promise;
	let t0;
	let nav0;
	let promise_1;
	let t1;
	let div5;
	let div1;
	let a;
	let t2;
	let t3;
	let div4;
	let nav1;
	let t4;
	let div2;
	let button0;
	let span;
	let t5;
	let t6;
	let icon0;
	let t7;
	let promise_2;
	let t8;
	let div3;
	let button1;
	let icon1;
	let t9;
	let current;
	let mounted;
	let dispose;

	let info = {
		ctx,
		current: null,
		token: null,
		hasCatch: false,
		pending: create_pending_block_2,
		then: create_then_block_2,
		catch: create_catch_block_2,
		value: 25
	};

	handle_promise(promise = /*main_site*/ ctx[6].symbols.match({ name: "Site Navigation" }), info);

	let info_1 = {
		ctx,
		current: null,
		token: null,
		hasCatch: false,
		pending: create_pending_block_1,
		then: create_then_block_1,
		catch: create_catch_block_1,
		value: 20,
		blocks: [,,,]
	};

	handle_promise(promise_1 = /*main_site*/ ctx[6].symbols.match({ name: "Footer" }), info_1);
	let each_value_2 = /*nav*/ ctx[0];
	let each_blocks = [];

	for (let i = 0; i < each_value_2.length; i += 1) {
		each_blocks[i] = create_each_block_2(get_each_context_2(ctx, each_value_2, i));
	}

	icon0 = new Component$1({ props: { icon: "tabler:chevron-down" } });

	let info_2 = {
		ctx,
		current: null,
		token: null,
		hasCatch: false,
		pending: create_pending_block,
		then: create_then_block,
		catch: create_catch_block,
		value: 14
	};

	handle_promise(promise_2 = new /*Site*/ ctx[5]().pages.filter(func), info_2);

	icon1 = new Component$1({
			props: {
				height: "30",
				icon: "material-symbols:menu"
			}
		});

	let if_block = /*mobileNavOpen*/ ctx[1] && create_if_block$1(ctx);

	return {
		c() {
			div6 = element("div");
			header = element("header");
			div0 = element("div");
			info.block.c();
			t0 = space();
			nav0 = element("nav");
			info_1.block.c();
			t1 = space();
			div5 = element("div");
			div1 = element("div");
			a = element("a");
			t2 = text("Primo Docs");
			t3 = space();
			div4 = element("div");
			nav1 = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t4 = space();
			div2 = element("div");
			button0 = element("button");
			span = element("span");
			t5 = text("Guides");
			t6 = space();
			create_component(icon0.$$.fragment);
			t7 = space();
			info_2.block.c();
			t8 = space();
			div3 = element("div");
			button1 = element("button");
			create_component(icon1.$$.fragment);
			t9 = space();
			if (if_block) if_block.c();
			this.h();
		},
		l(nodes) {
			div6 = claim_element(nodes, "DIV", { class: true, id: true });
			var div6_nodes = children(div6);
			header = claim_element(div6_nodes, "HEADER", { class: true });
			var header_nodes = children(header);
			div0 = claim_element(header_nodes, "DIV", { class: true });
			var div0_nodes = children(div0);
			info.block.l(div0_nodes);
			t0 = claim_space(div0_nodes);
			nav0 = claim_element(div0_nodes, "NAV", { class: true });
			var nav0_nodes = children(nav0);
			info_1.block.l(nav0_nodes);
			nav0_nodes.forEach(detach);
			div0_nodes.forEach(detach);
			t1 = claim_space(header_nodes);
			div5 = claim_element(header_nodes, "DIV", { class: true });
			var div5_nodes = children(div5);
			div1 = claim_element(div5_nodes, "DIV", { class: true });
			var div1_nodes = children(div1);
			a = claim_element(div1_nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			t2 = claim_text(a_nodes, "Primo Docs");
			a_nodes.forEach(detach);
			div1_nodes.forEach(detach);
			t3 = claim_space(div5_nodes);
			div4 = claim_element(div5_nodes, "DIV", { class: true });
			var div4_nodes = children(div4);
			nav1 = claim_element(div4_nodes, "NAV", { class: true });
			var nav1_nodes = children(nav1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav1_nodes);
			}

			t4 = claim_space(nav1_nodes);
			div2 = claim_element(nav1_nodes, "DIV", { class: true });
			var div2_nodes = children(div2);
			button0 = claim_element(div2_nodes, "BUTTON", { class: true });
			var button0_nodes = children(button0);
			span = claim_element(button0_nodes, "SPAN", {});
			var span_nodes = children(span);
			t5 = claim_text(span_nodes, "Guides");
			span_nodes.forEach(detach);
			t6 = claim_space(button0_nodes);
			claim_component(icon0.$$.fragment, button0_nodes);
			button0_nodes.forEach(detach);
			t7 = claim_space(div2_nodes);
			info_2.block.l(div2_nodes);
			div2_nodes.forEach(detach);
			nav1_nodes.forEach(detach);
			t8 = claim_space(div4_nodes);
			div3 = claim_element(div4_nodes, "DIV", { class: true });
			var div3_nodes = children(div3);
			button1 = claim_element(div3_nodes, "BUTTON", { id: true, class: true });
			var button1_nodes = children(button1);
			claim_component(icon1.$$.fragment, button1_nodes);
			button1_nodes.forEach(detach);
			div3_nodes.forEach(detach);
			div4_nodes.forEach(detach);
			t9 = claim_space(div5_nodes);
			if (if_block) if_block.l(div5_nodes);
			div5_nodes.forEach(detach);
			header_nodes.forEach(detach);
			div6_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav0, "class", "svelte-2f98hs");
			attr(div0, "class", "parent-nav section-container svelte-2f98hs");
			toggle_class(div0, "loaded", /*loaded*/ ctx[3]);
			attr(a, "href", "/");
			attr(a, "class", "link svelte-2f98hs");
			attr(div1, "class", "logos svelte-2f98hs");
			attr(button0, "class", "title svelte-2f98hs");
			attr(div2, "class", "dropdown svelte-2f98hs");
			toggle_class(div2, "active", /*showing_dropdown*/ ctx[2]);
			attr(nav1, "class", "svelte-2f98hs");
			attr(button1, "id", "open");
			attr(button1, "class", "svelte-2f98hs");
			attr(div3, "class", "call-to-action svelte-2f98hs");
			attr(div4, "class", "navigation svelte-2f98hs");
			attr(div5, "class", "section-container svelte-2f98hs");
			attr(header, "class", "svelte-2f98hs");
			attr(div6, "class", "section");
			attr(div6, "id", "section-048949ec");
		},
		m(target, anchor) {
			insert_hydration(target, div6, anchor);
			append_hydration(div6, header);
			append_hydration(header, div0);
			info.block.m(div0, info.anchor = null);
			info.mount = () => div0;
			info.anchor = t0;
			append_hydration(div0, t0);
			append_hydration(div0, nav0);
			info_1.block.m(nav0, info_1.anchor = null);
			info_1.mount = () => nav0;
			info_1.anchor = null;
			append_hydration(header, t1);
			append_hydration(header, div5);
			append_hydration(div5, div1);
			append_hydration(div1, a);
			append_hydration(a, t2);
			append_hydration(div5, t3);
			append_hydration(div5, div4);
			append_hydration(div4, nav1);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav1, null);
				}
			}

			append_hydration(nav1, t4);
			append_hydration(nav1, div2);
			append_hydration(div2, button0);
			append_hydration(button0, span);
			append_hydration(span, t5);
			append_hydration(button0, t6);
			mount_component(icon0, button0, null);
			append_hydration(div2, t7);
			info_2.block.m(div2, info_2.anchor = null);
			info_2.mount = () => div2;
			info_2.anchor = null;
			append_hydration(div4, t8);
			append_hydration(div4, div3);
			append_hydration(div3, button1);
			mount_component(icon1, button1, null);
			append_hydration(div5, t9);
			if (if_block) if_block.m(div5, null);
			current = true;

			if (!mounted) {
				dispose = [
					listen(button0, "click", /*click_handler*/ ctx[10]),
					listen(button1, "click", /*toggleMobileNav*/ ctx[4])
				];

				mounted = true;
			}
		},
		p(new_ctx, [dirty]) {
			ctx = new_ctx;
			update_await_block_branch(info, ctx, dirty);
			update_await_block_branch(info_1, ctx, dirty);

			if (!current || dirty & /*loaded*/ 8) {
				toggle_class(div0, "loaded", /*loaded*/ ctx[3]);
			}

			if (dirty & /*nav, window*/ 1) {
				each_value_2 = /*nav*/ ctx[0];
				let i;

				for (i = 0; i < each_value_2.length; i += 1) {
					const child_ctx = get_each_context_2(ctx, each_value_2, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
					} else {
						each_blocks[i] = create_each_block_2(child_ctx);
						each_blocks[i].c();
						each_blocks[i].m(nav1, t4);
					}
				}

				for (; i < each_blocks.length; i += 1) {
					each_blocks[i].d(1);
				}

				each_blocks.length = each_value_2.length;
			}

			update_await_block_branch(info_2, ctx, dirty);

			if (!current || dirty & /*showing_dropdown*/ 4) {
				toggle_class(div2, "active", /*showing_dropdown*/ ctx[2]);
			}

			if (/*mobileNavOpen*/ ctx[1]) {
				if (if_block) {
					if_block.p(ctx, dirty);

					if (dirty & /*mobileNavOpen*/ 2) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block$1(ctx);
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(div5, null);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}
		},
		i(local) {
			if (current) return;
			transition_in(info_1.block);
			transition_in(icon0.$$.fragment, local);
			transition_in(icon1.$$.fragment, local);
			transition_in(if_block);
			current = true;
		},
		o(local) {
			for (let i = 0; i < 3; i += 1) {
				const block = info_1.blocks[i];
				transition_out(block);
			}

			transition_out(icon0.$$.fragment, local);
			transition_out(icon1.$$.fragment, local);
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div6);
			info.block.d();
			info.token = null;
			info = null;
			info_1.block.d();
			info_1.token = null;
			info_1 = null;
			destroy_each(each_blocks, detaching);
			destroy_component(icon0);
			info_2.block.d();
			info_2.token = null;
			info_2 = null;
			destroy_component(icon1);
			if (if_block) if_block.d();
			mounted = false;
			run_all(dispose);
		}
	};
}

function parent_href(link) {
	return link.url.startsWith("/")
	? `https://primocms.org${link.url}`
	: link.url;
}

const func = page => page.parent === "092114f6-8259-4f21-8c08-3e5dfcfe2e47";

function instance$2($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { description } = $$props;
	let { secondary_logo } = $$props;
	let { nav } = $$props;
	let mobileNavOpen = false;
	let showing_dropdown = false;

	function toggleMobileNav() {
		$$invalidate(1, mobileNavOpen = !mobileNavOpen);
	}

	class Site {
		constructor(url = '') {
			this.url = url;
			this.pages = this.createActions("pages");
			this.symbols = this.createActions("symbols");
		}

		createActions(property) {
			const url = this.url;

			return {
				match: async args => {
					const [prop] = Object.entries(args);
					const [key, value] = prop;
					const { data } = await axios.get(`${url}/primo.json`);
					const [item] = data[property].filter(item => item[key] === value);
					return item;
				},
				filter: async fn => {
					const { data } = await axios.get(`${url}/primo.json`);
					const items = data[property].filter(fn);
					return items;
				}
			};
		}

		async on_load(fn) {
			const { data } = await axios.get(`${this.url}/primo.json`);
			fn(data);
		}
	}

	// function Actions(property, url) {
	//   return {
	//     match: async (args) => {
	//       const [prop] = Object.entries(args);
	//       const [key, value] = prop;
	//       const { data } = await axios.get(`${url}/primo.json`);
	//       const [item] = data[property].filter((item) => item[key] === value);
	//       return item;
	//     },
	//     filter: async (fn) => {
	//       const { data } = await axios.get(`${url}/primo.json`);
	//       const items = data[property].filter(fn);
	//       return items;
	//     },
	//   };
	// }
	// function Site(url = "") {
	//   this.url = url;
	//   this.pages = Actions("pages", url);
	//   this.symbols = Actions("symbols", url);
	// }
	// Site.prototype.on_load = async function (fn) {
	//   console.log(this);
	//   const { data } = await axios.get(`${this.url}/primo.json`);
	//   fn(data);
	// };
	const main_site = new Site("https://primocms.org");

	let loaded = false;

	main_site.on_load(() => {
		$$invalidate(3, loaded = true);
	});

	const click_handler = () => $$invalidate(2, showing_dropdown = !showing_dropdown);

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(7, title = $$props.title);
		if ('description' in $$props) $$invalidate(8, description = $$props.description);
		if ('secondary_logo' in $$props) $$invalidate(9, secondary_logo = $$props.secondary_logo);
		if ('nav' in $$props) $$invalidate(0, nav = $$props.nav);
	};

	return [
		nav,
		mobileNavOpen,
		showing_dropdown,
		loaded,
		toggleMobileNav,
		Site,
		main_site,
		title,
		description,
		secondary_logo,
		click_handler
	];
}

class Component$2 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$2, create_fragment$2, safe_not_equal, {
			title: 7,
			description: 8,
			secondary_logo: 9,
			nav: 0
		});
	}
}

var commonjsGlobal = typeof globalThis !== "undefined" ? globalThis : typeof window !== "undefined" ? window : typeof global !== "undefined" ? global : typeof self !== "undefined" ? self : {};
function createCommonjsModule(fn, basedir, module) {
  return module = {
    path: basedir,
    exports: {},
    require: function(path, base) {
      return commonjsRequire(path, base === void 0 || base === null ? module.path : base);
    }
  }, fn(module, module.exports), module.exports;
}
function commonjsRequire() {
  throw new Error("Dynamic requires are not currently supported by @rollup/plugin-commonjs");
}
var showdown = createCommonjsModule(function(module) {
  (function() {
    function getDefaultOpts(simple) {
      var defaultOptions = {
        omitExtraWLInCodeBlocks: {
          defaultValue: false,
          describe: "Omit the default extra whiteline added to code blocks",
          type: "boolean"
        },
        noHeaderId: {
          defaultValue: false,
          describe: "Turn on/off generated header id",
          type: "boolean"
        },
        prefixHeaderId: {
          defaultValue: false,
          describe: "Add a prefix to the generated header ids. Passing a string will prefix that string to the header id. Setting to true will add a generic 'section-' prefix",
          type: "string"
        },
        rawPrefixHeaderId: {
          defaultValue: false,
          describe: 'Setting this option to true will prevent showdown from modifying the prefix. This might result in malformed IDs (if, for instance, the " char is used in the prefix)',
          type: "boolean"
        },
        ghCompatibleHeaderId: {
          defaultValue: false,
          describe: "Generate header ids compatible with github style (spaces are replaced with dashes, a bunch of non alphanumeric chars are removed)",
          type: "boolean"
        },
        rawHeaderId: {
          defaultValue: false,
          describe: `Remove only spaces, ' and " from generated header ids (including prefixes), replacing them with dashes (-). WARNING: This might result in malformed ids`,
          type: "boolean"
        },
        headerLevelStart: {
          defaultValue: false,
          describe: "The header blocks level start",
          type: "integer"
        },
        parseImgDimensions: {
          defaultValue: false,
          describe: "Turn on/off image dimension parsing",
          type: "boolean"
        },
        simplifiedAutoLink: {
          defaultValue: false,
          describe: "Turn on/off GFM autolink style",
          type: "boolean"
        },
        excludeTrailingPunctuationFromURLs: {
          defaultValue: false,
          describe: "Excludes trailing punctuation from links generated with autoLinking",
          type: "boolean"
        },
        literalMidWordUnderscores: {
          defaultValue: false,
          describe: "Parse midword underscores as literal underscores",
          type: "boolean"
        },
        literalMidWordAsterisks: {
          defaultValue: false,
          describe: "Parse midword asterisks as literal asterisks",
          type: "boolean"
        },
        strikethrough: {
          defaultValue: false,
          describe: "Turn on/off strikethrough support",
          type: "boolean"
        },
        tables: {
          defaultValue: false,
          describe: "Turn on/off tables support",
          type: "boolean"
        },
        tablesHeaderId: {
          defaultValue: false,
          describe: "Add an id to table headers",
          type: "boolean"
        },
        ghCodeBlocks: {
          defaultValue: true,
          describe: "Turn on/off GFM fenced code blocks support",
          type: "boolean"
        },
        tasklists: {
          defaultValue: false,
          describe: "Turn on/off GFM tasklist support",
          type: "boolean"
        },
        smoothLivePreview: {
          defaultValue: false,
          describe: "Prevents weird effects in live previews due to incomplete input",
          type: "boolean"
        },
        smartIndentationFix: {
          defaultValue: false,
          describe: "Tries to smartly fix indentation in es6 strings",
          type: "boolean"
        },
        disableForced4SpacesIndentedSublists: {
          defaultValue: false,
          describe: "Disables the requirement of indenting nested sublists by 4 spaces",
          type: "boolean"
        },
        simpleLineBreaks: {
          defaultValue: false,
          describe: "Parses simple line breaks as <br> (GFM Style)",
          type: "boolean"
        },
        requireSpaceBeforeHeadingText: {
          defaultValue: false,
          describe: "Makes adding a space between `#` and the header text mandatory (GFM Style)",
          type: "boolean"
        },
        ghMentions: {
          defaultValue: false,
          describe: "Enables github @mentions",
          type: "boolean"
        },
        ghMentionsLink: {
          defaultValue: "https://github.com/{u}",
          describe: "Changes the link generated by @mentions. Only applies if ghMentions option is enabled.",
          type: "string"
        },
        encodeEmails: {
          defaultValue: true,
          describe: "Encode e-mail addresses through the use of Character Entities, transforming ASCII e-mail addresses into its equivalent decimal entities",
          type: "boolean"
        },
        openLinksInNewWindow: {
          defaultValue: false,
          describe: "Open all links in new windows",
          type: "boolean"
        },
        backslashEscapesHTMLTags: {
          defaultValue: false,
          describe: "Support for HTML Tag escaping. ex: <div>foo</div>",
          type: "boolean"
        },
        emoji: {
          defaultValue: false,
          describe: "Enable emoji support. Ex: `this is a :smile: emoji`",
          type: "boolean"
        },
        underline: {
          defaultValue: false,
          describe: "Enable support for underline. Syntax is double or triple underscores: `__underline word__`. With this option enabled, underscores no longer parses into `<em>` and `<strong>`",
          type: "boolean"
        },
        ellipsis: {
          defaultValue: true,
          describe: "Replaces three dots with the ellipsis unicode character",
          type: "boolean"
        },
        completeHTMLDocument: {
          defaultValue: false,
          describe: "Outputs a complete html document, including `<html>`, `<head>` and `<body>` tags",
          type: "boolean"
        },
        metadata: {
          defaultValue: false,
          describe: "Enable support for document metadata (defined at the top of the document between `\xAB\xAB\xAB` and `\xBB\xBB\xBB` or between `---` and `---`).",
          type: "boolean"
        },
        splitAdjacentBlockquotes: {
          defaultValue: false,
          describe: "Split adjacent blockquote blocks",
          type: "boolean"
        }
      };
      if (simple === false) {
        return JSON.parse(JSON.stringify(defaultOptions));
      }
      var ret = {};
      for (var opt in defaultOptions) {
        if (defaultOptions.hasOwnProperty(opt)) {
          ret[opt] = defaultOptions[opt].defaultValue;
        }
      }
      return ret;
    }
    function allOptionsOn() {
      var options = getDefaultOpts(true), ret = {};
      for (var opt in options) {
        if (options.hasOwnProperty(opt)) {
          ret[opt] = true;
        }
      }
      return ret;
    }
    var showdown2 = {}, parsers = {}, extensions2 = {}, globalOptions = getDefaultOpts(true), setFlavor2 = "vanilla", flavor = {
      github: {
        omitExtraWLInCodeBlocks: true,
        simplifiedAutoLink: true,
        excludeTrailingPunctuationFromURLs: true,
        literalMidWordUnderscores: true,
        strikethrough: true,
        tables: true,
        tablesHeaderId: true,
        ghCodeBlocks: true,
        tasklists: true,
        disableForced4SpacesIndentedSublists: true,
        simpleLineBreaks: true,
        requireSpaceBeforeHeadingText: true,
        ghCompatibleHeaderId: true,
        ghMentions: true,
        backslashEscapesHTMLTags: true,
        emoji: true,
        splitAdjacentBlockquotes: true
      },
      original: {
        noHeaderId: true,
        ghCodeBlocks: false
      },
      ghost: {
        omitExtraWLInCodeBlocks: true,
        parseImgDimensions: true,
        simplifiedAutoLink: true,
        excludeTrailingPunctuationFromURLs: true,
        literalMidWordUnderscores: true,
        strikethrough: true,
        tables: true,
        tablesHeaderId: true,
        ghCodeBlocks: true,
        tasklists: true,
        smoothLivePreview: true,
        simpleLineBreaks: true,
        requireSpaceBeforeHeadingText: true,
        ghMentions: false,
        encodeEmails: true
      },
      vanilla: getDefaultOpts(true),
      allOn: allOptionsOn()
    };
    showdown2.helper = {};
    showdown2.extensions = {};
    showdown2.setOption = function(key, value) {
      globalOptions[key] = value;
      return this;
    };
    showdown2.getOption = function(key) {
      return globalOptions[key];
    };
    showdown2.getOptions = function() {
      return globalOptions;
    };
    showdown2.resetOptions = function() {
      globalOptions = getDefaultOpts(true);
    };
    showdown2.setFlavor = function(name) {
      if (!flavor.hasOwnProperty(name)) {
        throw Error(name + " flavor was not found");
      }
      showdown2.resetOptions();
      var preset = flavor[name];
      setFlavor2 = name;
      for (var option in preset) {
        if (preset.hasOwnProperty(option)) {
          globalOptions[option] = preset[option];
        }
      }
    };
    showdown2.getFlavor = function() {
      return setFlavor2;
    };
    showdown2.getFlavorOptions = function(name) {
      if (flavor.hasOwnProperty(name)) {
        return flavor[name];
      }
    };
    showdown2.getDefaultOptions = function(simple) {
      return getDefaultOpts(simple);
    };
    showdown2.subParser = function(name, func) {
      if (showdown2.helper.isString(name)) {
        if (typeof func !== "undefined") {
          parsers[name] = func;
        } else {
          if (parsers.hasOwnProperty(name)) {
            return parsers[name];
          } else {
            throw Error("SubParser named " + name + " not registered!");
          }
        }
      }
    };
    showdown2.extension = function(name, ext) {
      if (!showdown2.helper.isString(name)) {
        throw Error("Extension 'name' must be a string");
      }
      name = showdown2.helper.stdExtName(name);
      if (showdown2.helper.isUndefined(ext)) {
        if (!extensions2.hasOwnProperty(name)) {
          throw Error("Extension named " + name + " is not registered!");
        }
        return extensions2[name];
      } else {
        if (typeof ext === "function") {
          ext = ext();
        }
        if (!showdown2.helper.isArray(ext)) {
          ext = [ext];
        }
        var validExtension = validate(ext, name);
        if (validExtension.valid) {
          extensions2[name] = ext;
        } else {
          throw Error(validExtension.error);
        }
      }
    };
    showdown2.getAllExtensions = function() {
      return extensions2;
    };
    showdown2.removeExtension = function(name) {
      delete extensions2[name];
    };
    showdown2.resetExtensions = function() {
      extensions2 = {};
    };
    function validate(extension2, name) {
      var errMsg = name ? "Error in " + name + " extension->" : "Error in unnamed extension", ret = {
        valid: true,
        error: ""
      };
      if (!showdown2.helper.isArray(extension2)) {
        extension2 = [extension2];
      }
      for (var i = 0; i < extension2.length; ++i) {
        var baseMsg = errMsg + " sub-extension " + i + ": ", ext = extension2[i];
        if (typeof ext !== "object") {
          ret.valid = false;
          ret.error = baseMsg + "must be an object, but " + typeof ext + " given";
          return ret;
        }
        if (!showdown2.helper.isString(ext.type)) {
          ret.valid = false;
          ret.error = baseMsg + 'property "type" must be a string, but ' + typeof ext.type + " given";
          return ret;
        }
        var type = ext.type = ext.type.toLowerCase();
        if (type === "language") {
          type = ext.type = "lang";
        }
        if (type === "html") {
          type = ext.type = "output";
        }
        if (type !== "lang" && type !== "output" && type !== "listener") {
          ret.valid = false;
          ret.error = baseMsg + "type " + type + ' is not recognized. Valid values: "lang/language", "output/html" or "listener"';
          return ret;
        }
        if (type === "listener") {
          if (showdown2.helper.isUndefined(ext.listeners)) {
            ret.valid = false;
            ret.error = baseMsg + '. Extensions of type "listener" must have a property called "listeners"';
            return ret;
          }
        } else {
          if (showdown2.helper.isUndefined(ext.filter) && showdown2.helper.isUndefined(ext.regex)) {
            ret.valid = false;
            ret.error = baseMsg + type + ' extensions must define either a "regex" property or a "filter" method';
            return ret;
          }
        }
        if (ext.listeners) {
          if (typeof ext.listeners !== "object") {
            ret.valid = false;
            ret.error = baseMsg + '"listeners" property must be an object but ' + typeof ext.listeners + " given";
            return ret;
          }
          for (var ln in ext.listeners) {
            if (ext.listeners.hasOwnProperty(ln)) {
              if (typeof ext.listeners[ln] !== "function") {
                ret.valid = false;
                ret.error = baseMsg + '"listeners" property must be an hash of [event name]: [callback]. listeners.' + ln + " must be a function but " + typeof ext.listeners[ln] + " given";
                return ret;
              }
            }
          }
        }
        if (ext.filter) {
          if (typeof ext.filter !== "function") {
            ret.valid = false;
            ret.error = baseMsg + '"filter" must be a function, but ' + typeof ext.filter + " given";
            return ret;
          }
        } else if (ext.regex) {
          if (showdown2.helper.isString(ext.regex)) {
            ext.regex = new RegExp(ext.regex, "g");
          }
          if (!(ext.regex instanceof RegExp)) {
            ret.valid = false;
            ret.error = baseMsg + '"regex" property must either be a string or a RegExp object, but ' + typeof ext.regex + " given";
            return ret;
          }
          if (showdown2.helper.isUndefined(ext.replace)) {
            ret.valid = false;
            ret.error = baseMsg + '"regex" extensions must implement a replace string or function';
            return ret;
          }
        }
      }
      return ret;
    }
    showdown2.validateExtension = function(ext) {
      var validateExtension2 = validate(ext, null);
      if (!validateExtension2.valid) {
        console.warn(validateExtension2.error);
        return false;
      }
      return true;
    };
    if (!showdown2.hasOwnProperty("helper")) {
      showdown2.helper = {};
    }
    showdown2.helper.isString = function(a) {
      return typeof a === "string" || a instanceof String;
    };
    showdown2.helper.isFunction = function(a) {
      var getType = {};
      return a && getType.toString.call(a) === "[object Function]";
    };
    showdown2.helper.isArray = function(a) {
      return Array.isArray(a);
    };
    showdown2.helper.isUndefined = function(value) {
      return typeof value === "undefined";
    };
    showdown2.helper.forEach = function(obj, callback) {
      if (showdown2.helper.isUndefined(obj)) {
        throw new Error("obj param is required");
      }
      if (showdown2.helper.isUndefined(callback)) {
        throw new Error("callback param is required");
      }
      if (!showdown2.helper.isFunction(callback)) {
        throw new Error("callback param must be a function/closure");
      }
      if (typeof obj.forEach === "function") {
        obj.forEach(callback);
      } else if (showdown2.helper.isArray(obj)) {
        for (var i = 0; i < obj.length; i++) {
          callback(obj[i], i, obj);
        }
      } else if (typeof obj === "object") {
        for (var prop in obj) {
          if (obj.hasOwnProperty(prop)) {
            callback(obj[prop], prop, obj);
          }
        }
      } else {
        throw new Error("obj does not seem to be an array or an iterable object");
      }
    };
    showdown2.helper.stdExtName = function(s) {
      return s.replace(/[_?*+\/\\.^-]/g, "").replace(/\s/g, "").toLowerCase();
    };
    function escapeCharactersCallback(wholeMatch, m1) {
      var charCodeToEscape = m1.charCodeAt(0);
      return "\xA8E" + charCodeToEscape + "E";
    }
    showdown2.helper.escapeCharactersCallback = escapeCharactersCallback;
    showdown2.helper.escapeCharacters = function(text, charsToEscape, afterBackslash) {
      var regexString = "([" + charsToEscape.replace(/([\[\]\\])/g, "\\$1") + "])";
      if (afterBackslash) {
        regexString = "\\\\" + regexString;
      }
      var regex = new RegExp(regexString, "g");
      text = text.replace(regex, escapeCharactersCallback);
      return text;
    };
    showdown2.helper.unescapeHTMLEntities = function(txt) {
      return txt.replace(/&quot;/g, '"').replace(/&lt;/g, "<").replace(/&gt;/g, ">").replace(/&amp;/g, "&");
    };
    var rgxFindMatchPos = function(str, left, right, flags) {
      var f = flags || "", g = f.indexOf("g") > -1, x = new RegExp(left + "|" + right, "g" + f.replace(/g/g, "")), l = new RegExp(left, f.replace(/g/g, "")), pos = [], t, s, m, start, end;
      do {
        t = 0;
        while (m = x.exec(str)) {
          if (l.test(m[0])) {
            if (!t++) {
              s = x.lastIndex;
              start = s - m[0].length;
            }
          } else if (t) {
            if (!--t) {
              end = m.index + m[0].length;
              var obj = {
                left: {start, end: s},
                match: {start: s, end: m.index},
                right: {start: m.index, end},
                wholeMatch: {start, end}
              };
              pos.push(obj);
              if (!g) {
                return pos;
              }
            }
          }
        }
      } while (t && (x.lastIndex = s));
      return pos;
    };
    showdown2.helper.matchRecursiveRegExp = function(str, left, right, flags) {
      var matchPos = rgxFindMatchPos(str, left, right, flags), results = [];
      for (var i = 0; i < matchPos.length; ++i) {
        results.push([
          str.slice(matchPos[i].wholeMatch.start, matchPos[i].wholeMatch.end),
          str.slice(matchPos[i].match.start, matchPos[i].match.end),
          str.slice(matchPos[i].left.start, matchPos[i].left.end),
          str.slice(matchPos[i].right.start, matchPos[i].right.end)
        ]);
      }
      return results;
    };
    showdown2.helper.replaceRecursiveRegExp = function(str, replacement, left, right, flags) {
      if (!showdown2.helper.isFunction(replacement)) {
        var repStr = replacement;
        replacement = function() {
          return repStr;
        };
      }
      var matchPos = rgxFindMatchPos(str, left, right, flags), finalStr = str, lng = matchPos.length;
      if (lng > 0) {
        var bits = [];
        if (matchPos[0].wholeMatch.start !== 0) {
          bits.push(str.slice(0, matchPos[0].wholeMatch.start));
        }
        for (var i = 0; i < lng; ++i) {
          bits.push(replacement(str.slice(matchPos[i].wholeMatch.start, matchPos[i].wholeMatch.end), str.slice(matchPos[i].match.start, matchPos[i].match.end), str.slice(matchPos[i].left.start, matchPos[i].left.end), str.slice(matchPos[i].right.start, matchPos[i].right.end)));
          if (i < lng - 1) {
            bits.push(str.slice(matchPos[i].wholeMatch.end, matchPos[i + 1].wholeMatch.start));
          }
        }
        if (matchPos[lng - 1].wholeMatch.end < str.length) {
          bits.push(str.slice(matchPos[lng - 1].wholeMatch.end));
        }
        finalStr = bits.join("");
      }
      return finalStr;
    };
    showdown2.helper.regexIndexOf = function(str, regex, fromIndex) {
      if (!showdown2.helper.isString(str)) {
        throw "InvalidArgumentError: first parameter of showdown.helper.regexIndexOf function must be a string";
      }
      if (regex instanceof RegExp === false) {
        throw "InvalidArgumentError: second parameter of showdown.helper.regexIndexOf function must be an instance of RegExp";
      }
      var indexOf = str.substring(fromIndex || 0).search(regex);
      return indexOf >= 0 ? indexOf + (fromIndex || 0) : indexOf;
    };
    showdown2.helper.splitAtIndex = function(str, index) {
      if (!showdown2.helper.isString(str)) {
        throw "InvalidArgumentError: first parameter of showdown.helper.regexIndexOf function must be a string";
      }
      return [str.substring(0, index), str.substring(index)];
    };
    showdown2.helper.encodeEmailAddress = function(mail) {
      var encode = [
        function(ch) {
          return "&#" + ch.charCodeAt(0) + ";";
        },
        function(ch) {
          return "&#x" + ch.charCodeAt(0).toString(16) + ";";
        },
        function(ch) {
          return ch;
        }
      ];
      mail = mail.replace(/./g, function(ch) {
        if (ch === "@") {
          ch = encode[Math.floor(Math.random() * 2)](ch);
        } else {
          var r = Math.random();
          ch = r > 0.9 ? encode[2](ch) : r > 0.45 ? encode[1](ch) : encode[0](ch);
        }
        return ch;
      });
      return mail;
    };
    showdown2.helper.padEnd = function padEnd(str, targetLength, padString) {
      targetLength = targetLength >> 0;
      padString = String(padString || " ");
      if (str.length > targetLength) {
        return String(str);
      } else {
        targetLength = targetLength - str.length;
        if (targetLength > padString.length) {
          padString += padString.repeat(targetLength / padString.length);
        }
        return String(str) + padString.slice(0, targetLength);
      }
    };
    if (typeof console === "undefined") {
      console = {
        warn: function(msg) {
          alert(msg);
        },
        log: function(msg) {
          alert(msg);
        },
        error: function(msg) {
          throw msg;
        }
      };
    }
    showdown2.helper.regexes = {
      asteriskDashAndColon: /([*_:~])/g
    };
    showdown2.helper.emojis = {
      "+1": "\u{1F44D}",
      "-1": "\u{1F44E}",
      "100": "\u{1F4AF}",
      "1234": "\u{1F522}",
      "1st_place_medal": "\u{1F947}",
      "2nd_place_medal": "\u{1F948}",
      "3rd_place_medal": "\u{1F949}",
      "8ball": "\u{1F3B1}",
      a: "\u{1F170}\uFE0F",
      ab: "\u{1F18E}",
      abc: "\u{1F524}",
      abcd: "\u{1F521}",
      accept: "\u{1F251}",
      aerial_tramway: "\u{1F6A1}",
      airplane: "\u2708\uFE0F",
      alarm_clock: "\u23F0",
      alembic: "\u2697\uFE0F",
      alien: "\u{1F47D}",
      ambulance: "\u{1F691}",
      amphora: "\u{1F3FA}",
      anchor: "\u2693\uFE0F",
      angel: "\u{1F47C}",
      anger: "\u{1F4A2}",
      angry: "\u{1F620}",
      anguished: "\u{1F627}",
      ant: "\u{1F41C}",
      apple: "\u{1F34E}",
      aquarius: "\u2652\uFE0F",
      aries: "\u2648\uFE0F",
      arrow_backward: "\u25C0\uFE0F",
      arrow_double_down: "\u23EC",
      arrow_double_up: "\u23EB",
      arrow_down: "\u2B07\uFE0F",
      arrow_down_small: "\u{1F53D}",
      arrow_forward: "\u25B6\uFE0F",
      arrow_heading_down: "\u2935\uFE0F",
      arrow_heading_up: "\u2934\uFE0F",
      arrow_left: "\u2B05\uFE0F",
      arrow_lower_left: "\u2199\uFE0F",
      arrow_lower_right: "\u2198\uFE0F",
      arrow_right: "\u27A1\uFE0F",
      arrow_right_hook: "\u21AA\uFE0F",
      arrow_up: "\u2B06\uFE0F",
      arrow_up_down: "\u2195\uFE0F",
      arrow_up_small: "\u{1F53C}",
      arrow_upper_left: "\u2196\uFE0F",
      arrow_upper_right: "\u2197\uFE0F",
      arrows_clockwise: "\u{1F503}",
      arrows_counterclockwise: "\u{1F504}",
      art: "\u{1F3A8}",
      articulated_lorry: "\u{1F69B}",
      artificial_satellite: "\u{1F6F0}",
      astonished: "\u{1F632}",
      athletic_shoe: "\u{1F45F}",
      atm: "\u{1F3E7}",
      atom_symbol: "\u269B\uFE0F",
      avocado: "\u{1F951}",
      b: "\u{1F171}\uFE0F",
      baby: "\u{1F476}",
      baby_bottle: "\u{1F37C}",
      baby_chick: "\u{1F424}",
      baby_symbol: "\u{1F6BC}",
      back: "\u{1F519}",
      bacon: "\u{1F953}",
      badminton: "\u{1F3F8}",
      baggage_claim: "\u{1F6C4}",
      baguette_bread: "\u{1F956}",
      balance_scale: "\u2696\uFE0F",
      balloon: "\u{1F388}",
      ballot_box: "\u{1F5F3}",
      ballot_box_with_check: "\u2611\uFE0F",
      bamboo: "\u{1F38D}",
      banana: "\u{1F34C}",
      bangbang: "\u203C\uFE0F",
      bank: "\u{1F3E6}",
      bar_chart: "\u{1F4CA}",
      barber: "\u{1F488}",
      baseball: "\u26BE\uFE0F",
      basketball: "\u{1F3C0}",
      basketball_man: "\u26F9\uFE0F",
      basketball_woman: "\u26F9\uFE0F&zwj;\u2640\uFE0F",
      bat: "\u{1F987}",
      bath: "\u{1F6C0}",
      bathtub: "\u{1F6C1}",
      battery: "\u{1F50B}",
      beach_umbrella: "\u{1F3D6}",
      bear: "\u{1F43B}",
      bed: "\u{1F6CF}",
      bee: "\u{1F41D}",
      beer: "\u{1F37A}",
      beers: "\u{1F37B}",
      beetle: "\u{1F41E}",
      beginner: "\u{1F530}",
      bell: "\u{1F514}",
      bellhop_bell: "\u{1F6CE}",
      bento: "\u{1F371}",
      biking_man: "\u{1F6B4}",
      bike: "\u{1F6B2}",
      biking_woman: "\u{1F6B4}&zwj;\u2640\uFE0F",
      bikini: "\u{1F459}",
      biohazard: "\u2623\uFE0F",
      bird: "\u{1F426}",
      birthday: "\u{1F382}",
      black_circle: "\u26AB\uFE0F",
      black_flag: "\u{1F3F4}",
      black_heart: "\u{1F5A4}",
      black_joker: "\u{1F0CF}",
      black_large_square: "\u2B1B\uFE0F",
      black_medium_small_square: "\u25FE\uFE0F",
      black_medium_square: "\u25FC\uFE0F",
      black_nib: "\u2712\uFE0F",
      black_small_square: "\u25AA\uFE0F",
      black_square_button: "\u{1F532}",
      blonde_man: "\u{1F471}",
      blonde_woman: "\u{1F471}&zwj;\u2640\uFE0F",
      blossom: "\u{1F33C}",
      blowfish: "\u{1F421}",
      blue_book: "\u{1F4D8}",
      blue_car: "\u{1F699}",
      blue_heart: "\u{1F499}",
      blush: "\u{1F60A}",
      boar: "\u{1F417}",
      boat: "\u26F5\uFE0F",
      bomb: "\u{1F4A3}",
      book: "\u{1F4D6}",
      bookmark: "\u{1F516}",
      bookmark_tabs: "\u{1F4D1}",
      books: "\u{1F4DA}",
      boom: "\u{1F4A5}",
      boot: "\u{1F462}",
      bouquet: "\u{1F490}",
      bowing_man: "\u{1F647}",
      bow_and_arrow: "\u{1F3F9}",
      bowing_woman: "\u{1F647}&zwj;\u2640\uFE0F",
      bowling: "\u{1F3B3}",
      boxing_glove: "\u{1F94A}",
      boy: "\u{1F466}",
      bread: "\u{1F35E}",
      bride_with_veil: "\u{1F470}",
      bridge_at_night: "\u{1F309}",
      briefcase: "\u{1F4BC}",
      broken_heart: "\u{1F494}",
      bug: "\u{1F41B}",
      building_construction: "\u{1F3D7}",
      bulb: "\u{1F4A1}",
      bullettrain_front: "\u{1F685}",
      bullettrain_side: "\u{1F684}",
      burrito: "\u{1F32F}",
      bus: "\u{1F68C}",
      business_suit_levitating: "\u{1F574}",
      busstop: "\u{1F68F}",
      bust_in_silhouette: "\u{1F464}",
      busts_in_silhouette: "\u{1F465}",
      butterfly: "\u{1F98B}",
      cactus: "\u{1F335}",
      cake: "\u{1F370}",
      calendar: "\u{1F4C6}",
      call_me_hand: "\u{1F919}",
      calling: "\u{1F4F2}",
      camel: "\u{1F42B}",
      camera: "\u{1F4F7}",
      camera_flash: "\u{1F4F8}",
      camping: "\u{1F3D5}",
      cancer: "\u264B\uFE0F",
      candle: "\u{1F56F}",
      candy: "\u{1F36C}",
      canoe: "\u{1F6F6}",
      capital_abcd: "\u{1F520}",
      capricorn: "\u2651\uFE0F",
      car: "\u{1F697}",
      card_file_box: "\u{1F5C3}",
      card_index: "\u{1F4C7}",
      card_index_dividers: "\u{1F5C2}",
      carousel_horse: "\u{1F3A0}",
      carrot: "\u{1F955}",
      cat: "\u{1F431}",
      cat2: "\u{1F408}",
      cd: "\u{1F4BF}",
      chains: "\u26D3",
      champagne: "\u{1F37E}",
      chart: "\u{1F4B9}",
      chart_with_downwards_trend: "\u{1F4C9}",
      chart_with_upwards_trend: "\u{1F4C8}",
      checkered_flag: "\u{1F3C1}",
      cheese: "\u{1F9C0}",
      cherries: "\u{1F352}",
      cherry_blossom: "\u{1F338}",
      chestnut: "\u{1F330}",
      chicken: "\u{1F414}",
      children_crossing: "\u{1F6B8}",
      chipmunk: "\u{1F43F}",
      chocolate_bar: "\u{1F36B}",
      christmas_tree: "\u{1F384}",
      church: "\u26EA\uFE0F",
      cinema: "\u{1F3A6}",
      circus_tent: "\u{1F3AA}",
      city_sunrise: "\u{1F307}",
      city_sunset: "\u{1F306}",
      cityscape: "\u{1F3D9}",
      cl: "\u{1F191}",
      clamp: "\u{1F5DC}",
      clap: "\u{1F44F}",
      clapper: "\u{1F3AC}",
      classical_building: "\u{1F3DB}",
      clinking_glasses: "\u{1F942}",
      clipboard: "\u{1F4CB}",
      clock1: "\u{1F550}",
      clock10: "\u{1F559}",
      clock1030: "\u{1F565}",
      clock11: "\u{1F55A}",
      clock1130: "\u{1F566}",
      clock12: "\u{1F55B}",
      clock1230: "\u{1F567}",
      clock130: "\u{1F55C}",
      clock2: "\u{1F551}",
      clock230: "\u{1F55D}",
      clock3: "\u{1F552}",
      clock330: "\u{1F55E}",
      clock4: "\u{1F553}",
      clock430: "\u{1F55F}",
      clock5: "\u{1F554}",
      clock530: "\u{1F560}",
      clock6: "\u{1F555}",
      clock630: "\u{1F561}",
      clock7: "\u{1F556}",
      clock730: "\u{1F562}",
      clock8: "\u{1F557}",
      clock830: "\u{1F563}",
      clock9: "\u{1F558}",
      clock930: "\u{1F564}",
      closed_book: "\u{1F4D5}",
      closed_lock_with_key: "\u{1F510}",
      closed_umbrella: "\u{1F302}",
      cloud: "\u2601\uFE0F",
      cloud_with_lightning: "\u{1F329}",
      cloud_with_lightning_and_rain: "\u26C8",
      cloud_with_rain: "\u{1F327}",
      cloud_with_snow: "\u{1F328}",
      clown_face: "\u{1F921}",
      clubs: "\u2663\uFE0F",
      cocktail: "\u{1F378}",
      coffee: "\u2615\uFE0F",
      coffin: "\u26B0\uFE0F",
      cold_sweat: "\u{1F630}",
      comet: "\u2604\uFE0F",
      computer: "\u{1F4BB}",
      computer_mouse: "\u{1F5B1}",
      confetti_ball: "\u{1F38A}",
      confounded: "\u{1F616}",
      confused: "\u{1F615}",
      congratulations: "\u3297\uFE0F",
      construction: "\u{1F6A7}",
      construction_worker_man: "\u{1F477}",
      construction_worker_woman: "\u{1F477}&zwj;\u2640\uFE0F",
      control_knobs: "\u{1F39B}",
      convenience_store: "\u{1F3EA}",
      cookie: "\u{1F36A}",
      cool: "\u{1F192}",
      policeman: "\u{1F46E}",
      copyright: "\xA9\uFE0F",
      corn: "\u{1F33D}",
      couch_and_lamp: "\u{1F6CB}",
      couple: "\u{1F46B}",
      couple_with_heart_woman_man: "\u{1F491}",
      couple_with_heart_man_man: "\u{1F468}&zwj;\u2764\uFE0F&zwj;\u{1F468}",
      couple_with_heart_woman_woman: "\u{1F469}&zwj;\u2764\uFE0F&zwj;\u{1F469}",
      couplekiss_man_man: "\u{1F468}&zwj;\u2764\uFE0F&zwj;\u{1F48B}&zwj;\u{1F468}",
      couplekiss_man_woman: "\u{1F48F}",
      couplekiss_woman_woman: "\u{1F469}&zwj;\u2764\uFE0F&zwj;\u{1F48B}&zwj;\u{1F469}",
      cow: "\u{1F42E}",
      cow2: "\u{1F404}",
      cowboy_hat_face: "\u{1F920}",
      crab: "\u{1F980}",
      crayon: "\u{1F58D}",
      credit_card: "\u{1F4B3}",
      crescent_moon: "\u{1F319}",
      cricket: "\u{1F3CF}",
      crocodile: "\u{1F40A}",
      croissant: "\u{1F950}",
      crossed_fingers: "\u{1F91E}",
      crossed_flags: "\u{1F38C}",
      crossed_swords: "\u2694\uFE0F",
      crown: "\u{1F451}",
      cry: "\u{1F622}",
      crying_cat_face: "\u{1F63F}",
      crystal_ball: "\u{1F52E}",
      cucumber: "\u{1F952}",
      cupid: "\u{1F498}",
      curly_loop: "\u27B0",
      currency_exchange: "\u{1F4B1}",
      curry: "\u{1F35B}",
      custard: "\u{1F36E}",
      customs: "\u{1F6C3}",
      cyclone: "\u{1F300}",
      dagger: "\u{1F5E1}",
      dancer: "\u{1F483}",
      dancing_women: "\u{1F46F}",
      dancing_men: "\u{1F46F}&zwj;\u2642\uFE0F",
      dango: "\u{1F361}",
      dark_sunglasses: "\u{1F576}",
      dart: "\u{1F3AF}",
      dash: "\u{1F4A8}",
      date: "\u{1F4C5}",
      deciduous_tree: "\u{1F333}",
      deer: "\u{1F98C}",
      department_store: "\u{1F3EC}",
      derelict_house: "\u{1F3DA}",
      desert: "\u{1F3DC}",
      desert_island: "\u{1F3DD}",
      desktop_computer: "\u{1F5A5}",
      male_detective: "\u{1F575}\uFE0F",
      diamond_shape_with_a_dot_inside: "\u{1F4A0}",
      diamonds: "\u2666\uFE0F",
      disappointed: "\u{1F61E}",
      disappointed_relieved: "\u{1F625}",
      dizzy: "\u{1F4AB}",
      dizzy_face: "\u{1F635}",
      do_not_litter: "\u{1F6AF}",
      dog: "\u{1F436}",
      dog2: "\u{1F415}",
      dollar: "\u{1F4B5}",
      dolls: "\u{1F38E}",
      dolphin: "\u{1F42C}",
      door: "\u{1F6AA}",
      doughnut: "\u{1F369}",
      dove: "\u{1F54A}",
      dragon: "\u{1F409}",
      dragon_face: "\u{1F432}",
      dress: "\u{1F457}",
      dromedary_camel: "\u{1F42A}",
      drooling_face: "\u{1F924}",
      droplet: "\u{1F4A7}",
      drum: "\u{1F941}",
      duck: "\u{1F986}",
      dvd: "\u{1F4C0}",
      "e-mail": "\u{1F4E7}",
      eagle: "\u{1F985}",
      ear: "\u{1F442}",
      ear_of_rice: "\u{1F33E}",
      earth_africa: "\u{1F30D}",
      earth_americas: "\u{1F30E}",
      earth_asia: "\u{1F30F}",
      egg: "\u{1F95A}",
      eggplant: "\u{1F346}",
      eight_pointed_black_star: "\u2734\uFE0F",
      eight_spoked_asterisk: "\u2733\uFE0F",
      electric_plug: "\u{1F50C}",
      elephant: "\u{1F418}",
      email: "\u2709\uFE0F",
      end: "\u{1F51A}",
      envelope_with_arrow: "\u{1F4E9}",
      euro: "\u{1F4B6}",
      european_castle: "\u{1F3F0}",
      european_post_office: "\u{1F3E4}",
      evergreen_tree: "\u{1F332}",
      exclamation: "\u2757\uFE0F",
      expressionless: "\u{1F611}",
      eye: "\u{1F441}",
      eye_speech_bubble: "\u{1F441}&zwj;\u{1F5E8}",
      eyeglasses: "\u{1F453}",
      eyes: "\u{1F440}",
      face_with_head_bandage: "\u{1F915}",
      face_with_thermometer: "\u{1F912}",
      fist_oncoming: "\u{1F44A}",
      factory: "\u{1F3ED}",
      fallen_leaf: "\u{1F342}",
      family_man_woman_boy: "\u{1F46A}",
      family_man_boy: "\u{1F468}&zwj;\u{1F466}",
      family_man_boy_boy: "\u{1F468}&zwj;\u{1F466}&zwj;\u{1F466}",
      family_man_girl: "\u{1F468}&zwj;\u{1F467}",
      family_man_girl_boy: "\u{1F468}&zwj;\u{1F467}&zwj;\u{1F466}",
      family_man_girl_girl: "\u{1F468}&zwj;\u{1F467}&zwj;\u{1F467}",
      family_man_man_boy: "\u{1F468}&zwj;\u{1F468}&zwj;\u{1F466}",
      family_man_man_boy_boy: "\u{1F468}&zwj;\u{1F468}&zwj;\u{1F466}&zwj;\u{1F466}",
      family_man_man_girl: "\u{1F468}&zwj;\u{1F468}&zwj;\u{1F467}",
      family_man_man_girl_boy: "\u{1F468}&zwj;\u{1F468}&zwj;\u{1F467}&zwj;\u{1F466}",
      family_man_man_girl_girl: "\u{1F468}&zwj;\u{1F468}&zwj;\u{1F467}&zwj;\u{1F467}",
      family_man_woman_boy_boy: "\u{1F468}&zwj;\u{1F469}&zwj;\u{1F466}&zwj;\u{1F466}",
      family_man_woman_girl: "\u{1F468}&zwj;\u{1F469}&zwj;\u{1F467}",
      family_man_woman_girl_boy: "\u{1F468}&zwj;\u{1F469}&zwj;\u{1F467}&zwj;\u{1F466}",
      family_man_woman_girl_girl: "\u{1F468}&zwj;\u{1F469}&zwj;\u{1F467}&zwj;\u{1F467}",
      family_woman_boy: "\u{1F469}&zwj;\u{1F466}",
      family_woman_boy_boy: "\u{1F469}&zwj;\u{1F466}&zwj;\u{1F466}",
      family_woman_girl: "\u{1F469}&zwj;\u{1F467}",
      family_woman_girl_boy: "\u{1F469}&zwj;\u{1F467}&zwj;\u{1F466}",
      family_woman_girl_girl: "\u{1F469}&zwj;\u{1F467}&zwj;\u{1F467}",
      family_woman_woman_boy: "\u{1F469}&zwj;\u{1F469}&zwj;\u{1F466}",
      family_woman_woman_boy_boy: "\u{1F469}&zwj;\u{1F469}&zwj;\u{1F466}&zwj;\u{1F466}",
      family_woman_woman_girl: "\u{1F469}&zwj;\u{1F469}&zwj;\u{1F467}",
      family_woman_woman_girl_boy: "\u{1F469}&zwj;\u{1F469}&zwj;\u{1F467}&zwj;\u{1F466}",
      family_woman_woman_girl_girl: "\u{1F469}&zwj;\u{1F469}&zwj;\u{1F467}&zwj;\u{1F467}",
      fast_forward: "\u23E9",
      fax: "\u{1F4E0}",
      fearful: "\u{1F628}",
      feet: "\u{1F43E}",
      female_detective: "\u{1F575}\uFE0F&zwj;\u2640\uFE0F",
      ferris_wheel: "\u{1F3A1}",
      ferry: "\u26F4",
      field_hockey: "\u{1F3D1}",
      file_cabinet: "\u{1F5C4}",
      file_folder: "\u{1F4C1}",
      film_projector: "\u{1F4FD}",
      film_strip: "\u{1F39E}",
      fire: "\u{1F525}",
      fire_engine: "\u{1F692}",
      fireworks: "\u{1F386}",
      first_quarter_moon: "\u{1F313}",
      first_quarter_moon_with_face: "\u{1F31B}",
      fish: "\u{1F41F}",
      fish_cake: "\u{1F365}",
      fishing_pole_and_fish: "\u{1F3A3}",
      fist_raised: "\u270A",
      fist_left: "\u{1F91B}",
      fist_right: "\u{1F91C}",
      flags: "\u{1F38F}",
      flashlight: "\u{1F526}",
      fleur_de_lis: "\u269C\uFE0F",
      flight_arrival: "\u{1F6EC}",
      flight_departure: "\u{1F6EB}",
      floppy_disk: "\u{1F4BE}",
      flower_playing_cards: "\u{1F3B4}",
      flushed: "\u{1F633}",
      fog: "\u{1F32B}",
      foggy: "\u{1F301}",
      football: "\u{1F3C8}",
      footprints: "\u{1F463}",
      fork_and_knife: "\u{1F374}",
      fountain: "\u26F2\uFE0F",
      fountain_pen: "\u{1F58B}",
      four_leaf_clover: "\u{1F340}",
      fox_face: "\u{1F98A}",
      framed_picture: "\u{1F5BC}",
      free: "\u{1F193}",
      fried_egg: "\u{1F373}",
      fried_shrimp: "\u{1F364}",
      fries: "\u{1F35F}",
      frog: "\u{1F438}",
      frowning: "\u{1F626}",
      frowning_face: "\u2639\uFE0F",
      frowning_man: "\u{1F64D}&zwj;\u2642\uFE0F",
      frowning_woman: "\u{1F64D}",
      middle_finger: "\u{1F595}",
      fuelpump: "\u26FD\uFE0F",
      full_moon: "\u{1F315}",
      full_moon_with_face: "\u{1F31D}",
      funeral_urn: "\u26B1\uFE0F",
      game_die: "\u{1F3B2}",
      gear: "\u2699\uFE0F",
      gem: "\u{1F48E}",
      gemini: "\u264A\uFE0F",
      ghost: "\u{1F47B}",
      gift: "\u{1F381}",
      gift_heart: "\u{1F49D}",
      girl: "\u{1F467}",
      globe_with_meridians: "\u{1F310}",
      goal_net: "\u{1F945}",
      goat: "\u{1F410}",
      golf: "\u26F3\uFE0F",
      golfing_man: "\u{1F3CC}\uFE0F",
      golfing_woman: "\u{1F3CC}\uFE0F&zwj;\u2640\uFE0F",
      gorilla: "\u{1F98D}",
      grapes: "\u{1F347}",
      green_apple: "\u{1F34F}",
      green_book: "\u{1F4D7}",
      green_heart: "\u{1F49A}",
      green_salad: "\u{1F957}",
      grey_exclamation: "\u2755",
      grey_question: "\u2754",
      grimacing: "\u{1F62C}",
      grin: "\u{1F601}",
      grinning: "\u{1F600}",
      guardsman: "\u{1F482}",
      guardswoman: "\u{1F482}&zwj;\u2640\uFE0F",
      guitar: "\u{1F3B8}",
      gun: "\u{1F52B}",
      haircut_woman: "\u{1F487}",
      haircut_man: "\u{1F487}&zwj;\u2642\uFE0F",
      hamburger: "\u{1F354}",
      hammer: "\u{1F528}",
      hammer_and_pick: "\u2692",
      hammer_and_wrench: "\u{1F6E0}",
      hamster: "\u{1F439}",
      hand: "\u270B",
      handbag: "\u{1F45C}",
      handshake: "\u{1F91D}",
      hankey: "\u{1F4A9}",
      hatched_chick: "\u{1F425}",
      hatching_chick: "\u{1F423}",
      headphones: "\u{1F3A7}",
      hear_no_evil: "\u{1F649}",
      heart: "\u2764\uFE0F",
      heart_decoration: "\u{1F49F}",
      heart_eyes: "\u{1F60D}",
      heart_eyes_cat: "\u{1F63B}",
      heartbeat: "\u{1F493}",
      heartpulse: "\u{1F497}",
      hearts: "\u2665\uFE0F",
      heavy_check_mark: "\u2714\uFE0F",
      heavy_division_sign: "\u2797",
      heavy_dollar_sign: "\u{1F4B2}",
      heavy_heart_exclamation: "\u2763\uFE0F",
      heavy_minus_sign: "\u2796",
      heavy_multiplication_x: "\u2716\uFE0F",
      heavy_plus_sign: "\u2795",
      helicopter: "\u{1F681}",
      herb: "\u{1F33F}",
      hibiscus: "\u{1F33A}",
      high_brightness: "\u{1F506}",
      high_heel: "\u{1F460}",
      hocho: "\u{1F52A}",
      hole: "\u{1F573}",
      honey_pot: "\u{1F36F}",
      horse: "\u{1F434}",
      horse_racing: "\u{1F3C7}",
      hospital: "\u{1F3E5}",
      hot_pepper: "\u{1F336}",
      hotdog: "\u{1F32D}",
      hotel: "\u{1F3E8}",
      hotsprings: "\u2668\uFE0F",
      hourglass: "\u231B\uFE0F",
      hourglass_flowing_sand: "\u23F3",
      house: "\u{1F3E0}",
      house_with_garden: "\u{1F3E1}",
      houses: "\u{1F3D8}",
      hugs: "\u{1F917}",
      hushed: "\u{1F62F}",
      ice_cream: "\u{1F368}",
      ice_hockey: "\u{1F3D2}",
      ice_skate: "\u26F8",
      icecream: "\u{1F366}",
      id: "\u{1F194}",
      ideograph_advantage: "\u{1F250}",
      imp: "\u{1F47F}",
      inbox_tray: "\u{1F4E5}",
      incoming_envelope: "\u{1F4E8}",
      tipping_hand_woman: "\u{1F481}",
      information_source: "\u2139\uFE0F",
      innocent: "\u{1F607}",
      interrobang: "\u2049\uFE0F",
      iphone: "\u{1F4F1}",
      izakaya_lantern: "\u{1F3EE}",
      jack_o_lantern: "\u{1F383}",
      japan: "\u{1F5FE}",
      japanese_castle: "\u{1F3EF}",
      japanese_goblin: "\u{1F47A}",
      japanese_ogre: "\u{1F479}",
      jeans: "\u{1F456}",
      joy: "\u{1F602}",
      joy_cat: "\u{1F639}",
      joystick: "\u{1F579}",
      kaaba: "\u{1F54B}",
      key: "\u{1F511}",
      keyboard: "\u2328\uFE0F",
      keycap_ten: "\u{1F51F}",
      kick_scooter: "\u{1F6F4}",
      kimono: "\u{1F458}",
      kiss: "\u{1F48B}",
      kissing: "\u{1F617}",
      kissing_cat: "\u{1F63D}",
      kissing_closed_eyes: "\u{1F61A}",
      kissing_heart: "\u{1F618}",
      kissing_smiling_eyes: "\u{1F619}",
      kiwi_fruit: "\u{1F95D}",
      koala: "\u{1F428}",
      koko: "\u{1F201}",
      label: "\u{1F3F7}",
      large_blue_circle: "\u{1F535}",
      large_blue_diamond: "\u{1F537}",
      large_orange_diamond: "\u{1F536}",
      last_quarter_moon: "\u{1F317}",
      last_quarter_moon_with_face: "\u{1F31C}",
      latin_cross: "\u271D\uFE0F",
      laughing: "\u{1F606}",
      leaves: "\u{1F343}",
      ledger: "\u{1F4D2}",
      left_luggage: "\u{1F6C5}",
      left_right_arrow: "\u2194\uFE0F",
      leftwards_arrow_with_hook: "\u21A9\uFE0F",
      lemon: "\u{1F34B}",
      leo: "\u264C\uFE0F",
      leopard: "\u{1F406}",
      level_slider: "\u{1F39A}",
      libra: "\u264E\uFE0F",
      light_rail: "\u{1F688}",
      link: "\u{1F517}",
      lion: "\u{1F981}",
      lips: "\u{1F444}",
      lipstick: "\u{1F484}",
      lizard: "\u{1F98E}",
      lock: "\u{1F512}",
      lock_with_ink_pen: "\u{1F50F}",
      lollipop: "\u{1F36D}",
      loop: "\u27BF",
      loud_sound: "\u{1F50A}",
      loudspeaker: "\u{1F4E2}",
      love_hotel: "\u{1F3E9}",
      love_letter: "\u{1F48C}",
      low_brightness: "\u{1F505}",
      lying_face: "\u{1F925}",
      m: "\u24C2\uFE0F",
      mag: "\u{1F50D}",
      mag_right: "\u{1F50E}",
      mahjong: "\u{1F004}\uFE0F",
      mailbox: "\u{1F4EB}",
      mailbox_closed: "\u{1F4EA}",
      mailbox_with_mail: "\u{1F4EC}",
      mailbox_with_no_mail: "\u{1F4ED}",
      man: "\u{1F468}",
      man_artist: "\u{1F468}&zwj;\u{1F3A8}",
      man_astronaut: "\u{1F468}&zwj;\u{1F680}",
      man_cartwheeling: "\u{1F938}&zwj;\u2642\uFE0F",
      man_cook: "\u{1F468}&zwj;\u{1F373}",
      man_dancing: "\u{1F57A}",
      man_facepalming: "\u{1F926}&zwj;\u2642\uFE0F",
      man_factory_worker: "\u{1F468}&zwj;\u{1F3ED}",
      man_farmer: "\u{1F468}&zwj;\u{1F33E}",
      man_firefighter: "\u{1F468}&zwj;\u{1F692}",
      man_health_worker: "\u{1F468}&zwj;\u2695\uFE0F",
      man_in_tuxedo: "\u{1F935}",
      man_judge: "\u{1F468}&zwj;\u2696\uFE0F",
      man_juggling: "\u{1F939}&zwj;\u2642\uFE0F",
      man_mechanic: "\u{1F468}&zwj;\u{1F527}",
      man_office_worker: "\u{1F468}&zwj;\u{1F4BC}",
      man_pilot: "\u{1F468}&zwj;\u2708\uFE0F",
      man_playing_handball: "\u{1F93E}&zwj;\u2642\uFE0F",
      man_playing_water_polo: "\u{1F93D}&zwj;\u2642\uFE0F",
      man_scientist: "\u{1F468}&zwj;\u{1F52C}",
      man_shrugging: "\u{1F937}&zwj;\u2642\uFE0F",
      man_singer: "\u{1F468}&zwj;\u{1F3A4}",
      man_student: "\u{1F468}&zwj;\u{1F393}",
      man_teacher: "\u{1F468}&zwj;\u{1F3EB}",
      man_technologist: "\u{1F468}&zwj;\u{1F4BB}",
      man_with_gua_pi_mao: "\u{1F472}",
      man_with_turban: "\u{1F473}",
      tangerine: "\u{1F34A}",
      mans_shoe: "\u{1F45E}",
      mantelpiece_clock: "\u{1F570}",
      maple_leaf: "\u{1F341}",
      martial_arts_uniform: "\u{1F94B}",
      mask: "\u{1F637}",
      massage_woman: "\u{1F486}",
      massage_man: "\u{1F486}&zwj;\u2642\uFE0F",
      meat_on_bone: "\u{1F356}",
      medal_military: "\u{1F396}",
      medal_sports: "\u{1F3C5}",
      mega: "\u{1F4E3}",
      melon: "\u{1F348}",
      memo: "\u{1F4DD}",
      men_wrestling: "\u{1F93C}&zwj;\u2642\uFE0F",
      menorah: "\u{1F54E}",
      mens: "\u{1F6B9}",
      metal: "\u{1F918}",
      metro: "\u{1F687}",
      microphone: "\u{1F3A4}",
      microscope: "\u{1F52C}",
      milk_glass: "\u{1F95B}",
      milky_way: "\u{1F30C}",
      minibus: "\u{1F690}",
      minidisc: "\u{1F4BD}",
      mobile_phone_off: "\u{1F4F4}",
      money_mouth_face: "\u{1F911}",
      money_with_wings: "\u{1F4B8}",
      moneybag: "\u{1F4B0}",
      monkey: "\u{1F412}",
      monkey_face: "\u{1F435}",
      monorail: "\u{1F69D}",
      moon: "\u{1F314}",
      mortar_board: "\u{1F393}",
      mosque: "\u{1F54C}",
      motor_boat: "\u{1F6E5}",
      motor_scooter: "\u{1F6F5}",
      motorcycle: "\u{1F3CD}",
      motorway: "\u{1F6E3}",
      mount_fuji: "\u{1F5FB}",
      mountain: "\u26F0",
      mountain_biking_man: "\u{1F6B5}",
      mountain_biking_woman: "\u{1F6B5}&zwj;\u2640\uFE0F",
      mountain_cableway: "\u{1F6A0}",
      mountain_railway: "\u{1F69E}",
      mountain_snow: "\u{1F3D4}",
      mouse: "\u{1F42D}",
      mouse2: "\u{1F401}",
      movie_camera: "\u{1F3A5}",
      moyai: "\u{1F5FF}",
      mrs_claus: "\u{1F936}",
      muscle: "\u{1F4AA}",
      mushroom: "\u{1F344}",
      musical_keyboard: "\u{1F3B9}",
      musical_note: "\u{1F3B5}",
      musical_score: "\u{1F3BC}",
      mute: "\u{1F507}",
      nail_care: "\u{1F485}",
      name_badge: "\u{1F4DB}",
      national_park: "\u{1F3DE}",
      nauseated_face: "\u{1F922}",
      necktie: "\u{1F454}",
      negative_squared_cross_mark: "\u274E",
      nerd_face: "\u{1F913}",
      neutral_face: "\u{1F610}",
      new: "\u{1F195}",
      new_moon: "\u{1F311}",
      new_moon_with_face: "\u{1F31A}",
      newspaper: "\u{1F4F0}",
      newspaper_roll: "\u{1F5DE}",
      next_track_button: "\u23ED",
      ng: "\u{1F196}",
      no_good_man: "\u{1F645}&zwj;\u2642\uFE0F",
      no_good_woman: "\u{1F645}",
      night_with_stars: "\u{1F303}",
      no_bell: "\u{1F515}",
      no_bicycles: "\u{1F6B3}",
      no_entry: "\u26D4\uFE0F",
      no_entry_sign: "\u{1F6AB}",
      no_mobile_phones: "\u{1F4F5}",
      no_mouth: "\u{1F636}",
      no_pedestrians: "\u{1F6B7}",
      no_smoking: "\u{1F6AD}",
      "non-potable_water": "\u{1F6B1}",
      nose: "\u{1F443}",
      notebook: "\u{1F4D3}",
      notebook_with_decorative_cover: "\u{1F4D4}",
      notes: "\u{1F3B6}",
      nut_and_bolt: "\u{1F529}",
      o: "\u2B55\uFE0F",
      o2: "\u{1F17E}\uFE0F",
      ocean: "\u{1F30A}",
      octopus: "\u{1F419}",
      oden: "\u{1F362}",
      office: "\u{1F3E2}",
      oil_drum: "\u{1F6E2}",
      ok: "\u{1F197}",
      ok_hand: "\u{1F44C}",
      ok_man: "\u{1F646}&zwj;\u2642\uFE0F",
      ok_woman: "\u{1F646}",
      old_key: "\u{1F5DD}",
      older_man: "\u{1F474}",
      older_woman: "\u{1F475}",
      om: "\u{1F549}",
      on: "\u{1F51B}",
      oncoming_automobile: "\u{1F698}",
      oncoming_bus: "\u{1F68D}",
      oncoming_police_car: "\u{1F694}",
      oncoming_taxi: "\u{1F696}",
      open_file_folder: "\u{1F4C2}",
      open_hands: "\u{1F450}",
      open_mouth: "\u{1F62E}",
      open_umbrella: "\u2602\uFE0F",
      ophiuchus: "\u26CE",
      orange_book: "\u{1F4D9}",
      orthodox_cross: "\u2626\uFE0F",
      outbox_tray: "\u{1F4E4}",
      owl: "\u{1F989}",
      ox: "\u{1F402}",
      package: "\u{1F4E6}",
      page_facing_up: "\u{1F4C4}",
      page_with_curl: "\u{1F4C3}",
      pager: "\u{1F4DF}",
      paintbrush: "\u{1F58C}",
      palm_tree: "\u{1F334}",
      pancakes: "\u{1F95E}",
      panda_face: "\u{1F43C}",
      paperclip: "\u{1F4CE}",
      paperclips: "\u{1F587}",
      parasol_on_ground: "\u26F1",
      parking: "\u{1F17F}\uFE0F",
      part_alternation_mark: "\u303D\uFE0F",
      partly_sunny: "\u26C5\uFE0F",
      passenger_ship: "\u{1F6F3}",
      passport_control: "\u{1F6C2}",
      pause_button: "\u23F8",
      peace_symbol: "\u262E\uFE0F",
      peach: "\u{1F351}",
      peanuts: "\u{1F95C}",
      pear: "\u{1F350}",
      pen: "\u{1F58A}",
      pencil2: "\u270F\uFE0F",
      penguin: "\u{1F427}",
      pensive: "\u{1F614}",
      performing_arts: "\u{1F3AD}",
      persevere: "\u{1F623}",
      person_fencing: "\u{1F93A}",
      pouting_woman: "\u{1F64E}",
      phone: "\u260E\uFE0F",
      pick: "\u26CF",
      pig: "\u{1F437}",
      pig2: "\u{1F416}",
      pig_nose: "\u{1F43D}",
      pill: "\u{1F48A}",
      pineapple: "\u{1F34D}",
      ping_pong: "\u{1F3D3}",
      pisces: "\u2653\uFE0F",
      pizza: "\u{1F355}",
      place_of_worship: "\u{1F6D0}",
      plate_with_cutlery: "\u{1F37D}",
      play_or_pause_button: "\u23EF",
      point_down: "\u{1F447}",
      point_left: "\u{1F448}",
      point_right: "\u{1F449}",
      point_up: "\u261D\uFE0F",
      point_up_2: "\u{1F446}",
      police_car: "\u{1F693}",
      policewoman: "\u{1F46E}&zwj;\u2640\uFE0F",
      poodle: "\u{1F429}",
      popcorn: "\u{1F37F}",
      post_office: "\u{1F3E3}",
      postal_horn: "\u{1F4EF}",
      postbox: "\u{1F4EE}",
      potable_water: "\u{1F6B0}",
      potato: "\u{1F954}",
      pouch: "\u{1F45D}",
      poultry_leg: "\u{1F357}",
      pound: "\u{1F4B7}",
      rage: "\u{1F621}",
      pouting_cat: "\u{1F63E}",
      pouting_man: "\u{1F64E}&zwj;\u2642\uFE0F",
      pray: "\u{1F64F}",
      prayer_beads: "\u{1F4FF}",
      pregnant_woman: "\u{1F930}",
      previous_track_button: "\u23EE",
      prince: "\u{1F934}",
      princess: "\u{1F478}",
      printer: "\u{1F5A8}",
      purple_heart: "\u{1F49C}",
      purse: "\u{1F45B}",
      pushpin: "\u{1F4CC}",
      put_litter_in_its_place: "\u{1F6AE}",
      question: "\u2753",
      rabbit: "\u{1F430}",
      rabbit2: "\u{1F407}",
      racehorse: "\u{1F40E}",
      racing_car: "\u{1F3CE}",
      radio: "\u{1F4FB}",
      radio_button: "\u{1F518}",
      radioactive: "\u2622\uFE0F",
      railway_car: "\u{1F683}",
      railway_track: "\u{1F6E4}",
      rainbow: "\u{1F308}",
      rainbow_flag: "\u{1F3F3}\uFE0F&zwj;\u{1F308}",
      raised_back_of_hand: "\u{1F91A}",
      raised_hand_with_fingers_splayed: "\u{1F590}",
      raised_hands: "\u{1F64C}",
      raising_hand_woman: "\u{1F64B}",
      raising_hand_man: "\u{1F64B}&zwj;\u2642\uFE0F",
      ram: "\u{1F40F}",
      ramen: "\u{1F35C}",
      rat: "\u{1F400}",
      record_button: "\u23FA",
      recycle: "\u267B\uFE0F",
      red_circle: "\u{1F534}",
      registered: "\xAE\uFE0F",
      relaxed: "\u263A\uFE0F",
      relieved: "\u{1F60C}",
      reminder_ribbon: "\u{1F397}",
      repeat: "\u{1F501}",
      repeat_one: "\u{1F502}",
      rescue_worker_helmet: "\u26D1",
      restroom: "\u{1F6BB}",
      revolving_hearts: "\u{1F49E}",
      rewind: "\u23EA",
      rhinoceros: "\u{1F98F}",
      ribbon: "\u{1F380}",
      rice: "\u{1F35A}",
      rice_ball: "\u{1F359}",
      rice_cracker: "\u{1F358}",
      rice_scene: "\u{1F391}",
      right_anger_bubble: "\u{1F5EF}",
      ring: "\u{1F48D}",
      robot: "\u{1F916}",
      rocket: "\u{1F680}",
      rofl: "\u{1F923}",
      roll_eyes: "\u{1F644}",
      roller_coaster: "\u{1F3A2}",
      rooster: "\u{1F413}",
      rose: "\u{1F339}",
      rosette: "\u{1F3F5}",
      rotating_light: "\u{1F6A8}",
      round_pushpin: "\u{1F4CD}",
      rowing_man: "\u{1F6A3}",
      rowing_woman: "\u{1F6A3}&zwj;\u2640\uFE0F",
      rugby_football: "\u{1F3C9}",
      running_man: "\u{1F3C3}",
      running_shirt_with_sash: "\u{1F3BD}",
      running_woman: "\u{1F3C3}&zwj;\u2640\uFE0F",
      sa: "\u{1F202}\uFE0F",
      sagittarius: "\u2650\uFE0F",
      sake: "\u{1F376}",
      sandal: "\u{1F461}",
      santa: "\u{1F385}",
      satellite: "\u{1F4E1}",
      saxophone: "\u{1F3B7}",
      school: "\u{1F3EB}",
      school_satchel: "\u{1F392}",
      scissors: "\u2702\uFE0F",
      scorpion: "\u{1F982}",
      scorpius: "\u264F\uFE0F",
      scream: "\u{1F631}",
      scream_cat: "\u{1F640}",
      scroll: "\u{1F4DC}",
      seat: "\u{1F4BA}",
      secret: "\u3299\uFE0F",
      see_no_evil: "\u{1F648}",
      seedling: "\u{1F331}",
      selfie: "\u{1F933}",
      shallow_pan_of_food: "\u{1F958}",
      shamrock: "\u2618\uFE0F",
      shark: "\u{1F988}",
      shaved_ice: "\u{1F367}",
      sheep: "\u{1F411}",
      shell: "\u{1F41A}",
      shield: "\u{1F6E1}",
      shinto_shrine: "\u26E9",
      ship: "\u{1F6A2}",
      shirt: "\u{1F455}",
      shopping: "\u{1F6CD}",
      shopping_cart: "\u{1F6D2}",
      shower: "\u{1F6BF}",
      shrimp: "\u{1F990}",
      signal_strength: "\u{1F4F6}",
      six_pointed_star: "\u{1F52F}",
      ski: "\u{1F3BF}",
      skier: "\u26F7",
      skull: "\u{1F480}",
      skull_and_crossbones: "\u2620\uFE0F",
      sleeping: "\u{1F634}",
      sleeping_bed: "\u{1F6CC}",
      sleepy: "\u{1F62A}",
      slightly_frowning_face: "\u{1F641}",
      slightly_smiling_face: "\u{1F642}",
      slot_machine: "\u{1F3B0}",
      small_airplane: "\u{1F6E9}",
      small_blue_diamond: "\u{1F539}",
      small_orange_diamond: "\u{1F538}",
      small_red_triangle: "\u{1F53A}",
      small_red_triangle_down: "\u{1F53B}",
      smile: "\u{1F604}",
      smile_cat: "\u{1F638}",
      smiley: "\u{1F603}",
      smiley_cat: "\u{1F63A}",
      smiling_imp: "\u{1F608}",
      smirk: "\u{1F60F}",
      smirk_cat: "\u{1F63C}",
      smoking: "\u{1F6AC}",
      snail: "\u{1F40C}",
      snake: "\u{1F40D}",
      sneezing_face: "\u{1F927}",
      snowboarder: "\u{1F3C2}",
      snowflake: "\u2744\uFE0F",
      snowman: "\u26C4\uFE0F",
      snowman_with_snow: "\u2603\uFE0F",
      sob: "\u{1F62D}",
      soccer: "\u26BD\uFE0F",
      soon: "\u{1F51C}",
      sos: "\u{1F198}",
      sound: "\u{1F509}",
      space_invader: "\u{1F47E}",
      spades: "\u2660\uFE0F",
      spaghetti: "\u{1F35D}",
      sparkle: "\u2747\uFE0F",
      sparkler: "\u{1F387}",
      sparkles: "\u2728",
      sparkling_heart: "\u{1F496}",
      speak_no_evil: "\u{1F64A}",
      speaker: "\u{1F508}",
      speaking_head: "\u{1F5E3}",
      speech_balloon: "\u{1F4AC}",
      speedboat: "\u{1F6A4}",
      spider: "\u{1F577}",
      spider_web: "\u{1F578}",
      spiral_calendar: "\u{1F5D3}",
      spiral_notepad: "\u{1F5D2}",
      spoon: "\u{1F944}",
      squid: "\u{1F991}",
      stadium: "\u{1F3DF}",
      star: "\u2B50\uFE0F",
      star2: "\u{1F31F}",
      star_and_crescent: "\u262A\uFE0F",
      star_of_david: "\u2721\uFE0F",
      stars: "\u{1F320}",
      station: "\u{1F689}",
      statue_of_liberty: "\u{1F5FD}",
      steam_locomotive: "\u{1F682}",
      stew: "\u{1F372}",
      stop_button: "\u23F9",
      stop_sign: "\u{1F6D1}",
      stopwatch: "\u23F1",
      straight_ruler: "\u{1F4CF}",
      strawberry: "\u{1F353}",
      stuck_out_tongue: "\u{1F61B}",
      stuck_out_tongue_closed_eyes: "\u{1F61D}",
      stuck_out_tongue_winking_eye: "\u{1F61C}",
      studio_microphone: "\u{1F399}",
      stuffed_flatbread: "\u{1F959}",
      sun_behind_large_cloud: "\u{1F325}",
      sun_behind_rain_cloud: "\u{1F326}",
      sun_behind_small_cloud: "\u{1F324}",
      sun_with_face: "\u{1F31E}",
      sunflower: "\u{1F33B}",
      sunglasses: "\u{1F60E}",
      sunny: "\u2600\uFE0F",
      sunrise: "\u{1F305}",
      sunrise_over_mountains: "\u{1F304}",
      surfing_man: "\u{1F3C4}",
      surfing_woman: "\u{1F3C4}&zwj;\u2640\uFE0F",
      sushi: "\u{1F363}",
      suspension_railway: "\u{1F69F}",
      sweat: "\u{1F613}",
      sweat_drops: "\u{1F4A6}",
      sweat_smile: "\u{1F605}",
      sweet_potato: "\u{1F360}",
      swimming_man: "\u{1F3CA}",
      swimming_woman: "\u{1F3CA}&zwj;\u2640\uFE0F",
      symbols: "\u{1F523}",
      synagogue: "\u{1F54D}",
      syringe: "\u{1F489}",
      taco: "\u{1F32E}",
      tada: "\u{1F389}",
      tanabata_tree: "\u{1F38B}",
      taurus: "\u2649\uFE0F",
      taxi: "\u{1F695}",
      tea: "\u{1F375}",
      telephone_receiver: "\u{1F4DE}",
      telescope: "\u{1F52D}",
      tennis: "\u{1F3BE}",
      tent: "\u26FA\uFE0F",
      thermometer: "\u{1F321}",
      thinking: "\u{1F914}",
      thought_balloon: "\u{1F4AD}",
      ticket: "\u{1F3AB}",
      tickets: "\u{1F39F}",
      tiger: "\u{1F42F}",
      tiger2: "\u{1F405}",
      timer_clock: "\u23F2",
      tipping_hand_man: "\u{1F481}&zwj;\u2642\uFE0F",
      tired_face: "\u{1F62B}",
      tm: "\u2122\uFE0F",
      toilet: "\u{1F6BD}",
      tokyo_tower: "\u{1F5FC}",
      tomato: "\u{1F345}",
      tongue: "\u{1F445}",
      top: "\u{1F51D}",
      tophat: "\u{1F3A9}",
      tornado: "\u{1F32A}",
      trackball: "\u{1F5B2}",
      tractor: "\u{1F69C}",
      traffic_light: "\u{1F6A5}",
      train: "\u{1F68B}",
      train2: "\u{1F686}",
      tram: "\u{1F68A}",
      triangular_flag_on_post: "\u{1F6A9}",
      triangular_ruler: "\u{1F4D0}",
      trident: "\u{1F531}",
      triumph: "\u{1F624}",
      trolleybus: "\u{1F68E}",
      trophy: "\u{1F3C6}",
      tropical_drink: "\u{1F379}",
      tropical_fish: "\u{1F420}",
      truck: "\u{1F69A}",
      trumpet: "\u{1F3BA}",
      tulip: "\u{1F337}",
      tumbler_glass: "\u{1F943}",
      turkey: "\u{1F983}",
      turtle: "\u{1F422}",
      tv: "\u{1F4FA}",
      twisted_rightwards_arrows: "\u{1F500}",
      two_hearts: "\u{1F495}",
      two_men_holding_hands: "\u{1F46C}",
      two_women_holding_hands: "\u{1F46D}",
      u5272: "\u{1F239}",
      u5408: "\u{1F234}",
      u55b6: "\u{1F23A}",
      u6307: "\u{1F22F}\uFE0F",
      u6708: "\u{1F237}\uFE0F",
      u6709: "\u{1F236}",
      u6e80: "\u{1F235}",
      u7121: "\u{1F21A}\uFE0F",
      u7533: "\u{1F238}",
      u7981: "\u{1F232}",
      u7a7a: "\u{1F233}",
      umbrella: "\u2614\uFE0F",
      unamused: "\u{1F612}",
      underage: "\u{1F51E}",
      unicorn: "\u{1F984}",
      unlock: "\u{1F513}",
      up: "\u{1F199}",
      upside_down_face: "\u{1F643}",
      v: "\u270C\uFE0F",
      vertical_traffic_light: "\u{1F6A6}",
      vhs: "\u{1F4FC}",
      vibration_mode: "\u{1F4F3}",
      video_camera: "\u{1F4F9}",
      video_game: "\u{1F3AE}",
      violin: "\u{1F3BB}",
      virgo: "\u264D\uFE0F",
      volcano: "\u{1F30B}",
      volleyball: "\u{1F3D0}",
      vs: "\u{1F19A}",
      vulcan_salute: "\u{1F596}",
      walking_man: "\u{1F6B6}",
      walking_woman: "\u{1F6B6}&zwj;\u2640\uFE0F",
      waning_crescent_moon: "\u{1F318}",
      waning_gibbous_moon: "\u{1F316}",
      warning: "\u26A0\uFE0F",
      wastebasket: "\u{1F5D1}",
      watch: "\u231A\uFE0F",
      water_buffalo: "\u{1F403}",
      watermelon: "\u{1F349}",
      wave: "\u{1F44B}",
      wavy_dash: "\u3030\uFE0F",
      waxing_crescent_moon: "\u{1F312}",
      wc: "\u{1F6BE}",
      weary: "\u{1F629}",
      wedding: "\u{1F492}",
      weight_lifting_man: "\u{1F3CB}\uFE0F",
      weight_lifting_woman: "\u{1F3CB}\uFE0F&zwj;\u2640\uFE0F",
      whale: "\u{1F433}",
      whale2: "\u{1F40B}",
      wheel_of_dharma: "\u2638\uFE0F",
      wheelchair: "\u267F\uFE0F",
      white_check_mark: "\u2705",
      white_circle: "\u26AA\uFE0F",
      white_flag: "\u{1F3F3}\uFE0F",
      white_flower: "\u{1F4AE}",
      white_large_square: "\u2B1C\uFE0F",
      white_medium_small_square: "\u25FD\uFE0F",
      white_medium_square: "\u25FB\uFE0F",
      white_small_square: "\u25AB\uFE0F",
      white_square_button: "\u{1F533}",
      wilted_flower: "\u{1F940}",
      wind_chime: "\u{1F390}",
      wind_face: "\u{1F32C}",
      wine_glass: "\u{1F377}",
      wink: "\u{1F609}",
      wolf: "\u{1F43A}",
      woman: "\u{1F469}",
      woman_artist: "\u{1F469}&zwj;\u{1F3A8}",
      woman_astronaut: "\u{1F469}&zwj;\u{1F680}",
      woman_cartwheeling: "\u{1F938}&zwj;\u2640\uFE0F",
      woman_cook: "\u{1F469}&zwj;\u{1F373}",
      woman_facepalming: "\u{1F926}&zwj;\u2640\uFE0F",
      woman_factory_worker: "\u{1F469}&zwj;\u{1F3ED}",
      woman_farmer: "\u{1F469}&zwj;\u{1F33E}",
      woman_firefighter: "\u{1F469}&zwj;\u{1F692}",
      woman_health_worker: "\u{1F469}&zwj;\u2695\uFE0F",
      woman_judge: "\u{1F469}&zwj;\u2696\uFE0F",
      woman_juggling: "\u{1F939}&zwj;\u2640\uFE0F",
      woman_mechanic: "\u{1F469}&zwj;\u{1F527}",
      woman_office_worker: "\u{1F469}&zwj;\u{1F4BC}",
      woman_pilot: "\u{1F469}&zwj;\u2708\uFE0F",
      woman_playing_handball: "\u{1F93E}&zwj;\u2640\uFE0F",
      woman_playing_water_polo: "\u{1F93D}&zwj;\u2640\uFE0F",
      woman_scientist: "\u{1F469}&zwj;\u{1F52C}",
      woman_shrugging: "\u{1F937}&zwj;\u2640\uFE0F",
      woman_singer: "\u{1F469}&zwj;\u{1F3A4}",
      woman_student: "\u{1F469}&zwj;\u{1F393}",
      woman_teacher: "\u{1F469}&zwj;\u{1F3EB}",
      woman_technologist: "\u{1F469}&zwj;\u{1F4BB}",
      woman_with_turban: "\u{1F473}&zwj;\u2640\uFE0F",
      womans_clothes: "\u{1F45A}",
      womans_hat: "\u{1F452}",
      women_wrestling: "\u{1F93C}&zwj;\u2640\uFE0F",
      womens: "\u{1F6BA}",
      world_map: "\u{1F5FA}",
      worried: "\u{1F61F}",
      wrench: "\u{1F527}",
      writing_hand: "\u270D\uFE0F",
      x: "\u274C",
      yellow_heart: "\u{1F49B}",
      yen: "\u{1F4B4}",
      yin_yang: "\u262F\uFE0F",
      yum: "\u{1F60B}",
      zap: "\u26A1\uFE0F",
      zipper_mouth_face: "\u{1F910}",
      zzz: "\u{1F4A4}",
      octocat: '<img alt=":octocat:" height="20" width="20" align="absmiddle" src="https://assets-cdn.github.com/images/icons/emoji/octocat.png">',
      showdown: `<span style="font-family: 'Anonymous Pro', monospace; text-decoration: underline; text-decoration-style: dashed; text-decoration-color: #3e8b8a;text-underline-position: under;">S</span>`
    };
    showdown2.Converter = function(converterOptions) {
      var options = {}, langExtensions = [], outputModifiers = [], listeners = {}, setConvFlavor = setFlavor2, metadata = {
        parsed: {},
        raw: "",
        format: ""
      };
      _constructor();
      function _constructor() {
        converterOptions = converterOptions || {};
        for (var gOpt in globalOptions) {
          if (globalOptions.hasOwnProperty(gOpt)) {
            options[gOpt] = globalOptions[gOpt];
          }
        }
        if (typeof converterOptions === "object") {
          for (var opt in converterOptions) {
            if (converterOptions.hasOwnProperty(opt)) {
              options[opt] = converterOptions[opt];
            }
          }
        } else {
          throw Error("Converter expects the passed parameter to be an object, but " + typeof converterOptions + " was passed instead.");
        }
        if (options.extensions) {
          showdown2.helper.forEach(options.extensions, _parseExtension);
        }
      }
      function _parseExtension(ext, name) {
        name = name || null;
        if (showdown2.helper.isString(ext)) {
          ext = showdown2.helper.stdExtName(ext);
          name = ext;
          if (showdown2.extensions[ext]) {
            console.warn("DEPRECATION WARNING: " + ext + " is an old extension that uses a deprecated loading method.Please inform the developer that the extension should be updated!");
            legacyExtensionLoading(showdown2.extensions[ext], ext);
            return;
          } else if (!showdown2.helper.isUndefined(extensions2[ext])) {
            ext = extensions2[ext];
          } else {
            throw Error('Extension "' + ext + '" could not be loaded. It was either not found or is not a valid extension.');
          }
        }
        if (typeof ext === "function") {
          ext = ext();
        }
        if (!showdown2.helper.isArray(ext)) {
          ext = [ext];
        }
        var validExt = validate(ext, name);
        if (!validExt.valid) {
          throw Error(validExt.error);
        }
        for (var i = 0; i < ext.length; ++i) {
          switch (ext[i].type) {
            case "lang":
              langExtensions.push(ext[i]);
              break;
            case "output":
              outputModifiers.push(ext[i]);
              break;
          }
          if (ext[i].hasOwnProperty("listeners")) {
            for (var ln in ext[i].listeners) {
              if (ext[i].listeners.hasOwnProperty(ln)) {
                listen(ln, ext[i].listeners[ln]);
              }
            }
          }
        }
      }
      function legacyExtensionLoading(ext, name) {
        if (typeof ext === "function") {
          ext = ext(new showdown2.Converter());
        }
        if (!showdown2.helper.isArray(ext)) {
          ext = [ext];
        }
        var valid = validate(ext, name);
        if (!valid.valid) {
          throw Error(valid.error);
        }
        for (var i = 0; i < ext.length; ++i) {
          switch (ext[i].type) {
            case "lang":
              langExtensions.push(ext[i]);
              break;
            case "output":
              outputModifiers.push(ext[i]);
              break;
            default:
              throw Error("Extension loader error: Type unrecognized!!!");
          }
        }
      }
      function listen(name, callback) {
        if (!showdown2.helper.isString(name)) {
          throw Error("Invalid argument in converter.listen() method: name must be a string, but " + typeof name + " given");
        }
        if (typeof callback !== "function") {
          throw Error("Invalid argument in converter.listen() method: callback must be a function, but " + typeof callback + " given");
        }
        if (!listeners.hasOwnProperty(name)) {
          listeners[name] = [];
        }
        listeners[name].push(callback);
      }
      function rTrimInputText(text) {
        var rsp = text.match(/^\s*/)[0].length, rgx = new RegExp("^\\s{0," + rsp + "}", "gm");
        return text.replace(rgx, "");
      }
      this._dispatch = function dispatch(evtName, text, options2, globals) {
        if (listeners.hasOwnProperty(evtName)) {
          for (var ei = 0; ei < listeners[evtName].length; ++ei) {
            var nText = listeners[evtName][ei](evtName, text, this, options2, globals);
            if (nText && typeof nText !== "undefined") {
              text = nText;
            }
          }
        }
        return text;
      };
      this.listen = function(name, callback) {
        listen(name, callback);
        return this;
      };
      this.makeHtml = function(text) {
        if (!text) {
          return text;
        }
        var globals = {
          gHtmlBlocks: [],
          gHtmlMdBlocks: [],
          gHtmlSpans: [],
          gUrls: {},
          gTitles: {},
          gDimensions: {},
          gListLevel: 0,
          hashLinkCounts: {},
          langExtensions,
          outputModifiers,
          converter: this,
          ghCodeBlocks: [],
          metadata: {
            parsed: {},
            raw: "",
            format: ""
          }
        };
        text = text.replace(/¨/g, "\xA8T");
        text = text.replace(/\$/g, "\xA8D");
        text = text.replace(/\r\n/g, "\n");
        text = text.replace(/\r/g, "\n");
        text = text.replace(/\u00A0/g, "&nbsp;");
        if (options.smartIndentationFix) {
          text = rTrimInputText(text);
        }
        text = "\n\n" + text + "\n\n";
        text = showdown2.subParser("detab")(text, options, globals);
        text = text.replace(/^[ \t]+$/mg, "");
        showdown2.helper.forEach(langExtensions, function(ext) {
          text = showdown2.subParser("runExtension")(ext, text, options, globals);
        });
        text = showdown2.subParser("metadata")(text, options, globals);
        text = showdown2.subParser("hashPreCodeTags")(text, options, globals);
        text = showdown2.subParser("githubCodeBlocks")(text, options, globals);
        text = showdown2.subParser("hashHTMLBlocks")(text, options, globals);
        text = showdown2.subParser("hashCodeTags")(text, options, globals);
        text = showdown2.subParser("stripLinkDefinitions")(text, options, globals);
        text = showdown2.subParser("blockGamut")(text, options, globals);
        text = showdown2.subParser("unhashHTMLSpans")(text, options, globals);
        text = showdown2.subParser("unescapeSpecialChars")(text, options, globals);
        text = text.replace(/¨D/g, "$$");
        text = text.replace(/¨T/g, "\xA8");
        text = showdown2.subParser("completeHTMLDocument")(text, options, globals);
        showdown2.helper.forEach(outputModifiers, function(ext) {
          text = showdown2.subParser("runExtension")(ext, text, options, globals);
        });
        metadata = globals.metadata;
        return text;
      };
      this.makeMarkdown = this.makeMd = function(src, HTMLParser) {
        src = src.replace(/\r\n/g, "\n");
        src = src.replace(/\r/g, "\n");
        src = src.replace(/>[ \t]+</, ">\xA8NBSP;<");
        if (!HTMLParser) {
          if (window && window.document) {
            HTMLParser = window.document;
          } else {
            throw new Error("HTMLParser is undefined. If in a webworker or nodejs environment, you need to provide a WHATWG DOM and HTML such as JSDOM");
          }
        }
        var doc = HTMLParser.createElement("div");
        doc.innerHTML = src;
        var globals = {
          preList: substitutePreCodeTags(doc)
        };
        clean(doc);
        var nodes = doc.childNodes, mdDoc = "";
        for (var i = 0; i < nodes.length; i++) {
          mdDoc += showdown2.subParser("makeMarkdown.node")(nodes[i], globals);
        }
        function clean(node) {
          for (var n = 0; n < node.childNodes.length; ++n) {
            var child = node.childNodes[n];
            if (child.nodeType === 3) {
              if (!/\S/.test(child.nodeValue) && !/^[ ]+$/.test(child.nodeValue)) {
                node.removeChild(child);
                --n;
              } else {
                child.nodeValue = child.nodeValue.split("\n").join(" ");
                child.nodeValue = child.nodeValue.replace(/(\s)+/g, "$1");
              }
            } else if (child.nodeType === 1) {
              clean(child);
            }
          }
        }
        function substitutePreCodeTags(doc2) {
          var pres = doc2.querySelectorAll("pre"), presPH = [];
          for (var i2 = 0; i2 < pres.length; ++i2) {
            if (pres[i2].childElementCount === 1 && pres[i2].firstChild.tagName.toLowerCase() === "code") {
              var content = pres[i2].firstChild.innerHTML.trim(), language = pres[i2].firstChild.getAttribute("data-language") || "";
              if (language === "") {
                var classes = pres[i2].firstChild.className.split(" ");
                for (var c = 0; c < classes.length; ++c) {
                  var matches = classes[c].match(/^language-(.+)$/);
                  if (matches !== null) {
                    language = matches[1];
                    break;
                  }
                }
              }
              content = showdown2.helper.unescapeHTMLEntities(content);
              presPH.push(content);
              pres[i2].outerHTML = '<precode language="' + language + '" precodenum="' + i2.toString() + '"></precode>';
            } else {
              presPH.push(pres[i2].innerHTML);
              pres[i2].innerHTML = "";
              pres[i2].setAttribute("prenum", i2.toString());
            }
          }
          return presPH;
        }
        return mdDoc;
      };
      this.setOption = function(key, value) {
        options[key] = value;
      };
      this.getOption = function(key) {
        return options[key];
      };
      this.getOptions = function() {
        return options;
      };
      this.addExtension = function(extension2, name) {
        name = name || null;
        _parseExtension(extension2, name);
      };
      this.useExtension = function(extensionName) {
        _parseExtension(extensionName);
      };
      this.setFlavor = function(name) {
        if (!flavor.hasOwnProperty(name)) {
          throw Error(name + " flavor was not found");
        }
        var preset = flavor[name];
        setConvFlavor = name;
        for (var option in preset) {
          if (preset.hasOwnProperty(option)) {
            options[option] = preset[option];
          }
        }
      };
      this.getFlavor = function() {
        return setConvFlavor;
      };
      this.removeExtension = function(extension2) {
        if (!showdown2.helper.isArray(extension2)) {
          extension2 = [extension2];
        }
        for (var a = 0; a < extension2.length; ++a) {
          var ext = extension2[a];
          for (var i = 0; i < langExtensions.length; ++i) {
            if (langExtensions[i] === ext) {
              langExtensions.splice(i, 1);
            }
          }
          for (var ii = 0; ii < outputModifiers.length; ++ii) {
            if (outputModifiers[ii] === ext) {
              outputModifiers.splice(ii, 1);
            }
          }
        }
      };
      this.getAllExtensions = function() {
        return {
          language: langExtensions,
          output: outputModifiers
        };
      };
      this.getMetadata = function(raw) {
        if (raw) {
          return metadata.raw;
        } else {
          return metadata.parsed;
        }
      };
      this.getMetadataFormat = function() {
        return metadata.format;
      };
      this._setMetadataPair = function(key, value) {
        metadata.parsed[key] = value;
      };
      this._setMetadataFormat = function(format) {
        metadata.format = format;
      };
      this._setMetadataRaw = function(raw) {
        metadata.raw = raw;
      };
    };
    showdown2.subParser("anchors", function(text, options, globals) {
      text = globals.converter._dispatch("anchors.before", text, options, globals);
      var writeAnchorTag = function(wholeMatch, linkText, linkId, url, m5, m6, title) {
        if (showdown2.helper.isUndefined(title)) {
          title = "";
        }
        linkId = linkId.toLowerCase();
        if (wholeMatch.search(/\(<?\s*>? ?(['"].*['"])?\)$/m) > -1) {
          url = "";
        } else if (!url) {
          if (!linkId) {
            linkId = linkText.toLowerCase().replace(/ ?\n/g, " ");
          }
          url = "#" + linkId;
          if (!showdown2.helper.isUndefined(globals.gUrls[linkId])) {
            url = globals.gUrls[linkId];
            if (!showdown2.helper.isUndefined(globals.gTitles[linkId])) {
              title = globals.gTitles[linkId];
            }
          } else {
            return wholeMatch;
          }
        }
        url = url.replace(showdown2.helper.regexes.asteriskDashAndColon, showdown2.helper.escapeCharactersCallback);
        var result = '<a href="' + url + '"';
        if (title !== "" && title !== null) {
          title = title.replace(/"/g, "&quot;");
          title = title.replace(showdown2.helper.regexes.asteriskDashAndColon, showdown2.helper.escapeCharactersCallback);
          result += ' title="' + title + '"';
        }
        if (options.openLinksInNewWindow && !/^#/.test(url)) {
          result += ' rel="noopener noreferrer" target="\xA8E95Eblank"';
        }
        result += ">" + linkText + "</a>";
        return result;
      };
      text = text.replace(/\[((?:\[[^\]]*]|[^\[\]])*)] ?(?:\n *)?\[(.*?)]()()()()/g, writeAnchorTag);
      text = text.replace(/\[((?:\[[^\]]*]|[^\[\]])*)]()[ \t]*\([ \t]?<([^>]*)>(?:[ \t]*((["'])([^"]*?)\5))?[ \t]?\)/g, writeAnchorTag);
      text = text.replace(/\[((?:\[[^\]]*]|[^\[\]])*)]()[ \t]*\([ \t]?<?([\S]+?(?:\([\S]*?\)[\S]*?)?)>?(?:[ \t]*((["'])([^"]*?)\5))?[ \t]?\)/g, writeAnchorTag);
      text = text.replace(/\[([^\[\]]+)]()()()()()/g, writeAnchorTag);
      if (options.ghMentions) {
        text = text.replace(/(^|\s)(\\)?(@([a-z\d]+(?:[a-z\d.-]+?[a-z\d]+)*))/gmi, function(wm, st, escape, mentions, username) {
          if (escape === "\\") {
            return st + mentions;
          }
          if (!showdown2.helper.isString(options.ghMentionsLink)) {
            throw new Error("ghMentionsLink option must be a string");
          }
          var lnk = options.ghMentionsLink.replace(/\{u}/g, username), target = "";
          if (options.openLinksInNewWindow) {
            target = ' rel="noopener noreferrer" target="\xA8E95Eblank"';
          }
          return st + '<a href="' + lnk + '"' + target + ">" + mentions + "</a>";
        });
      }
      text = globals.converter._dispatch("anchors.after", text, options, globals);
      return text;
    });
    var simpleURLRegex = /([*~_]+|\b)(((https?|ftp|dict):\/\/|www\.)[^'">\s]+?\.[^'">\s]+?)()(\1)?(?=\s|$)(?!["<>])/gi, simpleURLRegex2 = /([*~_]+|\b)(((https?|ftp|dict):\/\/|www\.)[^'">\s]+\.[^'">\s]+?)([.!?,()\[\]])?(\1)?(?=\s|$)(?!["<>])/gi, delimUrlRegex = /()<(((https?|ftp|dict):\/\/|www\.)[^'">\s]+)()>()/gi, simpleMailRegex = /(^|\s)(?:mailto:)?([A-Za-z0-9!#$%&'*+-/=?^_`{|}~.]+@[-a-z0-9]+(\.[-a-z0-9]+)*\.[a-z]+)(?=$|\s)/gmi, delimMailRegex = /<()(?:mailto:)?([-.\w]+@[-a-z0-9]+(\.[-a-z0-9]+)*\.[a-z]+)>/gi, replaceLink = function(options) {
      return function(wm, leadingMagicChars, link, m2, m3, trailingPunctuation, trailingMagicChars) {
        link = link.replace(showdown2.helper.regexes.asteriskDashAndColon, showdown2.helper.escapeCharactersCallback);
        var lnkTxt = link, append = "", target = "", lmc = leadingMagicChars || "", tmc = trailingMagicChars || "";
        if (/^www\./i.test(link)) {
          link = link.replace(/^www\./i, "http://www.");
        }
        if (options.excludeTrailingPunctuationFromURLs && trailingPunctuation) {
          append = trailingPunctuation;
        }
        if (options.openLinksInNewWindow) {
          target = ' rel="noopener noreferrer" target="\xA8E95Eblank"';
        }
        return lmc + '<a href="' + link + '"' + target + ">" + lnkTxt + "</a>" + append + tmc;
      };
    }, replaceMail = function(options, globals) {
      return function(wholeMatch, b, mail) {
        var href = "mailto:";
        b = b || "";
        mail = showdown2.subParser("unescapeSpecialChars")(mail, options, globals);
        if (options.encodeEmails) {
          href = showdown2.helper.encodeEmailAddress(href + mail);
          mail = showdown2.helper.encodeEmailAddress(mail);
        } else {
          href = href + mail;
        }
        return b + '<a href="' + href + '">' + mail + "</a>";
      };
    };
    showdown2.subParser("autoLinks", function(text, options, globals) {
      text = globals.converter._dispatch("autoLinks.before", text, options, globals);
      text = text.replace(delimUrlRegex, replaceLink(options));
      text = text.replace(delimMailRegex, replaceMail(options, globals));
      text = globals.converter._dispatch("autoLinks.after", text, options, globals);
      return text;
    });
    showdown2.subParser("simplifiedAutoLinks", function(text, options, globals) {
      if (!options.simplifiedAutoLink) {
        return text;
      }
      text = globals.converter._dispatch("simplifiedAutoLinks.before", text, options, globals);
      if (options.excludeTrailingPunctuationFromURLs) {
        text = text.replace(simpleURLRegex2, replaceLink(options));
      } else {
        text = text.replace(simpleURLRegex, replaceLink(options));
      }
      text = text.replace(simpleMailRegex, replaceMail(options, globals));
      text = globals.converter._dispatch("simplifiedAutoLinks.after", text, options, globals);
      return text;
    });
    showdown2.subParser("blockGamut", function(text, options, globals) {
      text = globals.converter._dispatch("blockGamut.before", text, options, globals);
      text = showdown2.subParser("blockQuotes")(text, options, globals);
      text = showdown2.subParser("headers")(text, options, globals);
      text = showdown2.subParser("horizontalRule")(text, options, globals);
      text = showdown2.subParser("lists")(text, options, globals);
      text = showdown2.subParser("codeBlocks")(text, options, globals);
      text = showdown2.subParser("tables")(text, options, globals);
      text = showdown2.subParser("hashHTMLBlocks")(text, options, globals);
      text = showdown2.subParser("paragraphs")(text, options, globals);
      text = globals.converter._dispatch("blockGamut.after", text, options, globals);
      return text;
    });
    showdown2.subParser("blockQuotes", function(text, options, globals) {
      text = globals.converter._dispatch("blockQuotes.before", text, options, globals);
      text = text + "\n\n";
      var rgx = /(^ {0,3}>[ \t]?.+\n(.+\n)*\n*)+/gm;
      if (options.splitAdjacentBlockquotes) {
        rgx = /^ {0,3}>[\s\S]*?(?:\n\n)/gm;
      }
      text = text.replace(rgx, function(bq) {
        bq = bq.replace(/^[ \t]*>[ \t]?/gm, "");
        bq = bq.replace(/¨0/g, "");
        bq = bq.replace(/^[ \t]+$/gm, "");
        bq = showdown2.subParser("githubCodeBlocks")(bq, options, globals);
        bq = showdown2.subParser("blockGamut")(bq, options, globals);
        bq = bq.replace(/(^|\n)/g, "$1  ");
        bq = bq.replace(/(\s*<pre>[^\r]+?<\/pre>)/gm, function(wholeMatch, m1) {
          var pre = m1;
          pre = pre.replace(/^  /mg, "\xA80");
          pre = pre.replace(/¨0/g, "");
          return pre;
        });
        return showdown2.subParser("hashBlock")("<blockquote>\n" + bq + "\n</blockquote>", options, globals);
      });
      text = globals.converter._dispatch("blockQuotes.after", text, options, globals);
      return text;
    });
    showdown2.subParser("codeBlocks", function(text, options, globals) {
      text = globals.converter._dispatch("codeBlocks.before", text, options, globals);
      text += "\xA80";
      var pattern = /(?:\n\n|^)((?:(?:[ ]{4}|\t).*\n+)+)(\n*[ ]{0,3}[^ \t\n]|(?=¨0))/g;
      text = text.replace(pattern, function(wholeMatch, m1, m2) {
        var codeblock = m1, nextChar = m2, end = "\n";
        codeblock = showdown2.subParser("outdent")(codeblock, options, globals);
        codeblock = showdown2.subParser("encodeCode")(codeblock, options, globals);
        codeblock = showdown2.subParser("detab")(codeblock, options, globals);
        codeblock = codeblock.replace(/^\n+/g, "");
        codeblock = codeblock.replace(/\n+$/g, "");
        if (options.omitExtraWLInCodeBlocks) {
          end = "";
        }
        codeblock = "<pre><code>" + codeblock + end + "</code></pre>";
        return showdown2.subParser("hashBlock")(codeblock, options, globals) + nextChar;
      });
      text = text.replace(/¨0/, "");
      text = globals.converter._dispatch("codeBlocks.after", text, options, globals);
      return text;
    });
    showdown2.subParser("codeSpans", function(text, options, globals) {
      text = globals.converter._dispatch("codeSpans.before", text, options, globals);
      if (typeof text === "undefined") {
        text = "";
      }
      text = text.replace(/(^|[^\\])(`+)([^\r]*?[^`])\2(?!`)/gm, function(wholeMatch, m1, m2, m3) {
        var c = m3;
        c = c.replace(/^([ \t]*)/g, "");
        c = c.replace(/[ \t]*$/g, "");
        c = showdown2.subParser("encodeCode")(c, options, globals);
        c = m1 + "<code>" + c + "</code>";
        c = showdown2.subParser("hashHTMLSpans")(c, options, globals);
        return c;
      });
      text = globals.converter._dispatch("codeSpans.after", text, options, globals);
      return text;
    });
    showdown2.subParser("completeHTMLDocument", function(text, options, globals) {
      if (!options.completeHTMLDocument) {
        return text;
      }
      text = globals.converter._dispatch("completeHTMLDocument.before", text, options, globals);
      var doctype = "html", doctypeParsed = "<!DOCTYPE HTML>\n", title = "", charset = '<meta charset="utf-8">\n', lang = "", metadata = "";
      if (typeof globals.metadata.parsed.doctype !== "undefined") {
        doctypeParsed = "<!DOCTYPE " + globals.metadata.parsed.doctype + ">\n";
        doctype = globals.metadata.parsed.doctype.toString().toLowerCase();
        if (doctype === "html" || doctype === "html5") {
          charset = '<meta charset="utf-8">';
        }
      }
      for (var meta in globals.metadata.parsed) {
        if (globals.metadata.parsed.hasOwnProperty(meta)) {
          switch (meta.toLowerCase()) {
            case "doctype":
              break;
            case "title":
              title = "<title>" + globals.metadata.parsed.title + "</title>\n";
              break;
            case "charset":
              if (doctype === "html" || doctype === "html5") {
                charset = '<meta charset="' + globals.metadata.parsed.charset + '">\n';
              } else {
                charset = '<meta name="charset" content="' + globals.metadata.parsed.charset + '">\n';
              }
              break;
            case "language":
            case "lang":
              lang = ' lang="' + globals.metadata.parsed[meta] + '"';
              metadata += '<meta name="' + meta + '" content="' + globals.metadata.parsed[meta] + '">\n';
              break;
            default:
              metadata += '<meta name="' + meta + '" content="' + globals.metadata.parsed[meta] + '">\n';
          }
        }
      }
      text = doctypeParsed + "<html" + lang + ">\n<head>\n" + title + charset + metadata + "</head>\n<body>\n" + text.trim() + "\n</body>\n</html>";
      text = globals.converter._dispatch("completeHTMLDocument.after", text, options, globals);
      return text;
    });
    showdown2.subParser("detab", function(text, options, globals) {
      text = globals.converter._dispatch("detab.before", text, options, globals);
      text = text.replace(/\t(?=\t)/g, "    ");
      text = text.replace(/\t/g, "\xA8A\xA8B");
      text = text.replace(/¨B(.+?)¨A/g, function(wholeMatch, m1) {
        var leadingText = m1, numSpaces = 4 - leadingText.length % 4;
        for (var i = 0; i < numSpaces; i++) {
          leadingText += " ";
        }
        return leadingText;
      });
      text = text.replace(/¨A/g, "    ");
      text = text.replace(/¨B/g, "");
      text = globals.converter._dispatch("detab.after", text, options, globals);
      return text;
    });
    showdown2.subParser("ellipsis", function(text, options, globals) {
      if (!options.ellipsis) {
        return text;
      }
      text = globals.converter._dispatch("ellipsis.before", text, options, globals);
      text = text.replace(/\.\.\./g, "\u2026");
      text = globals.converter._dispatch("ellipsis.after", text, options, globals);
      return text;
    });
    showdown2.subParser("emoji", function(text, options, globals) {
      if (!options.emoji) {
        return text;
      }
      text = globals.converter._dispatch("emoji.before", text, options, globals);
      var emojiRgx = /:([\S]+?):/g;
      text = text.replace(emojiRgx, function(wm, emojiCode) {
        if (showdown2.helper.emojis.hasOwnProperty(emojiCode)) {
          return showdown2.helper.emojis[emojiCode];
        }
        return wm;
      });
      text = globals.converter._dispatch("emoji.after", text, options, globals);
      return text;
    });
    showdown2.subParser("encodeAmpsAndAngles", function(text, options, globals) {
      text = globals.converter._dispatch("encodeAmpsAndAngles.before", text, options, globals);
      text = text.replace(/&(?!#?[xX]?(?:[0-9a-fA-F]+|\w+);)/g, "&amp;");
      text = text.replace(/<(?![a-z\/?$!])/gi, "&lt;");
      text = text.replace(/</g, "&lt;");
      text = text.replace(/>/g, "&gt;");
      text = globals.converter._dispatch("encodeAmpsAndAngles.after", text, options, globals);
      return text;
    });
    showdown2.subParser("encodeBackslashEscapes", function(text, options, globals) {
      text = globals.converter._dispatch("encodeBackslashEscapes.before", text, options, globals);
      text = text.replace(/\\(\\)/g, showdown2.helper.escapeCharactersCallback);
      text = text.replace(/\\([`*_{}\[\]()>#+.!~=|:-])/g, showdown2.helper.escapeCharactersCallback);
      text = globals.converter._dispatch("encodeBackslashEscapes.after", text, options, globals);
      return text;
    });
    showdown2.subParser("encodeCode", function(text, options, globals) {
      text = globals.converter._dispatch("encodeCode.before", text, options, globals);
      text = text.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/([*_{}\[\]\\=~-])/g, showdown2.helper.escapeCharactersCallback);
      text = globals.converter._dispatch("encodeCode.after", text, options, globals);
      return text;
    });
    showdown2.subParser("escapeSpecialCharsWithinTagAttributes", function(text, options, globals) {
      text = globals.converter._dispatch("escapeSpecialCharsWithinTagAttributes.before", text, options, globals);
      var tags = /<\/?[a-z\d_:-]+(?:[\s]+[\s\S]+?)?>/gi, comments = /<!(--(?:(?:[^>-]|-[^>])(?:[^-]|-[^-])*)--)>/gi;
      text = text.replace(tags, function(wholeMatch) {
        return wholeMatch.replace(/(.)<\/?code>(?=.)/g, "$1`").replace(/([\\`*_~=|])/g, showdown2.helper.escapeCharactersCallback);
      });
      text = text.replace(comments, function(wholeMatch) {
        return wholeMatch.replace(/([\\`*_~=|])/g, showdown2.helper.escapeCharactersCallback);
      });
      text = globals.converter._dispatch("escapeSpecialCharsWithinTagAttributes.after", text, options, globals);
      return text;
    });
    showdown2.subParser("githubCodeBlocks", function(text, options, globals) {
      if (!options.ghCodeBlocks) {
        return text;
      }
      text = globals.converter._dispatch("githubCodeBlocks.before", text, options, globals);
      text += "\xA80";
      text = text.replace(/(?:^|\n)(?: {0,3})(```+|~~~+)(?: *)([^\s`~]*)\n([\s\S]*?)\n(?: {0,3})\1/g, function(wholeMatch, delim, language, codeblock) {
        var end = options.omitExtraWLInCodeBlocks ? "" : "\n";
        codeblock = showdown2.subParser("encodeCode")(codeblock, options, globals);
        codeblock = showdown2.subParser("detab")(codeblock, options, globals);
        codeblock = codeblock.replace(/^\n+/g, "");
        codeblock = codeblock.replace(/\n+$/g, "");
        codeblock = "<pre><code" + (language ? ' class="' + language + " language-" + language + '"' : "") + ">" + codeblock + end + "</code></pre>";
        codeblock = showdown2.subParser("hashBlock")(codeblock, options, globals);
        return "\n\n\xA8G" + (globals.ghCodeBlocks.push({text: wholeMatch, codeblock}) - 1) + "G\n\n";
      });
      text = text.replace(/¨0/, "");
      return globals.converter._dispatch("githubCodeBlocks.after", text, options, globals);
    });
    showdown2.subParser("hashBlock", function(text, options, globals) {
      text = globals.converter._dispatch("hashBlock.before", text, options, globals);
      text = text.replace(/(^\n+|\n+$)/g, "");
      text = "\n\n\xA8K" + (globals.gHtmlBlocks.push(text) - 1) + "K\n\n";
      text = globals.converter._dispatch("hashBlock.after", text, options, globals);
      return text;
    });
    showdown2.subParser("hashCodeTags", function(text, options, globals) {
      text = globals.converter._dispatch("hashCodeTags.before", text, options, globals);
      var repFunc = function(wholeMatch, match, left, right) {
        var codeblock = left + showdown2.subParser("encodeCode")(match, options, globals) + right;
        return "\xA8C" + (globals.gHtmlSpans.push(codeblock) - 1) + "C";
      };
      text = showdown2.helper.replaceRecursiveRegExp(text, repFunc, "<code\\b[^>]*>", "</code>", "gim");
      text = globals.converter._dispatch("hashCodeTags.after", text, options, globals);
      return text;
    });
    showdown2.subParser("hashElement", function(text, options, globals) {
      return function(wholeMatch, m1) {
        var blockText = m1;
        blockText = blockText.replace(/\n\n/g, "\n");
        blockText = blockText.replace(/^\n/, "");
        blockText = blockText.replace(/\n+$/g, "");
        blockText = "\n\n\xA8K" + (globals.gHtmlBlocks.push(blockText) - 1) + "K\n\n";
        return blockText;
      };
    });
    showdown2.subParser("hashHTMLBlocks", function(text, options, globals) {
      text = globals.converter._dispatch("hashHTMLBlocks.before", text, options, globals);
      var blockTags = [
        "pre",
        "div",
        "h1",
        "h2",
        "h3",
        "h4",
        "h5",
        "h6",
        "blockquote",
        "table",
        "dl",
        "ol",
        "ul",
        "script",
        "noscript",
        "form",
        "fieldset",
        "iframe",
        "math",
        "style",
        "section",
        "header",
        "footer",
        "nav",
        "article",
        "aside",
        "address",
        "audio",
        "canvas",
        "figure",
        "hgroup",
        "output",
        "video",
        "p"
      ], repFunc = function(wholeMatch, match, left, right) {
        var txt = wholeMatch;
        if (left.search(/\bmarkdown\b/) !== -1) {
          txt = left + globals.converter.makeHtml(match) + right;
        }
        return "\n\n\xA8K" + (globals.gHtmlBlocks.push(txt) - 1) + "K\n\n";
      };
      if (options.backslashEscapesHTMLTags) {
        text = text.replace(/\\<(\/?[^>]+?)>/g, function(wm, inside) {
          return "&lt;" + inside + "&gt;";
        });
      }
      for (var i = 0; i < blockTags.length; ++i) {
        var opTagPos, rgx1 = new RegExp("^ {0,3}(<" + blockTags[i] + "\\b[^>]*>)", "im"), patLeft = "<" + blockTags[i] + "\\b[^>]*>", patRight = "</" + blockTags[i] + ">";
        while ((opTagPos = showdown2.helper.regexIndexOf(text, rgx1)) !== -1) {
          var subTexts = showdown2.helper.splitAtIndex(text, opTagPos), newSubText1 = showdown2.helper.replaceRecursiveRegExp(subTexts[1], repFunc, patLeft, patRight, "im");
          if (newSubText1 === subTexts[1]) {
            break;
          }
          text = subTexts[0].concat(newSubText1);
        }
      }
      text = text.replace(/(\n {0,3}(<(hr)\b([^<>])*?\/?>)[ \t]*(?=\n{2,}))/g, showdown2.subParser("hashElement")(text, options, globals));
      text = showdown2.helper.replaceRecursiveRegExp(text, function(txt) {
        return "\n\n\xA8K" + (globals.gHtmlBlocks.push(txt) - 1) + "K\n\n";
      }, "^ {0,3}<!--", "-->", "gm");
      text = text.replace(/(?:\n\n)( {0,3}(?:<([?%])[^\r]*?\2>)[ \t]*(?=\n{2,}))/g, showdown2.subParser("hashElement")(text, options, globals));
      text = globals.converter._dispatch("hashHTMLBlocks.after", text, options, globals);
      return text;
    });
    showdown2.subParser("hashHTMLSpans", function(text, options, globals) {
      text = globals.converter._dispatch("hashHTMLSpans.before", text, options, globals);
      function hashHTMLSpan(html) {
        return "\xA8C" + (globals.gHtmlSpans.push(html) - 1) + "C";
      }
      text = text.replace(/<[^>]+?\/>/gi, function(wm) {
        return hashHTMLSpan(wm);
      });
      text = text.replace(/<([^>]+?)>[\s\S]*?<\/\1>/g, function(wm) {
        return hashHTMLSpan(wm);
      });
      text = text.replace(/<([^>]+?)\s[^>]+?>[\s\S]*?<\/\1>/g, function(wm) {
        return hashHTMLSpan(wm);
      });
      text = text.replace(/<[^>]+?>/gi, function(wm) {
        return hashHTMLSpan(wm);
      });
      text = globals.converter._dispatch("hashHTMLSpans.after", text, options, globals);
      return text;
    });
    showdown2.subParser("unhashHTMLSpans", function(text, options, globals) {
      text = globals.converter._dispatch("unhashHTMLSpans.before", text, options, globals);
      for (var i = 0; i < globals.gHtmlSpans.length; ++i) {
        var repText = globals.gHtmlSpans[i], limit = 0;
        while (/¨C(\d+)C/.test(repText)) {
          var num = RegExp.$1;
          repText = repText.replace("\xA8C" + num + "C", globals.gHtmlSpans[num]);
          if (limit === 10) {
            console.error("maximum nesting of 10 spans reached!!!");
            break;
          }
          ++limit;
        }
        text = text.replace("\xA8C" + i + "C", repText);
      }
      text = globals.converter._dispatch("unhashHTMLSpans.after", text, options, globals);
      return text;
    });
    showdown2.subParser("hashPreCodeTags", function(text, options, globals) {
      text = globals.converter._dispatch("hashPreCodeTags.before", text, options, globals);
      var repFunc = function(wholeMatch, match, left, right) {
        var codeblock = left + showdown2.subParser("encodeCode")(match, options, globals) + right;
        return "\n\n\xA8G" + (globals.ghCodeBlocks.push({text: wholeMatch, codeblock}) - 1) + "G\n\n";
      };
      text = showdown2.helper.replaceRecursiveRegExp(text, repFunc, "^ {0,3}<pre\\b[^>]*>\\s*<code\\b[^>]*>", "^ {0,3}</code>\\s*</pre>", "gim");
      text = globals.converter._dispatch("hashPreCodeTags.after", text, options, globals);
      return text;
    });
    showdown2.subParser("headers", function(text, options, globals) {
      text = globals.converter._dispatch("headers.before", text, options, globals);
      var headerLevelStart = isNaN(parseInt(options.headerLevelStart)) ? 1 : parseInt(options.headerLevelStart), setextRegexH1 = options.smoothLivePreview ? /^(.+)[ \t]*\n={2,}[ \t]*\n+/gm : /^(.+)[ \t]*\n=+[ \t]*\n+/gm, setextRegexH2 = options.smoothLivePreview ? /^(.+)[ \t]*\n-{2,}[ \t]*\n+/gm : /^(.+)[ \t]*\n-+[ \t]*\n+/gm;
      text = text.replace(setextRegexH1, function(wholeMatch, m1) {
        var spanGamut = showdown2.subParser("spanGamut")(m1, options, globals), hID = options.noHeaderId ? "" : ' id="' + headerId(m1) + '"', hLevel = headerLevelStart, hashBlock = "<h" + hLevel + hID + ">" + spanGamut + "</h" + hLevel + ">";
        return showdown2.subParser("hashBlock")(hashBlock, options, globals);
      });
      text = text.replace(setextRegexH2, function(matchFound, m1) {
        var spanGamut = showdown2.subParser("spanGamut")(m1, options, globals), hID = options.noHeaderId ? "" : ' id="' + headerId(m1) + '"', hLevel = headerLevelStart + 1, hashBlock = "<h" + hLevel + hID + ">" + spanGamut + "</h" + hLevel + ">";
        return showdown2.subParser("hashBlock")(hashBlock, options, globals);
      });
      var atxStyle = options.requireSpaceBeforeHeadingText ? /^(#{1,6})[ \t]+(.+?)[ \t]*#*\n+/gm : /^(#{1,6})[ \t]*(.+?)[ \t]*#*\n+/gm;
      text = text.replace(atxStyle, function(wholeMatch, m1, m2) {
        var hText = m2;
        if (options.customizedHeaderId) {
          hText = m2.replace(/\s?\{([^{]+?)}\s*$/, "");
        }
        var span = showdown2.subParser("spanGamut")(hText, options, globals), hID = options.noHeaderId ? "" : ' id="' + headerId(m2) + '"', hLevel = headerLevelStart - 1 + m1.length, header = "<h" + hLevel + hID + ">" + span + "</h" + hLevel + ">";
        return showdown2.subParser("hashBlock")(header, options, globals);
      });
      function headerId(m) {
        var title, prefix;
        if (options.customizedHeaderId) {
          var match = m.match(/\{([^{]+?)}\s*$/);
          if (match && match[1]) {
            m = match[1];
          }
        }
        title = m;
        if (showdown2.helper.isString(options.prefixHeaderId)) {
          prefix = options.prefixHeaderId;
        } else if (options.prefixHeaderId === true) {
          prefix = "section-";
        } else {
          prefix = "";
        }
        if (!options.rawPrefixHeaderId) {
          title = prefix + title;
        }
        if (options.ghCompatibleHeaderId) {
          title = title.replace(/ /g, "-").replace(/&amp;/g, "").replace(/¨T/g, "").replace(/¨D/g, "").replace(/[&+$,\/:;=?@"#{}|^¨~\[\]`\\*)(%.!'<>]/g, "").toLowerCase();
        } else if (options.rawHeaderId) {
          title = title.replace(/ /g, "-").replace(/&amp;/g, "&").replace(/¨T/g, "\xA8").replace(/¨D/g, "$").replace(/["']/g, "-").toLowerCase();
        } else {
          title = title.replace(/[^\w]/g, "").toLowerCase();
        }
        if (options.rawPrefixHeaderId) {
          title = prefix + title;
        }
        if (globals.hashLinkCounts[title]) {
          title = title + "-" + globals.hashLinkCounts[title]++;
        } else {
          globals.hashLinkCounts[title] = 1;
        }
        return title;
      }
      text = globals.converter._dispatch("headers.after", text, options, globals);
      return text;
    });
    showdown2.subParser("horizontalRule", function(text, options, globals) {
      text = globals.converter._dispatch("horizontalRule.before", text, options, globals);
      var key = showdown2.subParser("hashBlock")("<hr />", options, globals);
      text = text.replace(/^ {0,2}( ?-){3,}[ \t]*$/gm, key);
      text = text.replace(/^ {0,2}( ?\*){3,}[ \t]*$/gm, key);
      text = text.replace(/^ {0,2}( ?_){3,}[ \t]*$/gm, key);
      text = globals.converter._dispatch("horizontalRule.after", text, options, globals);
      return text;
    });
    showdown2.subParser("images", function(text, options, globals) {
      text = globals.converter._dispatch("images.before", text, options, globals);
      var inlineRegExp = /!\[([^\]]*?)][ \t]*()\([ \t]?<?([\S]+?(?:\([\S]*?\)[\S]*?)?)>?(?: =([*\d]+[A-Za-z%]{0,4})x([*\d]+[A-Za-z%]{0,4}))?[ \t]*(?:(["'])([^"]*?)\6)?[ \t]?\)/g, crazyRegExp = /!\[([^\]]*?)][ \t]*()\([ \t]?<([^>]*)>(?: =([*\d]+[A-Za-z%]{0,4})x([*\d]+[A-Za-z%]{0,4}))?[ \t]*(?:(?:(["'])([^"]*?)\6))?[ \t]?\)/g, base64RegExp = /!\[([^\]]*?)][ \t]*()\([ \t]?<?(data:.+?\/.+?;base64,[A-Za-z0-9+/=\n]+?)>?(?: =([*\d]+[A-Za-z%]{0,4})x([*\d]+[A-Za-z%]{0,4}))?[ \t]*(?:(["'])([^"]*?)\6)?[ \t]?\)/g, referenceRegExp = /!\[([^\]]*?)] ?(?:\n *)?\[([\s\S]*?)]()()()()()/g, refShortcutRegExp = /!\[([^\[\]]+)]()()()()()/g;
      function writeImageTagBase64(wholeMatch, altText, linkId, url, width, height, m5, title) {
        url = url.replace(/\s/g, "");
        return writeImageTag(wholeMatch, altText, linkId, url, width, height, m5, title);
      }
      function writeImageTag(wholeMatch, altText, linkId, url, width, height, m5, title) {
        var gUrls = globals.gUrls, gTitles = globals.gTitles, gDims = globals.gDimensions;
        linkId = linkId.toLowerCase();
        if (!title) {
          title = "";
        }
        if (wholeMatch.search(/\(<?\s*>? ?(['"].*['"])?\)$/m) > -1) {
          url = "";
        } else if (url === "" || url === null) {
          if (linkId === "" || linkId === null) {
            linkId = altText.toLowerCase().replace(/ ?\n/g, " ");
          }
          url = "#" + linkId;
          if (!showdown2.helper.isUndefined(gUrls[linkId])) {
            url = gUrls[linkId];
            if (!showdown2.helper.isUndefined(gTitles[linkId])) {
              title = gTitles[linkId];
            }
            if (!showdown2.helper.isUndefined(gDims[linkId])) {
              width = gDims[linkId].width;
              height = gDims[linkId].height;
            }
          } else {
            return wholeMatch;
          }
        }
        altText = altText.replace(/"/g, "&quot;").replace(showdown2.helper.regexes.asteriskDashAndColon, showdown2.helper.escapeCharactersCallback);
        url = url.replace(showdown2.helper.regexes.asteriskDashAndColon, showdown2.helper.escapeCharactersCallback);
        var result = '<img src="' + url + '" alt="' + altText + '"';
        if (title && showdown2.helper.isString(title)) {
          title = title.replace(/"/g, "&quot;").replace(showdown2.helper.regexes.asteriskDashAndColon, showdown2.helper.escapeCharactersCallback);
          result += ' title="' + title + '"';
        }
        if (width && height) {
          width = width === "*" ? "auto" : width;
          height = height === "*" ? "auto" : height;
          result += ' width="' + width + '"';
          result += ' height="' + height + '"';
        }
        result += " />";
        return result;
      }
      text = text.replace(referenceRegExp, writeImageTag);
      text = text.replace(base64RegExp, writeImageTagBase64);
      text = text.replace(crazyRegExp, writeImageTag);
      text = text.replace(inlineRegExp, writeImageTag);
      text = text.replace(refShortcutRegExp, writeImageTag);
      text = globals.converter._dispatch("images.after", text, options, globals);
      return text;
    });
    showdown2.subParser("italicsAndBold", function(text, options, globals) {
      text = globals.converter._dispatch("italicsAndBold.before", text, options, globals);
      function parseInside(txt, left, right) {
        return left + txt + right;
      }
      if (options.literalMidWordUnderscores) {
        text = text.replace(/\b___(\S[\s\S]*?)___\b/g, function(wm, txt) {
          return parseInside(txt, "<strong><em>", "</em></strong>");
        });
        text = text.replace(/\b__(\S[\s\S]*?)__\b/g, function(wm, txt) {
          return parseInside(txt, "<strong>", "</strong>");
        });
        text = text.replace(/\b_(\S[\s\S]*?)_\b/g, function(wm, txt) {
          return parseInside(txt, "<em>", "</em>");
        });
      } else {
        text = text.replace(/___(\S[\s\S]*?)___/g, function(wm, m) {
          return /\S$/.test(m) ? parseInside(m, "<strong><em>", "</em></strong>") : wm;
        });
        text = text.replace(/__(\S[\s\S]*?)__/g, function(wm, m) {
          return /\S$/.test(m) ? parseInside(m, "<strong>", "</strong>") : wm;
        });
        text = text.replace(/_([^\s_][\s\S]*?)_/g, function(wm, m) {
          return /\S$/.test(m) ? parseInside(m, "<em>", "</em>") : wm;
        });
      }
      if (options.literalMidWordAsterisks) {
        text = text.replace(/([^*]|^)\B\*\*\*(\S[\s\S]*?)\*\*\*\B(?!\*)/g, function(wm, lead, txt) {
          return parseInside(txt, lead + "<strong><em>", "</em></strong>");
        });
        text = text.replace(/([^*]|^)\B\*\*(\S[\s\S]*?)\*\*\B(?!\*)/g, function(wm, lead, txt) {
          return parseInside(txt, lead + "<strong>", "</strong>");
        });
        text = text.replace(/([^*]|^)\B\*(\S[\s\S]*?)\*\B(?!\*)/g, function(wm, lead, txt) {
          return parseInside(txt, lead + "<em>", "</em>");
        });
      } else {
        text = text.replace(/\*\*\*(\S[\s\S]*?)\*\*\*/g, function(wm, m) {
          return /\S$/.test(m) ? parseInside(m, "<strong><em>", "</em></strong>") : wm;
        });
        text = text.replace(/\*\*(\S[\s\S]*?)\*\*/g, function(wm, m) {
          return /\S$/.test(m) ? parseInside(m, "<strong>", "</strong>") : wm;
        });
        text = text.replace(/\*([^\s*][\s\S]*?)\*/g, function(wm, m) {
          return /\S$/.test(m) ? parseInside(m, "<em>", "</em>") : wm;
        });
      }
      text = globals.converter._dispatch("italicsAndBold.after", text, options, globals);
      return text;
    });
    showdown2.subParser("lists", function(text, options, globals) {
      function processListItems(listStr, trimTrailing) {
        globals.gListLevel++;
        listStr = listStr.replace(/\n{2,}$/, "\n");
        listStr += "\xA80";
        var rgx = /(\n)?(^ {0,3})([*+-]|\d+[.])[ \t]+((\[(x|X| )?])?[ \t]*[^\r]+?(\n{1,2}))(?=\n*(¨0| {0,3}([*+-]|\d+[.])[ \t]+))/gm, isParagraphed = /\n[ \t]*\n(?!¨0)/.test(listStr);
        if (options.disableForced4SpacesIndentedSublists) {
          rgx = /(\n)?(^ {0,3})([*+-]|\d+[.])[ \t]+((\[(x|X| )?])?[ \t]*[^\r]+?(\n{1,2}))(?=\n*(¨0|\2([*+-]|\d+[.])[ \t]+))/gm;
        }
        listStr = listStr.replace(rgx, function(wholeMatch, m1, m2, m3, m4, taskbtn, checked) {
          checked = checked && checked.trim() !== "";
          var item = showdown2.subParser("outdent")(m4, options, globals), bulletStyle = "";
          if (taskbtn && options.tasklists) {
            bulletStyle = ' class="task-list-item" style="list-style-type: none;"';
            item = item.replace(/^[ \t]*\[(x|X| )?]/m, function() {
              var otp = '<input type="checkbox" disabled style="margin: 0px 0.35em 0.25em -1.6em; vertical-align: middle;"';
              if (checked) {
                otp += " checked";
              }
              otp += ">";
              return otp;
            });
          }
          item = item.replace(/^([-*+]|\d\.)[ \t]+[\S\n ]*/g, function(wm2) {
            return "\xA8A" + wm2;
          });
          if (m1 || item.search(/\n{2,}/) > -1) {
            item = showdown2.subParser("githubCodeBlocks")(item, options, globals);
            item = showdown2.subParser("blockGamut")(item, options, globals);
          } else {
            item = showdown2.subParser("lists")(item, options, globals);
            item = item.replace(/\n$/, "");
            item = showdown2.subParser("hashHTMLBlocks")(item, options, globals);
            item = item.replace(/\n\n+/g, "\n\n");
            if (isParagraphed) {
              item = showdown2.subParser("paragraphs")(item, options, globals);
            } else {
              item = showdown2.subParser("spanGamut")(item, options, globals);
            }
          }
          item = item.replace("\xA8A", "");
          item = "<li" + bulletStyle + ">" + item + "</li>\n";
          return item;
        });
        listStr = listStr.replace(/¨0/g, "");
        globals.gListLevel--;
        if (trimTrailing) {
          listStr = listStr.replace(/\s+$/, "");
        }
        return listStr;
      }
      function styleStartNumber(list, listType) {
        if (listType === "ol") {
          var res = list.match(/^ *(\d+)\./);
          if (res && res[1] !== "1") {
            return ' start="' + res[1] + '"';
          }
        }
        return "";
      }
      function parseConsecutiveLists(list, listType, trimTrailing) {
        var olRgx = options.disableForced4SpacesIndentedSublists ? /^ ?\d+\.[ \t]/gm : /^ {0,3}\d+\.[ \t]/gm, ulRgx = options.disableForced4SpacesIndentedSublists ? /^ ?[*+-][ \t]/gm : /^ {0,3}[*+-][ \t]/gm, counterRxg = listType === "ul" ? olRgx : ulRgx, result = "";
        if (list.search(counterRxg) !== -1) {
          (function parseCL(txt) {
            var pos = txt.search(counterRxg), style2 = styleStartNumber(list, listType);
            if (pos !== -1) {
              result += "\n\n<" + listType + style2 + ">\n" + processListItems(txt.slice(0, pos), !!trimTrailing) + "</" + listType + ">\n";
              listType = listType === "ul" ? "ol" : "ul";
              counterRxg = listType === "ul" ? olRgx : ulRgx;
              parseCL(txt.slice(pos));
            } else {
              result += "\n\n<" + listType + style2 + ">\n" + processListItems(txt, !!trimTrailing) + "</" + listType + ">\n";
            }
          })(list);
        } else {
          var style = styleStartNumber(list, listType);
          result = "\n\n<" + listType + style + ">\n" + processListItems(list, !!trimTrailing) + "</" + listType + ">\n";
        }
        return result;
      }
      text = globals.converter._dispatch("lists.before", text, options, globals);
      text += "\xA80";
      if (globals.gListLevel) {
        text = text.replace(/^(( {0,3}([*+-]|\d+[.])[ \t]+)[^\r]+?(¨0|\n{2,}(?=\S)(?![ \t]*(?:[*+-]|\d+[.])[ \t]+)))/gm, function(wholeMatch, list, m2) {
          var listType = m2.search(/[*+-]/g) > -1 ? "ul" : "ol";
          return parseConsecutiveLists(list, listType, true);
        });
      } else {
        text = text.replace(/(\n\n|^\n?)(( {0,3}([*+-]|\d+[.])[ \t]+)[^\r]+?(¨0|\n{2,}(?=\S)(?![ \t]*(?:[*+-]|\d+[.])[ \t]+)))/gm, function(wholeMatch, m1, list, m3) {
          var listType = m3.search(/[*+-]/g) > -1 ? "ul" : "ol";
          return parseConsecutiveLists(list, listType, false);
        });
      }
      text = text.replace(/¨0/, "");
      text = globals.converter._dispatch("lists.after", text, options, globals);
      return text;
    });
    showdown2.subParser("metadata", function(text, options, globals) {
      if (!options.metadata) {
        return text;
      }
      text = globals.converter._dispatch("metadata.before", text, options, globals);
      function parseMetadataContents(content) {
        globals.metadata.raw = content;
        content = content.replace(/&/g, "&amp;").replace(/"/g, "&quot;");
        content = content.replace(/\n {4}/g, " ");
        content.replace(/^([\S ]+): +([\s\S]+?)$/gm, function(wm, key, value) {
          globals.metadata.parsed[key] = value;
          return "";
        });
      }
      text = text.replace(/^\s*«««+(\S*?)\n([\s\S]+?)\n»»»+\n/, function(wholematch, format, content) {
        parseMetadataContents(content);
        return "\xA8M";
      });
      text = text.replace(/^\s*---+(\S*?)\n([\s\S]+?)\n---+\n/, function(wholematch, format, content) {
        if (format) {
          globals.metadata.format = format;
        }
        parseMetadataContents(content);
        return "\xA8M";
      });
      text = text.replace(/¨M/g, "");
      text = globals.converter._dispatch("metadata.after", text, options, globals);
      return text;
    });
    showdown2.subParser("outdent", function(text, options, globals) {
      text = globals.converter._dispatch("outdent.before", text, options, globals);
      text = text.replace(/^(\t|[ ]{1,4})/gm, "\xA80");
      text = text.replace(/¨0/g, "");
      text = globals.converter._dispatch("outdent.after", text, options, globals);
      return text;
    });
    showdown2.subParser("paragraphs", function(text, options, globals) {
      text = globals.converter._dispatch("paragraphs.before", text, options, globals);
      text = text.replace(/^\n+/g, "");
      text = text.replace(/\n+$/g, "");
      var grafs = text.split(/\n{2,}/g), grafsOut = [], end = grafs.length;
      for (var i = 0; i < end; i++) {
        var str = grafs[i];
        if (str.search(/¨(K|G)(\d+)\1/g) >= 0) {
          grafsOut.push(str);
        } else if (str.search(/\S/) >= 0) {
          str = showdown2.subParser("spanGamut")(str, options, globals);
          str = str.replace(/^([ \t]*)/g, "<p>");
          str += "</p>";
          grafsOut.push(str);
        }
      }
      end = grafsOut.length;
      for (i = 0; i < end; i++) {
        var blockText = "", grafsOutIt = grafsOut[i], codeFlag = false;
        while (/¨(K|G)(\d+)\1/.test(grafsOutIt)) {
          var delim = RegExp.$1, num = RegExp.$2;
          if (delim === "K") {
            blockText = globals.gHtmlBlocks[num];
          } else {
            if (codeFlag) {
              blockText = showdown2.subParser("encodeCode")(globals.ghCodeBlocks[num].text, options, globals);
            } else {
              blockText = globals.ghCodeBlocks[num].codeblock;
            }
          }
          blockText = blockText.replace(/\$/g, "$$$$");
          grafsOutIt = grafsOutIt.replace(/(\n\n)?¨(K|G)\d+\2(\n\n)?/, blockText);
          if (/^<pre\b[^>]*>\s*<code\b[^>]*>/.test(grafsOutIt)) {
            codeFlag = true;
          }
        }
        grafsOut[i] = grafsOutIt;
      }
      text = grafsOut.join("\n");
      text = text.replace(/^\n+/g, "");
      text = text.replace(/\n+$/g, "");
      return globals.converter._dispatch("paragraphs.after", text, options, globals);
    });
    showdown2.subParser("runExtension", function(ext, text, options, globals) {
      if (ext.filter) {
        text = ext.filter(text, globals.converter, options);
      } else if (ext.regex) {
        var re = ext.regex;
        if (!(re instanceof RegExp)) {
          re = new RegExp(re, "g");
        }
        text = text.replace(re, ext.replace);
      }
      return text;
    });
    showdown2.subParser("spanGamut", function(text, options, globals) {
      text = globals.converter._dispatch("spanGamut.before", text, options, globals);
      text = showdown2.subParser("codeSpans")(text, options, globals);
      text = showdown2.subParser("escapeSpecialCharsWithinTagAttributes")(text, options, globals);
      text = showdown2.subParser("encodeBackslashEscapes")(text, options, globals);
      text = showdown2.subParser("images")(text, options, globals);
      text = showdown2.subParser("anchors")(text, options, globals);
      text = showdown2.subParser("autoLinks")(text, options, globals);
      text = showdown2.subParser("simplifiedAutoLinks")(text, options, globals);
      text = showdown2.subParser("emoji")(text, options, globals);
      text = showdown2.subParser("underline")(text, options, globals);
      text = showdown2.subParser("italicsAndBold")(text, options, globals);
      text = showdown2.subParser("strikethrough")(text, options, globals);
      text = showdown2.subParser("ellipsis")(text, options, globals);
      text = showdown2.subParser("hashHTMLSpans")(text, options, globals);
      text = showdown2.subParser("encodeAmpsAndAngles")(text, options, globals);
      if (options.simpleLineBreaks) {
        if (!/\n\n¨K/.test(text)) {
          text = text.replace(/\n+/g, "<br />\n");
        }
      } else {
        text = text.replace(/  +\n/g, "<br />\n");
      }
      text = globals.converter._dispatch("spanGamut.after", text, options, globals);
      return text;
    });
    showdown2.subParser("strikethrough", function(text, options, globals) {
      function parseInside(txt) {
        if (options.simplifiedAutoLink) {
          txt = showdown2.subParser("simplifiedAutoLinks")(txt, options, globals);
        }
        return "<del>" + txt + "</del>";
      }
      if (options.strikethrough) {
        text = globals.converter._dispatch("strikethrough.before", text, options, globals);
        text = text.replace(/(?:~){2}([\s\S]+?)(?:~){2}/g, function(wm, txt) {
          return parseInside(txt);
        });
        text = globals.converter._dispatch("strikethrough.after", text, options, globals);
      }
      return text;
    });
    showdown2.subParser("stripLinkDefinitions", function(text, options, globals) {
      var regex = /^ {0,3}\[([^\]]+)]:[ \t]*\n?[ \t]*<?([^>\s]+)>?(?: =([*\d]+[A-Za-z%]{0,4})x([*\d]+[A-Za-z%]{0,4}))?[ \t]*\n?[ \t]*(?:(\n*)["|'(](.+?)["|')][ \t]*)?(?:\n+|(?=¨0))/gm, base64Regex = /^ {0,3}\[([^\]]+)]:[ \t]*\n?[ \t]*<?(data:.+?\/.+?;base64,[A-Za-z0-9+/=\n]+?)>?(?: =([*\d]+[A-Za-z%]{0,4})x([*\d]+[A-Za-z%]{0,4}))?[ \t]*\n?[ \t]*(?:(\n*)["|'(](.+?)["|')][ \t]*)?(?:\n\n|(?=¨0)|(?=\n\[))/gm;
      text += "\xA80";
      var replaceFunc = function(wholeMatch, linkId, url, width, height, blankLines, title) {
        linkId = linkId.toLowerCase();
        if (text.toLowerCase().split(linkId).length - 1 < 2) {
          return wholeMatch;
        }
        if (url.match(/^data:.+?\/.+?;base64,/)) {
          globals.gUrls[linkId] = url.replace(/\s/g, "");
        } else {
          globals.gUrls[linkId] = showdown2.subParser("encodeAmpsAndAngles")(url, options, globals);
        }
        if (blankLines) {
          return blankLines + title;
        } else {
          if (title) {
            globals.gTitles[linkId] = title.replace(/"|'/g, "&quot;");
          }
          if (options.parseImgDimensions && width && height) {
            globals.gDimensions[linkId] = {
              width,
              height
            };
          }
        }
        return "";
      };
      text = text.replace(base64Regex, replaceFunc);
      text = text.replace(regex, replaceFunc);
      text = text.replace(/¨0/, "");
      return text;
    });
    showdown2.subParser("tables", function(text, options, globals) {
      if (!options.tables) {
        return text;
      }
      var tableRgx = /^ {0,3}\|?.+\|.+\n {0,3}\|?[ \t]*:?[ \t]*(?:[-=]){2,}[ \t]*:?[ \t]*\|[ \t]*:?[ \t]*(?:[-=]){2,}[\s\S]+?(?:\n\n|¨0)/gm, singeColTblRgx = /^ {0,3}\|.+\|[ \t]*\n {0,3}\|[ \t]*:?[ \t]*(?:[-=]){2,}[ \t]*:?[ \t]*\|[ \t]*\n( {0,3}\|.+\|[ \t]*\n)*(?:\n|¨0)/gm;
      function parseStyles(sLine) {
        if (/^:[ \t]*--*$/.test(sLine)) {
          return ' style="text-align:left;"';
        } else if (/^--*[ \t]*:[ \t]*$/.test(sLine)) {
          return ' style="text-align:right;"';
        } else if (/^:[ \t]*--*[ \t]*:$/.test(sLine)) {
          return ' style="text-align:center;"';
        } else {
          return "";
        }
      }
      function parseHeaders(header, style) {
        var id = "";
        header = header.trim();
        if (options.tablesHeaderId || options.tableHeaderId) {
          id = ' id="' + header.replace(/ /g, "_").toLowerCase() + '"';
        }
        header = showdown2.subParser("spanGamut")(header, options, globals);
        return "<th" + id + style + ">" + header + "</th>\n";
      }
      function parseCells(cell, style) {
        var subText = showdown2.subParser("spanGamut")(cell, options, globals);
        return "<td" + style + ">" + subText + "</td>\n";
      }
      function buildTable(headers, cells) {
        var tb = "<table>\n<thead>\n<tr>\n", tblLgn = headers.length;
        for (var i = 0; i < tblLgn; ++i) {
          tb += headers[i];
        }
        tb += "</tr>\n</thead>\n<tbody>\n";
        for (i = 0; i < cells.length; ++i) {
          tb += "<tr>\n";
          for (var ii = 0; ii < tblLgn; ++ii) {
            tb += cells[i][ii];
          }
          tb += "</tr>\n";
        }
        tb += "</tbody>\n</table>\n";
        return tb;
      }
      function parseTable(rawTable) {
        var i, tableLines = rawTable.split("\n");
        for (i = 0; i < tableLines.length; ++i) {
          if (/^ {0,3}\|/.test(tableLines[i])) {
            tableLines[i] = tableLines[i].replace(/^ {0,3}\|/, "");
          }
          if (/\|[ \t]*$/.test(tableLines[i])) {
            tableLines[i] = tableLines[i].replace(/\|[ \t]*$/, "");
          }
          tableLines[i] = showdown2.subParser("codeSpans")(tableLines[i], options, globals);
        }
        var rawHeaders = tableLines[0].split("|").map(function(s) {
          return s.trim();
        }), rawStyles = tableLines[1].split("|").map(function(s) {
          return s.trim();
        }), rawCells = [], headers = [], styles = [], cells = [];
        tableLines.shift();
        tableLines.shift();
        for (i = 0; i < tableLines.length; ++i) {
          if (tableLines[i].trim() === "") {
            continue;
          }
          rawCells.push(tableLines[i].split("|").map(function(s) {
            return s.trim();
          }));
        }
        if (rawHeaders.length < rawStyles.length) {
          return rawTable;
        }
        for (i = 0; i < rawStyles.length; ++i) {
          styles.push(parseStyles(rawStyles[i]));
        }
        for (i = 0; i < rawHeaders.length; ++i) {
          if (showdown2.helper.isUndefined(styles[i])) {
            styles[i] = "";
          }
          headers.push(parseHeaders(rawHeaders[i], styles[i]));
        }
        for (i = 0; i < rawCells.length; ++i) {
          var row = [];
          for (var ii = 0; ii < headers.length; ++ii) {
            if (showdown2.helper.isUndefined(rawCells[i][ii]))
              ;
            row.push(parseCells(rawCells[i][ii], styles[ii]));
          }
          cells.push(row);
        }
        return buildTable(headers, cells);
      }
      text = globals.converter._dispatch("tables.before", text, options, globals);
      text = text.replace(/\\(\|)/g, showdown2.helper.escapeCharactersCallback);
      text = text.replace(tableRgx, parseTable);
      text = text.replace(singeColTblRgx, parseTable);
      text = globals.converter._dispatch("tables.after", text, options, globals);
      return text;
    });
    showdown2.subParser("underline", function(text, options, globals) {
      if (!options.underline) {
        return text;
      }
      text = globals.converter._dispatch("underline.before", text, options, globals);
      if (options.literalMidWordUnderscores) {
        text = text.replace(/\b___(\S[\s\S]*?)___\b/g, function(wm, txt) {
          return "<u>" + txt + "</u>";
        });
        text = text.replace(/\b__(\S[\s\S]*?)__\b/g, function(wm, txt) {
          return "<u>" + txt + "</u>";
        });
      } else {
        text = text.replace(/___(\S[\s\S]*?)___/g, function(wm, m) {
          return /\S$/.test(m) ? "<u>" + m + "</u>" : wm;
        });
        text = text.replace(/__(\S[\s\S]*?)__/g, function(wm, m) {
          return /\S$/.test(m) ? "<u>" + m + "</u>" : wm;
        });
      }
      text = text.replace(/(_)/g, showdown2.helper.escapeCharactersCallback);
      text = globals.converter._dispatch("underline.after", text, options, globals);
      return text;
    });
    showdown2.subParser("unescapeSpecialChars", function(text, options, globals) {
      text = globals.converter._dispatch("unescapeSpecialChars.before", text, options, globals);
      text = text.replace(/¨E(\d+)E/g, function(wholeMatch, m1) {
        var charCodeToReplace = parseInt(m1);
        return String.fromCharCode(charCodeToReplace);
      });
      text = globals.converter._dispatch("unescapeSpecialChars.after", text, options, globals);
      return text;
    });
    showdown2.subParser("makeMarkdown.blockquote", function(node, globals) {
      var txt = "";
      if (node.hasChildNodes()) {
        var children = node.childNodes, childrenLength = children.length;
        for (var i = 0; i < childrenLength; ++i) {
          var innerTxt = showdown2.subParser("makeMarkdown.node")(children[i], globals);
          if (innerTxt === "") {
            continue;
          }
          txt += innerTxt;
        }
      }
      txt = txt.trim();
      txt = "> " + txt.split("\n").join("\n> ");
      return txt;
    });
    showdown2.subParser("makeMarkdown.codeBlock", function(node, globals) {
      var lang = node.getAttribute("language"), num = node.getAttribute("precodenum");
      return "```" + lang + "\n" + globals.preList[num] + "\n```";
    });
    showdown2.subParser("makeMarkdown.codeSpan", function(node) {
      return "`" + node.innerHTML + "`";
    });
    showdown2.subParser("makeMarkdown.emphasis", function(node, globals) {
      var txt = "";
      if (node.hasChildNodes()) {
        txt += "*";
        var children = node.childNodes, childrenLength = children.length;
        for (var i = 0; i < childrenLength; ++i) {
          txt += showdown2.subParser("makeMarkdown.node")(children[i], globals);
        }
        txt += "*";
      }
      return txt;
    });
    showdown2.subParser("makeMarkdown.header", function(node, globals, headerLevel) {
      var headerMark = new Array(headerLevel + 1).join("#"), txt = "";
      if (node.hasChildNodes()) {
        txt = headerMark + " ";
        var children = node.childNodes, childrenLength = children.length;
        for (var i = 0; i < childrenLength; ++i) {
          txt += showdown2.subParser("makeMarkdown.node")(children[i], globals);
        }
      }
      return txt;
    });
    showdown2.subParser("makeMarkdown.hr", function() {
      return "---";
    });
    showdown2.subParser("makeMarkdown.image", function(node) {
      var txt = "";
      if (node.hasAttribute("src")) {
        txt += "![" + node.getAttribute("alt") + "](";
        txt += "<" + node.getAttribute("src") + ">";
        if (node.hasAttribute("width") && node.hasAttribute("height")) {
          txt += " =" + node.getAttribute("width") + "x" + node.getAttribute("height");
        }
        if (node.hasAttribute("title")) {
          txt += ' "' + node.getAttribute("title") + '"';
        }
        txt += ")";
      }
      return txt;
    });
    showdown2.subParser("makeMarkdown.links", function(node, globals) {
      var txt = "";
      if (node.hasChildNodes() && node.hasAttribute("href")) {
        var children = node.childNodes, childrenLength = children.length;
        txt = "[";
        for (var i = 0; i < childrenLength; ++i) {
          txt += showdown2.subParser("makeMarkdown.node")(children[i], globals);
        }
        txt += "](";
        txt += "<" + node.getAttribute("href") + ">";
        if (node.hasAttribute("title")) {
          txt += ' "' + node.getAttribute("title") + '"';
        }
        txt += ")";
      }
      return txt;
    });
    showdown2.subParser("makeMarkdown.list", function(node, globals, type) {
      var txt = "";
      if (!node.hasChildNodes()) {
        return "";
      }
      var listItems = node.childNodes, listItemsLenght = listItems.length, listNum = node.getAttribute("start") || 1;
      for (var i = 0; i < listItemsLenght; ++i) {
        if (typeof listItems[i].tagName === "undefined" || listItems[i].tagName.toLowerCase() !== "li") {
          continue;
        }
        var bullet = "";
        if (type === "ol") {
          bullet = listNum.toString() + ". ";
        } else {
          bullet = "- ";
        }
        txt += bullet + showdown2.subParser("makeMarkdown.listItem")(listItems[i], globals);
        ++listNum;
      }
      txt += "\n<!-- -->\n";
      return txt.trim();
    });
    showdown2.subParser("makeMarkdown.listItem", function(node, globals) {
      var listItemTxt = "";
      var children = node.childNodes, childrenLenght = children.length;
      for (var i = 0; i < childrenLenght; ++i) {
        listItemTxt += showdown2.subParser("makeMarkdown.node")(children[i], globals);
      }
      if (!/\n$/.test(listItemTxt)) {
        listItemTxt += "\n";
      } else {
        listItemTxt = listItemTxt.split("\n").join("\n    ").replace(/^ {4}$/gm, "").replace(/\n\n+/g, "\n\n");
      }
      return listItemTxt;
    });
    showdown2.subParser("makeMarkdown.node", function(node, globals, spansOnly) {
      spansOnly = spansOnly || false;
      var txt = "";
      if (node.nodeType === 3) {
        return showdown2.subParser("makeMarkdown.txt")(node, globals);
      }
      if (node.nodeType === 8) {
        return "<!--" + node.data + "-->\n\n";
      }
      if (node.nodeType !== 1) {
        return "";
      }
      var tagName = node.tagName.toLowerCase();
      switch (tagName) {
        case "h1":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.header")(node, globals, 1) + "\n\n";
          }
          break;
        case "h2":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.header")(node, globals, 2) + "\n\n";
          }
          break;
        case "h3":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.header")(node, globals, 3) + "\n\n";
          }
          break;
        case "h4":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.header")(node, globals, 4) + "\n\n";
          }
          break;
        case "h5":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.header")(node, globals, 5) + "\n\n";
          }
          break;
        case "h6":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.header")(node, globals, 6) + "\n\n";
          }
          break;
        case "p":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.paragraph")(node, globals) + "\n\n";
          }
          break;
        case "blockquote":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.blockquote")(node, globals) + "\n\n";
          }
          break;
        case "hr":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.hr")(node, globals) + "\n\n";
          }
          break;
        case "ol":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.list")(node, globals, "ol") + "\n\n";
          }
          break;
        case "ul":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.list")(node, globals, "ul") + "\n\n";
          }
          break;
        case "precode":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.codeBlock")(node, globals) + "\n\n";
          }
          break;
        case "pre":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.pre")(node, globals) + "\n\n";
          }
          break;
        case "table":
          if (!spansOnly) {
            txt = showdown2.subParser("makeMarkdown.table")(node, globals) + "\n\n";
          }
          break;
        case "code":
          txt = showdown2.subParser("makeMarkdown.codeSpan")(node, globals);
          break;
        case "em":
        case "i":
          txt = showdown2.subParser("makeMarkdown.emphasis")(node, globals);
          break;
        case "strong":
        case "b":
          txt = showdown2.subParser("makeMarkdown.strong")(node, globals);
          break;
        case "del":
          txt = showdown2.subParser("makeMarkdown.strikethrough")(node, globals);
          break;
        case "a":
          txt = showdown2.subParser("makeMarkdown.links")(node, globals);
          break;
        case "img":
          txt = showdown2.subParser("makeMarkdown.image")(node, globals);
          break;
        default:
          txt = node.outerHTML + "\n\n";
      }
      return txt;
    });
    showdown2.subParser("makeMarkdown.paragraph", function(node, globals) {
      var txt = "";
      if (node.hasChildNodes()) {
        var children = node.childNodes, childrenLength = children.length;
        for (var i = 0; i < childrenLength; ++i) {
          txt += showdown2.subParser("makeMarkdown.node")(children[i], globals);
        }
      }
      txt = txt.trim();
      return txt;
    });
    showdown2.subParser("makeMarkdown.pre", function(node, globals) {
      var num = node.getAttribute("prenum");
      return "<pre>" + globals.preList[num] + "</pre>";
    });
    showdown2.subParser("makeMarkdown.strikethrough", function(node, globals) {
      var txt = "";
      if (node.hasChildNodes()) {
        txt += "~~";
        var children = node.childNodes, childrenLength = children.length;
        for (var i = 0; i < childrenLength; ++i) {
          txt += showdown2.subParser("makeMarkdown.node")(children[i], globals);
        }
        txt += "~~";
      }
      return txt;
    });
    showdown2.subParser("makeMarkdown.strong", function(node, globals) {
      var txt = "";
      if (node.hasChildNodes()) {
        txt += "**";
        var children = node.childNodes, childrenLength = children.length;
        for (var i = 0; i < childrenLength; ++i) {
          txt += showdown2.subParser("makeMarkdown.node")(children[i], globals);
        }
        txt += "**";
      }
      return txt;
    });
    showdown2.subParser("makeMarkdown.table", function(node, globals) {
      var txt = "", tableArray = [[], []], headings = node.querySelectorAll("thead>tr>th"), rows = node.querySelectorAll("tbody>tr"), i, ii;
      for (i = 0; i < headings.length; ++i) {
        var headContent = showdown2.subParser("makeMarkdown.tableCell")(headings[i], globals), allign = "---";
        if (headings[i].hasAttribute("style")) {
          var style = headings[i].getAttribute("style").toLowerCase().replace(/\s/g, "");
          switch (style) {
            case "text-align:left;":
              allign = ":---";
              break;
            case "text-align:right;":
              allign = "---:";
              break;
            case "text-align:center;":
              allign = ":---:";
              break;
          }
        }
        tableArray[0][i] = headContent.trim();
        tableArray[1][i] = allign;
      }
      for (i = 0; i < rows.length; ++i) {
        var r = tableArray.push([]) - 1, cols = rows[i].getElementsByTagName("td");
        for (ii = 0; ii < headings.length; ++ii) {
          var cellContent = " ";
          if (typeof cols[ii] !== "undefined") {
            cellContent = showdown2.subParser("makeMarkdown.tableCell")(cols[ii], globals);
          }
          tableArray[r].push(cellContent);
        }
      }
      var cellSpacesCount = 3;
      for (i = 0; i < tableArray.length; ++i) {
        for (ii = 0; ii < tableArray[i].length; ++ii) {
          var strLen = tableArray[i][ii].length;
          if (strLen > cellSpacesCount) {
            cellSpacesCount = strLen;
          }
        }
      }
      for (i = 0; i < tableArray.length; ++i) {
        for (ii = 0; ii < tableArray[i].length; ++ii) {
          if (i === 1) {
            if (tableArray[i][ii].slice(-1) === ":") {
              tableArray[i][ii] = showdown2.helper.padEnd(tableArray[i][ii].slice(-1), cellSpacesCount - 1, "-") + ":";
            } else {
              tableArray[i][ii] = showdown2.helper.padEnd(tableArray[i][ii], cellSpacesCount, "-");
            }
          } else {
            tableArray[i][ii] = showdown2.helper.padEnd(tableArray[i][ii], cellSpacesCount);
          }
        }
        txt += "| " + tableArray[i].join(" | ") + " |\n";
      }
      return txt.trim();
    });
    showdown2.subParser("makeMarkdown.tableCell", function(node, globals) {
      var txt = "";
      if (!node.hasChildNodes()) {
        return "";
      }
      var children = node.childNodes, childrenLength = children.length;
      for (var i = 0; i < childrenLength; ++i) {
        txt += showdown2.subParser("makeMarkdown.node")(children[i], globals, true);
      }
      return txt.trim();
    });
    showdown2.subParser("makeMarkdown.txt", function(node) {
      var txt = node.nodeValue;
      txt = txt.replace(/ +/g, " ");
      txt = txt.replace(/¨NBSP;/g, " ");
      txt = showdown2.helper.unescapeHTMLEntities(txt);
      txt = txt.replace(/([*_~|`])/g, "\\$1");
      txt = txt.replace(/^(\s*)>/g, "\\$1>");
      txt = txt.replace(/^#/gm, "\\#");
      txt = txt.replace(/^(\s*)([-=]{3,})(\s*)$/, "$1\\$2$3");
      txt = txt.replace(/^( {0,3}\d+)\./gm, "$1\\.");
      txt = txt.replace(/^( {0,3})([+-])/gm, "$1\\$2");
      txt = txt.replace(/]([\s]*)\(/g, "\\]$1\\(");
      txt = txt.replace(/^ {0,3}\[([\S \t]*?)]:/gm, "\\[$1]:");
      return txt;
    });
    var root = this;
    if (module.exports) {
      module.exports = showdown2;
    } else {
      root.showdown = showdown2;
    }
  }).call(commonjsGlobal);
});
var Converter = showdown.Converter;
var extension = showdown.extension;
var extensions = showdown.extensions;
var getAllExtensions = showdown.getAllExtensions;
var getDefaultOptions = showdown.getDefaultOptions;
var getFlavor = showdown.getFlavor;
var getFlavorOptions = showdown.getFlavorOptions;
var getOption = showdown.getOption;
var getOptions = showdown.getOptions;
var helper = showdown.helper;
var removeExtension = showdown.removeExtension;
var resetExtensions = showdown.resetExtensions;
var resetOptions = showdown.resetOptions;
var setFlavor = showdown.setFlavor;
var setOption = showdown.setOption;
var subParser = showdown.subParser;
var validateExtension = showdown.validateExtension;

/* generated by Svelte v3.58.0 */

function get_each_context$1(ctx, list, i) {
	const child_ctx = ctx.slice();
	child_ctx[15] = list[i];
	return child_ctx;
}

// (221:8) {#if link.active}
function create_if_block_3(ctx) {
	let icon;
	let current;
	icon = new Component$1({ props: { icon: "bx:chevron-right" } });

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (215:4) {#each header_links as link}
function create_each_block$1(ctx) {
	let a;
	let span;
	let t0_value = /*link*/ ctx[15].text + "";
	let t0;
	let t1;
	let t2;
	let a_href_value;
	let a_class_value;
	let current;
	let if_block = /*link*/ ctx[15].active && create_if_block_3();

	return {
		c() {
			a = element("a");
			span = element("span");
			t0 = text(t0_value);
			t1 = space();
			if (if_block) if_block.c();
			t2 = space();
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { href: true, class: true });
			var a_nodes = children(a);
			span = claim_element(a_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t0 = claim_text(span_nodes, t0_value);
			span_nodes.forEach(detach);
			t1 = claim_space(a_nodes);
			if (if_block) if_block.l(a_nodes);
			t2 = claim_space(a_nodes);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-v9kn9v");
			attr(a, "href", a_href_value = "#" + /*link*/ ctx[15].id);
			attr(a, "class", a_class_value = "" + (null_to_empty(/*link*/ ctx[15].level) + " svelte-v9kn9v"));
			toggle_class(a, "passed", /*link*/ ctx[15].passed);
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			append_hydration(a, span);
			append_hydration(span, t0);
			append_hydration(a, t1);
			if (if_block) if_block.m(a, null);
			append_hydration(a, t2);
			current = true;
		},
		p(ctx, dirty) {
			if ((!current || dirty & /*header_links*/ 16) && t0_value !== (t0_value = /*link*/ ctx[15].text + "")) set_data(t0, t0_value);

			if (/*link*/ ctx[15].active) {
				if (if_block) {
					if (dirty & /*header_links*/ 16) {
						transition_in(if_block, 1);
					}
				} else {
					if_block = create_if_block_3();
					if_block.c();
					transition_in(if_block, 1);
					if_block.m(a, t2);
				}
			} else if (if_block) {
				group_outros();

				transition_out(if_block, 1, 1, () => {
					if_block = null;
				});

				check_outros();
			}

			if (!current || dirty & /*header_links*/ 16 && a_href_value !== (a_href_value = "#" + /*link*/ ctx[15].id)) {
				attr(a, "href", a_href_value);
			}

			if (!current || dirty & /*header_links*/ 16 && a_class_value !== (a_class_value = "" + (null_to_empty(/*link*/ ctx[15].level) + " svelte-v9kn9v"))) {
				attr(a, "class", a_class_value);
			}

			if (!current || dirty & /*header_links, header_links*/ 16) {
				toggle_class(a, "passed", /*link*/ ctx[15].passed);
			}
		},
		i(local) {
			if (current) return;
			transition_in(if_block);
			current = true;
		},
		o(local) {
			transition_out(if_block);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			if (if_block) if_block.d();
		}
	};
}

// (228:4) {#if github_markdown_file}
function create_if_block_2(ctx) {
	let a;
	let icon;
	let t0;
	let span;
	let t1;
	let current;
	icon = new Component$1({ props: { icon: "bxs:edit" } });

	return {
		c() {
			a = element("a");
			create_component(icon.$$.fragment);
			t0 = space();
			span = element("span");
			t1 = text("suggest edits");
			this.h();
		},
		l(nodes) {
			a = claim_element(nodes, "A", { class: true, href: true, target: true });
			var a_nodes = children(a);
			claim_component(icon.$$.fragment, a_nodes);
			t0 = claim_space(a_nodes);
			span = claim_element(a_nodes, "SPAN", { class: true });
			var span_nodes = children(span);
			t1 = claim_text(span_nodes, "suggest edits");
			span_nodes.forEach(detach);
			a_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(span, "class", "svelte-v9kn9v");
			attr(a, "class", "button pr svelte-v9kn9v");
			attr(a, "href", "https://github.com/primocms/docs");
			attr(a, "target", "_blank");
		},
		m(target, anchor) {
			insert_hydration(target, a, anchor);
			mount_component(icon, a, null);
			append_hydration(a, t0);
			append_hydration(a, span);
			append_hydration(span, t1);
			current = true;
		},
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(a);
			destroy_component(icon);
		}
	};
}

// (237:4) {#if video_id}
function create_if_block_1$1(ctx) {
	let div;
	let iframe;
	let iframe_src_value;

	return {
		c() {
			div = element("div");
			iframe = element("iframe");
			this.h();
		},
		l(nodes) {
			div = claim_element(nodes, "DIV", { class: true });
			var div_nodes = children(div);

			iframe = claim_element(div_nodes, "IFRAME", {
				src: true,
				title: true,
				frameborder: true,
				allow: true,
				class: true
			});

			children(iframe).forEach(detach);
			div_nodes.forEach(detach);
			this.h();
		},
		h() {
			if (!src_url_equal(iframe.src, iframe_src_value = "https://www.youtube-nocookie.com/embed/" + /*video_id*/ ctx[0])) attr(iframe, "src", iframe_src_value);
			attr(iframe, "title", "YouTube video player");
			attr(iframe, "frameborder", "0");
			attr(iframe, "allow", "accelerometer; autoplay; clipboard-write; encrypted-media; gyroscope; picture-in-picture");
			iframe.allowFullscreen = true;
			attr(iframe, "class", "svelte-v9kn9v");
			attr(div, "class", "video svelte-v9kn9v");
		},
		m(target, anchor) {
			insert_hydration(target, div, anchor);
			append_hydration(div, iframe);
		},
		p(ctx, dirty) {
			if (dirty & /*video_id*/ 1 && !src_url_equal(iframe.src, iframe_src_value = "https://www.youtube-nocookie.com/embed/" + /*video_id*/ ctx[0])) {
				attr(iframe, "src", iframe_src_value);
			}
		},
		d(detaching) {
			if (detaching) detach(div);
		}
	};
}

// (251:6) {:else}
function create_else_block$1(ctx) {
	let icon;
	let current;

	icon = new Component$1({
			props: { icon: "line-md:loading-twotone-loop" }
		});

	return {
		c() {
			create_component(icon.$$.fragment);
		},
		l(nodes) {
			claim_component(icon.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(icon, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(icon.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(icon.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(icon, detaching);
		}
	};
}

// (249:6) {#if docs}
function create_if_block$2(ctx) {
	let html_tag;
	let html_anchor;

	return {
		c() {
			html_tag = new HtmlTagHydration(false);
			html_anchor = empty();
			this.h();
		},
		l(nodes) {
			html_tag = claim_html_tag(nodes, false);
			html_anchor = empty();
			this.h();
		},
		h() {
			html_tag.a = html_anchor;
		},
		m(target, anchor) {
			html_tag.m(/*docs*/ ctx[3], target, anchor);
			insert_hydration(target, html_anchor, anchor);
		},
		p(ctx, dirty) {
			if (dirty & /*docs*/ 8) html_tag.p(/*docs*/ ctx[3]);
		},
		i: noop,
		o: noop,
		d(detaching) {
			if (detaching) detach(html_anchor);
			if (detaching) html_tag.d();
		}
	};
}

function create_fragment$3(ctx) {
	let scrolling = false;

	let clear_scrolling = () => {
		scrolling = false;
	};

	let scrolling_timeout;
	let div1;
	let section;
	let nav;
	let t0;
	let main;
	let t1;
	let t2;
	let div0;
	let current_block_type_index;
	let if_block2;
	let t3;
	let link;
	let current;
	let mounted;
	let dispose;
	add_render_callback(/*onwindowscroll*/ ctx[9]);
	let each_value = /*header_links*/ ctx[4];
	let each_blocks = [];

	for (let i = 0; i < each_value.length; i += 1) {
		each_blocks[i] = create_each_block$1(get_each_context$1(ctx, each_value, i));
	}

	const out = i => transition_out(each_blocks[i], 1, 1, () => {
		each_blocks[i] = null;
	});

	let if_block0 = /*github_markdown_file*/ ctx[1] && create_if_block_2();
	let if_block1 = /*video_id*/ ctx[0] && create_if_block_1$1(ctx);
	const if_block_creators = [create_if_block$2, create_else_block$1];
	const if_blocks = [];

	function select_block_type(ctx, dirty) {
		if (/*docs*/ ctx[3]) return 0;
		return 1;
	}

	current_block_type_index = select_block_type(ctx);
	if_block2 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);

	return {
		c() {
			div1 = element("div");
			section = element("section");
			nav = element("nav");

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].c();
			}

			t0 = space();
			main = element("main");
			if (if_block0) if_block0.c();
			t1 = space();
			if (if_block1) if_block1.c();
			t2 = space();
			div0 = element("div");
			if_block2.c();
			t3 = space();
			link = element("link");
			this.h();
		},
		l(nodes) {
			div1 = claim_element(nodes, "DIV", { class: true, id: true });
			var div1_nodes = children(div1);
			section = claim_element(div1_nodes, "SECTION", { class: true });
			var section_nodes = children(section);
			nav = claim_element(section_nodes, "NAV", { class: true });
			var nav_nodes = children(nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				each_blocks[i].l(nav_nodes);
			}

			nav_nodes.forEach(detach);
			t0 = claim_space(section_nodes);
			main = claim_element(section_nodes, "MAIN", { class: true });
			var main_nodes = children(main);
			if (if_block0) if_block0.l(main_nodes);
			t1 = claim_space(main_nodes);
			if (if_block1) if_block1.l(main_nodes);
			t2 = claim_space(main_nodes);
			div0 = claim_element(main_nodes, "DIV", { class: true, "data-key": true });
			var div0_nodes = children(div0);
			if_block2.l(div0_nodes);
			div0_nodes.forEach(detach);
			main_nodes.forEach(detach);
			section_nodes.forEach(detach);
			t3 = claim_space(div1_nodes);
			link = claim_element(div1_nodes, "LINK", { rel: true, href: true });
			div1_nodes.forEach(detach);
			this.h();
		},
		h() {
			attr(nav, "class", "svelte-v9kn9v");
			attr(div0, "class", "content svelte-v9kn9v");
			attr(div0, "data-key", "content");
			attr(main, "class", "svelte-v9kn9v");
			attr(section, "class", "section-container svelte-v9kn9v");
			attr(link, "rel", "stylesheet");
			attr(link, "href", "https://unpkg.com/highlightjs@9.16.2/styles/solarized-dark.css");
			attr(div1, "class", "section");
			attr(div1, "id", "section-a27d2a89");
		},
		m(target, anchor) {
			insert_hydration(target, div1, anchor);
			append_hydration(div1, section);
			append_hydration(section, nav);

			for (let i = 0; i < each_blocks.length; i += 1) {
				if (each_blocks[i]) {
					each_blocks[i].m(nav, null);
				}
			}

			append_hydration(section, t0);
			append_hydration(section, main);
			if (if_block0) if_block0.m(main, null);
			append_hydration(main, t1);
			if (if_block1) if_block1.m(main, null);
			append_hydration(main, t2);
			append_hydration(main, div0);
			if_blocks[current_block_type_index].m(div0, null);
			/*div0_binding*/ ctx[10](div0);
			append_hydration(div1, t3);
			append_hydration(div1, link);
			current = true;

			if (!mounted) {
				dispose = listen(window, "scroll", () => {
					scrolling = true;
					clearTimeout(scrolling_timeout);
					scrolling_timeout = setTimeout(clear_scrolling, 100);
					/*onwindowscroll*/ ctx[9]();
				});

				mounted = true;
			}
		},
		p(ctx, [dirty]) {
			if (dirty & /*scrollY*/ 32 && !scrolling) {
				scrolling = true;
				clearTimeout(scrolling_timeout);
				scrollTo(window.pageXOffset, /*scrollY*/ ctx[5]);
				scrolling_timeout = setTimeout(clear_scrolling, 100);
			}

			if (dirty & /*header_links*/ 16) {
				each_value = /*header_links*/ ctx[4];
				let i;

				for (i = 0; i < each_value.length; i += 1) {
					const child_ctx = get_each_context$1(ctx, each_value, i);

					if (each_blocks[i]) {
						each_blocks[i].p(child_ctx, dirty);
						transition_in(each_blocks[i], 1);
					} else {
						each_blocks[i] = create_each_block$1(child_ctx);
						each_blocks[i].c();
						transition_in(each_blocks[i], 1);
						each_blocks[i].m(nav, null);
					}
				}

				group_outros();

				for (i = each_value.length; i < each_blocks.length; i += 1) {
					out(i);
				}

				check_outros();
			}

			if (/*github_markdown_file*/ ctx[1]) {
				if (if_block0) {
					if (dirty & /*github_markdown_file*/ 2) {
						transition_in(if_block0, 1);
					}
				} else {
					if_block0 = create_if_block_2();
					if_block0.c();
					transition_in(if_block0, 1);
					if_block0.m(main, t1);
				}
			} else if (if_block0) {
				group_outros();

				transition_out(if_block0, 1, 1, () => {
					if_block0 = null;
				});

				check_outros();
			}

			if (/*video_id*/ ctx[0]) {
				if (if_block1) {
					if_block1.p(ctx, dirty);
				} else {
					if_block1 = create_if_block_1$1(ctx);
					if_block1.c();
					if_block1.m(main, t2);
				}
			} else if (if_block1) {
				if_block1.d(1);
				if_block1 = null;
			}

			let previous_block_index = current_block_type_index;
			current_block_type_index = select_block_type(ctx);

			if (current_block_type_index === previous_block_index) {
				if_blocks[current_block_type_index].p(ctx, dirty);
			} else {
				group_outros();

				transition_out(if_blocks[previous_block_index], 1, 1, () => {
					if_blocks[previous_block_index] = null;
				});

				check_outros();
				if_block2 = if_blocks[current_block_type_index];

				if (!if_block2) {
					if_block2 = if_blocks[current_block_type_index] = if_block_creators[current_block_type_index](ctx);
					if_block2.c();
				} else {
					if_block2.p(ctx, dirty);
				}

				transition_in(if_block2, 1);
				if_block2.m(div0, null);
			}
		},
		i(local) {
			if (current) return;

			for (let i = 0; i < each_value.length; i += 1) {
				transition_in(each_blocks[i]);
			}

			transition_in(if_block0);
			transition_in(if_block2);
			current = true;
		},
		o(local) {
			each_blocks = each_blocks.filter(Boolean);

			for (let i = 0; i < each_blocks.length; i += 1) {
				transition_out(each_blocks[i]);
			}

			transition_out(if_block0);
			transition_out(if_block2);
			current = false;
		},
		d(detaching) {
			if (detaching) detach(div1);
			destroy_each(each_blocks, detaching);
			if (if_block0) if_block0.d();
			if (if_block1) if_block1.d();
			if_blocks[current_block_type_index].d();
			/*div0_binding*/ ctx[10](null);
			mounted = false;
			dispose();
		}
	};
}

function instance$3($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { description } = $$props;
	let { video_id } = $$props;
	let { content } = $$props;
	let { github_markdown_file } = $$props;
	const converter = new showdown.Converter({});
	let content_node;
	let docs;

	async function get_docs() {
		if (!github_markdown_file) {
			$$invalidate(3, docs = content.html);
		} else {
			const { data } = await axios.get(github_markdown_file);
			const converted = converter.makeHtml(data);

			// console.log({data, converted})
			$$invalidate(3, docs = converted);
		}
	}

	let header_links = [];

	async function createHeaderLinks(content_node) {
		await tick();
		if (!content_node) return;

		$$invalidate(4, header_links = Array.from(content_node.children).filter(n => ["H1", "H2"].includes(n.tagName)).map((n, i) => {
			return {
				level: n.tagName,
				text: n.textContent,
				id: n.id,
				node: n,
				top: n.offsetTop
			};
		}));
	}

	let scrollY;

	function setActiveLink(scrollY) {
		$$invalidate(4, header_links = header_links.map((link, i) => {
			const element = link.node;
			const top = element ? element.offsetTop : null;
			const passed = scrollY >= top;
			return { ...link, top, passed };
		}).map((link, i) => {
			const nextLink = header_links[i + 1];

			const active = nextLink
			? link.top < scrollY && scrollY < nextLink.top
			: false;

			return { ...link, active };
		}));
	}

	function onwindowscroll() {
		$$invalidate(5, scrollY = window.pageYOffset);
	}

	function div0_binding($$value) {
		binding_callbacks[$$value ? 'unshift' : 'push'](() => {
			content_node = $$value;
			$$invalidate(2, content_node);
		});
	}

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(6, title = $$props.title);
		if ('description' in $$props) $$invalidate(7, description = $$props.description);
		if ('video_id' in $$props) $$invalidate(0, video_id = $$props.video_id);
		if ('content' in $$props) $$invalidate(8, content = $$props.content);
		if ('github_markdown_file' in $$props) $$invalidate(1, github_markdown_file = $$props.github_markdown_file);
	};

	$$self.$$.update = () => {
		if ($$self.$$.dirty & /*github_markdown_file*/ 2) {
			 (get_docs());
		}

		if ($$self.$$.dirty & /*docs, content_node*/ 12) {
			 docs && createHeaderLinks(content_node);
		}

		if ($$self.$$.dirty & /*header_links, scrollY*/ 48) {
			// $: console.log({scrollY})
			 header_links.length > 0 && setActiveLink(scrollY);
		}
	};

	return [
		video_id,
		github_markdown_file,
		content_node,
		docs,
		header_links,
		scrollY,
		title,
		description,
		content,
		onwindowscroll,
		div0_binding
	];
}

class Component$3 extends SvelteComponent {
	constructor(options) {
		super();

		init(this, options, instance$3, create_fragment$3, safe_not_equal, {
			title: 6,
			description: 7,
			video_id: 0,
			content: 8,
			github_markdown_file: 1
		});
	}
}

/* generated by Svelte v3.58.0 */

function instance$4($$self, $$props, $$invalidate) {
	let { title } = $$props;
	let { description } = $$props;

	$$self.$$set = $$props => {
		if ('title' in $$props) $$invalidate(0, title = $$props.title);
		if ('description' in $$props) $$invalidate(1, description = $$props.description);
	};

	return [title, description];
}

class Component$4 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, instance$4, null, safe_not_equal, { title: 0, description: 1 });
	}
}

/* generated by Svelte v3.58.0 */

function create_fragment$4(ctx) {
	let component_0;
	let t0;
	let component_1;
	let t1;
	let component_2;
	let t2;
	let component_3;
	let current;

	component_0 = new Component({
			props: {
				title: "Primo Docs",
				description: "Primo is a free & open source, component-based CMS that makes it easy to build visually-editable static sites."
			}
		});

	component_1 = new Component$2({
			props: {
				title: "Primo Docs",
				description: "Primo is a free & open source, component-based CMS that makes it easy to build visually-editable static sites.",
				secondary_logo: {
					"url": "http://localhost:5173/primo-docs",
					"label": "docs"
				},
				nav: [
					{
						"link": {
							"url": "/getting-started",
							"label": "Getting Started"
						}
					},
					{
						"link": {
							"url": "/development",
							"label": "Development"
						}
					},
					{
						"link": {
							"url": "/publishing",
							"label": "Publishing"
						}
					}
				]
			}
		});

	component_2 = new Component$3({
			props: {
				title: "Primo Docs",
				description: "Primo is a free & open source, component-based CMS that makes it easy to build visually-editable static sites.",
				video_id: "",
				content: {
					"html": "<h1 id=\"primo\">Primo</h1>\n<p>Primo is a new kind of monolithic CMS that makes it significantly easier to publish websites by providing a delightful content management experience and an embedded development environment. Primo sites get uploaded to a Github repository as a static site bundle, from where they can be deployed to any web host (usually for free).</p>\n<h2 id=\"comparison\">Comparison</h2>\n<p>Primo is most technically different from traditional monolithic CMSs like WordPress, Drupal, and Joomla in that it doesn't host your site for you, but instead builds the site as a static bundle so that they can be hosted by a separate server. Additionally, Primo offers more immediate control over the site's code by embedding a modular development environment, where custom development in a traditional monolithic CMS is a much more involved process.</p>\n<h2 id=\"projectstatus\">Project Status</h2>\n<p>Primo version 2 is in Public Beta as of April 28, 2023. Version 2 introduces significant usability and stability improvements over version 1 and is much more scalable since it stores sites, pages, and sections in a database instead of a flat file backend.</p>\n<h2 id=\"howitworks\">How it works</h2>\n<p>Primo is a SvelteKit application using Supabase as a backend. Sites, pages, page sections, and symbols (i.e. parent components) are all stored in the database as individual rows containing each's code, fields, and content.</p>\n<p>On-page editing works by matching a block's field values to text, link, and image values or explicitly set <code>data-key</code> attributes within the block's rendered HTML. Editable text is powered by <code>contentEditable = true</code> and a TipTap/ProseMirror editor for Markdown fields. The dev environment is powered by CodeMirror.</p>\n<p>Rollup and the Svelte compiler are used to compile page blocks into Svelte components (alongside PostCSS for nesting) and to build the static files for the deployed website, which Primo then uploads to Github via its REST API.</p>",
					"markdown": "# Primo\n\nPrimo is a new kind of monolithic CMS that makes it significantly easier to publish websites by providing a delightful content management experience and an embedded development environment. Primo sites get uploaded to a Github repository as a static site bundle, from where they can be deployed to any web host (usually for free).\n\n## Comparison\n\nPrimo is most technically different from traditional monolithic CMSs like WordPress, Drupal, and Joomla in that it doesn't host your site for you, but instead builds the site as a static bundle so that they can be hosted by a separate server. Additionally, Primo offers more immediate control over the site's code by embedding a modular development environment, where custom development in a traditional monolithic CMS is a much more involved process.\n\n## Project Status\n\nPrimo version 2 is in Public Beta as of April 28, 2023. Version 2 introduces significant usability and stability improvements over version 1 and is much more scalable since it stores sites, pages, and sections in a database instead of a flat file backend.\n\n## How it works\n\nPrimo is a SvelteKit application using Supabase as a backend. Sites, pages, page sections, and symbols (i.e. parent components) are all stored in the database as individual rows containing each's code, fields, and content.\n\nOn-page editing works by matching a block's field values to text, link, and image values or explicitly set `data-key` attributes within the block's rendered HTML. Editable text is powered by `contentEditable = true` and a TipTap/ProseMirror editor for Markdown fields. The dev environment is powered by CodeMirror.\n\nRollup and the Svelte compiler are used to compile page blocks into Svelte components (alongside PostCSS for nesting) and to build the static files for the deployed website, which Primo then uploads to Github via its REST API.\n\n"
				},
				github_markdown_file: "https://raw.githubusercontent.com/primocms/primo/master/README.md"
			}
		});

	component_3 = new Component$4({
			props: {
				title: "Primo Docs",
				description: "Primo is a free & open source, component-based CMS that makes it easy to build visually-editable static sites."
			}
		});

	return {
		c() {
			create_component(component_0.$$.fragment);
			t0 = space();
			create_component(component_1.$$.fragment);
			t1 = space();
			create_component(component_2.$$.fragment);
			t2 = space();
			create_component(component_3.$$.fragment);
		},
		l(nodes) {
			claim_component(component_0.$$.fragment, nodes);
			t0 = claim_space(nodes);
			claim_component(component_1.$$.fragment, nodes);
			t1 = claim_space(nodes);
			claim_component(component_2.$$.fragment, nodes);
			t2 = claim_space(nodes);
			claim_component(component_3.$$.fragment, nodes);
		},
		m(target, anchor) {
			mount_component(component_0, target, anchor);
			insert_hydration(target, t0, anchor);
			mount_component(component_1, target, anchor);
			insert_hydration(target, t1, anchor);
			mount_component(component_2, target, anchor);
			insert_hydration(target, t2, anchor);
			mount_component(component_3, target, anchor);
			current = true;
		},
		p: noop,
		i(local) {
			if (current) return;
			transition_in(component_0.$$.fragment, local);
			transition_in(component_1.$$.fragment, local);
			transition_in(component_2.$$.fragment, local);
			transition_in(component_3.$$.fragment, local);
			current = true;
		},
		o(local) {
			transition_out(component_0.$$.fragment, local);
			transition_out(component_1.$$.fragment, local);
			transition_out(component_2.$$.fragment, local);
			transition_out(component_3.$$.fragment, local);
			current = false;
		},
		d(detaching) {
			destroy_component(component_0, detaching);
			if (detaching) detach(t0);
			destroy_component(component_1, detaching);
			if (detaching) detach(t1);
			destroy_component(component_2, detaching);
			if (detaching) detach(t2);
			destroy_component(component_3, detaching);
		}
	};
}

class Component$5 extends SvelteComponent {
	constructor(options) {
		super();
		init(this, options, null, create_fragment$4, safe_not_equal, {});
	}
}

export default Component$5;
