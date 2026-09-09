/* Keep expanded tactic states together beneath their source line. */
document.addEventListener('DOMContentLoaded', () => {
  for (const code of document.querySelectorAll('.code-content code.hl.lean.block')) {
    const lines = [{ toggles: [], anchor: null }];
    let line = lines[0];

    // Walk source text only. Hidden goal states contain their own newlines.
    function visit(node) {
      if (node.nodeType === Node.TEXT_NODE) {
        let text = node;
        let newline;
        while ((newline = text.textContent.indexOf('\n')) !== -1) {
          const rest = text.splitText(newline + 1);
          const anchor = document.createElement('span');
          anchor.className = 'lean-note-anchor';
          // Place the row after the line's final text and before its newline.
          const ending = text.splitText(newline);
          ending.before(anchor);
          line.anchor = anchor;
          line = { toggles: [], anchor: null };
          lines.push(line);
          text = rest;
        }
        return;
      }
      if (node.nodeType !== Node.ELEMENT_NODE) return;
      if (node.matches('.tactic-state, .hover-info')) return;
      if (node.matches('input.tactic-toggle')) {
        line.toggles.push(node);
        return;
      }
      for (const child of Array.from(node.childNodes)) visit(child);
    }
    visit(code);
    const end = document.createElement('span');
    end.className = 'lean-note-anchor';
    code.appendChild(end);
    line.anchor = end;
    code.classList.add('lean-notes-by-line');

    for (const sourceLine of lines) {
      if (!sourceLine.toggles.length) continue;
      const row = document.createElement('span');
      row.className = 'lean-note-row';
      sourceLine.anchor.appendChild(row);
      function update() {
        for (const token of row.querySelectorAll('*')) token._tippy?.destroy();
        row.replaceChildren();
        for (const toggle of sourceLine.toggles) {
          if (!toggle.checked) continue;
          const state = toggle.parentElement.querySelector(':scope > .tactic-state');
          if (!state) continue;
          const note = state.cloneNode(true);
          // Preserve goal-label associations without duplicating document IDs.
          const ids = new Map();
          for (const element of note.querySelectorAll('[id]')) {
            const id = `${toggle.id}-note-${element.id}`;
            ids.set(element.id, id);
            element.id = id;
          }
          for (const element of note.querySelectorAll('[for]')) {
            const id = ids.get(element.getAttribute('for'));
            if (id) element.setAttribute('for', id);
          }
          const originals = state.querySelectorAll('*');
          const copies = note.querySelectorAll('*');
          originals.forEach((original, index) => {
            if (original._tippy && typeof tippy === 'function') {
              tippy(copies[index], original._tippy.props);
            }
          });
          row.appendChild(note);
        }
        row.hidden = !row.childElementCount;
      }
      for (const toggle of sourceLine.toggles) toggle.addEventListener('change', () => queueMicrotask(update));
      update();
    }
  }
});
