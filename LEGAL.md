# Legal notes: licence, authorship, disclosure

This file explains the terms in plain words. The binding texts are [LICENSE](LICENSE) and
[NOTICE](NOTICE). It is not legal advice.

## Copyright and licence

* Copyright © 2026 0thernes LLC (Alexander S. Donahue), Washington, USA. All rights reserved.
* The files written for this project are under the **verification licence** in [LICENSE](LICENSE):
  anyone may download, build, run and study the repository to check, reproduce or referee the reported
  results, and may quote from it with attribution. Redistribution of modified versions and commercial
  use need the written permission of the copyright holder.
* This is not an open-source licence in the sense of the Open Source Initiative. It was chosen so that
  the work can be verified freely while other uses stay with the author.
* A preprint server or a journal needs its own licence for the paper (for example arXiv's non-exclusive
  licence to distribute). Granting one is the author's decision at submission and does not change the
  licence of this repository.

## Third-party components

`third_party/` holds unmodified copies of parts of three projects by Tsotchke, each under the MIT
licence, with the licence text and a provenance record in its directory: the Moonlab simulator (prebuilt
WebAssembly engine), quantum_rng, and one source file of quantum_geometric_tensor. The Lean development
depends on Mathlib (Apache 2.0), which is downloaded by Lake and not copied here. This project is derived
from those components and is not endorsed by their authors. See [NOTICE](NOTICE).

## Authorship and responsibility

* Author: Alexander S. Donahue, 0thernes LLC, ORCID [0009-0006-8168-9648](https://orcid.org/0009-0006-8168-9648).
  Correspondence: 0_0@0thernes.art.
* The research, the programs, the Lean proofs and the text were produced by an AI system (Claude,
  Anthropic) at the request and under the direction of the author, who is responsible for the release.
  A separate set of AI agent sessions wrote the independent companion review and the companion note in
  the same repository. This is stated in the paper (first page and Section 12) and here so that nobody
  is misled about how the work was made.
* An AI system is not an author and holds no rights in the work.
* The work was funded by the author through 0thernes LLC. There was no external funding and there are no
  competing interests.

## Prior work and priority

The spectral floor, the three classical cases in which it is attained, and the exact values for the
classical families are the work of the authors cited in the paper (Section 1.2 and the priority note on
its first page). No priority is claimed for them. Novelty of the results of Section 5 is claimed only to
the extent of a bounded literature search made on 9 November 2026.

## Status and warranty

Research preprint, not peer reviewed. The Lean statements are checked by the Lean kernel; everything
else is unrefereed. The work is provided as is, without warranty of any kind; see [LICENSE](LICENSE).

## Names

"0thernes" is the name under which the author's company works. Moonlab, quantum_rng,
quantum_geometric_tensor and Eshkol are projects of Tsotchke; Lean and Mathlib belong to their
communities; Claude is a product of Anthropic. Their names are used here only to identify them.
