# Zenodo: why no deposit has been made

Checked on 9 November 2026 against Zenodo's own pages:
[generative AI policy for depositors](https://support.zenodo.org/help/en-gb/13/227) and
[content not suitable for Zenodo](https://support.zenodo.org/help/en-gb/2-content/141-what-content-is-not-suitable-for-zenodo),
both published 27 April 2026.

## What the policy says

Zenodo requires that deposited content be grounded in research work conducted by its authors, with AI
used as a tool and not as the source of the research. It lists as unsuitable a paper produced by
prompting a language model and submitted without further research work, and it names as a warning sign
core ideas and findings that originate from AI output rather than from the uploader's own research. It
also requires disclosure of substantive AI use, forbids listing an AI tool as creator, and holds the
depositor fully responsible for the content. It invites depositors who are in doubt to ask its support
line.

## How that applies here

The paper states its own origin plainly: the research direction, the derivations, the programs, the Lean
proofs and the text were produced by an AI system at the request and under the direction of the author.
On a straightforward reading this is the situation the policy describes as outside Zenodo's scope, even
though the results are checked by a proof assistant and by independent programs. Correctness is not the
criterion the policy uses; human-conducted research is.

A deposit made anyway could be removed, and it would put the author's account at risk. So no record has
been created and no DOI has been reserved.

## Ways forward

1. **Ask Zenodo.** The support line can say whether a fully disclosed, formally verified work produced
   by an AI system under a person's direction is in scope. A message the author can send:

   > I would like to deposit a research preprint with its Lean 4 proofs, programs and data
   > (https://github.com/0thernes/hoggar-bound-lab). The research, the proofs and the text were produced
   > by an AI system (Claude) at my request and under my direction; this is disclosed on the first page
   > of the paper and would be disclosed in the record. The formal statements are checked by the Lean
   > kernel and the computations are reproducible. I am listed as the only author and take
   > responsibility for the release. Under your generative AI policy of 27 April 2026, is such a deposit
   > within Zenodo's scope? If it is, how would you like the AI contribution described?

2. **Deposit later, on the author's own research basis.** If the author works through the results,
   re-runs and extends them, and can describe that work, the record would rest on research the author
   conducted, with the AI system disclosed as a tool.

3. **Do without a Zenodo DOI for now.** The release is archived by Software Heritage (which gives a
   permanent identifier for the exact source tree) and by the Internet Archive, and an arXiv identifier
   serves the same purpose for the paper.

`ZENODO-METADATA.json` holds the metadata in case a deposit is made. The licence field is left open on
purpose: the repository uses a restrictive verification licence, and Zenodo's default licence should not
be accepted without a decision by the author.
