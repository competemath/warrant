# Security policy

WARRANT is a proof checker: the one thing that must never happen is that it accepts a proof of `False`, or accepts a
declaration whose type is not what the file says. Please report anything that could make it do so.

## How to report

Use GitHub's private vulnerability reporting: open the **Security** tab of this repository and choose
**Report a vulnerability**. The report stays private between you and the maintainers until a fix is out.

A useful report is an export file (the `lean4export` NDJSON format) that WARRANT accepts and should reject, or
rejects and should accept, with what you expected. A file that the official Lean kernel judges differently from
WARRANT is a report by itself.

## What is in scope

- **Soundness**: an accepted file in which a theorem's type is `False` or any other uninhabited proposition, or in
  which a declaration is accepted with a type it does not have.
- **The evidence discipline**: a way to construct an evidence value (`Wf`, `Typing`, `Conv`, `Prop`, `Inductive`)
  outside its minting module, or to carry one across an environment, universe substitution or context it was not
  minted for.
- **The checks that judge a pull request**: a PR that passes a check it should fail, a check that runs code from a PR
  with a write token, or a way to spoof the required `ci` status.

A valid file that WARRANT declines (exit 2) is a completeness gap, not a vulnerability: open an ordinary issue with
the file.
