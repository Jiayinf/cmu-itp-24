# Course Repository of Interactive Theorem Proving (21-321)

You should have installed this repository following the instructions on Piazza.
(See `assignment1.pdf` under the "Resources" tab.)
You can add your own files in the `CmuItp24` folder alongside the other ones.
It's best not to modify the original files.

Be sure to open the root directory from VS Code.

## Updating your local copy
You can pull the latest version of the lectures and assignments
by running the command
```
git pull
```
in the root directory.

We recommend that you also run the command
```
lake exe cache get
```
every time you update your local copy.
This command downloads a pre-checked version
of the `mathlib` mathematical library
from the cloud.
This way, Lean will not have to re-check all of `mathlib`
which would take a very long time.
