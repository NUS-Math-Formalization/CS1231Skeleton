-- import Game.Levels.DemoWorld
import Game.Levels.Proof
import Game.Levels.Set
import Game.Levels.Relation
import Game.Levels.EquivalenceRelation

-- Here's what we'll put on the title screen
Title "CS1231 Tutorial Exercise Game"
Introduction
"
Here are some exercises in CS1231, but in a game style!
You may navigate your proof through entering some commands, and we will check if your proof is correct.
Disclaimer: This game is experimental, and not affiliated with the official CS1231 module,
 and it is of course not mandatory.
"

Info "
Contact sunm07@u.nus.edu for any feedback or bug reports.
The game is based on a proof assistant called LEAN, to learn more, visit
https://lean-lang.org/ or https://adam.math.hhu.de/#/g/leanprover-community/nng4
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "CS1231 Tutorial Exercise Game"
CaptionLong "."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
