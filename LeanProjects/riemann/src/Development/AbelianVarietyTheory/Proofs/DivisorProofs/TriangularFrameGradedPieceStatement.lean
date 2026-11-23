import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameGradedPiece
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triangular_frame_graded_piece : ∀ (X : Scheme.{0}) (A : X.Opens) (F : X.Modules) (r : ℕ) (s : Fin r → Γ(F, A)) (hs : IsFrame s) (L : Fin r → LB X) (ρ : ∀ i k, Γ(X, A ⊓ (L i).U k)) (fl : Vert.Flag F r), Tri hs L ρ → (∀ (V : X.Opens) (e : Fin r → Γ(F, V)), IsFrame e → IsTri hs e → Spans fl V e) → ∀ (i : Fin r) (t : Γ(fl.F i.succ, A)), (fl.ι i.succ).app A t = s i → ∃ hσ : IsFrame fun _ : Fin 1 => (fl.π i).app A t, Tri hσ (fun _ => L i) (fun _ => ρ i) := by
  first | exact @GlobalTheory.TriFrame.grTri | exact GlobalTheory.TriFrame.grTri | (intros; apply GlobalTheory.TriFrame.grTri <;> assumption)
