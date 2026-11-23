import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagOfTriangularFrames
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flag_of_triangular_frames : ∀ (X : Scheme.{0}) [IsIntegral X] (A : X.Opens) (F : X.Modules) (r : ℕ) (s : Fin r → Γ(F, A)) (hs : IsFrame s), genericPoint X ∈ A → (∀ x : X, ∃ (V : X.Opens) (e : Fin r → Γ(F, V)), x ∈ V ∧ IsFrame e ∧ IsTri hs e) → ∃ fl : Vert.Flag F r, ∀ (V : X.Opens) (e : Fin r → Γ(F, V)), IsFrame e → IsTri hs e → Spans fl V e := by
  first | exact @GlobalTheory.TriFrame.exists_flag_spans | exact GlobalTheory.TriFrame.exists_flag_spans | (intros; apply GlobalTheory.TriFrame.exists_flag_spans <;> assumption)
