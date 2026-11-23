import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentInverseLimitCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_inverse_limit_compatible : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → (∀ n, Function.Surjective (cn t n)) → (∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A))) → (∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w) → (∀ (n : ℕ) (c : O) (w : Wmod A), cn t n (c • w) = c • cn t n w) → ∀ u : G.omega, ∃ w, ∀ n, cn t n w = u.1 n := by
  first | exact @GlobalTheory.SqZeroPt.cn_hits_compatible | exact GlobalTheory.SqZeroPt.cn_hits_compatible | (intros; apply GlobalTheory.SqZeroPt.cn_hits_compatible <;> assumption)
