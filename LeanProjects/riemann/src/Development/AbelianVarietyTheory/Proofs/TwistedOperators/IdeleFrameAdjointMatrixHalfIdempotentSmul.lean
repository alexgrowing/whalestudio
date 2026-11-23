import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section
namespace GlobalTheory.AdjScalar
variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem map_adj_smul {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (σ : R →+* R) {m n : ℕ}
    (G1 : Matrix (Fin m) (Fin m) R) (G2 : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin m) (Fin m) K)
    (Q : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin m) R) (a : R) :
    P * ((G1 * ((a • X).map σ)ᵀ * G2).map f) * Q = f (σ a) • (P * ((G1 * (X.map σ)ᵀ * G2).map f) * Q) := by
  have h1 : (a • X).map σ = σ a • X.map σ := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have h2 : ∀ (M : Matrix (Fin m) (Fin n) R) (b : R), (b • M).map f = f b • M.map f := by
    intro M b; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (a : AE D) (x : WO S T) :
    frMapAdj S T βS βT (a • x) = toEAf D (cA D a) • frMapAdj S T βS βT x :=
  map_adj_smul (toEAf D) (cA D) _ _ _ _ x a

theorem cA_incA' (c : D.host.E) : cA D (incA D c) = incA D (star c) := rfl

theorem smul_absorb {K : Type} [CommRing K] {m n : ℕ} (B : Matrix (Fin m) (Fin m) K) (F : Matrix (Fin m) (Fin n) K)
    (u v : K) (hF : u • F = F) : (u * v) • (B * F) = (1 : K) • (B * (v • F)) := by
  rw [one_smul, Matrix.mul_smul, mul_comm, mul_smul, ← Matrix.mul_smul B u F, hF]

theorem adjA_half_smul (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (e : AE D) (c : D.host.E) (x : WO S T) (h : IsHalf (cA D e) x) :
    adjA S T βS βT (e * incA D (star c)) x = adjA S T βS βT 1 (incA D c • x) := by
  have hx : cA D e • x = x := by
    ext i j; exact h i j
  have hF : toEAf D e • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
    conv_rhs => rw [← hx]
    rw [frMapAdj_smul, cA_cA]
  unfold adjA
  rw [frMapAdj_smul, cA_incA', map_one, map_mul]
  exact smul_absorb _ _ _ _ hF

end GlobalTheory.AdjScalar
