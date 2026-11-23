import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem boundQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) :
    Bound (σSt P K) ℚ_[l] (finrank ℚ_[l] ↥(K0 K)) := by
  intro U _ m₁ m₂ hts _ ρ
  have hm : m₂ = m₁ := by
    refine Module.ext' _ _ fun a u => ?_
    have h := hts.smul_assoc a (1 : ℚ_[l]) u
    rw [smul_eq_mul, mul_one, @one_smul ℚ_[l] U _ m₁.toDistribMulAction.toMulAction] at h
    exact h.symm
  subst hm
  obtain ⟨hfin, hb⟩ := GlobalTheory.CrysSst.finrank_Dst_le P AI T ρ
  rw [dinv_σSt]
  exact ⟨hfin, by rw [mul_comm]; exact hb⟩

private theorem pow_C {l : ℕ} [Fact l.Prime] (P : LocPrime l) (f : ℕ) (b : P.R.B) :
    (Polynomial.C ((ψCr P f) b) : Bst P) = (ψSt P f) (Polynomial.C b) := by
  induction f generalizing b with
  | zero => simp [ψCr, ψSt]
  | succ f ih =>
    simp only [ψCr, ψSt, pow_succ', Module.End.mul_apply] at ih ⊢
    rw [← ih]
    simp

theorem UpperTheory.Gal.crystallineComparison.stOfCr_of :
    AnnPer → BoundSt → StOfCr := by
  intro hP _ l _ P AI hT K V _ _ _ ρ hA
  obtain ⟨T⟩ := hT
  have hB := boundQ P AI T K
  have key : ∀ f : ℕ, _ := fun f => hP ℚ_[l] ↥(GK K) P.R.B (Bst P) (σCr P K) (ψCr P f) (σSt P K) (ψSt P f)
    (Polynomial.CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap Polynomial.C_injective
    (fun g b => (actSt_C P (g : GQ l) b).symm) (fun b => pow_C P f b) ℚ_[l] _ hB V ρ hA
  exact ⟨(key 0).1, fun f q n T' h => (key f).2 q n T' h⟩
