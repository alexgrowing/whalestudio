import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.TwistCrys

open GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W] [FiniteDimensional LL W]

theorem isCrys_twist (ht : TensorCrys PD LL) (hq : QuotCrys PD LL)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G W) (χ : G → LL)
    (lam : W →ₗ[LL] LL) (w : W) (hw : lam w = 1)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (cν : IsCrys PD ν) (cρ : IsCrys PD ρ) : IsCrys PD ρ' := by
  let f : V ⊗[LL] W →ₗ[LL] V := (TensorProduct.rid LL V).toLinearMap ∘ₗ lam.lTensor V
  have hf : ∀ v x, f (v ⊗ₜ x) = lam x • v := fun v x => by simp [f]
  refine hq (V ⊗[LL] W) (ρ.tprod ν) V ρ' f ?_ ?_ (ht V ρ W ν cρ cν)
  · intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul v y =>
      rw [Representation.tprod_apply, TensorProduct.map_tmul, hf, hf, hν, hρ, map_smul, map_smul,
        smul_eq_mul, mul_smul]
  · intro v
    exact ⟨v ⊗ₜ w, by rw [hf, hw, one_smul]⟩

theorem isCrys_twist_iff (ht : TensorCrys PD LL) (hq : QuotCrys PD LL) (hd : DualCrys PD LL)
    (ρ ρ' : Representation LL G V) (ν : Representation LL G W) (χ : G → LL)
    (lam : W →ₗ[LL] LL) (w : W) (hw : lam w = 1)
    (hν : ∀ g x, ν g x = χ g • x) (hρ : ∀ g x, ρ' g x = χ g • ρ g x)
    (cν : IsCrys PD ν) : IsCrys PD ρ ↔ IsCrys PD ρ' := by
  refine ⟨isCrys_twist PD ht hq ρ ρ' ν χ lam w hw hν hρ cν, ?_⟩
  have hinv : ∀ g, χ g⁻¹ * χ g = 1 := fun g => by
    have h1 : ν g⁻¹ (ν g w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    have h2 := congrArg lam h1
    rwa [hν, hν, map_smul, map_smul, hw, smul_eq_mul, smul_eq_mul, mul_one] at h2
  refine isCrys_twist PD ht hq ρ' ρ ν.dual (fun g => χ g⁻¹) (Module.Dual.eval LL W w) lam hw
    (fun g f => ?_) (fun g x => ?_) (hd W ν cν)
  · ext x
    simp [Representation.dual_apply, Module.Dual.transpose_apply, hν]
  · rw [hρ, smul_smul, hinv, one_smul]

end Generic

theorem isCrys_iff_of_twist : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ ρ' : Representation ↥LL.1 ↥(GK K) V) (ν : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1)) (χ : ↥(GK K) → ↥LL.1), (∀ g x, ν g x = χ g • x) → (∀ g x, ρ' g x = χ g • ρ g x) → IsCrys (P.PD K) ν → (IsCrys (P.PD K) ρ ↔ IsCrys (P.PD K) ρ') := by
  intro hF l _ P AI T K LL V _ _ _ _ _ ρ ρ' ν χ hν hρ cν
  have h := (fontaineFormalism_iff l P).1 (GlobalTheory.RegularRing.fontaineFormalism hF l P AI ⟨T⟩) K LL
  exact isCrys_twist_iff (P.PD K) h.2.2.2.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.2.2.1 ρ ρ' ν χ
    (LinearMap.proj 0) (fun _ => 1) rfl hν hρ cν

end GlobalTheory.TwistCrys
