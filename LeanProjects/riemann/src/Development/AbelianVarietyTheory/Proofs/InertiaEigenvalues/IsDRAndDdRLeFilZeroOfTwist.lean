import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

namespace GlobalTheory

section TwistDeRham

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)

theorem deRhamTwist_galoisAct_period (g : G) :
    PD.actdR g (PD.ι PD.t) = ((PD.χ g : Qpˣ) : Qp) • PD.ι PD.t := by
  rw [← PD.ι_comm, PD.t_act, ← algebraMap_smul K₀ ((PD.χ g : Qpˣ) : Qp) PD.t, map_smul,
    algebraMap_smul]

theorem drTwist_pow_mem (e : ℕ) : (PD.ι PD.t) ^ e ∈ PD.Fil (e : ℤ) := by
  induction e with
  | zero => simpa using PD.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact_mod_cast PD.Fil_mul _ _ _ _ ih PD.mem_filtration_one

theorem drTwist_Fil_le (e : ℕ) : PD.Fil (e : ℤ) ≤ PD.Fil 0 := by
  induction e with
  | zero => simp
  | succ n ih =>
    refine le_trans ?_ ih
    exact_mod_cast PD.Fil_anti (n : ℤ)

noncomputable def drTwistMap (e : ℕ) : K →ₗ[Qp] BdR :=
  (LinearMap.mulRight Qp ((PD.ι PD.t) ^ e)) ∘ₗ (IsScalarTower.toAlgHom Qp K BdR).toLinearMap

theorem drTwistMap_apply (e : ℕ) (k : K) :
    drTwistMap PD e k = algebraMap K BdR k * (PD.ι PD.t) ^ e := rfl

theorem drTwistMap_injective (e : ℕ) : Function.Injective (drTwistMap PD e) := by
  have hnt : Nontrivial BdR := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact PD.not_mem_filtration_two (by rw [Subsingleton.elim (PD.ι PD.t) 0]; exact Submodule.zero_mem _)
  intro a b hab
  rw [drTwistMap_apply, drTwistMap_apply] at hab
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  exact (algebraMap K BdR).injective (hu.mul_right_cancel hab)

theorem drTwistMap_mem (e : ℕ) (k : K) : drTwistMap PD e k ∈ PD.Fil 0 := by
  rw [drTwistMap_apply, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (drTwist_Fil_le PD e (drTwist_pow_mem PD e))

theorem drTwist_act_pow (e : ℕ) (g : G) :
    PD.actdR g ((PD.ι PD.t) ^ e) = ((PD.χ g : Qpˣ) : Qp) ^ e • (PD.ι PD.t) ^ e := by
  rw [map_pow, deRhamTwist_galoisAct_period, smul_pow]

theorem drTwistMap_fixed (e : ℕ) (g : G) (k : K) :
    (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (drTwistMap PD e k) = drTwistMap PD e k := by
  rw [drTwistMap_apply, map_mul, AlgEquiv.commutes, drTwist_act_pow, mul_smul_comm, smul_smul,
    ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul]

theorem drTwistMap_range (e : ℕ) (y : BdR)
    (hy : ∀ g, (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y = y) :
    ∃ k, drTwistMap PD e k = y := by
  have hu : IsUnit ((PD.ι PD.t) ^ e) := (PD.t_unit.map PD.ι).pow e
  obtain ⟨z, hz⟩ := hu.exists_left_inv
  have hyz : y = (y * z) * (PD.ι PD.t) ^ e := by rw [mul_assoc, hz, mul_one]
  obtain ⟨k, hk⟩ := PD.invdR (y * z) (fun g => by
    apply hu.mul_right_cancel
    have h := hy g
    rw [hyz, map_mul, drTwist_act_pow, mul_smul_comm, smul_smul,
      ← mul_pow, inv_mul_cancel₀ (PD.χ g).ne_zero, one_pow, one_smul] at h
    exact h)
  exact ⟨k, by rw [drTwistMap_apply, hk, ← hyz]⟩

variable {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V]
    [Module Qp V] [IsScalarTower Qp LL V] (ρ : Representation LL G V)

theorem drTwist_act_tmul (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) (g : G) (v : V) (y : BdR) :
    actVdR PD ρ g (v ⊗ₜ[Qp] y) =
      v ⊗ₜ[Qp] ((((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g y) := by
  have : actVdR PD ρ g (v ⊗ₜ[Qp] y) = ρ g v ⊗ₜ[Qp] PD.actdR g y := rfl
  rw [this, h, ← map_inv₀, ← map_pow, algebraMap_smul, smul_tmul]

theorem drTwist_range (e : ℕ)
    (h : ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) :
    LinearMap.range (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) =
      DdR PD ρ := by
  classical
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | tmul v k =>
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, AlgebraTensorModule.map_tmul, sub_eq_zero]
      intro g
      rw [drTwist_act_tmul PD ρ e h, drTwistMap_fixed]
  · intro x hx
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hx
    let b := Module.Basis.ofVectorSpace Qp V
    let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) b
    have hE : ∀ g (x : V ⊗[Qp] BdR) i, E (actVdR PD ρ g x) i =
        (((PD.χ g : Qpˣ) : Qp)⁻¹) ^ e • PD.actdR g (E x i) := by
      intro g x i
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb, smul_add]
      | tmul v y =>
        rw [drTwist_act_tmul PD ρ e h]
        simp only [E, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply]
        rw [← algebraMap_smul K (b.repr v i) y, map_smul, algebraMap_smul, smul_comm]
    have hx' : x = E.symm (E x) := (E.symm_apply_apply x).symm
    rw [hx', TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    obtain ⟨k, hk⟩ := drTwistMap_range PD e (E x i) (fun g => by rw [← hE, hx g])
    exact ⟨b i ⊗ₜ k, by rw [AlgebraTensorModule.map_tmul, hk]; rfl⟩

end TwistDeRham

theorem isDR_and_DdR_le_Fil_zero_of_twist : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) (e : ℕ), (∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x) → IsDR PD ρ ∧ DdR PD ρ ≤ FilV PD (LL := LL) (V := V) 0 := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ V _ _ _ _ _ ρ e h
  have hr := drTwist_range PD ρ e h
  constructor
  · have hinj : Function.Injective
        (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (drTwistMap PD e)) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ (drTwistMap_injective PD e)
    have := PD.finK
    unfold IsDR
    rw [← hr, LinearMap.finrank_range_of_inj hinj, Module.finrank_tensorProduct, mul_comm]
  · rw [← hr]
    rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add a b ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
    | tmul v k => exact ⟨v ⊗ₜ ⟨drTwistMap PD e k, drTwistMap_mem PD e k⟩, rfl⟩

end GlobalTheory
