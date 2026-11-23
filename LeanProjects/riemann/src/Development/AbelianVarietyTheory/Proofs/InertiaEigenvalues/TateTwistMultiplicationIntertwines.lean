import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module TensorProduct GlobalTheory.Pass GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.FontCmp
open GlobalTheory.RegularRing

namespace GlobalTheory.PcrisTwist

section Eigen

variable {I LL : Type} [Group I] [Field LL]

open Classical in

theorem exists_separating (S : Finset (I →* LLˣ)) (a : I →* LLˣ) :
    ∃ e : I →₀ LL, ∀ b ∈ S, (e.sum fun g c => c * (b g : LL)) = if b = a then 1 else 0 := by
  have h1 : LinearIndependent LL (fun b : S => fun g : I => ((b.1 g : LLˣ) : LL)) := by
    refine (linearIndependent_monoidHom I LL).comp (fun b : S => (Units.coeHom LL).comp b.1) ?_
    intro b b' h
    exact Subtype.ext (MonoidHom.ext fun g => Units.ext (DFunLike.congr_fun h g))
  have h2 := span_flip_eq_top_iff_linearIndependent.2 h1
  obtain ⟨e, he⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1
    (h2 ▸ Submodule.mem_top : (fun b : S => if b.1 = a then (1 : LL) else 0) ∈ _)
  refine ⟨e, fun b hb => ?_⟩
  have := congrFun he ⟨b, hb⟩
  simpa [Finsupp.sum, flip] using this

def eig {M : Type} [AddCommGroup M] [Module LL M] (T : I → M →ₗ[LL] M) (b : I →* LLˣ) : Submodule LL M :=
  ⨅ g : I, LinearMap.ker (T g - ((b g : LLˣ) : LL) • LinearMap.id)

theorem mem_eig {M : Type} [AddCommGroup M] [Module LL M] (T : I → M →ₗ[LL] M) (b : I →* LLˣ) (x : M) :
    x ∈ eig T b ↔ ∀ g, T g x = ((b g : LLˣ) : LL) • x := by
  simp [eig, Submodule.mem_iInf, sub_eq_zero]

theorem le_iSup_eig {M N J : Type} [AddCommGroup M] [Module LL M] [AddCommGroup N] [Module LL N]
    (S : Finset (I →* LLˣ)) (T : I → M →ₗ[LL] M) (D : Submodule LL M) (hD : ∀ g, ∀ x ∈ D, T g x ∈ D)
    (f : J → M →ₗ[LL] N) (T' : J → I → N →ₗ[LL] N) (hf : ∀ j g x, f j (T g x) = T' j g (f j x))
    (hS : ∀ j, ∀ x ∈ D, f j x ∈ ⨆ b ∈ S, eig (T' j) b) (hsep : ∀ x, (∀ j, f j x = 0) → x = 0) :
    D ≤ ⨆ b ∈ S, D ⊓ eig T b := by
  classical
  choose e he using exists_separating S
  let E : (I →* LLˣ) → M →ₗ[LL] M := fun a => (e a).sum fun g c => c • T g
  let E' : J → (I →* LLˣ) → N →ₗ[LL] N := fun j a => (e a).sum fun g c => c • T' j g
  have h1 : ∀ j a x, f j (E a x) = E' j a (f j x) := fun j a x => by
    simp [E, E', Finsupp.sum, hf]
  have h2 : ∀ j a, ∀ b ∈ S, ∀ y ∈ eig (T' j) b, E' j a y = if b = a then y else 0 := by
    intro j a b hb y hy
    have : E' j a y = ((e a).sum fun g c => c * (b g : LL)) • y := by
      simp [E', Finsupp.sum, (mem_eig _ _ _).1 hy, Finset.sum_smul, smul_smul]
    rw [this, he a b hb]
    split_ifs <;> simp
  have h3 : ∀ j, (⨆ b ∈ S, eig (T' j) b) ≤ LinearMap.ker (∑ a ∈ S, E' j a - LinearMap.id) := fun j =>
    iSup₂_le fun b hb y hy => by
      simp [h2 j _ b hb y hy, hb]
  have h4 : ∀ j a, (⨆ b ∈ S, eig (T' j) b) ≤ (eig (T' j) a).comap (E' j a) := fun j a =>
    iSup₂_le fun b hb y hy => by
      rw [Submodule.mem_comap, h2 j _ b hb y hy]
      split_ifs with h
      · exact h ▸ hy
      · exact Submodule.zero_mem _
  intro x hx
  have h5 : x = ∑ a ∈ S, E a x := by
    symm
    rw [← sub_eq_zero]
    refine hsep _ fun j => ?_
    simpa [h1] using h3 j (hS j x hx)
  rw [h5]
  refine Submodule.sum_mem _ fun a ha => Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha ⟨?_, ?_⟩)
  · simp only [E, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply]
    exact D.sum_mem fun g _ => D.smul_mem _ (hD g x hx)
  · refine (mem_eig _ _ _).2 fun g => ?_
    rw [← sub_eq_zero]
    refine hsep _ fun j => ?_
    rw [map_sub, map_smul, hf, h1, (mem_eig _ _ _).1 (h4 j a (hS j x hx)), sub_self]

end Eigen

section Pair

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]

variable (Qp B) in

def pairB (m : V →ₗ[LL] U →ₗ[LL] W) : V ⊗[Qp] B →ₗ[LL] U ⊗[Qp] B →ₗ[LL] W ⊗[Qp] B :=
  (TensorProduct.mk LL _ _).compr₂ (tensorB (TensorProduct.lift m) ∘ₗ prodB)

@[simp] theorem pairB_tmul (m : V →ₗ[LL] U →ₗ[LL] W) (v : V) (u : U) (b c : B) :
    pairB Qp B m (v ⊗ₜ b) (u ⊗ₜ c) = m v u ⊗ₜ (b * c) := by
  simp [pairB, prodB_tmul, tensorB]

theorem pairB_mB (m : V →ₗ[LL] U →ₗ[LL] W) (b : B) (x : V ⊗[Qp] B) (y : U ⊗[Qp] B) :
    pairB Qp B m x (mB LL b y) = mB LL b (pairB Qp B m x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v' c' => simp [mul_left_comm]

theorem act_pairB {ρ : Representation LL G V} {σ : Representation LL G U} {τ : Representation LL G W}
    {m : V →ₗ[LL] U →ₗ[LL] W} (hm : ∀ g v u, m (ρ g v) (σ g u) = τ g (m v u)) (g : G)
    (x : V ⊗[Qp] B) (y : U ⊗[Qp] B) :
    pairB Qp B m (actVB PD ρ g x) (actVB PD σ g y) = actVB PD τ g (pairB Qp B m x y) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, LinearMap.add_apply, ha, hc]
  | tmul v c =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, ha, hc]
    | tmul v' c' => simp [actVB, hm]

theorem pairB_sep [FiniteDimensional LL U] {m : V →ₗ[LL] U →ₗ[LL] W} (hm : Function.Injective m)
    (x : V ⊗[Qp] B) (hx : ∀ y, pairB Qp B m x y = 0) : x = 0 := by
  obtain ⟨r, hr⟩ := m.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hm)
  let u := Module.finBasis LL U
  let s : Fin (finrank LL U) → W →ₗ[LL] V := fun i => r ∘ₗ LinearMap.smulRightₗ (u.coord i)
  have hs : ∀ v, ∑ i, s i (m v (u i)) = v := by
    intro v
    have h1 : ∑ i, LinearMap.smulRightₗ (u.coord i) (m v (u i)) = m v := by
      refine u.ext fun j => ?_
      simp [Finsupp.single_apply]
    simp only [s, LinearMap.comp_apply]
    rw [← map_sum, h1]
    exact LinearMap.congr_fun hr v
  have key : ∀ x : V ⊗[Qp] B, ∑ i, tensorB (s i) (pairB Qp B m x (u i ⊗ₜ 1)) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add a c ha hc => simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib, ha, hc]
    | tmul v c => simp [tensorB, ← TensorProduct.sum_tmul, hs]
  rw [← key x]
  simp [hx]

theorem actVB_mul (ρ : Representation LL G V) (g h : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * h) x = actVB PD ρ g (actVB PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v c => simp [actVB]

theorem isCrys_of_pair [IsDomain B] [FiniteDimensional Qp LL] [FiniteDimensional LL V] [FiniteDimensional LL U]
    [FiniteDimensional LL W] (hf : FracInv PD) (hu : LineUnit PD)
    {ρ : Representation LL G V} {σ : Representation LL G U} {τ : Representation LL G W}
    {m : V →ₗ[LL] U →ₗ[LL] W} (hm : ∀ g v u, m (ρ g v) (σ g u) = τ g (m v u)) (hi : Function.Injective m)
    (hσ : IsCrys PD σ) (hτ : IsCrys PD τ) : IsCrys PD ρ := by
  refine subCrys PD LL hf _ (σ.dual.tprod τ) V ρ ((dualTensorHomEquiv LL U W).symm.toLinearMap ∘ₗ m) ?_
    ((dualTensorHomEquiv LL U W).symm.injective.comp hi)
    (tensorCrys PD LL hf hu _ _ _ _ (dualCrys PD LL hf hu _ _ hσ) hτ)
  intro g v
  apply (dualTensorHomEquiv LL U W).injective
  have h1 := LinearMap.congr_fun (Representation.dualTensorHom_comm σ τ g)
    ((dualTensorHomEquiv LL U W).symm (m v))
  have h2 : ∀ z, dualTensorHom LL U W z = dualTensorHomEquiv LL U W z := fun z => by
    simp [dualTensorHomEquiv]
  simp only [LinearMap.comp_apply, h2, LinearEquiv.apply_symm_apply] at h1
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Representation.tprod_apply, h1]
  ext u
  simp [Representation.linHom_apply, ← hm]

theorem tate_twist_multiplication_intertwines (g : G) (x : LL ⊗[Qp] B) :
    actVB PD (Representation.trivial LL G LL) g (mB LL PD.t x) =
      mB LL PD.t (actVB PD (WeaklyAdmissibleFiltrations.charRep (cycLL PD LL)) g x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v c =>
    simp [actVB, PD.t_act, WeaklyAdmissibleFiltrations.charRep, cycLL, ← Algebra.smul_def, smul_tmul]

include PD in
theorem mB_t_injective : Function.Injective (mB LL PD.t : V ⊗[Qp] B → V ⊗[Qp] B) := by
  obtain ⟨s, hs⟩ := PD.t_unit.exists_left_inv
  intro x y h
  rw [← mB_one (LL := LL) x, ← mB_one (LL := LL) y, ← hs, mB_mul, mB_mul, h]

theorem isCrys_cyc [IsDomain B] [FiniteDimensional Qp LL] (hf : FracInv PD) (hu : LineUnit PD) :
    IsCrys PD (WeaklyAdmissibleFiltrations.charRep (cycLL PD LL)) := by
  obtain ⟨s, hs⟩ := PD.t_unit.exists_right_inv
  rw [isCrys_iff_span PD hf hu]
  refine eq_top_of_tmul _ fun b v => ?_
  have h1 : b ⊗ₜ[Qp] v = (b * PD.t) • (s ⊗ₜ[Qp] v) := by
    rw [smul_tmul', smul_eq_mul, mul_assoc, hs, mul_one]
  rw [h1]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  change v ⊗ₜ[Qp] s ∈ Dcris PD _
  rw [mem_Dcris]
  intro g
  apply mB_t_injective PD (LL := LL)
  rw [← tate_twist_multiplication_intertwines, mB_tmul, hs]
  simp [actVB]

end Pair

section Pot

variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {U : Type} [AddCommGroup U] [Module LL U] [Module Qp U] [IsScalarTower Qp LL U]
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]

theorem actVB_resH (ρ : Representation LL G V) (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ h x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v c => simp [actVB, PC.actB_eq, PotCrysData.resH]

theorem mem_Dpcris (ρ : Representation LL G V) (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ h : PC.H, actVB PC.PD ρ h x = x := by
  simp only [PotCrysData.Dpcris, mem_Dcris, actVB_resH]

theorem act_mem_Dpcris (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] B) (hx : x ∈ PC.Dpcris ρ) :
    actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  rw [mem_Dpcris] at hx ⊢
  intro h
  have h1 := hx ⟨g⁻¹ * h * g, PC.normal.conj_mem' _ h.2 g⟩
  conv_rhs => rw [← h1]
  rw [← actVB_mul, ← actVB_mul]
  congr 2
  group

theorem Eig_eq (ρ : Representation LL G V) (a : PC.Iner →* LLˣ) :
    PC.Eig ρ PC.Iner a = PC.Dpcris ρ ⊓ eig (fun g : PC.Iner => actVB PC.PD ρ g) a := rfl

variable [IsDomain B] [FiniteDimensional Qp LL]

theorem inertia_of_pair [FiniteDimensional LL V] [FiniteDimensional LL U] [FiniteDimensional LL W]
    (hf : FracInv PC.PD') (hu : LineUnit PC.PD')
    {ρ : Representation LL G V} {σ : Representation LL G U} {τ : Representation LL G W}
    {m : V →ₗ[LL] U →ₗ[LL] W} (hm : ∀ g v u, m (ρ g v) (σ g u) = τ g (m v u)) (hi : Function.Injective m)
    (hσ : PC.IsPotCrys σ) (hτ : PC.IsPotCrys τ) {S SU SW : Finset (PC.Iner →* LLˣ)}
    (hU : PC.InertiaThrough σ SU) (hW : PC.InertiaThrough τ SW)
    (hS : ∀ b, b ∈ S ↔ ∃ w ∈ SW, ∃ u ∈ SU, b = w * u⁻¹) :
    PC.IsPotCrys ρ ∧ PC.InertiaThrough ρ S := by
  refine ⟨isCrys_of_pair PC.PD' hf hu (m := m) (fun g v u => hm g v u) hi hσ hτ, ?_, ?_, ?_⟩
  · intro b hb g hg
    obtain ⟨w, hw, u, hu, rfl⟩ := (hS b).1 hb
    simp [hW.1 w hw g hg, hU.1 u hu g hg]
  · intro b hb
    obtain ⟨w, hw, u, hu, rfl⟩ := (hS b).1 hb
    refine Nat.Coprime.coprime_dvd_left (Commute.all w u⁻¹).orderOf_mul_dvd_mul_orderOf ?_
    rw [orderOf_inv]
    exact Nat.Coprime.mul_left (hW.2.1 w hw) (hU.2.1 u hu)
  refine le_antisymm ?_ (iSup₂_le fun _ _ => inf_le_left)
  refine le_iSup_eig (J := {p : (PC.Iner →* LLˣ) × (U ⊗[Qp] B) // p.1 ∈ SU ∧ p.2 ∈ PC.Eig σ PC.Iner p.1})
    S (fun g : PC.Iner => actVB PC.PD ρ g) _ (fun g x hx => act_mem_Dpcris PC ρ g x hx)
    (fun j => (pairB Qp B m).flip j.1.2)
    (fun j g => (((j.1.1 g)⁻¹ : LLˣ) : LL) • actVB PC.PD τ g) ?_ ?_ ?_
  · rintro ⟨⟨a, y⟩, ha, hy⟩ g x
    have h1 := act_pairB PC.PD hm g x y
    rw [(mem_eig _ _ _).1 hy.2 g, map_smul] at h1
    simp only [LinearMap.flip_apply, LinearMap.smul_apply, ← h1, smul_smul, Units.inv_mul, one_smul]
  · rintro ⟨⟨a, y⟩, ha, hy⟩ x hx
    have h1 : pairB Qp B m x y ∈ PC.Dpcris τ := by
      rw [mem_Dpcris]
      intro h
      rw [← act_pairB PC.PD hm, (mem_Dpcris PC _ _).1 hx, (mem_Dpcris PC _ _).1 hy.1]
    rw [hW.2.2] at h1
    refine SetLike.le_def.1 (iSup₂_le fun w hw z hz => ?_) h1
    refine Submodule.mem_iSup_of_mem (w * a⁻¹) (Submodule.mem_iSup_of_mem ((hS _).2 ⟨w, hw, a, ha, rfl⟩) ?_)
    refine (mem_eig _ _ _).2 fun g => ?_
    have h2 : actVB PC.PD τ g z = _ := (mem_eig _ _ _).1 hz.2 g
    simp [h2, smul_smul, mul_comm]
  · intro x hx
    have h1 : PC.Dpcris σ ≤ LinearMap.ker (pairB Qp B m x) := by
      rw [hU.2.2]
      exact iSup₂_le fun a ha y hy => hx ⟨(a, y), ha, hy⟩
    refine pairB_sep hi x fun y => ?_
    induction y using cmp_ind PC.PD' (comparison_bijective PC.PD' hf hu _ hσ) with
    | h0 => simp
    | hadd y y' h h' => rw [map_add, h, h', add_zero]
    | hb b d => rw [pairB_mB, h1 d.2, map_zero]

theorem inertia_cyc (hf : FracInv PC.PD') (hu : LineUnit PC.PD') :
    PC.IsPotCrys (WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD LL)) ∧ PC.InertiaThrough (WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD LL)) {1} := by
  have e : PC.resH (WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD LL)) = WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD' LL) := by
    ext h
    simp [PotCrysData.resH, WeaklyAdmissibleFiltrations.charRep, cycLL, PC.χ_eq]
  refine ⟨?_, by simp, by simp, le_antisymm (fun x hx => ?_) (iSup₂_le fun _ _ => inf_le_left)⟩
  · unfold PotCrysData.IsPotCrys
    rw [e]
    exact isCrys_cyc PC.PD' hf hu
  refine Submodule.mem_iSup_of_mem 1 (Submodule.mem_iSup_of_mem (Finset.mem_singleton_self _) ⟨hx, ?_⟩)
  refine (mem_eig (fun g : PC.Iner => actVB PC.PD (WeaklyAdmissibleFiltrations.charRep (cycLL PC.PD LL)) g) 1 x).2 fun g => ?_
  have h1 : mB LL PC.PD.t x ∈ Dcris PC.PD' (Representation.trivial LL PC.H LL) := by
    rw [mem_Dcris]
    intro h
    rw [← PC.t_eq, tate_twist_multiplication_intertwines, ← e, (mem_Dcris _ _ _).1 hx]
  rw [unit_eq] at h1
  obtain ⟨y, hy⟩ := h1
  apply mB_t_injective PC.PD (LL := LL)
  rw [← tate_twist_multiplication_intertwines, MonoidHom.one_apply, Units.val_one, one_smul, ← hy]
  clear hy
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a c ha hc => simp only [map_add, ha, hc]
  | tmul v c => simp [actVB, g.2 c]

theorem inertia_twist [FiniteDimensional LL V] [FiniteDimensional LL W]
    (hf : FracInv PC.PD') (hu : LineUnit PC.PD') {ρ : Representation LL G V} {ρ' : Representation LL G W}
    {S S' : Finset (PC.Iner →* LLˣ)} (hA : PC.IsPotCrys ρ) (hI : PC.InertiaThrough ρ S)
    (χ : G →* LLˣ) (c : PC.Iner →* LLˣ) (ht : IsTwistRep χ⁻¹ ρ ρ') (hχ : PC.IsPotCrys (WeaklyAdmissibleFiltrations.charRep χ))
    (hc : PC.InertiaThrough (WeaklyAdmissibleFiltrations.charRep χ) {c}) (hs : ∀ b, b ∈ S' ↔ ∃ a ∈ S, b = a * c⁻¹) :
    PC.IsPotCrys ρ' ∧ PC.InertiaThrough ρ' S' := by
  obtain ⟨e, he⟩ := ht
  refine inertia_of_pair _ hf hu (m := (LinearMap.lsmul LL V).flip ∘ₗ e.symm.toLinearMap) ?_ ?_
    hχ hA hc hI fun b => by simpa using hs b
  · intro g v u
    obtain ⟨v, rfl⟩ := e.surjective v
    simp [he, WeaklyAdmissibleFiltrations.charRep, smul_smul, mul_comm, mul_left_comm]
  · intro v v' hv
    simpa using LinearMap.congr_fun hv 1

theorem inertia_dual [FiniteDimensional LL V] [FiniteDimensional LL W]
    (hf : FracInv PC.PD') (hu : LineUnit PC.PD') {ρ : Representation LL G V} {ρ' : Representation LL G W}
    {S S' : Finset (PC.Iner →* LLˣ)} (hA : PC.IsPotCrys ρ) (hI : PC.InertiaThrough ρ S)
    (P : V →ₗ[LL] W →ₗ[LL] LL) (hP : IsDual1 PC.PD ρ ρ' P) (hs : ∀ b, b ∈ S' ↔ ∃ a ∈ S, b = a⁻¹) :
    PC.IsPotCrys ρ' ∧ PC.InertiaThrough ρ' S' := by
  obtain ⟨h1, h2⟩ := inertia_cyc (LL := LL) _ hf hu
  refine inertia_of_pair _ hf hu (m := P.flip) (fun g v u => hP.1 g u v) ?_ hA h1 hI h2
    fun b => by simpa using hs b
  rw [injective_iff_map_eq_zero]
  exact fun y hy => hP.2.2.1 y fun x => LinearMap.congr_fun hy x

end Pot

theorem pcrisTensorL_of_tied : ∀ (L : LocTheory) (A : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (L l)),
    (∀ (l : ℕ) [Fact l.Prime], Nonempty (LocTied l (L l) (A l))) → PcrisTensorL L := by
  intro L AI hT l _ K K' LL h hN hF hS A A' Sig Sig' hA hI
  obtain ⟨T⟩ := hT l
  obtain ⟨C, hfit⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l (L l) (AI l) T
  haveI := LL.2
  haveI := isDomain_of_tied T K
  have hf : FracInv (pc (L l) h hN hF hS).PD' := fun b b' hb hg =>
    fracInv hfit (GlobalTheory.MemLoc.TensorInj.tensorInj l C) K' b b' hb fun g => by
      obtain ⟨g, rfl⟩ := (GKinEquiv h).surjective g
      exact hg g
  have hu : LineUnit (pc (L l) h hN hF hS).PD' := fun b hb hg =>
    lineUnit hfit (GlobalTheory.MemLoc.core_regular l C) K' b hb fun g => by
      obtain ⟨g, rfl⟩ := (GKinEquiv h).surjective g
      exact hg g
  exact ⟨inertia_twist _ hf hu hA hI, inertia_dual _ hf hu hA hI⟩

end GlobalTheory.PcrisTwist
