import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfForallMemFilV

noncomputable section

namespace GlobalTheory.DRFil

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module

theorem exists_fin_basis_subset_of_isField {F M : Type} [CommRing F] (hF : IsField F) [AddCommGroup M]
    [Module F M] [Module.Finite F M] (S : Set M) (h : Submodule.span F S = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n) F M), ∀ i, b i ∈ S := by
  let := hF.toField
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent F S
  have hsp : ⊤ ≤ Submodule.span F (Set.range ((↑) : t → M)) := by
    rw [Subtype.range_coe, hspan, h]
  let bt : Basis t F M := Basis.mk hli hsp
  have : Finite t := Module.Finite.finite_basis bt
  refine ⟨Nat.card t, bt.reindex (Finite.equivFin t), fun i => ?_⟩
  rw [Basis.reindex_apply, Basis.mk_apply]
  exact htS (Subtype.prop _)

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)

def mulRHom (Qp : Type) [Field Qp] (F : Type) [CommRing F] [Algebra Qp F] (V : Type) [AddCommGroup V]
    [Module Qp V] : F →+* Module.End Qp (V ⊗[Qp] F) where
  toFun b := mulR Qp F Qp V b
  map_one' := LinearMap.ext fun x => by
    rw [← sm_one_tmul, ← Algebra.TensorProduct.one_def, sm_one]; rfl
  map_mul' a b := LinearMap.ext fun x => by
    rw [Module.End.mul_apply, ← sm_one_tmul, ← sm_one_tmul, ← sm_one_tmul, ← sm_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  map_zero' := LinearMap.ext fun x => by
    rw [← sm_one_tmul, TensorProduct.tmul_zero, map_zero]
  map_add' a b := LinearMap.ext fun x => by
    rw [LinearMap.add_apply, ← sm_one_tmul, ← sm_one_tmul, ← sm_one_tmul, TensorProduct.tmul_add,
      map_add, LinearMap.add_apply]

theorem spans_dual_base {V : Type} [AddCommGroup V] [Module Qp V] [FiniteDimensional Qp V]
    (ρ : Representation Qp G V) {V' : Type} [AddCommGroup V'] [Module Qp V']
    (ρ' : Representation Qp G V') (β : V →ₗ[Qp] V' →ₗ[Qp] Qp) (hF : IsField F)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hb : Function.Bijective β.flip)
    (h : Spans PD ρ) : Spans PD ρ' := by
  classical
  let _ : Module F (V ⊗[Qp] F) := Module.compHom (V ⊗[Qp] F) (mulRHom Qp F V)
  have hsm : ∀ (c : F) (y : V ⊗[Qp] F), c • y = mulR Qp F Qp V c y := fun _ _ => rfl
  let bV := Module.finBasis Qp V
  let κ : Fin (Module.finrank Qp V) → (V ⊗[Qp] F) →ₗ[Qp] F := fun k =>
    (TensorProduct.lid Qp F).toLinearMap ∘ₗ TensorProduct.map (bV.coord k) LinearMap.id
  have hκ : ∀ k (v : V) (c : F), κ k (v ⊗ₜ c) = bV.coord k v • c := fun k v c => by simp [κ]
  have hκmul : ∀ k (c : F) (y : V ⊗[Qp] F), κ k (c • y) = c * κ k y := by
    intro k c y
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero, mul_zero]
    | tmul v a => simp only [hsm, mulR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, hκ, mul_smul_comm]
    | add y₁ y₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂, mul_add]
  have hdec : ∀ y : V ⊗[Qp] F, y = ∑ k, κ k y • (bV k ⊗ₜ[Qp] (1 : F)) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      simp only [hκ, hsm, mulR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, mul_one]
      conv_lhs => rw [← bV.sum_repr v]
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [TensorProduct.smul_tmul, Basis.coord_apply]
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add, add_smul, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) h₁ h₂
  have hspanD : Submodule.span F (DdR PD ρ : Set (V ⊗[Qp] F)) = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨m, b, d, hd, rfl⟩ := h y
    exact Submodule.sum_mem _ fun i _ => by
      rw [← hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hd i))
  have hfin : Module.Finite F (V ⊗[Qp] F) := by
    refine ⟨⟨Finset.univ.image fun k => bV k ⊗ₜ[Qp] (1 : F), eq_top_iff.2 fun y _ => ?_⟩⟩
    rw [hdec y]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  obtain ⟨m, E, hE⟩ := exists_fin_basis_subset_of_isField hF (DdR PD ρ : Set (V ⊗[Qp] F)) hspanD
  have hinv : ∀ y : V ⊗[Qp] F, y ∈ DdR PD ρ ↔ ∀ g, actVdR PD ρ g y = y := by
    intro y
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hinv' : ∀ y : V' ⊗[Qp] F, y ∈ DdR PD ρ' ↔ ∀ g, actVdR PD ρ' g y = y := by
    intro y
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
  have hact : ∀ g (c : F) (y : V ⊗[Qp] F),
      actVdR PD ρ g (c • y) = PD.actdR g c • actVdR PD ρ g y := by
    intro g c y
    induction y using TensorProduct.induction_on with
    | zero => simp only [smul_zero, map_zero]
    | tmul v a => simp [hsm, mulR, actVdR]
    | add y₁ y₂ h₁ h₂ => simp only [smul_add, map_add, h₁, h₂]
  have hcoord : ∀ g i (y : V ⊗[Qp] F), E.coord i (actVdR PD ρ g y) = PD.actdR g (E.coord i y) := by
    intro g i y
    have h1 : actVdR PD ρ g y = ∑ j, PD.actdR g (E.repr y j) • E j := by
      conv_lhs => rw [← E.sum_repr y]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hact, (hinv _).1 (hE j) g]
    rw [h1, map_sum]
    simp [Basis.coord_apply, Finsupp.single_apply]
  let e := LinearEquiv.ofBijective β.flip hb
  let w : Fin (Module.finrank Qp V) → V' := fun j => e.symm (bV.coord j)
  have hw : ∀ x j, β x (w j) = bV.coord j x := fun x j => by
    have h1 : β.flip (w j) = bV.coord j := e.apply_symm_apply (bV.coord j)
    exact LinearMap.congr_fun h1 x
  have hw' : ∀ v' : V', v' = ∑ j, β (bV j) v' • w j := by
    intro v'
    apply hb.1
    refine LinearMap.ext fun x => ?_
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, hw, smul_eq_mul]
    conv_lhs => rw [← bV.sum_repr x]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Basis.coord_apply]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  let π : V → (V' ⊗[Qp] F) →ₗ[Qp] F := fun x =>
    (TensorProduct.lid Qp F).toLinearMap ∘ₗ TensorProduct.map (β x) LinearMap.id
  have hπ : ∀ x v' (c : F), π x (v' ⊗ₜ c) = β x v' • c := fun x v' c => by simp [π]
  have hπmul : ∀ x (c : F) z, π x (mulR Qp F Qp V' c z) = c * π x z := by
    intro x c z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero, mul_zero]
    | tmul v' a => simp only [mulR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
        LinearMap.mulLeft_apply, hπ, mul_smul_comm]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂, mul_add]
  have hπact : ∀ g x z, π (ρ g x) (actVdR PD ρ' g z) = PD.actdR g (π x z) := by
    intro g x z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v' a =>
      simp [actVdR, hπ, hβ, Algebra.smul_def, IsScalarTower.algebraMap_apply Qp K F]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  have hzdec : ∀ z : V' ⊗[Qp] F, z = ∑ j, w j ⊗ₜ π (bV j) z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul v' a =>
      simp only [hπ]
      conv_lhs => rw [hw' v']
      rw [TensorProduct.sum_tmul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.smul_tmul]
    | add z₁ z₂ h₁ h₂ =>
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) h₁ h₂
  have hπext : ∀ z z' : V' ⊗[Qp] F, (∀ x, π x z = π x z') → z = z' := by
    intro z z' hz
    rw [hzdec z, hzdec z']
    simp only [hz]
  let d' : Fin m → V' ⊗[Qp] F := fun i => ∑ j, w j ⊗ₜ[Qp] E.coord i (bV j ⊗ₜ[Qp] (1 : F))
  have hπd' : ∀ x i, π x (d' i) = E.coord i (x ⊗ₜ[Qp] (1 : F)) := by
    intro x i
    rw [hdec (x ⊗ₜ[Qp] (1 : F)), map_sum]
    simp only [d', map_sum, hπ, hw, hκ, map_smul, smul_eq_mul, smul_one_mul]
  have hd'inv : ∀ i g, actVdR PD ρ' g (d' i) = d' i := by
    intro i g
    apply hπext
    intro x
    have hx : ρ g (ρ g⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [← hx, hπact, hπd', hπd', ← hcoord]
    simp [actVdR]
  intro y'
  let c : Fin m → F := fun i => ∑ k, π (bV k) y' * κ k (E i)
  refine ⟨m, c, d', fun i => (hinv' _).2 (hd'inv i), ?_⟩
  apply hπext
  intro x
  rw [map_sum]
  simp only [hπmul, hπd']
  have hx1 : x ⊗ₜ[Qp] (1 : F) = ∑ i, E.coord i (x ⊗ₜ[Qp] (1 : F)) • E i := by
    simp only [Basis.coord_apply]
    exact (E.sum_repr _).symm
  have key : ∀ k, κ k (x ⊗ₜ[Qp] (1 : F)) = ∑ i, E.coord i (x ⊗ₜ[Qp] (1 : F)) * κ k (E i) := by
    intro k
    conv_lhs => rw [hx1]
    rw [map_sum]
    simp only [hκmul]
  calc π x y' = ∑ k, bV.coord k x • π (bV k) y' := by
        conv_lhs => rw [hzdec y']
        simp only [map_sum, hπ, hw]
    _ = ∑ k, π (bV k) y' * κ k (x ⊗ₜ[Qp] (1 : F)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hκ, mul_smul_comm, mul_one]
    _ = ∑ k, π (bV k) y' * ∑ i, E.coord i (x ⊗ₜ[Qp] (1 : F)) * κ k (E i) := by
        simp only [key]
    _ = ∑ i, c i * E.coord i (x ⊗ₜ[Qp] (1 : F)) := by
        simp only [c, Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

variable (Qp) in

def resRep (ρ : Representation LL G V) : Representation Qp G V where
  toFun g := (ρ g).restrictScalars Qp
  map_one' := LinearMap.ext fun x => by simp
  map_mul' a b := LinearMap.ext fun x => by simp

theorem spans_resRep_iff (ρ : Representation LL G V) : Spans PD (resRep Qp ρ) ↔ Spans PD ρ := by
  have hm : ∀ (b : F) (y : V ⊗[Qp] F), mulR Qp F Qp V b y = mulR Qp F LL V b y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v c => simp [mulR]
    | add x z hx hz => rw [map_add, map_add, hx, hz]
  have hd : ∀ y : V ⊗[Qp] F, y ∈ DdR PD (resRep Qp ρ) ↔ y ∈ DdR PD ρ := by
    intro y
    have ha : ∀ g, actVdR PD (resRep Qp ρ) g y = actVdR PD ρ g y := by
      intro g
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v c => simp [actVdR, resRep]
      | add x z hx hz => rw [map_add, map_add, hx, hz]
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, ha]
  unfold Spans
  simp only [hd, hm]

theorem spans_dual [FiniteDimensional Qp LL] [CharZero Qp] [FiniteDimensional LL V]
    (ρ : Representation LL G V)
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL) (hF : IsField F)
    (hβ : ∀ g x y, β (ρ g x) (ρ' g y) = β x y) (hb : Function.Bijective β.flip)
    (h : Spans PD ρ) : Spans PD ρ' := by
  have hVf : FiniteDimensional Qp V := Module.Finite.trans LL V
  let e := LinearEquiv.ofBijective β.flip hb
  have hV'L : FiniteDimensional LL V' := Module.Finite.equiv e.symm
  have hV'f : FiniteDimensional Qp V' := Module.Finite.trans LL V'
  let tr : LL →ₗ[Qp] Qp := Algebra.trace Qp LL
  let β₀ : V →ₗ[Qp] V' →ₗ[Qp] Qp := LinearMap.mk₂ Qp (fun x y => tr (β x y))
    (fun x₁ x₂ y => by simp only [map_add, LinearMap.add_apply])
    (fun c x y => by
      simp only [LinearMap.map_smul_of_tower, LinearMap.smul_apply, map_smul])
    (fun x y₁ y₂ => by simp only [map_add])
    (fun c x y => by simp only [LinearMap.map_smul_of_tower, map_smul])
  have hβ₀ : ∀ g x y, β₀ (resRep Qp ρ g x) (resRep Qp ρ' g y) = β₀ x y := by
    intro g x y
    show tr (β (ρ g x) (ρ' g y)) = tr (β x y)
    rw [hβ]
  have hinj : Function.Injective β₀.flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : ∀ x, β x y = 0 := by
      intro x
      refine (traceForm_nondegenerate Qp LL).1 (β x y) (fun c => ?_)
      have := LinearMap.congr_fun hy (c • x)
      simp only [LinearMap.flip_apply, LinearMap.zero_apply] at this
      rw [Algebra.traceForm_apply, mul_comm]
      change tr (c * β x y) = 0
      rw [← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.map_smul]
      exact this
    apply hb.1
    rw [map_zero]
    ext x
    exact h1 x
  have hrank : Module.finrank Qp V' = Module.finrank Qp (V →ₗ[Qp] Qp) := by
    rw [← Module.finrank_mul_finrank Qp LL V', LinearEquiv.finrank_eq e,
      Subspace.dual_finrank_eq, Module.finrank_mul_finrank]
    exact (Subspace.dual_finrank_eq (K := Qp) (V := V)).symm
  have hb₀ : Function.Bijective β₀.flip :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hinj⟩
  have h₀ : Spans PD (resRep Qp ρ) := (spans_resRep_iff PD ρ).2 h
  exact (spans_resRep_iff PD ρ').1 (spans_dual_base PD (resRep Qp ρ) (resRep Qp ρ') β₀ hF hβ₀ hb₀ h₀)

end Period

theorem spans_dual_of_spans : ∀ {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F] [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F] (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL] [FiniteDimensional Qp LL] [FiniteDimensional Qp K] [CharZero Qp] {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [FiniteDimensional LL V] (ρ : Representation LL G V) {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V'] [FiniteDimensional LL V'] (ρ' : Representation LL G V') (β : V →ₗ[LL] V' →ₗ[LL] LL), IsField F → (∀ g x y, β (ρ g x) (ρ' g y) = β x y) → Function.Bijective β.flip → Spans PD ρ → Spans PD ρ' := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B F _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _ _ V _ _ _ _ _ ρ V' _ _ _ _ _ ρ' β hF hβ hb h
  exact spans_dual PD ρ ρ' β hF hβ hb h

end GlobalTheory.DRFil
