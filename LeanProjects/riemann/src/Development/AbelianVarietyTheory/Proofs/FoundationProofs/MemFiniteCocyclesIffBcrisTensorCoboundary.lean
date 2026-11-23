import Mathlib
import Formalism.WeaklyAdmissibleFiltrations.Statement

noncomputable section

namespace GlobalTheory.CoeffExt

open Formalism.WeaklyAdmissibleFiltrations TensorProduct Module

section Linear

variable {R : Type} [Ring R] {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module R W]
  [Module R W'] {ι : Type}

def subEquiv (E : W' ≃ₗ[R] (ι → W)) (S' : Submodule R W') (S : Submodule R W)
    (h : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) : ↥S' ≃ₗ[R] (ι → ↥S) where
  toFun x i := ⟨E x i, (h x).1 x.2 i⟩
  invFun y := ⟨E.symm fun i => (y i : W), (h _).2 fun i => by simp⟩
  map_add' x y := by funext i; apply Subtype.ext; simp
  map_smul' c x := by funext i; apply Subtype.ext; simp
  left_inv x := by apply Subtype.ext; simp
  right_inv y := by funext i; apply Subtype.ext; simp

end Linear

section Length

variable {O O' : Type} [CommRing O] [CommRing O'] [Algebra O O'] {W W' : Type} [AddCommGroup W]
  [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W'] [IsScalarTower O O' W'] {ι : Type}
  [Fintype ι]

theorem length_subquot (E : W' ≃ₗ[O] (ι → W)) (S' N' : Submodule O' W') (S N : Submodule O W)
    (hS : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) (hN : ∀ x, x ∈ N' ↔ ∀ i, E x i ∈ N) :
    Module.length O (↥S' ⧸ N'.comap S'.subtype) =
      Fintype.card ι * Module.length O (↥S ⧸ N.comap S.subtype) := by
  classical

  let ψ : ι → (↥S' →ₗ[O] ↥S) := fun i => LinearMap.codRestrict S
    ((LinearMap.proj i ∘ₗ E.toLinearMap) ∘ₗ (S'.subtype.restrictScalars O)) (fun x => (hS x).1 x.2 i)
  let Φ : ↥S' →ₗ[O] (ι → ↥S ⧸ N.comap S.subtype) :=
    LinearMap.pi fun i => (N.comap S.subtype).mkQ ∘ₗ ψ i
  have hψ : ∀ (x : ↥S') i, ((ψ i x : ↥S) : W) = E x i := fun _ _ => rfl
  have hΦ : ∀ x : ↥S', Φ x = 0 ↔ x ∈ N'.comap S'.subtype := by
    intro x
    rw [Submodule.mem_comap, Submodule.coe_subtype, hN, funext_iff]
    simp only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, hψ]
  have hsurj : Function.Surjective Φ := by
    intro y
    choose s hs using fun i => Submodule.Quotient.mk_surjective _ (y i)
    have hw : E.symm (fun i => (s i : W)) ∈ S' := (hS _).2 (by simp)
    refine ⟨⟨_, hw⟩, ?_⟩
    funext i
    rw [← hs i]
    simp only [Φ, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply]
    congr 1
    apply Subtype.ext
    rw [hψ]
    simp
  have hker : LinearMap.ker Φ = (N'.comap S'.subtype).restrictScalars O := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem]
    exact hΦ x
  let e : (↥S' ⧸ N'.comap S'.subtype) ≃ₗ[O] (ι → ↥S ⧸ N.comap S.subtype) :=
    (Submodule.Quotient.restrictScalarsEquiv O (N'.comap S'.subtype)).symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ Φ.quotKerEquivOfSurjective hsurj
  rw [e.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]

end Length

section Tensor

variable {Qp : Type} [Field Qp] {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
  [Algebra Qp LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
  [Module LL' V'] [IsScalarTower Qp LL' V']
  {ι : Type} [Fintype ι] [DecidableEq ι] (E : V' ≃ₗ[LL] (ι → V))

def tensCoord (C : Type) [AddCommGroup C] [Module Qp C] :
    V' ⊗[Qp] C ≃ₗ[LL] (ι → V ⊗[Qp] C) :=
  LinearEquiv.ofLinearMap
    (LinearMap.pi fun i => AlgebraTensorModule.map (LinearMap.proj i ∘ₗ E.toLinearMap) LinearMap.id)
    (∑ i, AlgebraTensorModule.map (E.symm.toLinearMap ∘ₗ LinearMap.single LL (fun _ => V) i)
      LinearMap.id ∘ₗ LinearMap.proj i)
    (by
      refine LinearMap.pi_ext' fun j => ?_
      refine AlgebraTensorModule.ext fun v c => ?_
      funext i
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.id_apply,
        LinearMap.single_apply, LinearMap.proj_apply]
      rw [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
      by_cases h : i = j
      · subst h; simp
      · simp [Pi.single_eq_of_ne h])
    (by
      refine AlgebraTensorModule.ext fun v c => ?_
      simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.id_apply,
        LinearMap.proj_apply, LinearMap.pi_apply, AlgebraTensorModule.map_tmul,
        LinearMap.single_apply, LinearEquiv.coe_coe]
      rw [← sum_tmul, ← map_sum, Finset.univ_sum_single, E.symm_apply_apply])

@[simp] theorem tensCoord_tmul {C : Type} [AddCommGroup C] [Module Qp C] (v : V') (c : C) (i : ι) :
    tensCoord E C (v ⊗ₜ[Qp] c) i = E v i ⊗ₜ[Qp] c := rfl

theorem tensCoord_map {C D : Type} [AddCommGroup C] [Module Qp C] [AddCommGroup D] [Module Qp D]
    (φ' : V' →ₗ[LL'] V') (φ : V →ₗ[LL] V) (h : ∀ x i, E (φ' x) i = φ (E x i)) (ψ : C →ₗ[Qp] D)
    (x : V' ⊗[Qp] C) (i : ι) :
    tensCoord E D (AlgebraTensorModule.map φ' ψ x) i =
      AlgebraTensorModule.map φ ψ (tensCoord E C x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [h]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

end Tensor

section Period

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [IsScalarTower LL LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}

omit [Algebra LL LL'] [IsScalarTower LL LL' V'] in
theorem tensCoord_actVB (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (g : G) (x : V' ⊗[Qp] B)
    (i : ι) : tensCoord E B (actVB PD ρ' g x) i = actVB PD ρ g (tensCoord E B x i) := by
  unfold actVB
  exact tensCoord_map E (ρ' g) (ρ g) (hE g) _ x i

omit [Algebra LL LL'] [IsScalarTower LL LL' V'] in
theorem tensCoord_actVdR (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (g : G) (x : V' ⊗[Qp] BdR)
    (i : ι) : tensCoord E BdR (actVdR PD ρ' g x) i = actVdR PD ρ g (tensCoord E BdR x i) := by
  unfold actVdR
  exact tensCoord_map E (ρ' g) (ρ g) (hE g) _ x i

omit [Algebra LL LL'] [IsScalarTower LL LL' V'] in
theorem mem_Dcris_iff (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (x : V' ⊗[Qp] B) :
    x ∈ Dcris PD ρ' ↔ ∀ i, tensCoord E B x i ∈ Dcris PD ρ := by
  have key : ∀ {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
      (r : Representation LL G W) (y : W ⊗[Qp] B), y ∈ Dcris PD r ↔ ∀ g, actVB PD r g y = y := by
    intro W _ _ _ _ r y
    simp [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]
  have key' : x ∈ Dcris PD ρ' ↔ ∀ g, actVB PD ρ' g x = x := by
    simp [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]
  rw [key']
  constructor
  · intro hx i
    rw [key]
    intro g
    rw [← tensCoord_actVB PD hE g x i, hx g]
  · intro hx g
    apply (tensCoord E B).injective
    funext i
    rw [tensCoord_actVB PD hE]
    exact (key _ _).1 (hx i) g

theorem finrank_fun' {F M : Type} [Field F] [AddCommGroup M] [Module F M] (ι : Type) [Fintype ι] :
    finrank F (ι → M) = Fintype.card ι * finrank F M := by
  by_cases hM : Module.Finite F M
  · simp [Module.finrank_pi_fintype]
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i⟩⟩
    · rw [Module.finrank_zero_of_subsingleton]
      simp
    ·
      have hnot : ¬ Module.Finite F (ι → M) := fun h =>
        hM (Module.Finite.of_surjective (LinearMap.proj i : (ι → M) →ₗ[F] M)
          (fun m => ⟨fun _ => m, rfl⟩))
      rw [Module.finrank_of_not_finite hnot, Module.finrank_of_not_finite hM, mul_zero]

theorem isCrys_ext (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
    (hι : finrank LL LL' = Fintype.card ι) [Nonempty ι] (h : IsCrys PD ρ) : IsCrys PD ρ' := by
  unfold IsCrys at h ⊢
  have hn : 0 < Fintype.card ι := Fintype.card_pos

  let eD : ↥((Dcris PD ρ').restrictScalars LL) ≃ₗ[LL] (ι → ↥(Dcris PD ρ)) :=
    subEquiv (tensCoord E B) _ _ (fun x => mem_Dcris_iff PD hE x)
  have h1 : finrank LL ↥(Dcris PD ρ') = Fintype.card ι * finrank LL ↥(Dcris PD ρ) := by
    have h0 := eD.finrank_eq
    rw [finrank_fun'] at h0
    exact h0
  have h2 : finrank LL V' = Fintype.card ι * finrank LL V := by
    rw [E.finrank_eq, finrank_fun']
  have t1 := Module.finrank_mul_finrank LL LL' ↥(Dcris PD ρ')
  have t2 := Module.finrank_mul_finrank LL LL' V'
  rw [hι] at t1 t2
  have e1 : finrank LL' ↥(Dcris PD ρ') = finrank Qp K₀ * finrank LL V :=
    Nat.eq_of_mul_eq_mul_left hn (by rw [t1, h1, h])
  have e2 : finrank LL' V' = finrank LL V := Nat.eq_of_mul_eq_mul_left hn (by rw [t2, h2])
  rw [e1, e2]

theorem mem_FildR_iff (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (τ : K →ₐ[Qp] LL)
    (τ' : K →ₐ[Qp] LL') (hτ : ∀ c, τ' c = algebraMap LL LL' (τ c)) (a : ℤ) (x : V' ⊗[Qp] BdR) :
    x ∈ FildR PD ρ' τ' a ↔ ∀ i, tensCoord E BdR x i ∈ FildR PD ρ τ a := by

  have hA : ∀ y : V' ⊗[Qp] BdR, y ∈ DdR PD ρ' ↔ ∀ i, tensCoord E BdR y i ∈ DdR PD ρ := by
    intro y
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    constructor
    · intro hy i g
      rw [← tensCoord_actVdR PD hE g y i, hy g]
    · intro hy g
      apply (tensCoord E BdR).injective
      funext i
      rw [tensCoord_actVdR PD hE]
      exact hy i g

  have hmul : ∀ (c : K) (y : V' ⊗[Qp] BdR) i,
      tensCoord E BdR (mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL') c y) i =
        mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c (tensCoord E BdR y i) :=
    fun c y i => tensCoord_map E LinearMap.id LinearMap.id (fun _ _ => rfl) _ y i
  have hsm : ∀ (c : K) (y : V' ⊗[Qp] BdR) i,
      tensCoord E BdR (τ' c • y) i = τ c • tensCoord E BdR y i := by
    intro c y i
    rw [hτ, algebraMap_smul, map_smul, Pi.smul_apply]
  have hB : ∀ y : V' ⊗[Qp] BdR, (∀ c : K, mulVdR (K := K) (BdR := BdR) (V := V') (LL := LL') c y =
      τ' c • y) ↔ ∀ i, ∀ c : K, mulVdR (K := K) (BdR := BdR) (V := V) (LL := LL) c
        (tensCoord E BdR y i) = τ c • tensCoord E BdR y i := by
    intro y
    constructor
    · intro hy i c
      rw [← hmul, ← hsm, hy c]
    · intro hy c
      apply (tensCoord E BdR).injective
      funext i
      rw [hmul, hsm]
      exact hy i c

  have hC : ∀ y : V' ⊗[Qp] BdR, y ∈ FilV PD (LL := LL') (V := V') a ↔
      ∀ i, tensCoord E BdR y i ∈ FilV PD (LL := LL) (V := V) a := by
    intro y
    have hmap : ∀ (z : V' ⊗[Qp] ↥((PD.Fil a).restrictScalars Qp)) i,
        tensCoord E BdR (AlgebraTensorModule.map (LinearMap.id : V' →ₗ[LL'] V')
          ((PD.Fil a).restrictScalars Qp).subtype z) i =
        AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) ((PD.Fil a).restrictScalars Qp).subtype
          (tensCoord E _ z i) :=
      fun z i => tensCoord_map E LinearMap.id LinearMap.id (fun _ _ => rfl) _ z i
    simp only [FilV, LinearMap.mem_range]
    constructor
    · rintro ⟨z, rfl⟩ i
      exact ⟨tensCoord E _ z i, (hmap z i).symm⟩
    · intro hy
      choose z hz using hy
      refine ⟨(tensCoord E _).symm z, ?_⟩
      apply (tensCoord E BdR).injective
      funext i
      rw [hmap, LinearEquiv.apply_symm_apply, hz i]
  simp only [FildR, DdRE, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  rw [hA, hB, hC]
  simp only [forall_and]

theorem jumpsInV_ext (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (τ : K →ₐ[Qp] LL)
    (τ' : K →ₐ[Qp] LL') (hτ : ∀ c, τ' c = algebraMap LL LL' (τ c)) (S : Set ℤ)
    (h : JumpsInV PD ρ τ S) : JumpsInV PD ρ' τ' S := by
  unfold JumpsInV IsJumpV at *
  intro a ha
  apply h a
  intro heq
  apply ha
  ext x
  rw [mem_FildR_iff PD hE τ τ' hτ, mem_FildR_iff PD hE τ τ' hτ, heq]

end Period

section Cochains

variable {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  {V V' : Type} [AddCommGroup V] [AddCommGroup V'] [Module LL V] [Module LL V'] [Module O V]
  [Module O V'] [IsScalarTower O LL V] [IsScalarTower O LL V'] {ι : Type}

def funCoord (O : Type) [CommRing O] [Algebra O LL] [Module O V] [Module O V']
    [IsScalarTower O LL V] [IsScalarTower O LL V'] (G : Type) (E : V' ≃ₗ[LL] (ι → V)) :
    (G → V') ≃ₗ[O] (ι → G → V) where
  toFun c i g := E (c g) i
  invFun c g := E.symm fun i => c i g
  map_add' x y := by funext i g; simp
  map_smul' a x := by
    funext i g
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [← algebraMap_smul LL a, map_smul, Pi.smul_apply, algebraMap_smul]
  left_inv x := by funext g; simp
  right_inv y := by funext i g; simp

@[simp] theorem funCoord_apply (G : Type) (E : V' ≃ₗ[LL] (ι → V)) (c : G → V') (i : ι) (g : G) :
    funCoord O G E c i g = E (c g) i := rfl

end Cochains

section Lat

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL] [Algebra Qp LL']
    {O O' : Type} [CommRing O] [CommRing O'] [Algebra O LL] [Algebra O' LL']
    {ι : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace G]

section One

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    [Module LL' V'] [IsScalarTower Qp LL' V'] [Module O V'] [IsScalarTower O LL V']
    [Module O' V'] [IsScalarTower O' LL' V']
    [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL' V']
    {ρ : Representation LL G V} {ρ' : Representation LL' G V'}
    {E : V' ≃ₗ[LL] (ι → V)} {L : Lattice (O := O) ρ} {L' : Lattice (O := O') ρ'}

theorem mem_continuous_cocycles_iff_coords (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (hc : Continuous E)
    (hs : Continuous E.symm) (c : G → V') :
    c ∈ continuousCocycles ρ' ↔ ∀ i, funCoord O G E c i ∈ continuousCocycles ρ := by
  change (Continuous c ∧ ∀ g h, c (g * h) = c g + ρ' g (c h)) ↔
    ∀ i, (Continuous (funCoord O G E c i) ∧ ∀ g h, funCoord O G E c i (g * h) =
      funCoord O G E c i g + ρ g (funCoord O G E c i h))
  simp only [funCoord_apply]
  constructor
  · rintro ⟨hcont, hcoc⟩ i
    refine ⟨(continuous_apply i).comp (hc.comp hcont), fun g h => ?_⟩
    rw [hcoc, map_add, Pi.add_apply, hE]
  · intro H
    refine ⟨?_, fun g h => ?_⟩
    · have hcont : Continuous fun g => E.symm (fun i => E (c g) i) :=
        hs.comp (continuous_pi fun i => (H i).1)
      simpa using hcont
    · apply E.injective
      funext i
      rw [map_add, Pi.add_apply, (H i).2 g h, hE]

theorem mem_finiteCocycles_iff_bcrisTensor_coboundary (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (hc : Continuous E)
    (hs : Continuous E.symm) (c : G → V') :
    c ∈ finiteCocycles PD ρ' ↔ ∀ i, funCoord O G E c i ∈ finiteCocycles PD ρ := by
  change (c ∈ continuousCocycles ρ' ∧ ∃ x : V' ⊗[Qp] B, ∀ g, c g ⊗ₜ[Qp] (1 : B) = actVB PD ρ' g x - x) ↔
    ∀ i, (funCoord O G E c i ∈ continuousCocycles ρ ∧
      ∃ x : V ⊗[Qp] B, ∀ g, funCoord O G E c i g ⊗ₜ[Qp] (1 : B) = actVB PD ρ g x - x)
  rw [mem_continuous_cocycles_iff_coords (O := O) hE hc hs]
  simp only [funCoord_apply]
  constructor
  · rintro ⟨hz, x, hx⟩ i
    refine ⟨hz i, tensCoord E B x i, fun g => ?_⟩
    rw [← tensCoord_tmul E (c g) (1 : B) i, hx g, map_sub, Pi.sub_apply, tensCoord_actVB PD hE]
  · intro H
    have hz : ∀ i, funCoord O G E c i ∈ continuousCocycles ρ := fun i => (H i).1
    choose x hx using fun i => (H i).2
    refine ⟨hz, (tensCoord E B).symm x, fun g => ?_⟩
    apply (tensCoord E B).injective
    funext i
    rw [tensCoord_tmul, map_sub, Pi.sub_apply, tensCoord_actVB PD hE, LinearEquiv.apply_symm_apply,
      hx i g]

theorem mem_Z1fT_iff (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (hc : Continuous E)
    (hs : Continuous E.symm) (hL : ∀ x, x ∈ L'.T ↔ ∀ i, E x i ∈ L.T) (c : G → V') :
    c ∈ latticeFiniteCocycles PD L' ↔ ∀ i, funCoord O G E c i ∈ latticeFiniteCocycles PD L := by
  simp only [latticeFiniteCocycles, latticeCocycles, Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_pi,
    Set.mem_univ, true_implies]
  rw [mem_continuous_cocycles_iff_coords (O := O) hE hc hs, mem_finiteCocycles_iff_bcrisTensor_coboundary (O := O) PD hE hc hs]
  simp only [hL, funCoord_apply]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩ i
    exact ⟨⟨h1 i, fun g => h2 g i⟩, h3 i⟩
  · intro H
    exact ⟨⟨fun i => (H i).1.1, fun g i => (H i).1.2 g⟩, fun i => (H i).2⟩

omit [TopologicalSpace G] [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
  [TopologicalSpace V'] [ContinuousAdd V'] [ContinuousConstSMul LL' V'] [Fintype ι]
  [DecidableEq ι] in
theorem mem_B1T_iff (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
    (hL : ∀ x, x ∈ L'.T ↔ ∀ i, E x i ∈ L.T) (c : G → V') :
    c ∈ latticeCoboundaries L' ↔ ∀ i, funCoord O G E c i ∈ latticeCoboundaries L := by
  simp only [latticeCoboundaries, Submodule.mem_map, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨x, hx, rfl⟩ i
    refine ⟨E x i, (hL x).1 hx i, ?_⟩
    funext g
    simp [cob, hE]
  · intro H
    choose x hx hcx using H
    refine ⟨E.symm x, (hL _).2 (by simpa using hx), ?_⟩
    funext g
    apply E.injective
    funext i
    have h1 := congrFun (hcx i) g
    simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, funCoord_apply]
      at h1 ⊢
    rw [map_sub, Pi.sub_apply, hE, LinearEquiv.apply_symm_apply, h1]

end One

section Two

variable {V₁ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
    [Module O V₁] [IsScalarTower O LL V₁]
    [TopologicalSpace V₁] [ContinuousAdd V₁] [ContinuousConstSMul LL V₁]
    {V₁' : Type} [AddCommGroup V₁'] [Module LL V₁'] [Module Qp V₁'] [IsScalarTower Qp LL V₁']
    [Module LL' V₁'] [IsScalarTower Qp LL' V₁'] [Module O V₁'] [IsScalarTower O LL V₁']
    [Module O' V₁'] [IsScalarTower O' LL' V₁']
    [TopologicalSpace V₁'] [ContinuousAdd V₁'] [ContinuousConstSMul LL' V₁']
    {ρ₁ : Representation LL G V₁} {ρ₁' : Representation LL' G V₁'}
    {E₁ : V₁' ≃ₗ[LL] (ι → V₁)} {L₁ : Lattice (O := O) ρ₁} {L₁' : Lattice (O := O') ρ₁'}
    {V₂ : Type} [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
    [Module O V₂] [IsScalarTower O LL V₂]
    [TopologicalSpace V₂] [ContinuousAdd V₂] [ContinuousConstSMul LL V₂]
    {V₂' : Type} [AddCommGroup V₂'] [Module LL V₂'] [Module Qp V₂'] [IsScalarTower Qp LL V₂']
    [Module LL' V₂'] [IsScalarTower Qp LL' V₂'] [Module O V₂'] [IsScalarTower O LL V₂']
    [Module O' V₂'] [IsScalarTower O' LL' V₂']
    [TopologicalSpace V₂'] [ContinuousAdd V₂'] [ContinuousConstSMul LL' V₂']
    {ρ₂ : Representation LL G V₂} {ρ₂' : Representation LL' G V₂'}
    {E₂ : V₂' ≃ₗ[LL] (ι → V₂)} {L₂ : Lattice (O := O) ρ₂} {L₂' : Lattice (O := O') ρ₂'}
    (F : LatHom L₁ L₂) (F' : LatHom L₁' L₂')

theorem mem_ImF_iff (hE₁ : ∀ g x i, E₁ (ρ₁' g x) i = ρ₁ g (E₁ x i)) (hc₁ : Continuous E₁)
    (hs₁ : Continuous E₁.symm) (hL₁ : ∀ x, x ∈ L₁'.T ↔ ∀ i, E₁ x i ∈ L₁.T)
    (hE₂ : ∀ g x i, E₂ (ρ₂' g x) i = ρ₂ g (E₂ x i))
    (hL₂ : ∀ x, x ∈ L₂'.T ↔ ∀ i, E₂ x i ∈ L₂.T)
    (hF : ∀ x i, E₂ (F'.f x) i = F.f (E₁ x i)) (c : G → V₂') :
    c ∈ F'.ImF PD ↔ ∀ i, funCoord O G E₂ c i ∈ F.ImF PD := by
  have post_coord : ∀ (x : G → V₁') i,
      funCoord O G E₂ (F'.post x) i = F.post (funCoord O G E₁ x i) := by
    intro x i
    funext g
    simp [LatHom.post, hF]
  unfold LatHom.ImF
  constructor
  · intro hc i
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hc
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    refine Submodule.mem_sup.2 ⟨F.post (funCoord O G E₁ x i),
      Submodule.mem_map_of_mem ((mem_Z1fT_iff PD hE₁ hc₁ hs₁ hL₁ x).1 hx i),
      funCoord O G E₂ z i, (mem_B1T_iff hE₂ hL₂ z).1 hz i, ?_⟩
    rw [map_add, Pi.add_apply, post_coord]
  · intro H
    choose y hy z hz hyz using fun i => Submodule.mem_sup.1 (H i)
    choose x hx hxy using fun i => Submodule.mem_map.1 (hy i)
    refine Submodule.mem_sup.2 ⟨F'.post ((funCoord O G E₁).symm x),
      Submodule.mem_map_of_mem ((mem_Z1fT_iff PD hE₁ hc₁ hs₁ hL₁ _).2 (by simpa using hx)),
      (funCoord O G E₂).symm z, (mem_B1T_iff hE₂ hL₂ _).2 (by simpa using hz), ?_⟩
    apply (funCoord O G E₂).injective
    funext i
    rw [map_add, Pi.add_apply, post_coord, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, hxy i, hyz i]

omit [TopologicalSpace G] [Fintype ι] [DecidableEq ι] [ContinuousAdd V₁] [ContinuousConstSMul LL V₁]
  [ContinuousAdd V₁'] [ContinuousConstSMul LL' V₁'] [ContinuousAdd V₂] [ContinuousConstSMul LL V₂]
  [ContinuousAdd V₂'] [ContinuousConstSMul LL' V₂'] [Module O V₁'] [IsScalarTower O LL V₁']
  [Module O V₂'] [IsScalarTower O LL V₂'] in
theorem onto_ext (hL₁ : ∀ x, x ∈ L₁'.T ↔ ∀ i, E₁ x i ∈ L₁.T)
    (hL₂ : ∀ x, x ∈ L₂'.T ↔ ∀ i, E₂ x i ∈ L₂.T)
    (hF : ∀ x i, E₂ (F'.f x) i = F.f (E₁ x i)) (h : F.Onto) : F'.Onto := by
  unfold LatHom.Onto at h ⊢
  intro y hy
  have hyi : ∀ i, E₂ y i ∈ L₂.T := (hL₂ y).1 hy
  choose x hx hfx using fun i => h _ (hyi i)
  refine ⟨E₁.symm x, (hL₁ _).2 (by simpa using hx), ?_⟩
  apply E₂.injective
  funext i
  rw [hF, LinearEquiv.apply_symm_apply, hfx]

theorem col_ext [Algebra O O'] [IsLocalRing O] [IsLocalRing O'] [IsLocalHom (algebraMap O O')]
    [IsScalarTower O O' V₂']
    (hE₁ : ∀ g x i, E₁ (ρ₁' g x) i = ρ₁ g (E₁ x i)) (hc₁ : Continuous E₁)
    (hs₁ : Continuous E₁.symm) (hL₁ : ∀ x, x ∈ L₁'.T ↔ ∀ i, E₁ x i ∈ L₁.T)
    (hE₂ : ∀ g x i, E₂ (ρ₂' g x) i = ρ₂ g (E₂ x i)) (hc₂ : Continuous E₂)
    (hs₂ : Continuous E₂.symm) (hL₂ : ∀ x, x ∈ L₂'.T ↔ ∀ i, E₂ x i ∈ L₂.T)
    (hF : ∀ x i, E₂ (F'.f x) i = F.f (E₁ x i)) :
    F'.col PD * Module.length (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') =
      Fintype.card ι * F.col PD := by
  unfold LatHom.col
  rw [← IsLocalRing.length_restrictScalars O O',
    length_subquot (funCoord O G E₂) _ _ _ _ (mem_Z1fT_iff PD hE₂ hc₂ hs₂ hL₂)
      (mem_ImF_iff PD F F' hE₁ hc₁ hs₁ hL₁ hE₂ hL₂ hF)]

end Two

private theorem length_quotient_eq_card_mul_of_pi_equiv {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module R W] [Module R W'] [Module R' W']
    [IsScalarTower R R' W'] {ι : Type} [Fintype ι] (E : W' ≃ₗ[R] (ι → W))
    (N' : Submodule R' W') (N : Submodule R W) (hN : ∀ x, x ∈ N' ↔ ∀ i, E x i ∈ N) :
    Module.length R (W' ⧸ N') = Fintype.card ι * Module.length R (W ⧸ N) := by
  classical
  let Φ : W' →ₗ[R] (ι → W ⧸ N) := LinearMap.pi fun i => N.mkQ ∘ₗ (LinearMap.proj i ∘ₗ E.toLinearMap)
  have hsurj : Function.Surjective Φ := by
    intro y
    choose s hs using fun i => Submodule.Quotient.mk_surjective _ (y i)
    refine ⟨E.symm s, ?_⟩
    funext i
    simp [Φ, ← hs i]
  have hker : LinearMap.ker Φ = N'.restrictScalars R := by
    ext x
    rw [LinearMap.mem_ker, Submodule.restrictScalars_mem, hN, funext_iff]
    simp [Φ, Submodule.Quotient.mk_eq_zero]
  let e : (W' ⧸ N') ≃ₗ[R] (ι → W ⧸ N) :=
    (Submodule.Quotient.restrictScalarsEquiv R N').symm ≪≫ₗ
      Submodule.quotEquivOfEq _ _ hker.symm ≪≫ₗ Φ.quotKerEquivOfSurjective hsurj
  rw [e.length_eq, Module.length_pi, ENat.card_eq_coe_fintype_card]

omit [TopologicalSpace G] [DecidableEq ι] in

theorem lenOl_ext [Algebra O O'] [IsLocalRing O] [IsLocalRing O'] [IsLocalHom (algebraMap O O')]
    (b : Basis ι O O') :
    lenOl PD (O := O') * Module.length (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField O') =
      Fintype.card ι * lenOl PD (O := O) := by
  unfold lenOl
  rw [← IsLocalRing.length_restrictScalars O O']
  rw [length_quotient_eq_card_mul_of_pi_equiv b.equivFun (Ideal.span {((PD.p : ℕ) : O')}) (Ideal.span {((PD.p : ℕ) : O)})]
  intro x
  have hcast : ∀ y : O', ((PD.p : ℕ) : O') * y = ((PD.p : ℕ) : O) • y := fun y => by
    rw [Algebra.smul_def, map_natCast]
  simp only [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩ i
    refine ⟨b.equivFun y i, ?_⟩
    rw [hcast, map_smul, Pi.smul_apply, smul_eq_mul]
  · intro H
    choose a ha using H
    refine ⟨b.equivFun.symm a, ?_⟩
    apply b.equivFun.injective
    rw [hcast, map_smul, LinearEquiv.apply_symm_apply]
    funext i
    rw [ha i, Pi.smul_apply, smul_eq_mul]

end Lat

theorem descend_bound {m k f : ℕ∞} {m' k' d : ℕ} (hd : 0 < d) (hf : f ≠ ⊤)
    (hm : (m' : ℕ∞) * f = d * m) (hk : (k' : ℕ∞) * f = d * k) {β : ℝ} (h : (m' : ℝ) ≤ β * k') :
    ∃ a c : ℕ, m = a ∧ k = c ∧ (a : ℝ) ≤ β * c := by
  lift f to ℕ using hf
  have hmt : m ≠ ⊤ := by
    rintro rfl
    have h1 : ((m' * f : ℕ) : ℕ∞) = ⊤ := by
      push_cast
      simpa [ENat.mul_top, hd.ne'] using hm
    exact ENat.natCast_ne_top _ h1
  have hkt : k ≠ ⊤ := by
    rintro rfl
    have h1 : ((k' * f : ℕ) : ℕ∞) = ⊤ := by
      push_cast
      simpa [ENat.mul_top, hd.ne'] using hk
    exact ENat.natCast_ne_top _ h1
  lift m to ℕ using hmt
  lift k to ℕ using hkt
  refine ⟨m, k, rfl, rfl, ?_⟩
  have hm' : (d : ℝ) * m = m' * f := by exact_mod_cast hm.symm
  have hk' : (d : ℝ) * k = k' * f := by exact_mod_cast hk.symm
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd

  have hle : (d : ℝ) * m ≤ d * (β * k) := by
    rw [hm', show (d : ℝ) * (β * k) = β * (d * k) by ring, hk']
    calc (m' : ℝ) * f ≤ (β * k') * f := mul_le_mul_of_nonneg_right h (Nat.cast_nonneg f)
      _ = β * (k' * f) := by ring
  exact le_of_mul_le_mul_left hle hdpos

theorem finrank_ext {O O' : Type} [CommRing O] [CommRing O'] [Nontrivial O'] [Algebra O O']
    {W W' : Type} [AddCommGroup W] [AddCommGroup W'] [Module O W] [Module O W'] [Module O' W']
    [IsScalarTower O O' W'] {ι : Type} [Fintype ι] (b : Basis ι O O') (E : W' ≃ₗ[O] (ι → W))
    (S' : Submodule O' W') (S : Submodule O W) [Module.Free O' ↥S'] [Module.Free O ↥S]
    (hS : ∀ x, x ∈ S' ↔ ∀ i, E x i ∈ S) : finrank O' ↥S' = finrank O ↥S := by
  have : Nontrivial O := (algebraMap O O').domain_nontrivial
  have : Module.Free O O' := Module.Free.of_basis b
  have : Nonempty ι := b.index_nonempty
  have hn : 0 < Fintype.card ι := Fintype.card_pos

  let eS : ↥(S'.restrictScalars O) ≃ₗ[O] (ι → ↥S) := subEquiv E (S'.restrictScalars O) S hS
  have hpi : finrank O (ι → ↥S) = Fintype.card ι * finrank O ↥S :=
    (Finsupp.linearEquivFunOnFinite O ↥S ι).finrank_eq.symm.trans (finrank_finsupp O ↥S)
  have t := Module.finrank_mul_finrank O O' ↥S'
  have t' : finrank O ↥S' = finrank O (ι → ↥S) := eS.finrank_eq
  rw [Module.finrank_eq_card_basis b, t', hpi] at t
  exact Nat.eq_of_mul_eq_mul_left hn t

end GlobalTheory.CoeffExt
