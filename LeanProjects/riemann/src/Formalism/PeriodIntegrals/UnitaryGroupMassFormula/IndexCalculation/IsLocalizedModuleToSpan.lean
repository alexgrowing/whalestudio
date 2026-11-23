import Mathlib
import Formalism.PeriodIntegrals.IdxCalc
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ElementDenominator

noncomputable section

namespace PI.Dv.IdxW

open Module

section Gen

variable {R : Type*} [CommRing R] (S : Submonoid R)

theorem lenS_exact {A B C : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hf : Function.Injective f)
    (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Module.length (Localization S) (LocalizedModule S B) =
      Module.length (Localization S) (LocalizedModule S A) +
        Module.length (Localization S) (LocalizedModule S C) :=
  Module.length_eq_add_of_exact (LocalizedModule.map S f) (LocalizedModule.map S g)
    (LocalizedModule.map_injective S f hf) (LocalizedModule.map_surjective S g hg)
    (LocalizedModule.map_exact S f g hfg)

variable {V : Type*} [AddCommGroup V] [Module R V]

def lenS (M N : Submodule R V) : ℕ∞ :=
  Module.length (Localization S) (LocalizedModule S (↥M ⧸ N.comap M.subtype))

theorem comap_inf (M N : Submodule R V) : N.comap M.subtype = (M ⊓ N).comap M.subtype := by
  ext x
  simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
  exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem lenS_inf (M N : Submodule R V) : lenS S M N = lenS S M (M ⊓ N) := by
  unfold lenS
  rw [comap_inf M N]

theorem lenS_add (P N M : Submodule R V) (hPN : P ≤ N) (hNM : N ≤ M) :
    lenS S M P = lenS S M N + lenS S N P := by
  let f : (↥N ⧸ P.comap N.subtype) →ₗ[R] (↥M ⧸ P.comap M.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hNM) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact hx)
  let g : (↥M ⧸ P.comap M.subtype) →ₗ[R] (↥M ⧸ N.comap M.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => hPN hx)
  have key := lenS_exact S f g ?_ ?_ ?_
  · unfold lenS
    rw [key, add_comm]
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [LinearMap.mem_ker] at hy
      dsimp only [f] at hy
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
      exact hy
  · intro z
    induction z using Submodule.Quotient.induction_on with
    | H x => exact ⟨Submodule.Quotient.mk x, rfl⟩
  · intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro hy
        dsimp only [g] at hy
        rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hy
        exact ⟨Submodule.Quotient.mk ⟨x, hy⟩, rfl⟩
      · rintro ⟨w, hw⟩
        rw [← hw]
        induction w using Submodule.Quotient.induction_on with
        | H z =>
          dsimp only [f, g]
          rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
          exact z.2

theorem lenS_le (P N M : Submodule R V) (hPN : P ≤ N) (hNM : N ≤ M) :
    lenS S M N ≤ lenS S M P := by
  rw [lenS_add S P N M hPN hNM]
  exact le_self_add

theorem lenS_eq_zero (M N : Submodule R V) (h : ∀ x ∈ M, ∃ s ∈ S, s • x ∈ N) :
    lenS S M N = 0 := by
  unfold lenS
  have : Subsingleton (LocalizedModule S (↥M ⧸ N.comap M.subtype)) := by
    rw [IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S _)]
    intro m
    induction m using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨s, hs, hsx⟩ := h x.1 x.2
      exact ⟨s, hs, by
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        exact hsx⟩
  exact Module.length_eq_zero

theorem lenS_of_le (M N : Submodule R V) (h : M ≤ N) : lenS S M N = 0 :=
  lenS_eq_zero S M N fun x hx => ⟨1, S.one_mem, by rw [one_smul]; exact h hx⟩

theorem length_quot_free {A : Type*} [CommRing A] [StrongRankCondition A] (J : Ideal A)
    (N : Type*) [AddCommGroup N] [Module A N] [Module.Free A N] [Module.Finite A N] :
    Module.length A (N ⧸ J • (⊤ : Submodule A N)) =
      (Module.finrank A N : ℕ∞) * Module.length A (A ⧸ J) := by
  let b := Module.finBasis A N
  let e : (N ⧸ J • (⊤ : Submodule A N)) ≃ₗ[A] (Fin (Module.finrank A N) → A ⧸ J) :=
    (TensorProduct.quotTensorEquivQuotSMul N J).symm ≪≫ₗ
      TensorProduct.congr (LinearEquiv.refl A (A ⧸ J)) b.equivFun ≪≫ₗ
        TensorProduct.piScalarRight A A (A ⧸ J) (Fin (Module.finrank A N))
  rw [e.length_eq, Module.length_pi_of_fintype]
  simp

end Gen

section Frac

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [IsDomain R] [Algebra R K]
  [IsFractionRing R K] {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

variable (K) in
include K in
theorem smul_eq_zero_iff' {c : R} (hc : c ≠ 0) {x : V} : c • x = 0 ↔ x = 0 := by
  rw [← algebraMap_smul K c x, smul_eq_zero]
  have : algebraMap R K c ≠ 0 := by
    intro h
    exact hc ((IsFractionRing.injective R K) (by rw [h, map_zero]))
  simp [this]

theorem eltDen (Y : Submodule R V) {y : V} (hy : y ∈ Submodule.span K (Y : Set V)) :
    ∃ s : R, s ≠ 0 ∧ s • y ∈ Y :=
  _root_.UpperTheory.Reformulated.B.ElementDenominator.eltDen Y hy

theorem den (X Y : Submodule R V) (hX : X.FG) (hXY : ∀ x ∈ X, x ∈ Submodule.span K (Y : Set V)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x ∈ X, c • x ∈ Y := by
  classical
  obtain ⟨s, rfl⟩ := hX
  have hc : ∀ a ∈ s, ∃ c : R, c ≠ 0 ∧ c • a ∈ Y := fun a ha =>
    eltDen (K := K) Y (hXY a (Submodule.subset_span ha))
  choose! c hc0 hcY using hc
  refine ⟨∏ a ∈ s, c a, Finset.prod_ne_zero_iff.mpr hc0, ?_⟩
  intro x hx
  induction hx using Submodule.span_induction with
  | mem a ha =>
    rw [← Finset.prod_erase_mul s c ha, mul_smul]
    exact Y.smul_mem _ (hcY a ha)
  | zero => rw [smul_zero]; exact Y.zero_mem
  | add x y _ _ hx hy => rw [smul_add]; exact Y.add_mem hx hy
  | smul r x _ hx => rw [smul_comm]; exact Y.smul_mem r hx

omit [IsScalarTower R K V] in
theorem den_of_span (X Y : Submodule R V) (hX : X.FG) [IsScalarTower R K V]
    (h : Submodule.span K (X : Set V) = Submodule.span K (Y : Set V)) :
    ∃ c : R, c ≠ 0 ∧ ∀ x ∈ X, c • x ∈ Y :=
  den (K := K) X Y hX fun x hx => h ▸ Submodule.subset_span hx

variable (K) in
include K in
theorem isTorsionFree_V : Module.IsTorsionFree R V :=
  Module.isTorsionFree_iff_smul_eq_zero.mpr fun r v h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · exact Or.inr ((smul_eq_zero_iff' K hr).mp h)

variable (K) in
include K in
theorem isTorsionFree_sub (M : Submodule R V) : Module.IsTorsionFree R M :=
  Module.isTorsionFree_iff_smul_eq_zero.mpr fun r v h => by
    by_cases hr : r = 0
    · exact Or.inl hr
    · refine Or.inr (Subtype.ext ?_)
      have : r • (v : V) = 0 := by rw [← Submodule.coe_smul, h, Submodule.coe_zero]
      exact (smul_eq_zero_iff' K hr).mp this

def toSpan (M : Submodule R V) : ↥M →ₗ[R] ↥(Submodule.span K (M : Set V)) where
  toFun x := ⟨x, Submodule.subset_span x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance isLocalizedModule_toSpan (M : Submodule R V) :
    IsLocalizedModule (nonZeroDivisors R) (toSpan (K := K) M) where
  map_units x := by
    rw [Module.End.isUnit_iff]
    have hx0 : (x : R) ≠ 0 := nonZeroDivisors.ne_zero x.2
    have hx' : algebraMap R K x ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors x.2
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      apply Subtype.ext
      have : (x : R) • ((y : V) - z) = 0 := by
        rw [smul_sub, sub_eq_zero]
        exact congrArg Subtype.val hyz
      exact sub_eq_zero.mp ((smul_eq_zero_iff' K hx0).mp this)
    · intro y
      refine ⟨(algebraMap R K x)⁻¹ • y, ?_⟩
      apply Subtype.ext
      show (x : R) • ((algebraMap R K x)⁻¹ • (y : V)) = y
      rw [← algebraMap_smul K (x : R), smul_smul, mul_inv_cancel₀ hx', one_smul]
  surj y := by
    obtain ⟨s, hs, hsy⟩ := eltDen (K := K) M y.2
    refine ⟨(⟨s • (y : V), hsy⟩, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), ?_⟩
    apply Subtype.ext
    rfl
  exists_of_eq {x₁ x₂} h := by
    refine ⟨1, ?_⟩
    have h' := congrArg Subtype.val h
    have : x₁ = x₂ := Subtype.ext h'
    rw [this]

theorem finrank_span_eq (M : Submodule R V) :
    Module.finrank K (Submodule.span K (M : Set V)) = Module.finrank R M := by
  rw [IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl]
  exact IsLocalizedModule.finrank_eq (nonZeroDivisors R) (toSpan (K := K) M) le_rfl

end Frac

end PI.Dv.IdxW
