import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLengthCutGlobal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped Pointwise

universe u v

namespace LengthCutGlobal

section Layers

variable {C : Type u} [CommRing C] (P : Ideal C) [P.IsPrime]

theorem length_localized_add {N M Q : Type*} [AddCommGroup N] [Module C N] [AddCommGroup M]
    [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl N) +
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl Q) := by
  let fN := LocalizedModule.mkLinearMap P.primeCompl N
  let fM := LocalizedModule.mkLinearMap P.primeCompl M
  let fQ := LocalizedModule.mkLinearMap P.primeCompl Q
  exact Module.length_eq_add_of_exact
    ((IsLocalizedModule.map P.primeCompl fN fM f).extendScalarsOfIsLocalization P.primeCompl
      (Localization.AtPrime P))
    ((IsLocalizedModule.map P.primeCompl fM fQ g).extendScalarsOfIsLocalization P.primeCompl
      (Localization.AtPrime P))
    (IsLocalizedModule.map_injective P.primeCompl fN fM f hf)
    (IsLocalizedModule.map_surjective P.primeCompl fM fQ g hg)
    (IsLocalizedModule.map_exact P.primeCompl fN fM fQ f g H)

omit [P.IsPrime] in

theorem length_quotSMulTop_add (y : C) {N M Q : Type*} [AddCommGroup N] [Module C N]
    [AddCommGroup M] [Module C M] [AddCommGroup Q] [Module C Q] (f : N →ₗ[C] M) (g : M →ₗ[C] Q)
    (hf : Function.Injective f) (hg : Function.Surjective g) (H : Function.Exact f g)
    (hy : ∀ q : Q, y • q = 0 → q = 0) :
    Module.length C (QuotSMulTop y M) =
      Module.length C (QuotSMulTop y N) + Module.length C (QuotSMulTop y Q) := by
  refine Module.length_eq_add_of_exact (QuotSMulTop.map y f) (QuotSMulTop.map y g) ?_
    (QuotSMulTop.map_surjective y hg) (QuotSMulTop.map_exact y H hg)
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [QuotSMulTop.map_apply_mk, Submodule.Quotient.mk_eq_zero,
    Submodule.mem_smul_pointwise_iff_exists] at hx
  obtain ⟨m, -, hm⟩ := hx
  have hgm : g m = 0 := hy _ (by rw [← map_smul, hm]; exact (H (f n)).2 ⟨n, rfl⟩)
  obtain ⟨n', rfl⟩ := (H m).1 hgm
  have hn : n = y • n' := hf (by rw [map_smul, hm])
  rw [Submodule.Quotient.mk_eq_zero, hn]
  exact Submodule.smul_mem_pointwise_smul n' y ⊤ trivial

theorem lengths_of_subsingleton (y : C) (X : Type*) [AddCommGroup X] [Module C X] [Subsingleton X] :
    Module.length C (QuotSMulTop y X) = 0 ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = 0 := by
  have : Subsingleton (QuotSMulTop y X) := (Submodule.mkQ_surjective _).subsingleton
  exact ⟨Module.length_eq_zero, Module.length_eq_zero⟩

theorem smul_injective_pi {y : C} (hy : y ∉ P) (n : ℕ) (v : Fin n → C ⧸ P) (h : y • v = 0) :
    v = 0 := by
  funext i
  have hi := congrFun h i
  rw [Pi.smul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Pi.zero_apply] at hi
  exact (mul_eq_zero.1 hi).resolve_left (fun h => hy (Ideal.Quotient.eq_zero_iff_mem.1 h))

omit [P.IsPrime] in

theorem length_quotSMulTop_quot {y : C} (hmax : (P ⊔ Ideal.span {y}).IsMaximal) :
    Module.length C (QuotSMulTop y (C ⧸ P)) = 1 := by
  let g : C →ₗ[C] QuotSMulTop y (C ⧸ P) :=
    (y • (⊤ : Submodule C (C ⧸ P))).mkQ ∘ₗ Algebra.linearMap C (C ⧸ P)
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp Ideal.Quotient.mk_surjective
  have hker : LinearMap.ker g = P ⊔ Ideal.span {y} := by
    ext x
    simp only [g, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
      Algebra.linearMap_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and]
    constructor
    · rintro ⟨t, ht⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective t
      have hmem : x - y * c ∈ P := by
        rw [← Ideal.Quotient.eq, map_mul, ← Ideal.Quotient.algebraMap_eq, ← ht, Algebra.smul_def]
        rfl
      rw [show x = (x - y * c) + y * c by ring]
      exact Submodule.add_mem_sup hmem (Ideal.mem_span_singleton'.2 ⟨c, mul_comm c y⟩)
    · intro hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hb
      refine ⟨Ideal.Quotient.mk P c, ?_⟩
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_add,
        Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_add, map_mul, mul_comm]
  rw [← (g.quotKerEquivOfSurjective hg).length_eq, hker]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.1 hmax))

theorem length_localized_quot :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (C ⧸ P)) = 1 := by
  let S := Localization.AtPrime P
  have hJ : (P : Submodule C C).localized' S P.primeCompl (Algebra.linearMap C S) =
      IsLocalRing.maximalIdeal S := by
    rw [Submodule.localized'_eq_span, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map]
    rfl
  let e := (IsLocalizedModule.linearEquiv P.primeCompl
    ((P : Submodule C C).toLocalizedQuotient' S P.primeCompl (Algebra.linearMap C S))
    (LocalizedModule.mkLinearMap P.primeCompl (C ⧸ P))).extendScalarsOfIsLocalization P.primeCompl S
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ hJ).length_eq]
  exact Module.length_eq_one_iff.2 (isSimpleModule_iff_isCoatom.mpr
    (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal S)))

theorem lengths_pi {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) (n : ℕ) :
    Module.length C (QuotSMulTop y (Fin n → C ⧸ P)) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (Fin n → C ⧸ P)) = n := by
  induction n with
  | zero =>
    simp only [CharP.cast_eq_zero]
    exact lengths_of_subsingleton P y (Fin 0 → C ⧸ P)
  | succ n ih =>
    let f : (C ⧸ P) →ₗ[C] (Fin (n + 1) → C ⧸ P) := LinearMap.single C (fun _ => C ⧸ P) 0
    let g : (Fin (n + 1) → C ⧸ P) →ₗ[C] (Fin n → C ⧸ P) := LinearMap.funLeft C (C ⧸ P) Fin.succ
    have hf : Function.Injective f := fun a b h => by simpa [f] using congrFun h 0
    have hg : Function.Surjective g :=
      LinearMap.funLeft_surjective_of_injective _ _ _ (Fin.succ_injective n)
    have H : Function.Exact f g := by
      intro v
      constructor
      · intro hv
        refine ⟨v 0, funext fun i => ?_⟩
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [f]
        · have hj : v j.succ = 0 := congrFun hv j
          simp [f, hj, Fin.succ_ne_zero]
      · rintro ⟨t, rfl⟩
        funext j
        simp [f, g, LinearMap.funLeft, Fin.succ_ne_zero]
    rw [length_quotSMulTop_add y f g hf hg H (smul_injective_pi P hy n),
      length_localized_add P f g hf hg H, ih.1, ih.2, length_quotSMulTop_quot P hmax,
      length_localized_quot P]
    constructor <;> push_cast <;> ring

theorem lengths_free {y : C} (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal) {n : ℕ}
    {X : Type*} [AddCommGroup X] [Module C X] (e : X ≃ₗ[C] (Fin n → C ⧸ P)) :
    Module.length C (QuotSMulTop y X) = n ∧
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl X) = n := by
  rw [(QuotSMulTop.congr y e).length_eq,
    (IsLocalizedModule.mapEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl X)
      (LocalizedModule.mkLinearMap P.primeCompl (Fin n → C ⧸ P)) (Localization.AtPrime P) e).length_eq]
  exact lengths_pi P hy hmax n

end Layers

theorem lengths_eq {C : Type u} [CommRing C] [IsNoetherianRing C] (P : Ideal C) [P.IsPrime] (y : C)
    (hPID : IsPrincipalIdealRing (C ⧸ P)) (hy : y ∉ P) (hmax : (P ⊔ Ideal.span {y}).IsMaximal)
    (k : ℕ) :
    ∀ (M : Type v) [AddCommGroup M] [Module C M] [Module.Finite C M],
      (∀ p ∈ P ^ k, ∀ m : M, p • m = 0) → (∀ s ∉ P, ∀ m : M, s • m = 0 → m = 0) →
      Module.length C (QuotSMulTop y M) =
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M) := by
  induction k with
  | zero =>
    intro M _ _ _ hann _
    have : Subsingleton M := ⟨fun a b => by
      rw [← one_smul C a, ← one_smul C b, hann 1 (by simp) a, hann 1 (by simp) b]⟩
    rw [(lengths_of_subsingleton P y M).1, (lengths_of_subsingleton P y M).2]
  | succ k ih =>
    intro M _ _ _ hann hinj
    have := hPID

    have : Module.Finite C (Submodule.torsionBySet C M (P : Set C)) :=
      Module.Finite.of_injective (Submodule.torsionBySet C M (P : Set C)).subtype
        (Submodule.torsionBySet C M (P : Set C)).injective_subtype
    have : Module.Finite (C ⧸ P) (Submodule.torsionBySet C M (P : Set C)) :=
      Module.Finite.of_restrictScalars_finite C (C ⧸ P) _
    have : Module.IsTorsionFree (C ⧸ P) (Submodule.torsionBySet C M (P : Set C)) := by
      refine Module.IsTorsionFree.of_smul_eq_zero fun r n h => ?_
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective r
      by_cases hs : s ∈ P
      · exact Or.inl (Ideal.Quotient.eq_zero_iff_mem.2 hs)
      · right
        rw [Submodule.torsionBySet.mk_smul] at h
        exact Subtype.ext (hinj s hs n (congrArg Subtype.val h))
    obtain ⟨r, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := C ⧸ P)
      (M := Submodule.torsionBySet C M (P : Set C))
    have hN := lengths_free P hy hmax (b.equivFun.restrictScalars C)

    have hannQ : ∀ p ∈ P ^ k, ∀ q : M ⧸ Submodule.torsionBySet C M (P : Set C), p • q = 0 := by
      intro p hp q
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      rw [smul_smul]
      exact hann _ (by rw [pow_succ']; exact Ideal.mul_mem_mul ha hp) m
    have hinjQ : ∀ s ∉ P, ∀ q : M ⧸ Submodule.torsionBySet C M (P : Set C), s • q = 0 → q = 0 := by
      intro s hs q hq
      obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_torsionBySet_iff] at hq
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      apply hinj s hs
      rw [smul_comm]
      exact hq ⟨a, ha⟩
    have hQ := ih (M ⧸ Submodule.torsionBySet C M (P : Set C)) hannQ hinjQ
    let N := Submodule.torsionBySet C M (P : Set C)
    rw [length_quotSMulTop_add y N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N) (hinjQ y hy),
      length_localized_add P N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
        (LinearMap.exact_subtype_mkQ N), hQ, hN.1, hN.2]

theorem proof : LengthCutGlobal.Statement.{u, v} := by
  intro C _ _ P _ y M _ _ _ hnil hPID hy hmax hinj
  obtain ⟨k, hk⟩ := hnil
  rw [Submodule.ideal_span_singleton_smul]
  refine lengths_eq P y hPID hy hmax k M (fun p hp m => ?_) hinj
  rw [hk, Ideal.zero_eq_bot, Ideal.mem_bot] at hp
  rw [hp, zero_smul]

end LengthCutGlobal

end GroundTheory.Heights₂.Heights
