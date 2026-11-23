import Mathlib
import Formalism.CharacterColumnKernels.StatementRho
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
import ReciprocityTheory.Hypotheses.GalCohDefs
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuot
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg.Shape

def kerProd {O : Type} [CommRing O] (c : O) {ι M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] :
    LinearMap.ker (c • LinearMap.id : (ι → M) × N →ₗ[O] (ι → M) × N) ≃
      (ι → LinearMap.ker (c • LinearMap.id : M →ₗ[O] M)) ×
        LinearMap.ker (c • LinearMap.id : N →ₗ[O] N) where
  toFun x := (fun i => ⟨x.1.1 i, by
      have h := LinearMap.mem_ker.1 x.2
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Prod.ext_iff, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, funext_iff, Pi.smul_apply, Pi.zero_apply] at h
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact h.1 i⟩, ⟨x.1.2, by
      have h := LinearMap.mem_ker.1 x.2
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Prod.ext_iff, Prod.smul_fst,
        Prod.smul_snd, Prod.fst_zero, Prod.snd_zero] at h
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      exact h.2⟩)
  invFun y := ⟨(fun i => (y.1 i).1, y.2.1), by
      simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply, Prod.ext_iff,
        Prod.smul_fst, Prod.smul_snd, Prod.fst_zero, Prod.snd_zero, funext_iff, Pi.smul_apply,
        Pi.zero_apply]
      refine ⟨fun i => ?_, ?_⟩
      · have := (y.1 i).2
        simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using this
      · have := y.2.2
        simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using this⟩
  left_inv x := rfl
  right_inv y := rfl

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem card_ker_prod [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ)
    {H : Type} [AddCommGroup H] [Module O H] {a : ℕ} {F : Type} [AddCommGroup F] [Module O F]
    (φ : H ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) (n : ℕ) :
    Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : H →ₗ[O] H)) =
      (Nat.card (IsLocalRing.ResidueField O) ^ n) ^ a *
        Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) := by
  have hK : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Formalism.NG.KO O →ₗ[O] Formalism.NG.KO O)) =
      Nat.card (IsLocalRing.ResidueField O) ^ n :=
    (levKO_card hϖ (LinearEquiv.refl O (Formalism.NG.KO O)) n).2
  have h1 : Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : H →ₗ[O] H)) =
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id :
        (Fin a → Formalism.NG.KO O) × F →ₗ[O] (Fin a → Formalism.NG.KO O) × F)) :=
    Nat.card_congr (levCongr φ (ϖ ^ n))
  rw [h1, Nat.card_congr (kerProd (ϖ ^ n)), Nat.card_prod, Nat.card_fun, hK, Nat.card_eq_fintype_card (α := Fin a), Fintype.card_fin]

theorem cyclic_of_card_ker_le [Finite (IsLocalRing.ResidueField O)] {ϖ : O} (hϖ : Irreducible ϖ)
    {F : Type} [AddCommGroup F] [Module O F] [Finite F]
    (h : Nat.card (LinearMap.ker (ϖ • LinearMap.id : F →ₗ[O] F)) ≤
      Nat.card (IsLocalRing.ResidueField O)) :
    ∃ c0 : F, ∀ y : F, ∃ a : O, y = a • c0 := by
  set g : F →ₗ[O] F := ϖ • LinearMap.id with hg
  have hQ : Nat.card (F ⧸ LinearMap.range g) ≤ Nat.card (IsLocalRing.ResidueField O) := by
    have e1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range g)
    have e2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker g)
    have e3 := Nat.card_congr (LinearMap.quotKerEquivRange g).toEquiv
    have hr : 0 < Nat.card (LinearMap.range g) := Nat.card_pos
    rw [e3, e1, mul_comm (Nat.card (LinearMap.ker g))] at e2
    rw [Nat.eq_of_mul_eq_mul_left hr e2]
    exact h
  have hx : ∃ x : F, ∀ y : F, y ∈ Submodule.span O {x} ⊔ LinearMap.range g := by
    by_cases hs : Subsingleton (F ⧸ LinearMap.range g)
    · refine ⟨0, fun y => ?_⟩
      have : (Submodule.Quotient.mk y : F ⧸ LinearMap.range g) = 0 := Subsingleton.elim _ _
      exact Submodule.mem_sup_right ((Submodule.Quotient.mk_eq_zero _).1 this)
    · rw [not_subsingleton_iff_nontrivial] at hs
      haveI : Finite (F ⧸ LinearMap.range g) :=
        Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
      obtain ⟨xb, hxb⟩ := exists_ne (0 : F ⧸ LinearMap.range g)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ xb
      set t := LinearMap.toSpanSingleton O (F ⧸ LinearMap.range g)
        (Submodule.Quotient.mk x) with ht
      have hker : LinearMap.ker t = IsLocalRing.maximalIdeal O := by
        symm
        apply (IsLocalRing.maximalIdeal.isMaximal O).eq_of_le
        · intro htop
          apply hxb
          have h1 : (1 : O) ∈ LinearMap.ker t := htop ▸ Submodule.mem_top
          simpa [ht] using h1
        · rw [hϖ.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
            LinearMap.mem_ker, ht, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
            Submodule.Quotient.mk_eq_zero]
          exact ⟨x, rfl⟩
      have hrange : LinearMap.range t = ⊤ := by
        by_contra hne
        obtain ⟨z, hz⟩ : ∃ z, z ∉ LinearMap.range t := by
          by_contra hall
          push_neg at hall
          exact hne (eq_top_iff.2 fun z _ => hall z)
        have hlt : Nat.card (LinearMap.range t) < Nat.card (F ⧸ LinearMap.range g) :=
          Finite.card_subtype_lt (p := fun w => w ∈ LinearMap.range t) hz
        have hc : Nat.card (LinearMap.range t) = Nat.card (IsLocalRing.ResidueField O) := by
          rw [← Nat.card_congr (LinearMap.quotKerEquivRange t).toEquiv, hker]
          rfl
        omega
      refine ⟨x, fun y => ?_⟩
      obtain ⟨a, ha⟩ : ∃ a, t a = Submodule.Quotient.mk y := by
        have hy : (Submodule.Quotient.mk y : F ⧸ LinearMap.range g) ∈ LinearMap.range t :=
          hrange ▸ Submodule.mem_top
        exact hy
      rw [ht, LinearMap.toSpanSingleton_apply, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.eq] at ha
      have hy : y = a • x - (a • x - y) := by abel
      rw [hy]
      exact Submodule.sub_mem _
        (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
        (Submodule.mem_sup_right ha)
  obtain ⟨x, hx⟩ := hx
  have hfg : (⊤ : Submodule O F).FG :=
    ⟨(Set.finite_univ (α := F)).toFinset, by simp⟩
  have hle : (⊤ : Submodule O F) ≤ Submodule.span O {x} := by
    apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg (IsLocalRing.maximalIdeal_le_jacobson ⊥)
    intro y _
    have hsub : LinearMap.range g ≤ IsLocalRing.maximalIdeal O • (⊤ : Submodule O F) := by
      rintro _ ⟨z, rfl⟩
      have hm : ϖ ∈ IsLocalRing.maximalIdeal O := by
        rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
      exact Submodule.smul_mem_smul hm Submodule.mem_top
    have hmono : Submodule.span O {x} ⊔ LinearMap.range g ≤
        Submodule.span O {x} ⊔ IsLocalRing.maximalIdeal O • (⊤ : Submodule O F) :=
      sup_le_sup_left hsub _
    exact hmono (hx y)
  refine ⟨x, fun y => ?_⟩
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hle Submodule.mem_top)
  exact ⟨a, ha.symm⟩

theorem quotShape_of_counts : ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)]
    {ϖ : O}, Irreducible ϖ → ∀ {X : Type} [AddCommGroup X] [Module O X] (Hc : Submodule O X) (d a : ℕ)
    {F : Type} [AddCommGroup F] [Module O F] [Finite F], (Hc ≃ₗ[O] (Fin a → Formalism.NG.KO O) × F) →
    (∃ C : ℕ, ∀ n : ℕ, 0 < n →
      Nat.card (IsLocalRing.ResidueField O) ^ (n * d) ≤ Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ∧
      Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : Hc →ₗ[O] Hc)) ≤ C * Nat.card (IsLocalRing.ResidueField O) ^ (n * d)) →
    Nat.card (LinearMap.ker (ϖ ^ 1 • LinearMap.id : Hc →ₗ[O] Hc)) ≤ Nat.card (IsLocalRing.ResidueField O) ^ (d + 1) →
    Formalism.RepresentationBoundsCohomology.JT.QuotShape Hc ⊥ d := by
  intro O _ _ _ _ ϖ hϖ X _ _ Hc d a F _ _ _ φ hC h1
  have hq : 2 ≤ Nat.card (IsLocalRing.ResidueField O) := Finite.one_lt_card
  have hcard := card_ker_prod hϖ φ
  have hF1 : ∀ n : ℕ, 1 ≤ Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) :=
    fun n => Nat.card_pos
  have hFle : ∀ n : ℕ, Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) ≤ Nat.card F :=
    fun n => Nat.card_le_card_of_injective _ Subtype.val_injective
  obtain ⟨C, hC⟩ := hC
  have hlt : ∀ m : ℕ, m < Nat.card (IsLocalRing.ResidueField O) ^ m := fun m =>
    lt_of_lt_of_le Nat.lt_two_pow_self (Nat.pow_le_pow_left hq m)
  have had : a = d := by
    rcases lt_trichotomy a d with h | h | h
    · exfalso
      have hn := (hC (Nat.card F + 1) (Nat.succ_pos _)).1
      rw [hcard] at hn
      set q := Nat.card (IsLocalRing.ResidueField O)
      set n := Nat.card F + 1
      have h2 : (q ^ n) ^ a * q ^ n ≤ q ^ (n * d) := by
        rw [← pow_succ, ← pow_mul]
        exact Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left n h)
      have hpos : 0 < (q ^ n) ^ a := by positivity
      have h3 : (q ^ n) ^ a * q ^ n ≤ (q ^ n) ^ a * Nat.card F :=
        h2.trans (hn.trans (Nat.mul_le_mul_left _ (hFle n)))
      have h4 := Nat.le_of_mul_le_mul_left h3 hpos
      have h5 := hlt n
      omega
    · exact h
    · exfalso
      have hn := (hC (C + 1) (Nat.succ_pos _)).2
      rw [hcard] at hn
      set q := Nat.card (IsLocalRing.ResidueField O)
      set n := C + 1
      have h2 : q ^ (n * d) * q ^ n ≤ (q ^ n) ^ a := by
        rw [← pow_add, ← pow_mul]
        exact Nat.pow_le_pow_right (by omega) (by nlinarith)
      have h3 : (q ^ n) ^ a ≤ (q ^ n) ^ a * Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id : F →ₗ[O] F)) :=
        Nat.le_mul_of_pos_right _ (hF1 n)
      have hpos : 0 < q ^ (n * d) := by positivity
      have h4 : q ^ (n * d) * q ^ n ≤ q ^ (n * d) * C := by
        rw [mul_comm (q ^ (n * d)) C]; exact h2.trans (h3.trans hn)
      have h5 := Nat.le_of_mul_le_mul_left h4 hpos
      have h6 := hlt n
      omega
  subst had
  have hsoc : Nat.card (LinearMap.ker (ϖ • LinearMap.id : F →ₗ[O] F)) ≤
      Nat.card (IsLocalRing.ResidueField O) := by
    have h1' := h1
    rw [hcard 1] at h1'
    simp only [pow_one] at h1'
    rw [pow_succ] at h1'
    have hpos : 0 < Nat.card (IsLocalRing.ResidueField O) ^ a := by positivity
    have := Nat.le_of_mul_le_mul_left h1' hpos
    exact this
  obtain ⟨c0, hc0⟩ := cyclic_of_card_ker_le hϖ hsoc
  have hbot : (⊥ : Submodule O X).comap Hc.subtype = ⊥ := by
    rw [Submodule.comap_bot, Submodule.ker_subtype]
  let e0 : (Hc ⧸ (⊥ : Submodule O X).comap Hc.subtype) ≃ₗ[O] Hc :=
    Submodule.quotEquivOfEqBot _ hbot
  let ι : (Fin a → Formalism.NG.KO O) →ₗ[O] (Hc ⧸ (⊥ : Submodule O X).comap Hc.subtype) :=
    e0.symm.toLinearMap ∘ₗ φ.symm.toLinearMap ∘ₗ LinearMap.inl O _ F
  let π : (Hc ⧸ (⊥ : Submodule O X).comap Hc.subtype) →ₗ[O] F :=
    LinearMap.snd O _ F ∘ₗ φ.toLinearMap ∘ₗ e0.toLinearMap
  refine ⟨F, inferInstance, inferInstance, ι, π, ?_, ?_, c0, hc0⟩
  · intro u v huv
    have := congrArg (fun z => (φ (e0 z)).1) huv
    simpa only [ι, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.inl_apply] using this
  · intro y
    constructor
    · intro hy
      refine ⟨(φ (e0 y)).1, ?_⟩
      apply e0.injective
      apply φ.injective
      simp only [π, LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply,
        LinearEquiv.coe_coe] at hy
      simp only [ι, LinearMap.coe_comp, Function.comp_apply, LinearMap.inl_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
      exact Prod.ext rfl hy.symm
    · rintro ⟨u, rfl⟩
      simp only [ι, π, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.inl_apply, LinearMap.snd_apply]

end GlobalTheory.ShapeNeg.Shape
