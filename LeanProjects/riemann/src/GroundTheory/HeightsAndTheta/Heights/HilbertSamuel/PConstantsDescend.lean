import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsConstantsDescend
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Polynomial

namespace ConstantsDescend

section Fibre

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem aeval_mk_map (θ : B) (I : Ideal A) (P : A[X]) :
    aeval (Ideal.Quotient.mk (I.map (algebraMap A B)) θ) (P.map (algebraMap A (A ⧸ I))) =
      Ideal.Quotient.mk (I.map (algebraMap A B)) (aeval θ P) := by
  rw [aeval_map_algebraMap]
  exact aeval_algHom_apply (Ideal.Quotient.mkₐ A (I.map (algebraMap A B))) θ P

theorem exists_ringHom_of_root (θ : B) (hgen : Algebra.adjoin A {θ} = ⊤) (I : Ideal A) [I.IsMaximal]
    (σ : A ⧸ I →+* ℂ) (β : ℂ)
    (hβ : ((minpoly (A ⧸ I) (Ideal.Quotient.mk (I.map (algebraMap A B)) θ)).map σ).IsRoot β) :
    ∃ w : B →+* ℂ, w.comp (algebraMap A B) = σ.comp (Ideal.Quotient.mk I) ∧ w θ = β := by
  classical
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  let f : A[X] →+* B := (aeval θ).toRingHom
  have hf : Function.Surjective f := by
    intro b
    have hb : b ∈ Algebra.adjoin A {θ} := hgen ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨P, rfl⟩ := hb
    exact ⟨P, rfl⟩
  let g : A[X] →+* ℂ := eval₂RingHom (σ.comp (Ideal.Quotient.mk I)) β
  have hg : ∀ P : A[X], g P = ((P.map (algebraMap A (A ⧸ I))).map σ).eval β := by
    intro P
    rw [eval_map, eval₂_map, Ideal.Quotient.algebraMap_eq]
    rfl
  have hker : RingHom.ker f ≤ RingHom.ker g := by
    intro P hP
    rw [RingHom.mem_ker] at hP ⊢
    have h1 : aeval (Ideal.Quotient.mk (I.map (algebraMap A B)) θ) (P.map (algebraMap A (A ⧸ I))) = 0 := by
      rw [aeval_mk_map]
      change Ideal.Quotient.mk _ (f P) = 0
      rw [hP, map_zero]
    obtain ⟨r, hr⟩ := minpoly.dvd _ _ h1
    rw [hg, hr, Polynomial.map_mul, eval_mul, hβ.eq_zero, zero_mul]
  obtain ⟨w, hw⟩ : ∃ w : B →+* ℂ, ∀ P, w (f P) = g P := by
    refine ⟨(Ideal.Quotient.lift (RingHom.ker f) g hker).comp
      (RingHom.quotientKerEquivOfSurjective hf).symm.toRingHom, fun P => ?_⟩
    have he : (RingHom.quotientKerEquivOfSurjective hf).symm (f P) = Ideal.Quotient.mk (RingHom.ker f) P := by
      rw [RingEquiv.symm_apply_eq]
      rfl
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, he]
    exact Ideal.Quotient.lift_mk _ _ _
  refine ⟨w, ?_, ?_⟩
  · ext a
    have := hw (C a)
    simp only [f, g, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C, coe_eval₂RingHom, eval₂_C] at this
    simpa using this
  · have := hw X
    simpa [f, g] using this

variable [Algebra ℚ A] [Algebra.FiniteType ℚ A]

theorem exists_sub_mem_map (θ : B) (hgen : Algebra.adjoin A {θ} = ⊤) (p : ℚ[X]) (hpm : p.Monic)
    (hps : p.Separable) (hp : aeval θ (p.map (algebraMap ℚ A)) = 0)
    (huniq : ∀ w w' : B →+* ℂ, w.comp (algebraMap A B) = w'.comp (algebraMap A B) → w θ = w' θ)
    (I : Ideal A) [I.IsMaximal] (hI : I.map (algebraMap A B) ≠ ⊤) (b : B) :
    ∃ a : A, b - algebraMap A B a ∈ I.map (algebraMap A B) := by
  classical
  set J := I.map (algebraMap A B) with hJ
  letI : Field (A ⧸ I) := Ideal.Quotient.field I
  haveI : Nontrivial (B ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hI
  haveI : Algebra.FiniteType ℚ (A ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ I) (Ideal.Quotient.mkₐ_surjective ℚ I)
  haveI : Module.Finite ℚ (A ⧸ I) := finite_of_finite_type_of_isJacobsonRing ℚ (A ⧸ I)
  haveI : Algebra.IsAlgebraic ℚ (A ⧸ I) := Algebra.IsAlgebraic.of_finite ℚ _
  let σ : A ⧸ I →ₐ[ℚ] ℂ := IsAlgClosed.lift
  set θ' := Ideal.Quotient.mk J θ with hθ'def
  have hpF : p.map (algebraMap ℚ (A ⧸ I)) = (p.map (algebraMap ℚ A)).map (algebraMap A (A ⧸ I)) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  have hθ' : aeval θ' (p.map (algebraMap ℚ (A ⧸ I))) = 0 := by
    rw [hpF, hθ'def, aeval_mk_map, hp, map_zero]
  have hint : IsIntegral (A ⧸ I) θ' := ⟨_, hpm.map _, hθ'⟩
  have hmem : θ' ∈ (algebraMap (A ⧸ I) (B ⧸ J)).range := by
    by_contra hn
    have h2 := (minpoly.two_le_natDegree_iff hint).2 hn
    set q := (minpoly (A ⧸ I) θ').map (σ : A ⧸ I →+* ℂ) with hq
    have hs1 : (p.map (algebraMap ℚ (A ⧸ I))).Separable := hps.map
    have hs2 : (minpoly (A ⧸ I) θ').Separable := hs1.of_dvd (minpoly.dvd _ _ hθ')
    have hsep : q.Separable := hs2.map
    have hq0 : q ≠ 0 := (Polynomial.map_ne_zero (minpoly.ne_zero hint))
    have hcard : q.roots.toFinset.card = (minpoly (A ⧸ I) θ').natDegree := by
      rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree,
        natDegree_map]
    obtain ⟨β₁, h₁, β₂, h₂, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < q.roots.toFinset.card)
    rw [Multiset.mem_toFinset, mem_roots hq0] at h₁ h₂
    obtain ⟨w₁, hw₁, hθ₁⟩ := exists_ringHom_of_root θ hgen I σ β₁ h₁
    obtain ⟨w₂, hw₂, hθ₂⟩ := exists_ringHom_of_root θ hgen I σ β₂ h₂
    exact hne (hθ₁ ▸ hθ₂ ▸ huniq w₁ w₂ (hw₁.trans hw₂.symm))
  let S : Subalgebra A B := (⊥ : Subalgebra A (B ⧸ J)).comap (Ideal.Quotient.mkₐ A J)
  have hθS : θ ∈ S := by
    obtain ⟨c, hc⟩ := hmem
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
    show Ideal.Quotient.mkₐ A J θ ∈ (⊥ : Subalgebra A (B ⧸ J))
    have he : Ideal.Quotient.mkₐ A J θ = algebraMap A (B ⧸ J) a := by
      rw [Ideal.Quotient.mkₐ_eq_mk, ← hθ'def, ← hc, Ideal.Quotient.algebraMap_quotient_map_quotient,
        Ideal.Quotient.mk_algebraMap]
    rw [he]
    exact Subalgebra.algebraMap_mem _ a
  have hbS : b ∈ S := by
    have : Algebra.adjoin A {θ} ≤ S := Algebra.adjoin_le (Set.singleton_subset_iff.2 hθS)
    exact this (hgen ▸ Algebra.mem_top)
  obtain ⟨a, ha⟩ := Algebra.mem_bot.1 hbS
  refine ⟨a, ?_⟩
  rw [← Ideal.Quotient.eq]
  have he : Ideal.Quotient.mk J b = algebraMap A (B ⧸ J) a := ha.symm
  rw [he, Ideal.Quotient.mk_algebraMap]

theorem algebraMap_surjective (hinj : Function.Injective (algebraMap A B)) (θ : B)
    (hgen : Algebra.adjoin A {θ} = ⊤) (p : ℚ[X]) (hpm : p.Monic) (hps : p.Separable)
    (hp : aeval θ (p.map (algebraMap ℚ A)) = 0)
    (huniq : ∀ w w' : B →+* ℂ, w.comp (algebraMap A B) = w'.comp (algebraMap A B) → w θ = w' θ) :
    Function.Surjective (algebraMap A B) := by
  classical
  have hθA : IsIntegral A θ := ⟨p.map (algebraMap ℚ A), hpm.map _, hp⟩
  haveI : Algebra.IsIntegral A B :=
    ⟨fun b => adjoin_le_integralClosure hθA (hgen ▸ Algebra.mem_top : b ∈ Algebra.adjoin A {θ})⟩
  haveI : Algebra.FiniteType A B := ⟨⟨{θ}, by simpa using hgen⟩⟩
  haveI : Module.Finite A B := Algebra.finite_iff_isIntegral_and_finiteType.2 ⟨inferInstance, inferInstance⟩
  set N := LinearMap.range (Algebra.linearMap A B) with hN
  have hann : Module.annihilator A (B ⧸ N) = ⊤ := by
    by_contra hne
    obtain ⟨I, hI, hle⟩ := Ideal.exists_le_maximal _ hne
    have hIB : I.map (algebraMap A B) ≠ ⊤ := by
      have hk : RingHom.ker (algebraMap A B) ≤ I := by
        rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
        exact bot_le
      obtain ⟨Q, hQ, hQI⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral I hk
      intro htop
      apply hQ.ne_top
      rw [eq_top_iff, ← htop, Ideal.map_le_iff_le_comap, hQI]
    have hsmul : (⊤ : Submodule A (B ⧸ N)) ≤ I • ⊤ := by
      rintro x -
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N x
      obtain ⟨a, ha⟩ := exists_sub_mem_map θ hgen p hpm hps hp huniq I hIB b
      have h1 : b - algebraMap A B a ∈ I • (⊤ : Submodule A B) := by
        rw [Ideal.smul_top_eq_map]
        exact ha
      have h2 : N.mkQ (b - algebraMap A B a) ∈ I • (⊤ : Submodule A (B ⧸ N)) := by
        have := Submodule.mem_map_of_mem (f := N.mkQ) h1
        rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this
      have h3 : N.mkQ (algebraMap A B a) = 0 := (Submodule.Quotient.mk_eq_zero N).2 ⟨a, rfl⟩
      rw [map_sub, h3, sub_zero] at h2
      exact h2
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I ⊤
      (Module.finite_def.1 inferInstance) hsmul
    have hr' : r ∈ I := hle (Module.mem_annihilator.2 fun x => hr x Submodule.mem_top)
    exact hI.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using I.sub_mem hr' hr1))
  intro b
  have h1 : (1 : A) ∈ Module.annihilator A (B ⧸ N) := hann ▸ Submodule.mem_top
  have h0 : (Submodule.Quotient.mk b : B ⧸ N) = 0 := by
    simpa using Module.mem_annihilator.1 h1 (Submodule.Quotient.mk b)
  obtain ⟨a, ha⟩ := (Submodule.Quotient.mk_eq_zero N).1 h0
  exact ⟨a, ha⟩

end Fibre

theorem exists_nat_mul_mem {Ω : Type*} [Field Ω] [CharZero Ω] (R : Subalgebra ℤ Ω) {x : Ω}
    (hx : x ∈ Algebra.adjoin ℚ (R : Set Ω)) : ∃ n : ℕ, 0 < n ∧ (n : Ω) * x ∈ R := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_pos, ?_⟩
    have : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [eq_ratCast, ← Rat.cast_natCast, ← Rat.cast_mul, mul_comm, Rat.mul_den_eq_num, Rat.cast_intCast]
    rw [this]
    exact Subalgebra.intCast_mem R _
  | add x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (x + y) = (n₂ : Ω) * ((n₁ : Ω) * x) + (n₁ : Ω) * ((n₂ : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact R.add_mem (R.mul_mem (Subalgebra.natCast_mem R _) hx) (R.mul_mem (Subalgebra.natCast_mem R _) hy)
  | mul x y _ _ hx hy =>
    obtain ⟨n₁, h₁, hx⟩ := hx
    obtain ⟨n₂, h₂, hy⟩ := hy
    refine ⟨n₁ * n₂, Nat.mul_pos h₁ h₂, ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (x * y) = ((n₁ : Ω) * x) * ((n₂ : Ω) * y) := by
      push_cast; ring
    rw [this]
    exact R.mul_mem hx hy

theorem exists_primitive {F Ω : Type*} [Field F] [CharZero F] [Field Ω] [Algebra F Ω] (S : Finset Ω)
    (hS : ∀ s ∈ S, IsIntegral F s) :
    ∃ θ : Ω, IsIntegral F θ ∧ θ ∈ Algebra.adjoin F (S : Set Ω) ∧
      ∀ x ∈ IntermediateField.adjoin F (S : Set Ω), x ∈ Algebra.adjoin F {θ} := by
  haveI : FiniteDimensional F (IntermediateField.adjoin F (S : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => hS x hx
  obtain ⟨α, hα⟩ := Field.exists_primitive_element F (IntermediateField.adjoin F (S : Set Ω))
  have hθint : IsIntegral F (α : Ω) := (IsIntegral.of_finite F α).map (IntermediateField.adjoin F (S : Set Ω)).val
  have hK : IntermediateField.adjoin F {(α : Ω)} = IntermediateField.adjoin F (S : Set Ω) := by
    simpa only [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top] using
      congr_arg IntermediateField.lift hα
  refine ⟨α, hθint, ?_, fun x hx => ?_⟩
  · have h1 : (α : Ω) ∈ IntermediateField.adjoin F (S : Set Ω) := α.2
    rw [← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun x hx => (hS x hx).isAlgebraic)] at h1
    exact h1
  · rw [← hK, ← IntermediateField.mem_toSubalgebra, IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (fun y hy => by rw [Set.mem_singleton_iff.1 hy]; exact hθint.isAlgebraic)] at hx
    exact hx

theorem mem_of_unique_extension {Ω : Type*} [Field Ω] [CharZero Ω] (A : Subalgebra ℚ Ω) [Algebra.FiniteType ℚ A]
    (θ : Ω) (hθ : IsIntegral ℚ θ)
    (huniq : ∀ w w' : Algebra.adjoin A {θ} →+* ℂ,
      w.comp (algebraMap A (Algebra.adjoin A {θ})) = w'.comp (algebraMap A (Algebra.adjoin A {θ})) →
        w ⟨θ, Algebra.subset_adjoin rfl⟩ = w' ⟨θ, Algebra.subset_adjoin rfl⟩) :
    θ ∈ A := by
  have hgen : Algebra.adjoin A {(⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})} = ⊤ := by
    have := Algebra.adjoin_adjoin_coe_preimage (R := A) (s := ({θ} : Set Ω))
    convert this using 2
    ext x
    simp [Subtype.ext_iff]
  have hinj : Function.Injective (algebraMap A (Algebra.adjoin A {θ})) := by
    intro x y h
    apply Subtype.ext
    have := congrArg (Algebra.adjoin A {θ}).val h
    rw [AlgHom.commutes, AlgHom.commutes] at this
    exact this
  have hpB : aeval (⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})
      ((minpoly ℚ θ).map (algebraMap ℚ A)) = 0 := by
    have h := aeval_algHom_apply (Algebra.adjoin A {θ}).val ⟨θ, Algebra.subset_adjoin rfl⟩
      ((minpoly ℚ θ).map (algebraMap ℚ A))
    rw [aeval_map_algebraMap] at h
    have h0 : (Algebra.adjoin A {θ}).val (aeval (⟨θ, Algebra.subset_adjoin rfl⟩ : Algebra.adjoin A {θ})
        ((minpoly ℚ θ).map (algebraMap ℚ A))) = 0 := by
      rw [← h]
      exact minpoly.aeval ℚ θ
    exact (map_eq_zero_iff _ Subtype.val_injective).1 h0
  obtain ⟨a, ha⟩ := algebraMap_surjective hinj _ hgen (minpoly ℚ θ) (minpoly.monic hθ)
    (minpoly.irreducible hθ).separable hpB huniq ⟨θ, Algebra.subset_adjoin rfl⟩
  have h1 : (Algebra.adjoin A {θ}).val (algebraMap A _ a) = θ := congrArg Subtype.val ha
  rw [AlgHom.commutes] at h1
  rw [← h1]
  exact a.2

theorem agree_on_adjoin {Ω : Type*} [Field Ω] [CharZero Ω] (R T : Subalgebra ℤ Ω) (A : Subalgebra ℚ Ω)
    (B : Subalgebra A Ω) (hRA : ∀ r ∈ R, r ∈ A) (θ : Ω) (hθB : θ ∈ B)
    (hTθ : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ {θ})
    (H : ∀ w w' : ↥(R ⊔ T) →+* ℂ,
      w.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom →
        w.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom =
          w'.comp (Subalgebra.inclusion (le_sup_right : T ≤ R ⊔ T)).toRingHom)
    (w w' : B →+* ℂ) (hw : w.comp (algebraMap A B) = w'.comp (algebraMap A B)) :
    ∀ x ∈ Algebra.adjoin ℚ (T : Set Ω), x ∈ (RingHom.eqLocus w w').map B.val.toRingHom := by
  have hTB : ∀ t ∈ T, t ∈ B := fun t ht =>
    (Algebra.adjoin_le (Set.singleton_subset_iff.2 hθB) : Algebra.adjoin ℚ {θ} ≤ B.restrictScalars ℚ) (hTθ t ht)
  have hsub : ∀ x ∈ R ⊔ T, x ∈ B := by
    have : R ⊔ T ≤ B.restrictScalars ℤ :=
      sup_le (fun r hr => B.algebraMap_mem (⟨r, hRA r hr⟩ : A)) (fun t ht => hTB t ht)
    exact fun x hx => this hx
  let ι : ↥(R ⊔ T) →+* B := ((R ⊔ T).val : ↥(R ⊔ T) →ₐ[ℤ] Ω).toRingHom.codRestrict B fun x => hsub x.1 x.2
  have hR' : (w.comp ι).comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom =
      (w'.comp ι).comp (Subalgebra.inclusion (le_sup_left : R ≤ R ⊔ T)).toRingHom := by
    ext ⟨r, hr⟩
    exact RingHom.congr_fun hw (⟨r, hRA r hr⟩ : A)
  have hT' := H _ _ hR'
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem t ht =>
    refine Subring.mem_map.2 ⟨⟨t, hTB t ht⟩, ?_, rfl⟩
    exact RingHom.congr_fun hT' ⟨t, ht⟩
  | algebraMap q =>
    refine Subring.mem_map.2 ⟨algebraMap A B (algebraMap ℚ A q), RingHom.congr_fun hw _, ?_⟩
    exact (B.val.commutes _).trans (IsScalarTower.algebraMap_apply ℚ A Ω q).symm
  | add x y _ _ hx hy => exact Subring.add_mem _ hx hy
  | mul x y _ _ hx hy => exact Subring.mul_mem _ hx hy

theorem proof : ConstantsDescend.Statement := by
  intro Ω _ _ R T hR hT H
  classical

  obtain ⟨S, hS⟩ := (Module.Finite.iff_fg (N := Subalgebra.toSubmodule T)).1 hT
  have hST : ∀ s ∈ S, s ∈ T := fun s hs => by
    have : s ∈ Subalgebra.toSubmodule T := hS ▸ Submodule.subset_span hs
    exact this
  have hTspan : ∀ t ∈ T, t ∈ Submodule.span ℤ (S : Set Ω) := fun t ht => by
    rw [hS]
    exact ht
  have hintQ : ∀ s ∈ S, IsIntegral ℚ s := fun s hs =>
    ((IsIntegral.of_finite ℤ (⟨s, hST s hs⟩ : T)).map T.val).tower_top

  obtain ⟨θ, hθint, hθT', hKθ⟩ := exists_primitive S hintQ
  have hθT : θ ∈ Algebra.adjoin ℚ (T : Set Ω) := Algebra.adjoin_mono (fun s hs => hST s hs) hθT'
  have hTθ : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ {θ} := fun t ht => hKθ t <|
    Submodule.span_induction (p := fun x _ => x ∈ IntermediateField.adjoin ℚ (S : Set Ω))
      (fun x hx => IntermediateField.subset_adjoin ℚ _ hx) (IntermediateField.zero_mem _)
      (fun x y _ _ hx hy => IntermediateField.add_mem _ hx hy) (fun z x _ hx => zsmul_mem hx z) (hTspan t ht)

  obtain ⟨s, hs⟩ := hR
  have hAfg : (Algebra.adjoin ℚ (R : Set Ω)).FG := ⟨s, by rw [← hs, Algebra.adjoin_adjoin_of_tower]⟩
  haveI : Algebra.FiniteType ℚ (Algebra.adjoin ℚ (R : Set Ω)) := (Subalgebra.fg_iff_finiteType _).1 hAfg

  have hθA : θ ∈ Algebra.adjoin ℚ (R : Set Ω) := by
    refine mem_of_unique_extension _ θ hθint fun w w' hw => ?_
    obtain ⟨y, hy, hyθ⟩ := Subring.mem_map.1 (agree_on_adjoin R T _
      (Algebra.adjoin (Algebra.adjoin ℚ (R : Set Ω)) {θ}) (fun r hr => Algebra.subset_adjoin hr) θ
      (Algebra.subset_adjoin (Set.mem_singleton θ)) hTθ H w w' hw θ hθT)
    have : y = ⟨θ, Algebra.subset_adjoin rfl⟩ := Subtype.ext hyθ
    rw [← this]
    exact hy

  have hTA : ∀ t ∈ T, t ∈ Algebra.adjoin ℚ (R : Set Ω) := fun t ht =>
    (Algebra.adjoin_le (Set.singleton_subset_iff.2 hθA) : Algebra.adjoin ℚ {θ} ≤ _) (hTθ t ht)

  have hn : ∀ s ∈ S, ∃ n : ℕ, 0 < n ∧ (n : Ω) * s ∈ R := fun s hs => exists_nat_mul_mem R (hTA s (hST s hs))
  choose! n hn0 hnR using hn
  refine ⟨∏ s ∈ S, n s, Finset.prod_pos hn0, fun t ht => ?_⟩
  refine Submodule.span_induction (p := fun x _ => ((∏ s ∈ S, n s : ℕ) : Ω) * x ∈ R) ?_ ?_ ?_ ?_ (hTspan t ht)
  · intro x hx
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n hx
    rw [hk, Nat.cast_mul, mul_comm ((n x : ℕ) : Ω), mul_assoc]
    exact R.mul_mem (Subalgebra.natCast_mem R k) (hnR x hx)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact R.add_mem hx hy
  · intro z x _ hx
    rw [mul_smul_comm]
    exact zsmul_mem hx z

end ConstantsDescend

end GroundTheory.Heights₂.Heights.HilbertSamuel
