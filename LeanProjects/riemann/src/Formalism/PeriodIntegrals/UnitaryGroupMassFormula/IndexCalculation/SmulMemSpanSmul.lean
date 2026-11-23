import Mathlib
import Formalism.PeriodIntegrals.IdxCalc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IndexCalculation.IsLocalizedModuleToSpan

noncomputable section

namespace PI.Dv.IdxW

open NumberField IsDedekindDomain Module

section Gen

variable {R : Type*} [CommRing R] {V : Type*} [AddCommGroup V] [Module R V]

theorem comap_smul_top (I : Ideal R) (M : Submodule R V) :
    (I • M).comap M.subtype = I • (⊤ : Submodule R M) := by
  have e := Submodule.map_smul'' I (⊤ : Submodule R M) M.subtype
  rw [Submodule.map_subtype_top] at e
  rw [← e, Submodule.comap_map_eq_of_injective M.injective_subtype]

theorem ideal_localized' (S : Submonoid R) (I : Ideal R) :
    I.localized' (Localization S) S (Algebra.linearMap R (Localization S)) =
      I.map (algebraMap R (Localization S)) := by
  exact Ideal.localized'_eq_map (Localization S) S I

theorem span_smul_le (c : R) (M N : Submodule R V) (h : ∀ x ∈ M, c • x ∈ N) :
    Ideal.span {c} • M ≤ N := by
  rw [Submodule.smul_le]
  intro r hr x hx
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hr
  rw [mul_smul]
  exact N.smul_mem a (h x hx)

theorem smul_mem_span_smul (c : R) (M : Submodule R V) {x : V} (hx : x ∈ M) :
    c • x ∈ Ideal.span {c} • M := by
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) hx

theorem lenS_ker_img (S : Submonoid R) {V' : Type*} [AddCommGroup V'] [Module R V']
    (φ : V →ₗ[R] V') (k : Submodule R V) (hk : ∀ x, x ∈ k ↔ φ x = 0) (D X : Submodule R V)
    (hDX : D ≤ X) :
    lenS S X D = lenS S (X ⊓ k) (D ⊓ k) + lenS S (X.map φ) (D.map φ) := by
  let f0 : ↥(X ⊓ k) →ₗ[R] ↥X := Submodule.inclusion inf_le_left
  let g0 : ↥X →ₗ[R] ↥(X.map φ) := φ.submoduleMap X
  let f := Submodule.mapQ ((D ⊓ k).comap (X ⊓ k).subtype) (D.comap X.subtype) f0 (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, f0, Submodule.coe_inclusion] at hx ⊢
    exact (Submodule.mem_inf.1 hx).1)
  let g := Submodule.mapQ (D.comap X.subtype) ((D.map φ).comap (X.map φ).subtype) g0 (by
    intro x hx
    simp only [Submodule.mem_comap, Submodule.subtype_apply, g0, LinearMap.submoduleMap_coe_apply] at hx ⊢
    exact Submodule.mem_map_of_mem hx)
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    induction a using Submodule.Quotient.induction_on with
    | H x =>
      simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
        Submodule.subtype_apply, f0, Submodule.coe_inclusion] at ha ⊢
      exact Submodule.mem_inf.2 ⟨ha, (Submodule.mem_inf.1 x.2).2⟩
  have hg : Function.Surjective g := by
    intro c
    induction c using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨x, hx, hxy⟩ := Submodule.mem_map.1 y.2
      refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, ?_⟩
      simp only [g, Submodule.mapQ_apply]
      congr 1
      ext
      simp [g0, hxy]
  have hex : Function.Exact f g := by
    intro b
    induction b using Submodule.Quotient.induction_on with
    | H x =>
      constructor
      · intro h
        simp only [g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.subtype_apply, g0, LinearMap.submoduleMap_coe_apply] at h
        obtain ⟨d, hd, hdx⟩ := Submodule.mem_map.1 h
        have hmem : (x : V) - d ∈ X ⊓ k :=
          Submodule.mem_inf.2 ⟨X.sub_mem x.2 (hDX hd), (hk _).2 (by rw [map_sub, hdx, sub_self])⟩
        refine ⟨Submodule.Quotient.mk ⟨(x : V) - d, hmem⟩, ?_⟩
        simp only [f, Submodule.mapQ_apply]
        rw [Submodule.Quotient.eq]
        simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, f0,
          Submodule.coe_inclusion, sub_sub_cancel_left, neg_mem_iff]
        exact hd
      · rintro ⟨a, ha⟩
        rw [← ha]
        induction a using Submodule.Quotient.induction_on with
        | H z =>
          simp only [f, g, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
            Submodule.subtype_apply, f0, g0, LinearMap.submoduleMap_coe_apply, Submodule.coe_inclusion]
          rw [(hk _).1 (Submodule.mem_inf.1 z.2).2]
          exact Submodule.zero_mem _
  unfold lenS
  exact Module.length_eq_add_of_exact (LocalizedModule.map S f) (LocalizedModule.map S g)
    (LocalizedModule.map_injective S f hf) (LocalizedModule.map_surjective S g hg)
    (LocalizedModule.map_exact S f g hex)

end Gen

variable {K : Type} [Field K] [NumberField K]

instance instIsPrimeW (w : HeightOneSpectrum (𝓞 K)) : w.asIdeal.IsPrime := w.isPrime

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [Module K V] [IsScalarTower (𝓞 K) K V] in
theorem lenAt_eq (w : HeightOneSpectrum (𝓞 K)) (M N : Submodule (𝓞 K) V) :
    lenAt w M N = lenS w.asIdeal.primeCompl M N := rfl

theorem len_pow (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) (hM : M.FG) (F : ℕ) :
    lenS w.asIdeal.primeCompl M ((w.asIdeal ^ F) • M) = ((F * Formalism.HN.rkK M : ℕ) : ℕ∞) := by
  set S := w.asIdeal.primeCompl with hS
  have hSle : S ≤ nonZeroDivisors (𝓞 K) := Ideal.primeCompl_le_nonZeroDivisors _
  have : IsDiscreteValuationRing (Localization.AtPrime w.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) w.ne_bot
      (Localization.AtPrime w.asIdeal)
  have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM
  have : Module.IsTorsionFree (𝓞 K) M := isTorsionFree_sub K M
  have : Module.Finite (Localization S) (LocalizedModule S M) :=
    Module.Finite.of_isLocalizedModule S (LocalizedModule.mkLinearMap S M)
  have : Module.Free (Localization S) (LocalizedModule S M) :=
    Module.free_of_finite_type_torsion_free'
  have hr : Module.finrank (Localization S) (LocalizedModule S M) = Formalism.HN.rkK M := by
    rw [IsLocalization.finrank_eq (Localization S) S hSle,
      IsLocalizedModule.finrank_eq S (LocalizedModule.mkLinearMap S M) hSle]
    unfold Formalism.HN.rkK
    rw [finrank_span_eq (K := K)]
  have hloc : ((w.asIdeal ^ F • (⊤ : Submodule (𝓞 K) M)).localized S) =
      (IsLocalRing.maximalIdeal (Localization.AtPrime w.asIdeal) ^ F) •
        (⊤ : Submodule (Localization S) (LocalizedModule S M)) := by
    dsimp only [Submodule.localized]
    rw [Submodule.localized'_smul, Submodule.localized'_top, ideal_localized', Ideal.map_pow,
      Localization.AtPrime.map_eq_maximalIdeal]
  unfold lenS
  rw [comap_smul_top, ← (localizedQuotientEquiv S (w.asIdeal ^ F • (⊤ : Submodule (𝓞 K) M))).length_eq,
    hloc, length_quot_free, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, hr]
  push_cast
  ring

theorem fact (w : HeightOneSpectrum (𝓞 K)) {c : 𝓞 K} (hc : c ≠ 0) :
    ∃ k : ℕ, Formalism.BasicNotions.vAdd w (algebraMap (𝓞 K) K c) = k ∧ c ∈ w.asIdeal ^ k ∧
      ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∀ y ∈ w.asIdeal ^ k, s * y ∈ Ideal.span {c} := by
  classical
  set v := w.intValuation c with hv
  have hv0 : v ≠ 0 := w.intValuation_ne_zero c hc
  have hv1 : v ≤ 1 := w.intValuation_le_one c
  have hval : w.valuation K (algebraMap (𝓞 K) K c) = v := w.valuation_of_algebraMap c
  obtain ⟨m, hm⟩ : ∃ m : ℤ, v = WithZero.exp m := ⟨WithZero.log v, (WithZero.exp_log hv0).symm⟩
  have hm0 : m ≤ 0 := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at hv1
    exact hv1
  have hkm : (((-m).toNat : ℕ) : ℤ) = -m := by omega
  have hck : c ∈ w.asIdeal ^ (-m).toNat := by
    rw [← w.intValuation_le_pow_iff_mem, ← hv, hm, hkm, neg_neg]
  have hck1 : c ∉ w.asIdeal ^ ((-m).toNat + 1) := by
    intro h
    have h' := (w.intValuation_le_pow_iff_mem c _).2 h
    rw [← hv, hm, WithZero.exp_le_exp] at h'
    push_cast at h'
    omega
  refine ⟨(-m).toNat, ?_, hck, ?_⟩
  · simp only [Formalism.BasicNotions.vAdd, hval, hm, WithZero.log_exp]
    omega
  obtain ⟨J, hJ⟩ : w.asIdeal ^ (-m).toNat ∣ Ideal.span {c} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hck)
  have hJp : ¬ J ≤ w.asIdeal := by
    intro hle
    apply hck1
    have hle' : Ideal.span {c} ≤ w.asIdeal ^ ((-m).toNat + 1) := by
      rw [hJ, pow_succ]
      exact Ideal.mul_mono_right hle
    exact hle' (Ideal.mem_span_singleton_self c)
  obtain ⟨s, hsJ, hsp⟩ := SetLike.not_le_iff_exists.1 hJp
  refine ⟨s, hsp, fun y hy => ?_⟩
  rw [hJ, mul_comm s y]
  exact Ideal.mul_mem_mul hy hsJ

private lemma lenS_unit_lemma_2 {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
    (S : Submonoid R) (X Y : Submodule R W) (s : R) (hs : s ∈ S) (h : ∀ x ∈ X, s • x ∈ Y) :
    lenS S X Y = 0 := by
  unfold lenS
  rw [Module.length_eq_zero_iff]
  have hall : ∀ a : LocalizedModule S (↥X ⧸ Y.comap X.subtype), a = 0 := by
    intro a
    induction a using LocalizedModule.induction_on with
    | h m t =>
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [← LocalizedModule.zero_mk (1 : S), LocalizedModule.mk_eq]
        refine ⟨⟨s, hs⟩, ?_⟩
        simp only [one_smul, smul_zero]
        rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
        simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
        exact h _ x.2
  exact ⟨fun a b => by rw [hall a, hall b]⟩

private lemma lenS_split_lemma {R : Type*} [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
    (S : Submonoid R) (M N D : Submodule R W) (hDM : D ≤ M) (hDN : D ≤ N) :
    lenS S M D = lenS S M N + lenS S (M ⊓ N) D := by
  have hk : ∀ x, x ∈ N ↔ N.mkQ x = 0 := fun x => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have h1 := lenS_ker_img S N.mkQ N hk D M hDM
  have h2 := lenS_ker_img S N.mkQ N hk (M ⊓ N) M inf_le_left
  have hbot : ∀ E : Submodule R W, E ≤ N → E.map N.mkQ = ⊥ := fun E hE => by
    refine eq_bot_iff.2 fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
    rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hE hx
  have hz : lenS S (M ⊓ N) (M ⊓ N ⊓ N) = 0 :=
    lenS_unit_lemma_2 S _ _ 1 (Submonoid.one_mem S) (fun x hx => by
      rw [one_smul]
      exact Submodule.mem_inf.2 ⟨hx, (Submodule.mem_inf.1 hx).2⟩)
  rw [inf_eq_left.2 hDN, hbot D hDN] at h1
  rw [hbot _ inf_le_right, hz, zero_add] at h2
  have e : N.comap M.subtype = (M ⊓ N).comap M.subtype := by
    ext x
    simp [Submodule.mem_inf, x.2]
  have hc : lenS S M N = lenS S M (M ⊓ N) := by
    unfold lenS
    rw [e]
  rw [h1, hc, h2, add_comm]

theorem len_c (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) (hM : M.FG) {c : 𝓞 K}
    (hc : c ≠ 0) :
    ∃ k : ℕ, Formalism.BasicNotions.vAdd w (algebraMap (𝓞 K) K c) = k ∧
      lenS w.asIdeal.primeCompl M (Ideal.span {c} • M) = ((k * Formalism.HN.rkK M : ℕ) : ℕ∞) := by
  obtain ⟨k, hk, hck, s, hs, hsy⟩ := fact w hc
  refine ⟨k, hk, ?_⟩
  have hle1 : Ideal.span {c} • M ≤ (w.asIdeal ^ k) • M :=
    Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem _).2 hck)
  have hle2 : (w.asIdeal ^ k) • M ≤ M := Submodule.smul_le_right
  rw [lenS_split_lemma _ M ((w.asIdeal ^ k) • M) _ (hle1.trans hle2) hle1, len_pow w M hM k]
  rw [lenS_unit_lemma_2 w.asIdeal.primeCompl _ _ s hs, add_zero]
  intro x hx
  have hx2 : x ∈ (w.asIdeal ^ k) • M := (Submodule.mem_inf.1 hx).2
  refine Submodule.smul_induction_on (p := fun x => s • x ∈ Ideal.span {c} • M) hx2
    (fun y hy z hz => ?_) (fun a b ha hb => ?_)
  · rw [← mul_smul]
    exact Submodule.smul_mem_smul (hsy y hy) hz
  · simp only [smul_add]
    exact Submodule.add_mem _ ha hb

theorem lenS_ne_top (w : HeightOneSpectrum (𝓞 K)) (X Y : Submodule (𝓞 K) V) (hX : X.FG)
    {c : 𝓞 K} (hc : c ≠ 0) (h : ∀ x ∈ X, c • x ∈ Y) : lenS w.asIdeal.primeCompl X Y ≠ ⊤ := by
  obtain ⟨k, -, hk⟩ := len_c w X hX hc
  have hD : Ideal.span {c} • X ≤ Y := span_smul_le c X Y h
  have e := lenS_split_lemma w.asIdeal.primeCompl X Y _ Submodule.smul_le_right hD
  rw [hk] at e
  intro htop
  rw [htop, top_add] at e
  exact ENat.coe_ne_top _ e

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem idx_via (w : HeightOneSpectrum (𝓞 K)) (M N D : Submodule (𝓞 K) V) (hDM : D ≤ M)
    (hDN : D ≤ N) (hM : lenS w.asIdeal.primeCompl M D ≠ ⊤)
    (hN : lenS w.asIdeal.primeCompl N D ≠ ⊤) :
    idxAt w M N = ((lenS w.asIdeal.primeCompl M D).toNat : ℤ) -
      (lenS w.asIdeal.primeCompl N D).toNat := by
  have lenS_zero : ∀ X Y : Submodule (𝓞 K) V, X ≤ Y → lenS w.asIdeal.primeCompl X Y = 0 := by
    intro X Y h
    unfold lenS
    rw [Module.length_eq_zero_iff]
    have : Subsingleton (↥X ⧸ Y.comap X.subtype) := by
      rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
      intro x _
      exact h x.2
    constructor
    intro a b
    induction a using LocalizedModule.induction_on with
    | h m s =>
      induction b using LocalizedModule.induction_on with
      | h m' s' =>
        rw [Subsingleton.elim m 0, Subsingleton.elim m' 0, LocalizedModule.zero_mk,
          LocalizedModule.zero_mk]
  have split : ∀ M N D : Submodule (𝓞 K) V, D ≤ M → D ≤ N →
      lenS w.asIdeal.primeCompl M D = lenS w.asIdeal.primeCompl M N +
        lenS w.asIdeal.primeCompl (M ⊓ N) D := by
    intro M N D hDM hDN
    have hk : ∀ x, x ∈ N ↔ N.mkQ x = 0 := fun x => by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    have h1 := lenS_ker_img w.asIdeal.primeCompl N.mkQ N hk D M hDM
    have h2 := lenS_ker_img w.asIdeal.primeCompl N.mkQ N hk (M ⊓ N) M inf_le_left
    have hbot : ∀ E : Submodule (𝓞 K) V, E ≤ N → E.map N.mkQ = ⊥ := fun E hE => by
      refine eq_bot_iff.2 fun y hy => ?_
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
      rw [Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hE hx
    rw [inf_eq_left.2 hDN, hbot D hDN] at h1
    rw [hbot _ inf_le_right, lenS_zero _ _ (le_inf le_rfl inf_le_right), zero_add] at h2
    have hc : lenS w.asIdeal.primeCompl M N = lenS w.asIdeal.primeCompl M (M ⊓ N) := by
      have e : N.comap M.subtype = (M ⊓ N).comap M.subtype := by
        ext x
        simp [Submodule.mem_inf, x.2]
      unfold lenS
      rw [e]
    rw [h1, hc, h2, add_comm]
  have hs := split M N D hDM hDN
  have hs' := split N M D hDN hDM
  rw [inf_comm] at hs'
  unfold PI.Dv.idxAt
  rw [lenAt_eq, lenAt_eq, hs, hs']
  rw [hs] at hM
  rw [hs'] at hN
  rw [ENat.toNat_add (WithTop.add_ne_top.1 hM).1 (WithTop.add_ne_top.1 hM).2,
    ENat.toNat_add (WithTop.add_ne_top.1 hN).1 (WithTop.add_ne_top.1 hN).2]
  push_cast
  ring

end PI.Dv.IdxW
