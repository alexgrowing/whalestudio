import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.ImportsBis
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Imports
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartResidueDegree

theorem aeval_mul_of_isHomogeneous {F : Type} [Field F] {n : ℕ} {A : Type*} [CommRing A] [Algebra F A]
    {g : MvPolynomial (Fin n) F} {d : ℕ} (hg : g.IsHomogeneous d) (a : A) (x : Fin n → A) :
    aeval (fun m => a * x m) g = a ^ d * aeval x g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hd := hg (mem_support_iff.mp hs)
  simp only [aeval_monomial, mul_pow]
  rw [Finsupp.prod_mul, Finsupp.prod_pow, Finsupp.prod_pow, Finset.prod_pow_eq_pow_sum, ← hd,
    Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [smul_eq_mul, Pi.one_apply, mul_one]
  ring

theorem exists_chartHom {F : Type} [Field F] {n e : ℕ} {I W : Ideal (MvPolynomial (Fin n) F)} [W.IsPrime]
    (hWh : IsHomogIdeal W) (hIW : I ≤ W) {t : Fin n → F}
    (ξ : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ W))
    (hξ : ∀ h, aeval ξ h = algebraMap _ (FractionRing (MvPolynomial (Fin n) F ⧸ W)) (Ideal.Quotient.mk W h))
    (ℓ : FractionRing (MvPolynomial (Fin n) F ⧸ W)) (hℓdef : ℓ = aeval ξ (linForm t)) (hℓ : ℓ ≠ 0)
    (c : Fin n → FractionRing (MvPolynomial (Fin n) F ⧸ W)) (hc : ∑ j, c j * ξ j = 1) :
    ∃ ΦI : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ W)),
      (∀ s, ΦI (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) s) = aeval (genSubst ξ c) s) ∧
      (∀ h, ΦI (chartX I t e h) = C (aeval (fun m => ξ m / ℓ) h)) ∧
      ∀ h ∈ W, aeval (fun m => ξ m / ℓ) h = 0 := by
  let Φ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →ₐ[F] MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ W)) :=
    aeval (Sum.elim (fun m => C (ξ m / ℓ)) (genSubst ξ c))
  have hΦinl : ∀ h, Φ (rename Sum.inl h) = C (aeval (fun m => ξ m / ℓ) h) := by
    intro h
    rw [aeval_rename, Sum.elim_comp_inl, ← algebraMap_eq]
    exact aeval_algebraMap_apply _ _ _
  have hΦinr : ∀ h, Φ (rename Sum.inr h) = aeval (genSubst ξ c) h := by
    intro h
    rw [aeval_rename, Sum.elim_comp_inr]
  have hdeh : ∀ h ∈ W, aeval (fun m => ξ m / ℓ) h = 0 := by
    intro h hh
    rw [← sum_homogeneousComponent h, map_sum]
    refine Finset.sum_eq_zero fun d _ => ?_
    have : (fun m => ξ m / ℓ) = fun m => ℓ⁻¹ * ξ m := funext fun m => by rw [div_eq_inv_mul]
    rw [this, aeval_mul_of_isHomogeneous (homogeneousComponent_isHomogeneous d h), hξ,
      Ideal.Quotient.eq_zero_iff_mem.mpr (hWh h hh d), map_zero, mul_zero]
  have hlt1 : aeval (fun m => ξ m / ℓ) (linForm t - 1) = 0 := by
    have : (fun m => ξ m / ℓ) = fun m => ℓ⁻¹ * ξ m := funext fun m => by rw [div_eq_inv_mul]
    have hlin : (linForm t).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ fun _ _ => isHomogeneous_C_mul_X _ _
    rw [map_sub, map_one, this, aeval_mul_of_isHomogeneous hlin, pow_one, ← hℓdef,
      inv_mul_cancel₀ hℓ, sub_self]
  have hJ : chartIncIdeal I t e ≤ RingHom.ker Φ := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      refine sup_le (fun h hh => ?_) ?_
      · rw [Ideal.mem_comap, RingHom.mem_ker, hΦinl, hdeh h (hIW hh), C_0]
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, RingHom.mem_ker,
          hΦinl, hlt1, C_0]
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker, map_sum]
      simp only [map_mul, Φ, aeval_X, Sum.elim_inl, Sum.elim_inr, genSubst]
      set S := ∑ l, X (i, l) * C (ξ l)
      have h1 : ∑ m, X (i, m) * C (ξ m / ℓ) = S * C ℓ⁻¹ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [div_eq_mul_inv, C_mul, mul_assoc]
      have h2 : ∑ m, S * C (c m) * C (ξ m / ℓ) = S * C ℓ⁻¹ := by
        simp_rw [mul_assoc, ← C_mul, ← Finset.mul_sum, ← map_sum]
        congr 2
        simp_rw [div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul]
        rw [hc, one_mul]
      simp_rw [sub_mul, Finset.sum_sub_distrib]
      rw [h1, h2, sub_self]

  let ΦI : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (FractionRing (MvPolynomial (Fin n) F ⧸ W)) :=
    Ideal.Quotient.lift (chartIncIdeal I t e) Φ.toRingHom fun a ha => hJ ha
  have hΦIS : ∀ s : MvPolynomial (Fin e × Fin n) F, ΦI (algebraMap _ (ChartInc I t e) s) = aeval (genSubst ξ c) s := by
    intro s
    show ΦI (Ideal.Quotient.mk _ (rename Sum.inr s)) = _
    exact hΦinr s
  have hΦIX : ∀ h, ΦI (chartX I t e h) = C (aeval (fun m => ξ m / ℓ) h) := by
    intro h
    show ΦI (Ideal.Quotient.mk _ (rename Sum.inl h)) = _
    exact hΦinl h
  exact ⟨ΦI, hΦIS, hΦIX, hdeh⟩

theorem ratio {K σ : Type*} [Field K] {n : ℕ} (ξ τ : Fin n → K) (A : Fin n → MvPolynomial σ K)
    (B : MvPolynomial σ K) (ℓ' : K) (hB : B ≠ 0) (hℓ : ∑ l, τ l * ξ l ≠ 0)
    (hrel : ∀ m, A m * C ℓ' = B * C (ξ m)) :
    ∑ l, C (τ l) * A l ≠ 0 ∧ ∀ m, A m = C (ξ m / ∑ l, τ l * ξ l) * ∑ l, C (τ l) * A l := by
  set ℓ := ∑ l, τ l * ξ l
  have hCℓ : (C ℓ : MvPolynomial σ K) ≠ 0 := by rwa [Ne, C_eq_zero]
  have hsum : (∑ l, C (τ l) * A l) * C ℓ' = B * C ℓ := by
    calc (∑ l, C (τ l) * A l) * C ℓ' = ∑ l, C (τ l) * (A l * C ℓ') := by
          rw [Finset.sum_mul]; simp only [mul_assoc]
      _ = ∑ l, B * C (τ l * ξ l) := Finset.sum_congr rfl fun l _ => by rw [hrel l, C_mul]; ring
      _ = B * C ℓ := by rw [← Finset.mul_sum, ← map_sum]
  have hprod : (∑ l, C (τ l) * A l) * C ℓ' ≠ 0 := by rw [hsum]; exact mul_ne_zero hB hCℓ
  refine ⟨left_ne_zero_of_mul hprod, fun m => ?_⟩
  have hηC : C (ξ m / ℓ) * C ℓ = (C (ξ m) : MvPolynomial σ K) := by rw [← C_mul, div_mul_cancel₀ _ hℓ]
  apply mul_right_cancel₀ (mul_ne_zero (right_ne_zero_of_mul hprod) hCℓ)
  linear_combination (C ℓ) * hrel m - (C (ξ m / ℓ) * C ℓ) * hsum - (B * C ℓ) * hηC

theorem length_quotient_eq_one {O R : Type*} [CommRing O] [CommRing R] [Algebra O R] (𝔓 : Ideal R)
    (hmax : (𝔓.comap (algebraMap O R)).IsMaximal) (hsurj : ∀ x : R, ∃ o : O, x - algebraMap O R o ∈ 𝔓) :
    Module.length O (R ⧸ 𝔓) = 1 := by
  have hs : Function.Surjective (algebraMap O (R ⧸ 𝔓)) := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨o, ho⟩ := hsurj x
    refine ⟨o, ?_⟩
    rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq, ← neg_sub]
    exact 𝔓.neg_mem ho
  have hkerf : RingHom.ker (Algebra.ofId O (R ⧸ 𝔓)) = 𝔓.comap (algebraMap O R) := by
    ext o
    rw [RingHom.mem_ker, Ideal.mem_comap, Algebra.ofId_apply, ← Ideal.Quotient.mk_algebraMap,
      Ideal.Quotient.eq_zero_iff_mem]
  rw [← (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId O (R ⧸ 𝔓)) hs).toLinearEquiv.length_eq,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, hkerf]
  exact hmax

end ChartResidueDegree

open ChartResidueDegree in

theorem ChartResidueDegree.proof (h₁ : ChowFormBirational.Statement) (h₂ : ChartFinite.Statement)
    (h₃ : ChartKernel.Statement) (h₄ : ConeDimOfChowForm.Statement) (h₅ : ConeDimComponent.Statement)
    (h₆ : ChowFormExists.Statement) (h₇ : IncidenceGeneric.Statement) (h₈ : ChartLocalOrder.Statement) :
    ChartResidueDegree.Statement := by
  intro F _ _ n e I W f t u q p _ hI hf hu hq hp hqt hW hqW htW
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := by
    cases e with
    | zero =>
      exfalso
      have h0 : coeff 0 q ≠ 0 := fun h => hq.ne_zero (by rw [eq_C_of_isEmpty q, h, C_0])
      exact hq.not_isUnit (by rw [eq_C_of_isEmpty q]; exact (Ne.isUnit h0).map C)
    | succ k => exact ⟨k, rfl⟩

  have hIW : I ≤ W := le_trans le_sup_left hW.1.1.2
  have hdim := h₄ F n (k + 1 + 1) I f hI hf
  obtain ⟨hWp, hWdim⟩ := h₅ F n (k + 1) I W u hI hdim hu hW
  obtain ⟨g, hg⟩ := h₆ F n (k + 1) W hWp hWdim
  have := hWp.isPrime

  set K := FractionRing (MvPolynomial (Fin n) F ⧸ W)
  set ξ := genPt W with hξdef
  have hξ : ∀ h : MvPolynomial (Fin n) F, aeval ξ h = algebraMap _ K (Ideal.Quotient.mk W h) := by
    intro h
    have : (aeval ξ : MvPolynomial (Fin n) F →ₐ[F] K) =
        (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ W) K).comp (Ideal.Quotient.mkₐ F W) := by
      ext m; simp [ξ, genPt]
      all_goals rfl
    rw [this]; rfl
  set ℓ := aeval ξ (linForm t) with hℓdef
  have hℓ : ℓ ≠ 0 := by
    rw [hℓdef, hξ]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ K)).mpr
      fun h => htW (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hℓsum : ℓ = ∑ l, algebraMap F K (t l) * ξ l := by
    simp [hℓdef, linForm, map_sum]
    all_goals rfl
  set c : Fin n → K := fun m => algebraMap F K (t m) / ℓ with hcdef
  have hc : ∑ j, c j * ξ j = 1 := by
    simp only [hcdef, div_mul_eq_mul_div, ← Finset.sum_div, ← hℓsum, div_self hℓ]
  have hIG := fun h => h₇ F n (k + 1) W c hc h
  have hc' : ∑ j, c j * genPt W j = 1 := hc
  rw [← hξdef] at hIG
  clear_value c ℓ ξ
  obtain ⟨ΦI, hΦIS, hΦIX, hdeh⟩ :=
    exists_chartHom (e := k + 1) (I := I) hWp.isHomog hIW ξ hξ ℓ hℓdef hℓ c hc

  have hgen := isChowForm_iff.mp hg
  have hpinc : p = incIdeal W (k + 1) := by
    rw [hp, hgen.2]
    have hgq : g ∣ q := by rw [← Ideal.mem_span_singleton, ← hgen.2]; exact hqW
    obtain ⟨a, ha⟩ := hgq
    rcases hq.irreducible.isUnit_or_isUnit ha with hu' | hu'
    · exfalso
      have h1 : (1 : MvPolynomial (Fin (k + 1) × Fin n) F) ∈ incIdeal W (k + 1) := by
        rw [hgen.2, Ideal.span_singleton_eq_top.mpr hu']; trivial
      rw [hIG] at h1
      simp at h1
    · exact Ideal.span_singleton_eq_span_singleton.mpr (Associated.symm ⟨hu'.unit, ha.symm⟩)

  set L := FractionRing (MvPolynomial (Fin (k + 1) × Fin n) K)
  have hunit : ∀ y : Algebra.algebraMapSubmonoid (ChartInc I t (k + 1)) p.primeCompl,
      IsUnit ((algebraMap _ L).comp ΦI y) := by
    rintro ⟨_, s, hs, rfl⟩
    refine isUnit_iff_ne_zero.mpr ?_
    rw [RingHom.comp_apply, hΦIS]
    refine (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr fun h0 => hs ?_
    rw [hpinc]
    exact (hIG s).mpr h0
  let ψ : ChartLoc I t (k + 1) p →+* L := IsLocalization.lift hunit
  have hψ : ∀ a, ψ (algebraMap _ (ChartLoc I t (k + 1) p) a) = algebraMap _ L (ΦI a) :=
    fun a => IsLocalization.lift_eq hunit a
  have hω : ∀ h : MvPolynomial (Fin (k + 1) × Fin n) F, ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
      (algebraMap _ (Localization.AtPrime p) h)) = algebraMap _ L (aeval (genSubst ξ c) h) := by
    intro h
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply _ (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p), hψ, hΦIS]

  set 𝔓 := chartIdeal I t (k + 1) p W with h𝔓def
  obtain ⟨h𝔓prime, -⟩ := h₈ F n (k + 1) I W f t u q p hI hf hu hq hp hqt hW hqW htW
  have hJW : chartIncIdeal W t (k + 1) ≤
      (W.map (chartX I t (k + 1))).comap (Ideal.Quotient.mk (chartIncIdeal I t (k + 1))) := by
    have hz : ∀ a ∈ chartIncIdeal I t (k + 1),
        Ideal.Quotient.mk (chartIncIdeal I t (k + 1)) a ∈ W.map (chartX I t (k + 1)) := fun a ha => by
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact Ideal.zero_mem _
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      refine sup_le (fun h hh => ?_) ?_
      · exact Ideal.mem_map_of_mem (chartX I t (k + 1)) hh
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
        exact hz _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _
          (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hz _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  have hqS : algebraMap _ (ChartInc I t (k + 1)) q ∈ W.map (chartX I t (k + 1)) := by
    have h0 : algebraMap _ (ChartInc W t (k + 1)) q = 0 := by
      rw [← RingHom.mem_ker, h₃ F n (k + 1) W t hWp htW]; exact hqW
    change Ideal.Quotient.mk _ (rename Sum.inr q) = 0 at h0
    exact hJW (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  have h𝔓q : algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
      (algebraMap _ (Localization.AtPrime p) q) ∈ 𝔓 := by
    rw [← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply _ (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)]
    exact Ideal.mem_map_of_mem _ hqS
  have hcomap : (𝔓.comap (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p))).IsMaximal := by
    have hle : IsLocalRing.maximalIdeal (Localization.AtPrime p) ≤
        𝔓.comap (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)) := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal p, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [hp, Ideal.mem_span_singleton] at hx
      obtain ⟨a, rfl⟩ := hx
      rw [Ideal.mem_comap, Ideal.mem_comap, map_mul, map_mul]
      exact Ideal.mul_mem_right _ _ h𝔓q
    rw [← (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ h𝔓prime.ne_top) hle]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t (k + 1) p) :=
    h₂ F n (k + 1) I f t p hI hf fun h => hqt (by rw [hp] at h; exact Ideal.mem_span_singleton.mp h)
  have h𝔓max : 𝔓.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔓 hcomap
  have h𝔓ker : 𝔓 ≤ RingHom.ker ψ := by
    rw [h𝔓def, chartIdeal, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro h hh
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, hψ, hΦIX, hdeh h hh, C_0, map_zero]
  have hker : RingHom.ker ψ = 𝔓 := (h𝔓max.eq_of_le (RingHom.ker_ne_top ψ) h𝔓ker).symm

  obtain ⟨t', hD', hrel⟩ := h₁ F n k W g c hWp hg hc'
  rw [← hξdef] at hrel
  set Dt : MvPolynomial (Fin (k + 1) × Fin n) F := ∑ l, C (t l) * pderiv (0, l) g with hDtdef
  have hωC : ∀ a : F, aeval (genSubst ξ c) (C a : MvPolynomial (Fin (k + 1) × Fin n) F) =
      C (algebraMap F K a) := fun a => by rw [aeval_C, MvPolynomial.algebraMap_apply]
  have hB : aeval (genSubst ξ c) (∑ l, C (t' l) * pderiv (0, l) g) ≠ 0 := fun h0 => hD' ((hIG _).mpr h0)
  generalize aeval (genSubst ξ c) (∑ l, C (t' l) * pderiv (0, l) g) = B at hrel hB
  generalize ∑ l, algebraMap F K (t' l) * ξ l = ℓ' at hrel
  obtain ⟨hAt', hη'⟩ := ratio ξ (fun l => algebraMap F K (t l))
    (fun m => aeval (genSubst ξ c) (pderiv (0, m) g)) B ℓ' hB (hℓsum ▸ hℓ) hrel
  have hDtω : aeval (genSubst ξ c) Dt =
      ∑ l, C (algebraMap F K (t l)) * aeval (genSubst ξ c) (pderiv (0, l) g) := by
    rw [hDtdef, map_sum]
    simp only [map_mul, hωC]
  have hAt : aeval (genSubst ξ c) Dt ≠ 0 := by rw [hDtω]; exact hAt'
  have hη : ∀ m, aeval (genSubst ξ c) (pderiv (0, m) g) = C (ξ m / ℓ) * aeval (genSubst ξ c) Dt := by
    intro m; rw [hDtω, hℓsum]; exact hη' m
  have hDt : Dt ∈ p.primeCompl := fun h => hAt ((hIG Dt).mp (by rw [← hpinc]; exact h))

  have hgoodS : ∀ h : MvPolynomial (Fin (k + 1) × Fin n) F,
      ψ (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)
          (algebraMap (MvPolynomial (Fin (k + 1) × Fin n) F) (ChartInc I t (k + 1)) h)) =
        ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
          (algebraMap (MvPolynomial (Fin (k + 1) × Fin n) F) (Localization.AtPrime p) h)) := by
    intro h
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hgoodX : ∀ m, ψ (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p) (chartX I t (k + 1) (X m))) =
      ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
        (IsLocalization.mk' (Localization.AtPrime p) (pderiv (0, m) g) (⟨Dt, hDt⟩ : p.primeCompl))) := by
    intro m
    have hne : ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
        (algebraMap (MvPolynomial (Fin (k + 1) × Fin n) F) (Localization.AtPrime p) Dt)) ≠ 0 := by
      rw [hω]; exact (map_ne_zero_iff _ (IsFractionRing.injective _ L)).mpr hAt
    apply mul_right_cancel₀ hne
    have hspec : IsLocalization.mk' (Localization.AtPrime p) (pderiv (0, m) g) (⟨Dt, hDt⟩ : p.primeCompl) *
        algebraMap (MvPolynomial (Fin (k + 1) × Fin n) F) (Localization.AtPrime p) Dt =
          algebraMap _ (Localization.AtPrime p) (pderiv (0, m) g) := IsLocalization.mk'_spec _ _ _
    rw [← map_mul ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p) (IsLocalization.mk' _ _ _)),
      ← map_mul (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)), hspec, hω, hω, hψ, hΦIX,
      aeval_X, ← map_mul, hη m]
  let χ : MvPolynomial (Fin n ⊕ Fin (k + 1) × Fin n) F →+* ChartLoc I t (k + 1) p :=
    (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)).comp
      (Ideal.Quotient.mk (chartIncIdeal I t (k + 1)))
  have hgP : ∀ P : MvPolynomial (Fin n ⊕ Fin (k + 1) × Fin n) F, ∃ o : Localization.AtPrime p,
      ψ (χ P) = ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p) o) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      refine ⟨algebraMap _ _ (C a : MvPolynomial (Fin (k + 1) × Fin n) F), ?_⟩
      rw [← hgoodS]
      show _ = ψ (χ (rename Sum.inr (C a)))
      rw [rename_C]
    | add P₁ P₂ ih₁ ih₂ =>
      obtain ⟨o₁, e₁⟩ := ih₁
      obtain ⟨o₂, e₂⟩ := ih₂
      refine ⟨o₁ + o₂, ?_⟩
      simpa only [map_add] using congrArg₂ (· + ·) e₁ e₂
    | mul_X P v ih =>
      obtain ⟨o₁, e₁⟩ := ih
      cases v with
      | inl m =>
        refine ⟨o₁ * IsLocalization.mk' (Localization.AtPrime p) (pderiv (0, m) g) (⟨Dt, hDt⟩ : p.primeCompl), ?_⟩
        have e₂ : ψ (χ (X (Sum.inl m))) = ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
            (IsLocalization.mk' (Localization.AtPrime p) (pderiv (0, m) g) (⟨Dt, hDt⟩ : p.primeCompl))) := by
          rw [← hgoodX m]
          show _ = ψ (χ (rename Sum.inl (X m)))
          rw [rename_X]
        simpa only [map_mul] using congrArg₂ (· * ·) e₁ e₂
      | inr ij =>
        refine ⟨o₁ * algebraMap _ _ (X ij : MvPolynomial (Fin (k + 1) × Fin n) F), ?_⟩
        have e₂ : ψ (χ (X (Sum.inr ij))) = ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p)
            (algebraMap _ _ (X ij : MvPolynomial (Fin (k + 1) × Fin n) F))) := by
          rw [← hgoodS (X ij)]
          show _ = ψ (χ (rename Sum.inr (X ij)))
          rw [rename_X]
        simpa only [map_mul] using congrArg₂ (· * ·) e₁ e₂
  have hgood : ∀ x : ChartLoc I t (k + 1) p, ∃ o : Localization.AtPrime p,
      ψ x = ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p) o) := by
    intro x
    obtain ⟨⟨a, s⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (ChartInc I t (k + 1)) p.primeCompl) x
    dsimp only
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective (I := chartIncIdeal I t (k + 1)) a
    obtain ⟨s₀, hs₀, hs⟩ := s.2
    obtain ⟨o, ho⟩ := hgP P
    have ho' : ψ (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)
        (Ideal.Quotient.mk (chartIncIdeal I t (k + 1)) P)) =
          ψ (algebraMap (Localization.AtPrime p) (ChartLoc I t (k + 1) p) o) := ho
    have hne : ψ (algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p) s) ≠ 0 := by
      rw [hψ]; exact (hunit s).ne_zero
    refine ⟨o * IsLocalization.mk' (Localization.AtPrime p) (1 : MvPolynomial (Fin (k + 1) × Fin n) F)
      ⟨s₀, hs₀⟩, mul_right_cancel₀ hne ?_⟩
    have hx : IsLocalization.mk' (R := ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)
        (Ideal.Quotient.mk (chartIncIdeal I t (k + 1)) P) s *
        algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p) s =
          algebraMap (ChartInc I t (k + 1)) (ChartLoc I t (k + 1) p)
            (Ideal.Quotient.mk (chartIncIdeal I t (k + 1)) P) := IsLocalization.mk'_spec _ _ _
    rw [← map_mul ψ, hx, ho', ← hs,
      ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply (MvPolynomial (Fin (k + 1) × Fin n) F) (Localization.AtPrime p)
        (ChartLoc I t (k + 1) p), ← map_mul ψ, ← map_mul (algebraMap (Localization.AtPrime p) _), mul_assoc,
      IsLocalization.mk'_spec_mk, map_one, mul_one]

  refine length_quotient_eq_one 𝔓 hcomap fun x => ?_
  obtain ⟨o, ho⟩ := hgood x
  exact ⟨o, by rw [← hker, RingHom.mem_ker, map_sub, ho, sub_self]⟩

end

end GroundTheory.Heights₂.Heights
