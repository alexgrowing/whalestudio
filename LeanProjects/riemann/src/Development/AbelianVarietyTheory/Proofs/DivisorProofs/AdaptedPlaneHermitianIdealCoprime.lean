import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped nonZeroDivisors Matrix TensorProduct

namespace GlobalTheory.AdaptedPlaneIdeal

theorem count_eq_zero_of_val {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (h1 : ∀ s ∈ I, w.valuation E s ≤ 1)
    (h2 : ∃ s ∈ I, w.valuation E s = 1) : FractionalIdeal.count E w I = 0 := by
  obtain ⟨s₀, hs₀, hv₀⟩ := h2
  have hs0 : s₀ ≠ 0 := by rintro rfl; simp at hv₀
  apply le_antisymm
  · have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ s₀ ≤ I :=
      FractionalIdeal.spanSingleton_le_iff_mem.2 hs₀
    have := FractionalIdeal.count_mono E w ((FractionalIdeal.spanSingleton_ne_zero_iff).2 hs0) hle
    rw [ReciprocityTheory.Neutral.Bridge.HCFR.count_spanSingleton E w hs0, hv₀] at this
    simpa using this
  · obtain ⟨a, ha, hint⟩ := I.isFractional
    have ha0 : (a : 𝓞 E) ≠ 0 := nonZeroDivisors.ne_zero ha
    set k := (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(a : 𝓞 E)})).factors with hk
    have hspan : Ideal.span {(a : 𝓞 E)} ≠ 0 := by
      rw [Ideal.zero_eq_bot, ne_eq, Ideal.span_singleton_eq_bot]; exact ha0
    have hva : w.valuation E (algebraMap (𝓞 E) E a) = WithZero.exp (-(k : ℤ)) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha0]
    have hle : ((Ideal.span {(a : 𝓞 E)} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * I ≤
        ((w.asIdeal ^ k : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) := by
      intro z hz
      rw [FractionalIdeal.coeIdeal_span_singleton] at hz
      obtain ⟨s, hs, rfl⟩ := (FractionalIdeal.mem_singleton_mul).1 hz
      obtain ⟨r, hr⟩ := hint s hs
      rw [Algebra.smul_def] at hr
      refine (FractionalIdeal.mem_coeIdeal _).2 ⟨r, ?_, hr⟩
      rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
      change w.valuation E (algebraMap (𝓞 E) E r) ≤ _
      rw [hr, map_mul, hva]
      exact mul_le_of_le_one_right' (h1 s hs)
    have hne : ((Ideal.span {(a : 𝓞 E)} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) * I ≠ 0 :=
      mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hspan) hI
    have := FractionalIdeal.count_mono E w hne hle
    rw [FractionalIdeal.count_mul E w (FractionalIdeal.coeIdeal_ne_zero.2 hspan) hI, FractionalIdeal.count_coe E w hspan,
      FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow_self] at this
    omega

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    form σ J (a + b) y = form σ J a y + form σ J b y := by simp [form, add_dotProduct]

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (s : E) (a y : Fin n → E) :
    form σ J (s • a) y = s * form σ J a y := by simp [form, smul_dotProduct]

theorem form_swap {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (a b : Fin n → E) : form σ J b a = σ (form σ J a b) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, cm_conj_conj h, Finset.mul_sum, hJ]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem det_ne_zero_of_hasSig {n r s : ℕ} {J : Matrix (Fin n) (Fin n) E} (φ : E →+* ℂ)
    (h : HasSig (J.map φ) r s) : J.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  intro h0
  have hM : (J.map φ).det = 0 := by
    have := RingHom.map_det φ J
    rw [h0, map_zero] at this
    exact this.symm
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hM
  have hD : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  have h1 := Matrix.rank_of_isUnit _ hD
  rw [← hA] at h1
  have h2 : (Aᵀ * J.map φ * A.map star).rank ≤ (J.map φ).rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have h3 := LinearMap.finrank_range_add_finrank_ker (J.map φ).mulVecLin
  have h4 : 0 < Module.finrank ℂ (LinearMap.ker (J.map φ).mulVecLin) :=
    Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨v, hv⟩, fun e => hv0 (congrArg Subtype.val e)⟩
  rw [Module.finrank_fin_fun] at h3
  have h5 : (J.map φ).rank = Module.finrank ℂ (LinearMap.range (J.map φ).mulVecLin) := rfl
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h1
  omega

section Split

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}

theorem apply_mem_splitLat (τ : E →ₐ[F] Fv F v) {z : Fin n → E} (hz : z ∈ L) :
    (fun i => τ (z i)) ∈ splitLat τ L :=
  ⟨fun i => (1 : Fv F v) ⊗ₜ[F] z i, tmul_mem_latLoc (one_mem _) hz, funext fun i => by simp [splitVec]⟩

theorem val_le_one (τ : E →ₐ[F] Fv F v) {x₀ : Fin n → E}
    (hB : ∀ c : Fv F v, (c • fun i => τ (x₀ i)) ∈ splitLat τ L → c ∈ v.adicCompletionIntegers F)
    {s : E} (hs : s • x₀ ∈ L) : (splitPrime τ).valuation E s ≤ 1 := by
  rw [← valued_apply_eq_valuation]
  have := hB (τ s) (by
    have := apply_mem_splitLat τ hs
    convert this using 1
    funext i
    simp [map_mul])
  exact this

theorem exists_val_eq_one {σ : E →ₐ[F] E} {J : Matrix (Fin n) (Fin n) E} (τ : E →ₐ[F] Fv F v)
    {x₀ y₀ : Fin n → E} (hA : (fun i => τ (x₀ i)) ∈ splitLat τ L)
    (hB : ∀ c : Fv F v, (c • fun i => τ (x₀ i)) ∈ splitLat τ L → c ∈ v.adicCompletionIntegers F)
    (hxy : form σ J x₀ y₀ = 1) (hC : ∀ l ∈ L, form σ J l y₀ • x₀ ∈ L) :
    ∃ s, s • x₀ ∈ L ∧ (splitPrime τ).valuation E s = 1 := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ l ∈ L, Valued.v (τ (form σ J l y₀)) < 1 := fun l hl => by
    rw [valued_apply_eq_valuation]
    exact lt_of_le_of_ne (val_le_one τ hB (hC l hl)) (hcon _ (hC l hl))
  let φ : (Fin n → Fv F v) → Fv F v := fun u => u ⬝ᵥ (J.map τ *ᵥ fun j => τ (σ (y₀ j)))
  have hφ : ∀ l : Fin n → E, φ (fun i => τ (l i)) = τ (form σ J l y₀) := fun l => by
    simp [φ, form, dotProduct, Matrix.mulVec, map_sum, map_mul]
  have key : ∀ z ∈ latLoc F L v, Valued.v (φ (splitVec τ z)) < 1 := fun z hz => by
    refine latLoc_induction (p := fun z => Valued.v (φ (splitVec τ z)) < 1) (fun a ha l hl => ?_) ?_
      (fun y z hy hz => ?_) (fun y hy => ?_) hz
    · have e : splitVec τ (fun i => a ⊗ₜ[F] l i) = a • fun i => τ (l i) := funext fun i => by simp [splitVec]
      rw [e, show φ (a • fun i => τ (l i)) = a * φ (fun i => τ (l i)) from smul_dotProduct _ _ _, hφ, map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha) (hlt l hl)
    · have e : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun i => by simp [splitVec]
      rw [e]; simp [φ]
    · rw [splitVec_add, show φ (splitVec τ y + splitVec τ z) = φ (splitVec τ y) + φ (splitVec τ z) from
        add_dotProduct _ _ _]
      exact Valuation.map_add_lt _ hy hz
    · have e : splitVec τ (-y) = -splitVec τ y := funext fun i => by simp [splitVec]
      rw [e, show φ (-splitVec τ y) = -φ (splitVec τ y) from neg_dotProduct _ _, Valuation.map_neg]
      exact hy
  obtain ⟨z, hz, hze⟩ := hA
  have := key z hz
  rw [hze, hφ, hxy, map_one, map_one] at this
  exact lt_irrefl _ this

end Split

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Split

variable {v : HeightOneSpectrum (𝓞 F)} {n : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}

theorem col_facts (τ : E →ₐ[F] Fv F v) {β : GL (Fin n) (Fv F v)} (hβ : IsSplitBasis τ L β) (j : Fin n)
    {x₀ : Fin n → E} (hcol : ∀ r, β.1 r j = τ (x₀ r)) :
    (fun r => τ (x₀ r)) ∈ splitLat τ L ∧
      ∀ c : Fv F v, (c • fun r => τ (x₀ r)) ∈ splitLat τ L → c ∈ v.adicCompletionIntegers F := by
  have e : ∀ c : Fv F v, β.1 *ᵥ Pi.single j c = c • fun r => τ (x₀ r) := fun c => by
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hcol, mul_comm]
  refine ⟨?_, fun c hc => ?_⟩
  · have := (hβ (Pi.single j 1)).1 (fun i => by
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _])
    rwa [e, one_smul] at this
  · have := (hβ (Pi.single j c)).2 (by rwa [e]) j
    simpa using this

theorem pair_apply (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (τ : E →ₐ[F] Fv F v) (z' z : Fin n → E) :
    (fun i => (τ.comp σ) (z' i)) ⬝ᵥ Jᵀ.map τ *ᵥ (fun i => τ (z i)) = τ (form σ J z z') := by
  simp only [form, dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul,
    AlgHom.comp_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Split

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x z : Fin n → E) :
    hE σ Jᵀ x z = form σ J z x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp
  ring

end GlobalTheory.AdaptedPlaneIdeal

namespace GlobalTheory.AdaptedPlaneIdeal

theorem ideal_ne_zero_and_count_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {n n₁ : ℕ} (H : Plane E n n₁) (Y : Spc F E n) (Y₁ : Spc F E n₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → i₀ < n → i₁ < n →
    H.𝔟 ≠ 0 ∧ ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) ∈ B.P → FractionalIdeal.count E w H.𝔟 = 0 := by
  intro F E _ _ _ _ _ σ B n n₁ H Y Y₁ i₀ i₁ r s hB hY hH hi₀ hi₁
  have h := hB.cm
  have hyx : form σ Y.J H.y H.x = 1 := by rw [form_swap h hY.herm, hH.xy, map_one]
  have hCx : ∀ l ∈ Y.L, form σ Y.J l H.y • H.x ∈ Y.L := by
    intro l hl
    obtain ⟨a, t, u, ha, -, -, rfl⟩ := hH.split l hl
    have e : form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.y = a := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xy, hH.yy, (hH.orth u).2]; ring
    rw [e]; exact ha
  have hCy : ∀ l ∈ Y.L, form σ Y.J l H.x • H.y ∈ Y.L := by
    intro l hl
    obtain ⟨a, t, u, -, ht, -, rfl⟩ := hH.split l hl
    have e : form σ Y.J (a • H.x + H.ι *ᵥ u + t • H.y) H.x = t := by
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH.xx, hyx, (hH.orth u).1]; ring
    rw [e]; exact ht
  have hne : H.𝔟 ≠ 0 := by
    have hx : H.x ∈ Submodule.span E (Y.L : Set (Fin n → E)) := hY.lat.span_eq_top ▸ Submodule.mem_top
    obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (𝓞 E)⁰ E (Y.L : Set (Fin n → E)) H.x hx
    rw [Submodule.span_eq] at ht
    have hmem : algebraMap (𝓞 E) E t ∈ H.𝔟 := (hH.ideal _).2 (by rw [algebraMap_smul]; exact ht)
    intro h0
    rw [h0, FractionalIdeal.mem_zero_iff] at hmem
    exact nonZeroDivisors.coe_ne_zero t ((map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 hmem)
  refine ⟨hne, fun w hw => ?_⟩
  set v := w.under (𝓞 F) with hv
  let v' : B.P := ⟨v, hw⟩
  set τ := B.τ v' with hτ
  have hmem : w.asIdeal ∈ v.asIdeal.primesOver (𝓞 E) := ⟨w.isPrime, ⟨rfl⟩⟩
  rw [primesOver_eq_split h τ] at hmem
  have hbas : IsSplitBasis τ Y.L (Y.bas v) := hY.bas v'
  obtain ⟨hAx, hBx⟩ := col_facts τ hbas ⟨i₀, hi₀⟩ (x₀ := H.x) ((hH.bas v' ⟨i₀, hi₀⟩).1 rfl)
  obtain ⟨hAy, hBy⟩ := col_facts τ hbas ⟨i₁, hi₁⟩ (x₀ := H.y) ((hH.bas v' ⟨i₁, hi₁⟩).2.1 rfl)
  rcases hmem with e | e
  · have hw' : w = splitPrime τ := HeightOneSpectrum.ext e
    rw [hw']
    refine count_eq_zero_of_val _ hne (fun s hs => val_le_one τ hBx ((hH.ideal s).1 hs)) ?_
    obtain ⟨s, hs, hv1⟩ := exists_val_eq_one τ hAx hBx hH.xy hCx
    exact ⟨s, (hH.ideal s).2 hs, hv1⟩
  · have hw' : w = splitPrime (τ.comp σ) := HeightOneSpectrum.ext e
    rw [hw']
    obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
    have hND : IsHermND σ Y.Jᵀ :=
      ⟨fun i j => by simpa [Matrix.transpose_apply] using hY.herm j i,
        by rw [Matrix.det_transpose]; exact det_ne_zero_of_hasSig _ (hY.sig w₀)⟩
    have hSD : IsSelfDualAt σ Y.Jᵀ Y.L v := by
      refine (SelfDual.forall_isSelfDualAt_iff (σ := σ) hND.2 hY.lat).2 (fun z => (hY.dual z).trans ?_) v
      simp only [hE_transpose]
      exact forall₂_congr fun x _ => ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨r, hr⟩ => hr ▸ r.2⟩
    have hint : ∀ l ∈ Y.L, τ (form σ Y.J l H.x) ∈ v.adicCompletionIntegers F := fun l hl => by
      have := val_le_one τ hBy (hCy l hl)
      rw [← valued_apply_eq_valuation] at this
      exact this
    have hA' : (fun i => (τ.comp σ) (H.x i)) ∈ splitLat (τ.comp σ) Y.L := by
      rw [mem_splitLat_comp_iff h hND hSD]
      rintro _ ⟨z, hz, rfl⟩
      refine latLoc_induction (p := fun z => (fun i => (τ.comp σ) (H.x i)) ⬝ᵥ Y.Jᵀ.map τ *ᵥ splitVec τ z ∈
        v.adicCompletionIntegers F) (fun a ha l hl => ?_) ?_ (fun y z hy hz => ?_) (fun y hy => ?_) hz
      · have e1 : splitVec τ (fun i => a ⊗ₜ[F] l i) = a • fun i => τ (l i) := funext fun i => by simp [splitVec]
        rw [e1, Matrix.mulVec_smul, dotProduct_smul, pair_apply, smul_eq_mul]
        exact mul_mem ha (hint l hl)
      · have e1 : splitVec τ (0 : Fin n → Fv F v ⊗[F] E) = 0 := funext fun i => by simp [splitVec]
        rw [e1]; simp
      · rw [splitVec_add, Matrix.mulVec_add, dotProduct_add]; exact add_mem hy hz
      · have e1 : splitVec τ (-y) = -splitVec τ y := funext fun i => by simp [splitVec]
        rw [e1, Matrix.mulVec_neg, dotProduct_neg]; exact neg_mem hy
    have hB' : ∀ c : Fv F v, (c • fun i => (τ.comp σ) (H.x i)) ∈ splitLat (τ.comp σ) Y.L →
        c ∈ v.adicCompletionIntegers F := fun c hc => by
      have := (mem_splitLat_comp_iff h hND hSD).1 hc _ hAy
      rwa [smul_dotProduct, pair_apply, hyx, map_one, smul_eq_mul, mul_one] at this
    refine count_eq_zero_of_val _ hne (fun s hs => val_le_one (τ.comp σ) hB' ((hH.ideal s).1 hs)) ?_
    obtain ⟨s, hs, hv1⟩ := exists_val_eq_one (τ.comp σ) hA' hB' hH.xy hCx
    exact ⟨s, (hH.ideal s).2 hs, hv1⟩

end GlobalTheory.AdaptedPlaneIdeal
