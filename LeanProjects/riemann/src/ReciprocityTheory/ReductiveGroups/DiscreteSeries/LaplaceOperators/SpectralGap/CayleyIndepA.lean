import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.NonvanishingHypotheses

open Matrix
open scoped InnerProductSpace

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA

variable {n : ℕ} {ε : Fin n → Bool}

lemma kset_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.REAL.Kset ε) (hb : b ∈ Formalism.REAL.Kset ε) :
    a * b ∈ Formalism.REAL.Kset ε := by
  simp only [Formalism.REAL.Kset, Set.mem_setOf_eq] at ha hb ⊢
  refine ⟨Submonoid.mul_mem _ ha.1 hb.1, ?_⟩
  rw [mul_assoc, hb.2, ← mul_assoc, ha.2, mul_assoc]

lemma uj_mul {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ Formalism.MainNotions.S.UJset ε) (hb : b ∈ Formalism.MainNotions.S.UJset ε) :
    a * b ∈ Formalism.MainNotions.S.UJset ε := by
  simp only [Formalism.MainNotions.S.UJset, Formalism.REAL.inUJ, Set.mem_setOf_eq] at ha hb ⊢
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Formalism.REAL.Jm ε * (a * b) = bᴴ * (aᴴ * Formalism.REAL.Jm ε * a) * b := by
        simp only [mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [ha, hb]

lemma kset_uj {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.REAL.Kset ε) : g ∈ Formalism.MainNotions.S.UJset ε := by
  simp only [Formalism.REAL.Kset, Formalism.MainNotions.S.UJset, Formalism.REAL.inUJ, Set.mem_setOf_eq] at hg ⊢
  obtain ⟨hu, hc⟩ := hg
  have h1 : gᴴ * g = 1 := by
    have h2 := Matrix.mem_unitaryGroup_iff'.mp hu
    simpa [Matrix.star_eq_conjTranspose] using h2
  rw [mul_assoc, ← hc, ← mul_assoc, h1, one_mul]

lemma conj_back {a b g : Matrix (Fin n) (Fin n) ℂ} (hba : b * a = 1) : b * (a * g * b) * a = g := by
  calc b * (a * g * b) * a = (b * a) * g * (b * a) := by simp only [mul_assoc]
    _ = g := by rw [hba, one_mul, mul_one]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section Conj

variable (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {a b : Matrix (Fin n) (Fin n) ℂ}
  (hrep : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ₁)
  (hab : a * b = 1) (hba : b * a = 1) (ha : a ∈ Formalism.REAL.Kset ε) (hb : b ∈ Formalism.REAL.Kset ε)

include hrep hab ha hb in
lemma ab_cancel (x : H) : σ₁ a (σ₁ b x) = x := by
  have h := hrep.1.2 a (kset_uj ha) b (kset_uj hb)
  rw [hab, hrep.1.1] at h
  rw [← ContinuousLinearMap.comp_apply, ← h, ContinuousLinearMap.one_apply]

include hrep hba ha hb in
lemma ba_cancel (x : H) : σ₁ b (σ₁ a x) = x := by
  have h := hrep.1.2 b (kset_uj hb) a (kset_uj ha)
  rw [hba, hrep.1.1] at h
  rw [← ContinuousLinearMap.comp_apply, ← h, ContinuousLinearMap.one_apply]

include hrep ha hb in
lemma conj_apply {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Formalism.MainNotions.S.UJset ε) (x : H) :
    σ₁ (b * g * a) x = σ₁ b (σ₁ g (σ₁ a x)) := by
  have hb' := kset_uj hb
  have ha' := kset_uj ha
  rw [hrep.1.2 _ (uj_mul hb' hg) _ ha', hrep.1.2 _ hb' _ hg]
  simp only [ContinuousLinearMap.comp_apply]

include hrep hab ha hb in
lemma inner_b (w y : H) : ⟪w, σ₁ b y⟫_ℂ = ⟪σ₁ a w, y⟫_ℂ := by
  let f : H →ₗᵢ[ℂ] H := { toLinearMap := (σ₁ a : H →ₗ[ℂ] H), norm_map' := hrep.2.1 a (kset_uj ha) }
  have key : ⟪σ₁ a w, σ₁ a (σ₁ b y)⟫_ℂ = ⟪w, σ₁ b y⟫_ℂ := f.inner_map_map w (σ₁ b y)
  rw [ab_cancel σ₁ hrep hab ha hb y] at key
  exact key.symm

end Conj

end ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA

namespace ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA

variable {n : ℕ} {ε : Fin n → Bool}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (σ₁ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {a b : Matrix (Fin n) (Fin n) ℂ}
  (hrep : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ₁)
  (hab : a * b = 1) (hba : b * a = 1) (ha : a ∈ Formalism.REAL.Kset ε) (hb : b ∈ Formalism.REAL.Kset ε)

include hrep hab hba ha hb in
lemma urep_conj : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) (fun g => σ₁ (b * g * a)) := by
  have ha' := kset_uj ha
  have hb' := kset_uj hb
  have hmem : ∀ g ∈ Formalism.MainNotions.S.UJset ε, b * g * a ∈ Formalism.MainNotions.S.UJset ε :=
    fun g hg => uj_mul (uj_mul hb' hg) ha'
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · show σ₁ (b * 1 * a) = 1
    rw [mul_one, hba, hrep.1.1]
  · intro g hg h hh
    ext x
    simp only [ContinuousLinearMap.comp_apply]
    rw [conj_apply σ₁ hrep ha hb (uj_mul hg hh), conj_apply σ₁ hrep ha hb hg,
      conj_apply σ₁ hrep ha hb hh, ab_cancel σ₁ hrep hab ha hb, hrep.1.2 _ hg _ hh,
      ContinuousLinearMap.comp_apply]
  · intro g hg v
    exact hrep.2.1 _ (hmem g hg) v
  · intro v
    have hc : Continuous (fun g : Matrix (Fin n) (Fin n) ℂ => b * g * a) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact (hrep.2.2 v).comp hc.continuousOn hmem

include hab hba ha hb in
lemma irred_conj (hirr : Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) σ₁) :
    Formalism.MainNotions.S.IsIrredOn (Formalism.MainNotions.S.UJset ε) (fun g => σ₁ (b * g * a)) := by
  intro S hS hinv
  apply hirr S hS
  intro g hg v hv
  have hm : a * g * b ∈ Formalism.MainNotions.S.UJset ε := uj_mul (uj_mul (kset_uj ha) hg) (kset_uj hb)
  have h1 : σ₁ (b * (a * g * b) * a) v ∈ S := hinv (a * g * b) hm v hv
  rwa [conj_back hba] at h1

include hrep hab ha hb in
lemma coef_conj (v w : H) :
    Formalism.MainNotions.S.coefOn (ε := ε) (fun g => σ₁ (b * g * a)) v w = Formalism.MainNotions.S.coefOn (ε := ε) σ₁ (σ₁ a v) (σ₁ a w) := by
  funext g
  have hg : Formalism.MainNotions.S.umat g ∈ Formalism.MainNotions.S.UJset ε := g.2
  simp only [Formalism.MainNotions.S.coefOn]
  rw [conj_apply σ₁ hrep ha hb hg, inner_b σ₁ hrep hab ha hb]

include hrep hab ha hb in
lemma sqint_conj (hsq : Formalism.MainNotions.S.IsSqIntOn ε σ₁) : Formalism.MainNotions.S.IsSqIntOn ε (fun g => σ₁ (b * g * a)) := by
  intro v w
  rw [coef_conj σ₁ hrep hab ha hb v w]
  exact hsq (σ₁ a v) (σ₁ a w)

include ha hb in
lemma isKStable_biTranslate_of_isKStable {S : Submodule ℂ H} (h : Formalism.MainNotions.S.IsKStableOn ε σ₁ S) :
    Formalism.MainNotions.S.IsKStableOn ε (fun g => σ₁ (b * g * a)) S := by
  intro g hg v hv
  exact h _ (kset_mul (kset_mul hb hg) ha) v hv

include hba ha hb in
lemma isKStable_of_isKStable_biTranslate {S : Submodule ℂ H} (h : Formalism.MainNotions.S.IsKStableOn ε (fun g => σ₁ (b * g * a)) S) :
    Formalism.MainNotions.S.IsKStableOn ε σ₁ S := by
  intro g hg v hv
  have h1 : σ₁ (b * (a * g * b) * a) v ∈ S := h (a * g * b) (kset_mul (kset_mul ha hg) hb) v hv
  rwa [conj_back hba] at h1

include hrep hab ha hb in
lemma wt12 {μ : Fin n → ℝ} {v : H} (h : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ₁ μ v) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (fun g => σ₁ (b * g * a)) μ (σ₁ b v) := by
  intro θ hθ
  have e := conj_apply σ₁ hrep ha hb (kset_uj hθ) (σ₁ b v)
  rw [ab_cancel σ₁ hrep hab ha hb, h θ hθ, map_smul] at e
  exact e

include hrep hab ha hb in
lemma wt21 {μ : Fin n → ℝ} {v : H} (h : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) (fun g => σ₁ (b * g * a)) μ v) :
    Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) σ₁ μ (σ₁ a v) := by
  intro θ hθ
  have e := congrArg (fun y => σ₁ a y) ((conj_apply σ₁ hrep ha hb (kset_uj hθ) v).symm.trans (h θ hθ))
  rw [ab_cancel σ₁ hrep hab ha hb, map_smul] at e
  exact e

include hrep ha in
lemma ne_a {v : H} (hv : v ≠ 0) : σ₁ a v ≠ 0 := by
  intro h0
  apply hv
  have h1 := hrep.2.1 a (kset_uj ha) v
  rw [h0, norm_zero] at h1
  exact norm_eq_zero.mp h1.symm

include hrep hab hba ha hb in
lemma ktype_iff (μ : Fin n → ℝ) (S : Submodule ℂ H) :
    Formalism.MainNotions.S.IsKTypeOf ε (fun g => σ₁ (b * g * a)) μ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ₁ μ S := by
  have hst : ∀ T : Submodule ℂ H, Formalism.MainNotions.S.IsKStableOn ε (fun g => σ₁ (b * g * a)) T ↔
      Formalism.MainNotions.S.IsKStableOn ε σ₁ T :=
    fun T => ⟨isKStable_of_isKStable_biTranslate σ₁ hba ha hb, isKStable_biTranslate_of_isKStable σ₁ ha hb⟩
  constructor
  · rintro ⟨hfd, hs, hmin, ⟨v, hvS, hv0, hwt⟩, hdom⟩
    have hs' := (hst S).1 hs
    refine ⟨hfd, hs', fun S' hS' hst' => hmin S' hS' ((hst S').2 hst'),
      ⟨σ₁ a v, hs' a ha v hvS, ne_a σ₁ hrep ha hv0, wt21 σ₁ hrep hab ha hb hwt⟩, ?_⟩
    intro μ' u huS hu0 hwu
    exact hdom μ' (σ₁ b u) (hs' b hb u huS) (ne_a σ₁ hrep hb hu0) (wt12 σ₁ hrep hab ha hb hwu)
  · rintro ⟨hfd, hs, hmin, ⟨v, hvS, hv0, hwt⟩, hdom⟩
    refine ⟨hfd, (hst S).2 hs, fun S' hS' hst' => hmin S' hS' ((hst S').1 hst'),
      ⟨σ₁ b v, hs b hb v hvS, ne_a σ₁ hrep hb hv0, wt12 σ₁ hrep hab ha hb hwt⟩, ?_⟩
    intro μ' u huS hu0 hwu
    exact hdom μ' (σ₁ a u) (hs a ha u huS) (ne_a σ₁ hrep ha hu0) (wt21 σ₁ hrep hab ha hb hwu)

include hab hba ha hb in
lemma ds_conj (lam : Fin n → ℝ) (hds : Formalism.MainNotions.S.IsDS ε lam σ₁) :
    Formalism.MainNotions.S.IsDS ε lam (fun g => σ₁ (b * g * a)) ∧
      Formalism.MainNotions.S.lowKSub ε lam (fun g => σ₁ (b * g * a)) = Formalism.MainNotions.S.lowKSub ε lam σ₁ := by
  obtain ⟨hc, hnt, hrep, hirr, hsq, ⟨S0, hS0⟩, hmin⟩ := hds
  have hk : ∀ μ S, Formalism.MainNotions.S.IsKTypeOf ε (fun g => σ₁ (b * g * a)) μ S ↔ Formalism.MainNotions.S.IsKTypeOf ε σ₁ μ S :=
    fun μ S => ktype_iff σ₁ hrep hab hba ha hb μ S
  refine ⟨⟨hc, hnt, urep_conj σ₁ hrep hab hba ha hb, irred_conj σ₁ hab hba ha hb hirr,
    sqint_conj σ₁ hrep hab ha hb hsq, ⟨S0, (hk _ S0).2 hS0⟩, fun μ S h => hmin μ S ((hk μ S).1 h)⟩, ?_⟩
  simp only [Formalism.MainNotions.S.lowKSub, hk]

end ReciprocityTheory.ChartRestriction.DS.Lap.CayleyIndepA
