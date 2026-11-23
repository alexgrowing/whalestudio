import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

namespace GlobalTheory.PlaneHermTransfer

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sig_sig [NumberField F] [NumberField E] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) :
    σ (σ x) = x := by
  obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact φ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem det_smul_map (σ : E →ₐ[F] E) {m : ℕ} (c : E) (M : Matrix (Fin m) (Fin m) E) :
    (c • M.map σ).det = c ^ m * σ M.det := by
  rw [Matrix.det_smul, Fintype.card_fin, AlgHom.map_det]; rfl

theorem form_add_left (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (u v w : Fin m → E) :
    form σ J (u + v) w = form σ J u w + form σ J v w := by
  simp [form, add_dotProduct]

theorem form_smul_left (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (a : E)
    (u w : Fin m → E) : form σ J (a • u) w = a * form σ J u w := by
  simp [form, smul_dotProduct]

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (v w : Fin m → E) :
    form σ J v w = -σ (form σ J w v) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_mulVec (σ : E →ₐ[F] E) {m k : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (ι : Matrix (Fin m) (Fin k) E) (u u' : Fin k → E) :
    form σ J (ι *ᵥ u) (ι *ᵥ u') = form σ (ιᵀ * J * ι.map σ) u u' := by
  have : (fun i => σ ((ι *ᵥ u') i)) = ι.map σ *ᵥ (fun i => σ (u' i)) := by
    ext i; simp [Matrix.mulVec, dotProduct, map_sum]
  simp only [form]
  rw [this, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u,
    Matrix.vecMul_transpose]

theorem form_single (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (c : Fin m → E)
    (k : Fin m) : form σ J c (Pi.single k 1) = (c ᵥ* J) k := by
  have : (fun i => σ ((Pi.single k (1 : E) : Fin m → E) i)) = Pi.single k 1 := by
    ext i; by_cases h : i = k
    · subst h; simp
    · simp [h]
  simp only [form]
  rw [this, Matrix.dotProduct_mulVec]
  simp

theorem form_single_single (σ : E →ₐ[F] E) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (j k : Fin m) : form σ J (Pi.single j 1) (Pi.single k 1) = J j k := by
  rw [form_single]; simp

theorem det_ne_zero (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {m : ℕ}
    (J : Matrix (Fin (m + 2)) (Fin (m + 2)) E) (hJ : ∀ i j, σ (J j i) = -J i j)
    (x y : Fin (m + 2) → E) (ι : Matrix (Fin (m + 2)) (Fin m) E)
    (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (hu : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0)
    (hd : (ιᵀ * J * ι.map σ).det ≠ 0) : J.det ≠ 0 := by
  have hyx : form σ J y x = -1 := by rw [form_swap σ hσ J hJ, hxy, map_one]
  have key : ∀ (u : Fin m → E) (a b : E),
      (∀ w, form σ J (ι *ᵥ u + a • x + b • y) w = 0) → u = 0 ∧ a = 0 ∧ b = 0 := by
    intro u a b h
    have h1 := h x
    have h2 := h y
    simp only [form_add_left, form_smul_left, hxx, hyy, hxy, hyx, (hu u).1, (hu u).2] at h1 h2
    have hb : b = 0 := by simpa using h1
    have ha : a = 0 := by simpa using h2
    refine ⟨?_, ha, hb⟩
    subst ha hb
    by_contra hne
    apply hd
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨u, hne, ?_⟩
    ext k
    have h3 := h (ι *ᵥ Pi.single k 1)
    simp only [zero_smul, add_zero] at h3
    rw [form_mulVec, form_single] at h3
    simpa using h3
  let L : ((Fin m → E) × E × E) →ₗ[E] (Fin (m + 2) → E) :=
    (Matrix.mulVecLin ι).coprod
      ((LinearMap.toSpanSingleton E _ x).coprod (LinearMap.toSpanSingleton E _ y))
  have hL : ∀ p, L p = ι *ᵥ p.1 + p.2.1 • x + p.2.2 • y := by
    intro p; simp [L, add_assoc]
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, a, b⟩ hp
    rw [hL] at hp
    obtain ⟨h1, h2, h3⟩ := key u a b (fun w => by simp only at hp; rw [hp]; simp [form])
    simp [h1, h2, h3]
  have hsurj : Function.Surjective L := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp
  intro h0
  obtain ⟨v, hv, hvJ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  obtain ⟨⟨u, a, b⟩, rfl⟩ := hsurj v
  rw [hL] at hv hvJ
  obtain ⟨h1, h2, h3⟩ := key u a b (fun w => by
    simp only [form] at hvJ ⊢
    rw [Matrix.dotProduct_mulVec, hvJ]; simp)
  apply hv
  simp [h1, h2, h3]

theorem isHermND_of_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J → 0 < n₁ →
      ∀ c₀ : E, c₀ ≠ 0 → IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) := by
  intro F E _ _ _ _ _ σ hCM n n₁ W W₁ H hJ hn hxx hyy hxy hu hG hpos c₀ hc hH
  subst hn
  have hσ := sig_sig hCM
  have hd₁ : W₁.J.det ≠ 0 := by
    intro h0
    apply hH.2
    rw [det_smul_map, h0, map_zero, mul_zero]
  have hskew : ∀ i j, σ (W₁.J j i) = -W₁.J i j := by
    intro i j
    have e1 := form_single_single σ W₁.J j i
    have e2 := form_single_single σ W₁.J i j
    rw [← hG, ← form_mulVec] at e1 e2
    rw [hG] at e1 e2
    rw [← e1, ← e2, form_swap σ hσ W.J hJ (H.ι *ᵥ Pi.single i 1), neg_neg]
  have hne : W₁.J ≠ 0 := by
    intro h0
    apply hd₁
    haveI : Nonempty (Fin n₁) := ⟨⟨0, hpos⟩⟩
    rw [h0]; simp
  obtain ⟨j, i, hji⟩ : ∃ j i, W₁.J j i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hne (by ext j i; simpa using hcon j i)
  have hc₀ : σ c₀ = -c₀ := by
    have h1 := hH.1 i j
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ] at h1
    rw [hskew j i] at h1
    apply mul_right_cancel₀ hji
    rw [h1]; ring
  have hdJ : W.J.det ≠ 0 :=
    det_ne_zero σ hσ W.J hJ H.x H.y H.ι hxx hyy hxy hu (by rw [hG]; exact hd₁)
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hc₀]
    rw [hJ j i]; ring
  · rw [det_smul_map]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero σ).2 hdJ)

end GlobalTheory.PlaneHermTransfer
