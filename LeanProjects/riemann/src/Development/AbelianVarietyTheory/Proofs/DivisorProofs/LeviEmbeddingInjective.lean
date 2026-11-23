import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.LeviUnique

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  have hD : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ)) := by
    have hm : Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) *
        Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1 : Matrix (Fin s) (Fin s) ℂ) = 1 := by
      rw [Matrix.fromBlocks_multiply]
      simp [Matrix.fromBlocks_one]
    exact ⟨⟨_, _, hm, hm⟩, rfl⟩
  have hrank : n ≤ M.rank := by
    have h1 := Matrix.rank_of_isUnit _ hD
    rw [← hA] at h1
    have h2 : (Aᵀ * M * A.map star).rank ≤ M.rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    simp only [Fintype.card_sum, Fintype.card_fin] at h1
    omega
  intro hdet
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 hdet
  have hsurj : LinearMap.range M.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h3 := M.rank_le_card_width
    rw [Matrix.rank] at hrank h3
    simp only [Fintype.card_fin] at h3
    rw [Module.finrank_fin_fun]
    omega
  have hinj : Function.Injective M.mulVecLin :=
    LinearMap.injective_iff_surjective.2 (LinearMap.range_eq_top.1 hsurj)
  exact hv (hinj (by simpa using hMv))

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) : form σ J y x = σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hJ]
  ring

theorem form_add_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    form σ J (a + b) y = form σ J a y + form σ J b y := by
  simp [form, add_dotProduct]

theorem form_smul_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    form σ J (c • a) y = c * form σ J a y := by
  simp [form, smul_dotProduct]

theorem form_zero_left (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    form σ J 0 y = 0 := by
  simp [form]

end GlobalTheory.LeviUnique

namespace GlobalTheory.LeviUnique

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem plane_spans (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (J₁ : Matrix (Fin n₁) (Fin n₁) E) (hJ : ∀ i j, σ (J j i) = J i j) (hJ₁ : J₁.det ≠ 0) (H : Plane E n n₁)
    (hn : n = n₁ + 2) (xx : form σ J H.x H.x = 0) (yy : form σ J H.y H.y = 0) (xy : form σ J H.x H.y = 1)
    (orth : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0)
    (gram : H.ιᵀ * J * H.ι.map σ = J₁) (z : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y := by
  let ℓ : ((Fin n₁ → E) × E × E) →ₗ[E] (Fin n → E) :=
    (Matrix.mulVecLin H.ι).coprod ((LinearMap.id.smulRight H.x).coprod (LinearMap.id.smulRight H.y))
  have hℓ : ∀ p, ℓ p = H.ι *ᵥ p.1 + (p.2.1 • H.x + p.2.2 • H.y) := fun p => by
    simp [ℓ]
  have hinj : Function.Injective ℓ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨u, s, t⟩ h0
    rw [hℓ] at h0
    have hyx : form σ J H.y H.x = 1 := by rw [form_swap σ hσ hJ, xy, map_one]
    have hs : s = 0 := by
      have := congrArg (fun v => form σ J v H.y) h0
      simp only [form_add_left, form_smul_left, form_zero_left, (orth u).2, xy, yy] at this
      simpa using this
    have ht : t = 0 := by
      have := congrArg (fun v => form σ J v H.x) h0
      simp only [form_add_left, form_smul_left, form_zero_left, (orth u).1, xx, hyx] at this
      simpa using this
    subst hs ht
    have hu : H.ι *ᵥ u = 0 := by simpa using h0
    have hu' : u ᵥ* J₁ = 0 := by
      rw [← gram, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hu,
        Matrix.zero_vecMul, Matrix.zero_vecMul]
    have : u = 0 := by
      by_contra hne
      exact hJ₁ ((Matrix.exists_vecMul_eq_zero_iff).1 ⟨u, hne, hu'⟩)
    simp [this]
  have hdim : Module.finrank E ((Fin n₁ → E) × E × E) = Module.finrank E (Fin n → E) := by
    simp [Module.finrank_prod, Module.finrank_fin_fun, hn]
  have hsurj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).1 hinj
  obtain ⟨⟨u, s, t⟩, hp⟩ := hsurj z
  refine ⟨s, t, u, ?_⟩
  rw [← hp, hℓ]
  abel

end GlobalTheory.LeviUnique

namespace GlobalTheory.LeviUnique

theorem levi_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (t : (AE F E)ˣ) (h₁ : UA σ G₁.V.J) (h h' : UA σ G.V.J), IsLevi H t h₁ h → IsLevi H t h₁ h' → h = h' := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC hB hG hG₁ t h₁ h h' hl hl'
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply (B.emb w).1.injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2]
    simp
  have hJ₁ : G₁.V.J.det ≠ 0 := by
    intro h0
    apply det_ne_zero_of_hasSig (hG₁.hV.sig w)
    rw [show G₁.V.J.map (B.emb w).1 = ((B.emb w).1).mapMatrix G₁.V.J from rfl, ← RingHom.map_det, h0, map_zero]
  have hA := hC.hH
  have hspan := plane_spans σ hσ G.V.J G₁.V.J hG.hV.herm hJ₁ H hA.rank hA.xx hA.yy hA.xy hA.orth hA.gram
  have hincV : ∀ (n : ℕ) (u : Fin n → E) (c : E) (v : Fin n → E),
      incV F (c • u + v) = (inclR (AF F) c : AE F E) • incV F u + incV F v := fun n u c v => by
    funext i
    change inclR (AF F) (c * u i + v i) = (inclR (AF F) c : AE F E) * inclR (AF F) (u i) + inclR (AF F) (v i)
    rw [map_add, map_mul]
  have hincι : ∀ u, incV F (H.ι *ᵥ u) = incM F H.ι *ᵥ incV F u := fun u => by
    ext i; simp [incV, incM, RingHom.map_mulVec]; rfl
  have key : ∀ z : Fin (b + 2) → E, mat h *ᵥ incV F z = mat h' *ᵥ incV F z := fun z => by
    obtain ⟨s, r, u, rfl⟩ := hspan z
    have e : s • H.x + H.ι *ᵥ u + r • H.y = s • H.x + (r • H.y + H.ι *ᵥ u) := by abel
    rw [e, hincV, hincV, hincι]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hl.1, hl.2.1, hl.2.2, hl'.1, hl'.2.1, hl'.2.2]
  have hmat : mat h = mat h' := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    have hs : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
      ext k; by_cases hk : k = j
      · subst hk; simp [incV]
      · simp [incV, Pi.single_apply, hk]
    rw [hs] at this
    simpa [Matrix.mulVec_single_one] using this
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.LeviUnique
