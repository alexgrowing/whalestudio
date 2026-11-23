import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviUniqueCartan

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n' : ℕ}

theorem det_ne_zero_of_isCartan {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (e : E →+* ℂ) (θ : Matrix (Fin n) (Fin n) ℂ)
    (h : IsCartan (Complex.I • J.map e) θ) : J.det ≠ 0 := by
  intro hd
  obtain ⟨v, hv, hJv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
  have hx : star (fun i => e (v i)) ≠ 0 := by
    intro h0
    apply hv
    funext i
    have := congrFun h0 i
    simpa using this
  have hpos := h.2.2 _ hx
  have hz : (Complex.I • J.map e) *ᵥ star (star (fun i => e (v i))) = 0 := by
    rw [star_star, Matrix.smul_mulVec]
    have : J.map e *ᵥ (fun i => e (v i)) = 0 := by
      funext i
      have := RingHom.map_mulVec e J v i
      rw [hJv] at this
      simpa [Function.comp_def] using this.symm
    rw [this, smul_zero]
  rw [hz] at hpos
  simp at hpos

theorem form_swap (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (a b : Fin n → E) : σ (form σ J a b) = -form σ J b a := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem incV_add (a b : Fin n' → E) : incV F (a + b) = incV F a + incV F b := by
  funext i; simp [incV]

theorem incV_smul (s : E) (a : Fin n' → E) : incV F (s • a) = inclR (F := F) (AF F) s • incV F a := by
  funext i; simp [incV]

theorem incV_mulVec {k : ℕ} (M : Matrix (Fin n') (Fin k) E) (u : Fin k → E) :
    incV F (M *ᵥ u) = incM F M *ᵥ incV F u := by
  funext i
  exact RingHom.map_mulVec (inclR (F := F) (AF F)) M u i

theorem incV_single (j : Fin n') : incV F (Pi.single j (1 : E)) = Pi.single j 1 := by
  funext k
  by_cases hk : k = j
  · subst hk; simp [incV]
  · simp [incV, Pi.single_apply, hk]

theorem levi_unique {σ : E →ₐ[F] E} (B : Base F E) {n n₁ : ℕ} (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁)
    (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (Y.J j i) = -Y.J i j) (hP : IsIsoPlane σ B H Y Y₁)
    (t : (AE F E)ˣ) (h₁ : UA σ Y₁.J) (m m' : UA σ Y.J)
    (hm : IsLevi (W₁ := Y₁) H t h₁ m) (hm' : IsLevi (W₁ := Y₁) H t h₁ m') : m = m' := by
  obtain ⟨hn, hxx, hyy, hxy, horth, hgram, -, hcart⟩ := hP
  subst hn
  have hadd : ∀ a b c, form σ Y.J (a + b) c = form σ Y.J a c + form σ Y.J b c := fun a b c => by
    simp [form, add_dotProduct]
  have hsmul : ∀ (s : E) a c, form σ Y.J (s • a) c = s * form σ Y.J a c := fun s a c => by
    simp [form, smul_dotProduct]
  have hzero : ∀ c, form σ Y.J 0 c = 0 := fun c => by simp [form]
  have hyx : form σ Y.J H.y H.x = -1 := by
    have := form_swap σ hσ Y.J hJ H.x H.y
    rw [hxy, map_one] at this
    linear_combination this
  have hdet : Y₁.J.det ≠ 0 := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    exact det_ne_zero_of_isCartan _ _ _ (hcart w)
  let Φ : E × (Fin n₁ → E) × E →ₗ[E] (Fin (n₁ + 2) → E) :=
    (LinearMap.smulRight LinearMap.id H.x).comp (LinearMap.fst E E ((Fin n₁ → E) × E)) +
    (Matrix.mulVecLin H.ι).comp ((LinearMap.fst E (Fin n₁ → E) E).comp (LinearMap.snd E E ((Fin n₁ → E) × E))) +
    (LinearMap.smulRight LinearMap.id H.y).comp ((LinearMap.snd E (Fin n₁ → E) E).comp (LinearMap.snd E E ((Fin n₁ → E) × E)))
  have hΦ : ∀ s u r, Φ (s, u, r) = s • H.x + H.ι *ᵥ u + r • H.y := fun s u r => by
    simp [Φ]
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨s, u, r⟩ h
    rw [hΦ] at h
    have e1 := congrArg (fun z => form σ Y.J z H.y) h
    simp only [hadd, hsmul, hxy, hyy, (horth u).2, hzero] at e1
    have hs : s = 0 := by simpa using e1
    subst hs
    have e2 := congrArg (fun z => form σ Y.J z H.x) h
    simp only [hadd, hsmul, hxx, hyx, (horth u).1, hzero] at e2
    have hr : r = 0 := by simpa using e2
    subst hr
    have hu0 : H.ι *ᵥ u = 0 := by simpa using h
    have hu : u ᵥ* Y₁.J = 0 := by
      rw [← hgram, Matrix.mul_assoc, ← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, hu0, Matrix.zero_vecMul]
    have : u = 0 := by
      by_contra hne
      exact hdet (Matrix.exists_vecMul_eq_zero_iff.mp ⟨u, hne, hu⟩)
    subst this
    rfl
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp; omega)).mp hinj
  have key : ∀ z, mat m *ᵥ incV F z = mat m' *ᵥ incV F z := by
    intro z
    obtain ⟨⟨s, u, r⟩, rfl⟩ := hsurj z
    rw [hΦ, incV_add, incV_add, incV_smul, incV_smul, incV_mulVec]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hm.1, hm.2.1, hm.2.2, hm'.1, hm'.2.1, hm'.2.2]
  have hmat : mat m = mat m' := by
    ext i j
    have := congrFun (key (Pi.single j 1)) i
    rw [incV_single, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at this
    simpa using this
  exact Subtype.ext (Units.ext hmat)

end GlobalTheory.LeviUniqueCartan

end
