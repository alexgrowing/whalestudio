import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfiniteCompactLeviLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianVectorEigenDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFrameOrthogonalExtensionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

open GlobalTheory.RealLift Formalism.BasicNotions.TH Matrix

namespace GlobalTheory.AdaptedFrameW

theorem hyp_pair {n : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (hM : Mᴴ = M) (hθ : IsCartan M θ)
    (hx : x ≠ 0) (hxx : x ⬝ᵥ M *ᵥ star x = 0) :
    ∃ (e f : Fin n → ℂ) (k : ℂ), k ≠ 0 ∧ x = k • (e + f) ∧ θ *ᵥ x = k • (e - f) ∧ θ *ᵥ e = e ∧ θ *ᵥ f = -f ∧
      e ⬝ᵥ M *ᵥ star e = 1 ∧ f ⬝ᵥ M *ᵥ star f = -1 ∧ e ⬝ᵥ M *ᵥ star f = 0 ∧ f ⬝ᵥ M *ᵥ star e = 0 ∧
      ∀ u : Fin n → ℂ, u ⬝ᵥ M *ᵥ star x = 0 → u ⬝ᵥ M *ᵥ star (θ *ᵥ x) = 0 →
        u ⬝ᵥ M *ᵥ star e = 0 ∧ u ⬝ᵥ M *ᵥ star f = 0 ∧ e ⬝ᵥ M *ᵥ star u = 0 ∧ f ⬝ᵥ M *ᵥ star u = 0 :=
  GlobalTheory.T.hermitian_vector_eigen_decomposition M θ x hM hθ hx hxx

theorem frame_assemble {n n₁ r₁ s₁ : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ)
    (ι : Matrix (Fin n) (Fin n₁) ℂ) (C₁ : Matrix (Fin n₁) (Ix r₁ s₁) ℂ) (e f : Fin n → ℂ)
    (hn : (r₁ + 1) + (s₁ + 1) = n) (hC₁ : IsFrame (ιᵀ * M * ι.map star) C₁) (hθC₁ : θ₁ * C₁ = C₁ * Jm r₁ s₁)
    (hθι : θ * ι = ι * θ₁) (hθe : θ *ᵥ e = e) (hθf : θ *ᵥ f = -f) (hee : e ⬝ᵥ M *ᵥ star e = 1)
    (hff : f ⬝ᵥ M *ᵥ star f = -1) (hef : e ⬝ᵥ M *ᵥ star f = 0) (hfe : f ⬝ᵥ M *ᵥ star e = 0)
    (horth : ∀ u : Fin n₁ → ℂ, (ι *ᵥ u) ⬝ᵥ M *ᵥ star e = 0 ∧ (ι *ᵥ u) ⬝ᵥ M *ᵥ star f = 0 ∧
      e ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0 ∧ f ⬝ᵥ M *ᵥ star (ι *ᵥ u) = 0) :
    ∃ C : Matrix (Fin n) (Ix (r₁ + 1) (s₁ + 1)) ℂ, IsFrame M C ∧ θ * C = C * Jm (r₁ + 1) (s₁ + 1) ∧
      (∀ i, C i (.inl 0) = e i) ∧ (∀ i, C i (.inr 0) = f i) ∧
      ∀ a, a ≠ .inl 0 → a ≠ .inr 0 → ∃ z : Fin n₁ → ℂ, ∀ i, C i a = (ι *ᵥ z) i :=
  GlobalTheory.T.hermitian_frame_orthogonal_extension M θ θ₁ ι C₁ e f hn hC₁ hθC₁ hθι hθe hθf hee hff hef hfe horth

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem form_map (τ : E →+* ℂ) (hcm : ∀ z, τ (σ z) = star (τ z)) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (a b : Fin n → E) :
    (fun i => τ (a i)) ⬝ᵥ (Complex.I • J.map τ) *ᵥ star (fun i => τ (b i)) = Complex.I * τ (form σ J a b) := by
  simp only [form, dotProduct, mulVec, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_sum, map_mul, hcm, Pi.star_apply,
    star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end GlobalTheory.AdaptedFrameW

namespace GlobalTheory.AdaptedFrameW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem herm_of_skew (τ : E →+* ℂ) (hcm : ∀ z, τ (σ z) = star (τ z)) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) : (Complex.I • J.map τ)ᴴ = Complex.I • J.map τ := by
  ext i j
  simp only [conjTranspose_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, star_mul', Complex.star_def,
    Complex.conj_I]
  rw [← Complex.star_def, ← hcm, hJ, map_neg]
  ring

theorem orth_map (τ : E →+* ℂ) (hcm : ∀ z, τ (σ z) = star (τ z)) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (ι : Matrix (Fin n) (Fin n₁) E) (b : Fin n → E) (h : ∀ v, form σ J (ι *ᵥ v) b = 0) (u : Fin n₁ → ℂ) :
    (ι.map τ *ᵥ u) ⬝ᵥ (Complex.I • J.map τ) *ᵥ star (fun i => τ (b i)) = 0 := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm]
  have : (ι.map τ)ᵀ *ᵥ ((Complex.I • J.map τ) *ᵥ star (fun i => τ (b i))) = 0 := by
    funext k
    have h1 := form_map τ hcm J (ι *ᵥ Pi.single k 1) b
    rw [h, map_zero, mul_zero, mulVec_single_one] at h1
    exact h1
  rw [this, dotProduct_zero]

end GlobalTheory.AdaptedFrameW

namespace GlobalTheory.AdaptedFrameW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem gram_map (τ : E →+* ℂ) (hcm : ∀ z, τ (σ z) = star (τ z)) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (J₁ : Matrix (Fin n₁) (Fin n₁) E) (ι : Matrix (Fin n) (Fin n₁) E) (h : ιᵀ * J * ι.map σ = J₁) :
    (ι.map τ)ᵀ * (Complex.I • J.map τ) * (ι.map τ).map star = Complex.I • J₁.map τ := by
  have e : (ι.map τ).map star = (ι.map σ).map τ := by ext i j; simp [hcm]
  rw [e, ← h, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, Matrix.mul_smul, Matrix.smul_mul]

theorem exists_adaptedFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ i₀ i₁ r s r₁ s₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → r = r₁ + 1 → s = s₁ + 1 →
    ∃ (r₀ : Fin r) (s₀ : Fin s) (C : InfinitePlace F → Matrix (Fin d) (Formalism.BasicNotions.TH.Ix r s) ℂ),
      (∀ w, GlobalTheory.RealLift.IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)) ∧
      (∀ w, W.θ w * C w = C w * Formalism.BasicNotions.TH.Jm r s) ∧ GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ := by
  intro F E _ _ _ _ _ σ B d d₁ i₀ i₁ r s r₁ s₁ W W₁ H' hB hW hW₁ hH hr hs
  subst hr hs
  have hx0 : H'.x ≠ 0 := by
    intro h0
    have := hH.xy
    rw [h0] at this
    simp [form] at this
  have key : ∀ w, ∃ C : Matrix (Fin d) (Ix (r₁ + 1) (s₁ + 1)) ℂ,
      IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) C ∧ W.θ w * C = C * Jm (r₁ + 1) (s₁ + 1) ∧
      ((∃ c : ℂ, c ≠ 0 ∧ ∀ i, (B.emb w).1 (H'.x i) = c * (C i (.inl 0) + C i (.inr 0))) ∧
        (∃ c₁ c₂ : ℂ, ∀ i, (B.emb w).1 (H'.y i) = c₁ * C i (.inl 0) + c₂ * C i (.inr 0)) ∧
        ∀ a, a ≠ .inl 0 → a ≠ .inr 0 → ∃ z : Fin d₁ → ℂ, ∀ i, C i a = (H'.ι.map (B.emb w).1 *ᵥ z) i) := by
    intro w
    have hcm : ∀ z, (B.emb w).1 (σ z) = star ((B.emb w).1 z) := fun z => hB.cm.2.2.2 _ z
    rw [GlobalTheory.LeviKInf.incM_map_piInf]
    set τ : E →+* ℂ := (B.emb w).1 with hτ
    set M := Complex.I • W.J.map τ with hMdef
    set x : Fin d → ℂ := fun i => τ (H'.x i) with hxdef
    set y : Fin d → ℂ := fun i => τ (H'.y i) with hydef
    have hM : Mᴴ = M := herm_of_skew τ hcm hW.skew
    have hxne : x ≠ 0 := by
      intro h0; apply hx0; funext i
      have := congrFun h0 i
      simpa [hxdef] using this
    have hxx : x ⬝ᵥ M *ᵥ star x = 0 := by
      rw [form_map τ hcm W.J H'.x H'.x, hH.xx, map_zero, mul_zero]
    obtain ⟨c, hc, hyc⟩ := (hH.cartan w).2
    have hθx : W.θ w *ᵥ x = c⁻¹ • y := by
      have hy' : y = c • (W.θ w *ᵥ x) := by rw [hydef, hyc]
      rw [hy', smul_smul, inv_mul_cancel₀ hc, one_smul]
    obtain ⟨e, f, k, hk, hxk, hθxk, hθe, hθf, hee, hff, hef, hfe, hort⟩ := hyp_pair M (W.θ w) x hM (hW.cartan w) hxne hxx
    obtain ⟨C₁, hC₁, hθC₁⟩ := GlobalTheory.RealLift.frameEx_holds d₁ r₁ s₁ _ _ (hW₁.sig w) (hW₁.cartan w)
    have hg := gram_map τ hcm W.J W₁.J H'.ι hH.gram
    have hox : ∀ u, (H'.ι.map τ *ᵥ u) ⬝ᵥ M *ᵥ star x = 0 :=
      orth_map τ hcm W.J H'.ι H'.x (fun v => (hH.orth v).1)
    have hoy : ∀ u, (H'.ι.map τ *ᵥ u) ⬝ᵥ M *ᵥ star y = 0 :=
      orth_map τ hcm W.J H'.ι H'.y (fun v => (hH.orth v).2)
    have hoθ : ∀ u, (H'.ι.map τ *ᵥ u) ⬝ᵥ M *ᵥ star (W.θ w *ᵥ x) = 0 := by
      intro u
      rw [hθx, star_smul, mulVec_smul, dotProduct_smul, hoy, smul_zero]
    obtain ⟨C, hCf, hCθ, hCe, hCf0, hCo⟩ := frame_assemble M (W.θ w) (W₁.θ w) (H'.ι.map τ) C₁ e f (hW.sig w).1
      (by rw [hg]; exact hC₁) hθC₁ (hH.cartan w).1 hθe hθf hee hff hef hfe
      (fun u => hort _ (hox u) (hoθ u))
    refine ⟨C, hCf, hCθ, ⟨k, hk, fun i => ?_⟩, ⟨c * k, -(c * k), fun i => ?_⟩, hCo⟩
    · rw [hCe, hCf0]
      have := congrFun hxk i
      simpa [hxdef] using this
    · rw [hCe, hCf0]
      have h1 : y = c • (W.θ w *ᵥ x) := by rw [hθx, smul_smul, mul_inv_cancel₀ hc, one_smul]
      have := congrFun h1 i
      rw [hθxk] at this
      simp only [hydef, Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at this
      rw [this]; ring
  choose C hC using key
  exact ⟨0, 0, C, fun w => (hC w).1, fun w => (hC w).2.1, fun w => (hC w).2.2⟩

end GlobalTheory.AdaptedFrameW

end
