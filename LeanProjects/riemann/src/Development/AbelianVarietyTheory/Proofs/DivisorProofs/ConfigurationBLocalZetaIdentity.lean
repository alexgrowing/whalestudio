import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedRealFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDeriva
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

namespace GlobalTheory.FockFrames

section OnePlace

variable {R S : ℕ}

def sgn : Ix R S → ℂ
  | .inl _ => 1
  | .inr _ => -1

theorem jm_eq : Jm R S = Matrix.diagonal sgn := by
  ext (i | i) (j | j) <;> simp [Jm, Formalism.UG.Jpq, sgn, Matrix.one_apply, Matrix.diagonal_apply] <;> split_ifs <;> simp

theorem sgn_skipIx (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (c : Ix R S) : sgn (skipIx r₀ s₀ c) = sgn c := by
  cases c <;> rfl

theorem skipIx_ne (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (c : Ix R S) :
    skipIx r₀ s₀ c ≠ .inl r₀ ∧ skipIx r₀ s₀ c ≠ .inr s₀ := by
  cases c <;> simp [skipIx, Fin.succAbove_ne]

theorem jm_mul_jm : Jm R S * Jm R S = 1 := by
  rw [jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext c; cases c <;> simp [sgn]

theorem jm_submatrix (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) :
    (Jm (R + 1) (S + 1)).submatrix (skipIx r₀ s₀) (skipIx r₀ s₀) = Jm R S := by
  rw [jm_eq, jm_eq, Matrix.submatrix_diagonal _ _ (skipIx_injective r₀ s₀)]
  congr 1; funext c; exact sgn_skipIx r₀ s₀ c

theorem mul_eq_one_of_mul_eq_one {n : ℕ} (h : R + S = n) (C : Matrix (Fin n) (Ix R S) ℂ)
    (Y : Matrix (Ix R S) (Fin n) ℂ) (hY : Y * C = 1) : C * Y = 1 := by
  have e : Ix R S ≃ Fin n := Fintype.equivFinOfCardEq (by simp [h])
  exact (Matrix.mul_eq_one_comm_of_equiv e).1 hY

theorem map_star_mul {m n o : Type} [Fintype n] (X : Matrix m n ℂ) (Y : Matrix n o ℂ) :
    (X * Y).map star = X.map star * Y.map star := by
  ext i j
  simp [Matrix.mul_apply, star_sum, mul_comm]

theorem map_star_mulVec {m n : Type} [Fintype n] (K : Matrix m n ℂ) (u : n → ℂ) :
    K.map star *ᵥ star u = star (K *ᵥ u) := by
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]

variable {d d₁ : ℕ}

theorem small_frame (M : Matrix (Fin d) (Fin d) ℂ) (M₁ θ₁ : Matrix (Fin d₁) (Fin d₁) ℂ) (θ : Matrix (Fin d) (Fin d) ℂ)
    (K : Matrix (Fin d) (Fin d₁) ℂ) (C : Matrix (Fin d) (Ix (R + 1) (S + 1)) ℂ) (C₁ : Matrix (Fin d₁) (Ix R S) ℂ)
    (r₀ : Fin (R + 1)) (s₀ : Fin (S + 1)) (hd : R + S = d₁)
    (hgram : Kᵀ * M * K.map star = M₁) (hK : K * C₁ = C.submatrix id (skipIx r₀ s₀))
    (hC : IsFrame M C) (hθ : θ * C = C * Jm (R + 1) (S + 1)) (hθK : θ * K = K * θ₁) (hcart : IsCartan M₁ θ₁) :
    IsFrame M₁ C₁ ∧ θ₁ * C₁ = C₁ * Jm R S := by
  have hG : C₁ᵀ * M₁ * C₁.map star = Jm R S := by
    rw [← hgram]
    have e1 : C₁ᵀ * (Kᵀ * M * K.map star) * C₁.map star = (K * C₁)ᵀ * M * (K * C₁).map star := by
      rw [Matrix.transpose_mul, map_star_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, hK, ← jm_submatrix r₀ s₀, ← hC.1]
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
  have hinj : ∀ u : Fin d₁ → ℂ, K *ᵥ u = 0 → u = 0 := by
    intro u hu
    by_contra hne
    have hp := hcart.2.2 u hne
    have h0 : (θ₁ *ᵥ u) ⬝ᵥ M₁ *ᵥ star u = 0 := by
      rw [← hgram, ← Matrix.mulVec_mulVec, map_star_mulVec, hu, star_zero, Matrix.mulVec_zero, dotProduct_zero]
    rw [h0] at hp
    simp at hp
  refine ⟨⟨hG, (Jm R S * C₁ᵀ * M₁).map star, mul_eq_one_of_mul_eq_one hd _ _ ?_⟩, ?_⟩
  · have h1 : (Jm R S * C₁ᵀ * M₁) * C₁.map star = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc C₁ᵀ, hG, jm_mul_jm]
    have h2 := congrArg (Matrix.map · star) h1
    rw [map_star_mul (Jm R S * C₁ᵀ * M₁)] at h2
    have h3 : (C₁.map star).map star = C₁ := by ext i j; simp
    rw [h3] at h2
    rw [h2]
    ext i j
    simp [Matrix.one_apply]
  · have hX : K * (θ₁ * C₁ - C₁ * Jm R S) = 0 := by
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← hθK, Matrix.mul_assoc, ← Matrix.mul_assoc K C₁, hK, sub_eq_zero]
      ext i c
      have := congrFun (congrFun hθ i) (skipIx r₀ s₀ c)
      simp only [jm_eq, Matrix.mul_diagonal] at this ⊢
      simp only [Matrix.mul_apply, Matrix.submatrix_apply, id] at this ⊢
      rw [this, sgn_skipIx]
    ext j c
    have h := hinj (fun j => (θ₁ * C₁ - C₁ * Jm R S) j c) (by
      funext i
      have := congrFun (congrFun hX i) c
      simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this)
    have := congrFun h j
    simpa [sub_eq_zero] using this

end OnePlace

end GlobalTheory.FockFrames

namespace GlobalTheory.FockFrames

theorem incM_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) : (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem frames_beta : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ (P Q R₀ S₀ : ℕ) (A : InfinitePlace F → Matrix (Fin a) (Ix P Q) ℂ)
        (C₁ : InfinitePlace F → Matrix (Fin (a + b)) (Ix R₀ S₀) ℂ)
        (C : InfinitePlace F → Matrix (Fin (a + (b + 2))) (Ix (R₀ + 1) (S₀ + 1)) ℂ)
        (Φ₁ : Tens F P Q R₀ S₀ →ₗ[ℂ] SInf F (Fin a × Fin (a + b)))
        (Φ : Tens F P Q (R₀ + 1) (S₀ + 1) →ₗ[ℂ] SInf F (Fin a × Fin (a + (b + 2)))) (r₀ : Fin (R₀ + 1)) (s₀ : Fin (S₀ + 1)),
        GlobalTheory.FockBridge.IsFockData B G₁.M A C₁ Φ₁ ∧ GlobalTheory.FockBridge.IsFockData B G.M A C Φ ∧
        GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ ∧ IsCompat B H' C C₁ r₀ s₀ := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hCfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  have hb := hM.triple.base
  have hg := hM.triple.geo
  have hg₁ := hM₁.triple.geo
  have hep := hCfg.ep
  have heq := hCfg.eq
  have hbig := hg₁.aBig
  have hW : G.W.IsSkew σ B (a + b - (G₁.p + G₁.q) + 1) (G₁.p + G₁.q + 1) := by
    have e1 : a + (b + 2) - (G.p + G.q) = a + b - (G₁.p + G₁.q) + 1 := by omega
    have e2 : G.p + G.q = G₁.p + G₁.q + 1 := by omega
    have h := hg.hW
    rw [e1, e2] at h
    exact h
  obtain ⟨r₀, s₀, C, hC, hCθ, hAd⟩ := GlobalTheory.T.adapted_real_frame_exists F E σ B _ _ _ _ _ _ (a + b - (G₁.p + G₁.q)) (G₁.p + G₁.q)
    G.W G₁.W H' hb hW hg₁.hW hCfg.hH' rfl rfl
  have hz : ∀ w (c : Ix (a + b - (G₁.p + G₁.q)) (G₁.p + G₁.q)), ∃ z : Fin (a + b) → ℂ,
      ∀ i, C w i (skipIx r₀ s₀ c) = (H'.ι.map (B.emb w).1 *ᵥ z) i :=
    fun w c => (hAd w).2.2 _ (skipIx_ne r₀ s₀ c).1 (skipIx_ne r₀ s₀ c).2
  choose z hz using hz
  obtain ⟨C₁, hC₁⟩ : ∃ C₁ : InfinitePlace F → Matrix (Fin (a + b)) (Ix (a + b - (G₁.p + G₁.q)) (G₁.p + G₁.q)) ℂ,
      ∀ w j c, C₁ w j c = z w c j := ⟨fun w => Matrix.of fun j c => z w c j, fun _ _ _ => rfl⟩
  have hcomp : IsCompat B H' C C₁ r₀ s₀ := by
    intro w i c
    rw [hz w c i]
    simp [hC₁, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hK : ∀ w, H'.ι.map (B.emb w).1 * C₁ w = (C w).submatrix id (skipIx r₀ s₀) := by
    intro w; ext i c; exact (hcomp w i c).symm
  have hgram : ∀ w, (H'.ι.map (B.emb w).1)ᵀ * (Complex.I • G.W.J.map (B.emb w).1) * (H'.ι.map (B.emb w).1).map star =
      Complex.I • G₁.W.J.map (B.emb w).1 := by
    intro w
    have h := congrArg (fun Z => Matrix.map Z (B.emb w).1) hCfg.hH'.gram
    simp only [Matrix.map_mul, Matrix.transpose_map] at h
    have hσ : (H'.ι.map σ).map (B.emb w).1 = (H'.ι.map (B.emb w).1).map star := by
      ext i j
      simp [hb.cm.2.2.2]
    rw [hσ] at h
    rw [Matrix.mul_smul, Matrix.smul_mul, h]
  have hC₁f : ∀ w, IsFrame (Complex.I • G₁.W.J.map (B.emb w).1) (C₁ w) ∧
      G₁.W.θ w * C₁ w = C₁ w * Jm (a + b - (G₁.p + G₁.q)) (G₁.p + G₁.q) := fun w =>
    small_frame _ _ _ _ _ _ _ r₀ s₀ (by omega) (hgram w) (hK w) (by have := hC w; rwa [incM_map] at this) (hCθ w)
      (hCfg.hH'.cartan w).1 (hg₁.hW.cartan w)
  choose A hA hAθ using fun w => frameEx_holds _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map, one_smul]; exact hA w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC⟩
  have fr₁ : Framed B.emb (incM F G₁.V.J) (incM F G₁.W.J) 1 Complex.I A C₁ :=
    ⟨one_mul _, by rw [hCfg.eV]; exact hA1, fun w => by rw [incM_map]; exact (hC₁f w).1⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.FockMapEx.fockEx_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1
    Complex.I A C hb.cm hb.std fr
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.FockMapEx.fockEx_of_derEx GlobalTheory.HeisDer.derEx F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G₁.M.co 1
    Complex.I A C₁ hb.cm hb.std fr₁
  refine ⟨_, _, _, _, A, C₁, C, Φ₁, Φ, r₀, s₀, ⟨⟨fr₁, ?_, fun w => (hC₁f w).2⟩, hΦ₁⟩, ⟨⟨fr, hAθ, hCθ⟩, hΦ⟩, hAd, hcomp⟩
  rw [hCfg.eV]; exact hAθ

end GlobalTheory.FockFrames
