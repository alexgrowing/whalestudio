import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanAdeleCMPrescribedEmbeddingValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem exists_mat_at {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => GlobalTheory.PolRangeInf.exists_at_inf_values hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

theorem mat_eq_zero {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (D : Matrix m k (AE F E)) (hD : At (evI F) D) (h0 : ∀ w, D.map (piInf (τ w)) = 0) : D = 0 := by
  ext i j
  refine GlobalTheory.RealLift.KLineProof.eq_zero_of_piInf hcm τ (D i j) (fun u hu => ?_) (fun w => ?_)
  · have := congrFun (congrFun (hD u hu) i) j
    simpa using this
  · have := congrFun (congrFun (h0 w) i) j
    simpa using this

theorem at_add {m k : Type} {D D' : Matrix m k (AE F E)} (hD : At (evI F) D) (hD' : At (evI F) D') :
    At (evI F) (D + D') := by
  intro u hu; rw [smul_add, hD u hu, hD' u hu, add_zero]

theorem at_mul_left {m k l : Type} [Fintype k] {D : Matrix m k (AE F E)} (hD : At (evI F) D) (N : Matrix k l (AE F E)) :
    At (evI F) (D * N) := by
  intro u hu; rw [← Matrix.smul_mul, hD u hu, Matrix.zero_mul]

theorem at_mul_right {m k l : Type} [Fintype k] {D : Matrix k l (AE F E)} (hD : At (evI F) D) (N : Matrix m k (AE F E)) :
    At (evI F) (N * D) := by
  intro u hu; rw [← Matrix.mul_smul, hD u hu, Matrix.mul_zero]

theorem at_transpose {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) : At (evI F) Dᵀ := by
  intro u hu; rw [← Matrix.transpose_smul, hD u hu, Matrix.transpose_zero]

theorem at_map_cA (σ : E →ₐ[F] E) {m k : Type} {D : Matrix m k (AE F E)} (hD : At (evI F) D) :
    At (evI F) (D.map (cA σ)) := by
  intro u hu
  ext i j
  have := congrFun (congrFun (hD u hu) i) j
  simp only [Matrix.smul_apply, Matrix.zero_apply, Matrix.map_apply] at this ⊢
  rw [← map_smul, this, map_zero]

theorem map_cA_piInf {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {m k : Type}
    (D : Matrix m k (AE F E)) : (D.map (cA σ)).map (piInf τ) = (D.map (piInf τ)).map star := by
  ext i j
  simp [GlobalTheory.RealLift.KLineProof.piInf_cA hcm]

theorem cartan_conj {n r s : ℕ} (M θ₁ θ₂ : Matrix (Fin n) (Fin n) ℂ) (hs : HasSig M r s) (h₁ : IsCartan M θ₁)
    (h₂ : IsCartan M θ₂) :
    ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧ uᵀ * M * u.map star = M ∧ u * θ₁ = θ₂ * u := by
  obtain ⟨A₁, hF₁, hA₁⟩ := GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s M θ₁ hs h₁
  obtain ⟨A₂, hF₂, hA₂⟩ := GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s M θ₂ hs h₂
  obtain ⟨A₁', h11, h12⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₁
  obtain ⟨A₂', h21, h22⟩ := GlobalTheory.RealLift.KLineProof.frame_inv hF₂
  refine ⟨A₂ * A₁', A₁ * A₂', ?_, ?_, ?_⟩
  · calc A₂ * A₁' * (A₁ * A₂') = A₂ * (A₁' * A₁) * A₂' := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [h12, Matrix.mul_one, h21]
  · have e1 := hF₁.1
    have e2 := hF₂.1
    rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]
    calc A₁'ᵀ * A₂ᵀ * M * (A₂.map star * A₁'.map star)
        = A₁'ᵀ * (A₂ᵀ * M * A₂.map star) * A₁'.map star := by simp only [Matrix.mul_assoc]
      _ = A₁'ᵀ * (A₁ᵀ * M * A₁.map star) * A₁'.map star := by rw [e2, e1]
      _ = (A₁ * A₁')ᵀ * M * (A₁ * A₁').map star := by
          rw [Matrix.transpose_mul, GlobalTheory.RealLift.KLineProof.map_star_mul]; simp only [Matrix.mul_assoc]
      _ = M := by
          rw [h11, Matrix.transpose_one, Matrix.map_one _ (star_zero _) (star_one _), Matrix.one_mul, Matrix.mul_one]
  · have k1 : A₁' * θ₁ = Formalism.BasicNotions.TH.Jm r s * A₁' := by
      calc A₁' * θ₁ = A₁' * θ₁ * (A₁ * A₁') := by rw [h11, Matrix.mul_one]
        _ = A₁' * (θ₁ * A₁) * A₁' := by simp only [Matrix.mul_assoc]
        _ = (A₁' * A₁) * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [hA₁]; simp only [Matrix.mul_assoc]
        _ = Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [h12, Matrix.one_mul]
    calc A₂ * A₁' * θ₁ = A₂ * (A₁' * θ₁) := Matrix.mul_assoc _ _ _
      _ = A₂ * Formalism.BasicNotions.TH.Jm r s * A₁' := by rw [k1, Matrix.mul_assoc]
      _ = θ₂ * (A₂ * A₁') := by rw [← hA₂, Matrix.mul_assoc]

end GlobalTheory.CartanConjSkew

namespace GlobalTheory.CartanConjSkew

open scoped Matrix

theorem conj_skew : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n r s : ℕ) (X Y : Spc F E n), B.IsGood σ → X.IsSkew σ B r s → (reS X Y).IsSkew σ B r s →
    ∃ g ∈ UAt σ X (evI F), ∀ w, (mat g).map (piInf (B.emb w)) * X.θ w = Y.θ w * (mat g).map (piInf (B.emb w)) := by
  intro F E _ _ _ _ _ σ B n r s X Y hB hX hY
  have hcm := hB.cm
  have key : ∀ w, ∃ u v : Matrix (Fin n) (Fin n) ℂ, u * v = 1 ∧
      uᵀ * X.J.map (B.emb w).1 * u.map star = X.J.map (B.emb w).1 ∧ u * X.θ w = Y.θ w * u := by
    intro w
    obtain ⟨u, v, huv, hu, hθ⟩ := cartan_conj (Complex.I • X.J.map (B.emb w).1) (X.θ w) (Y.θ w) (hX.sig w)
      (hX.cartan w) (hY.cartan w)
    refine ⟨u, v, huv, ?_, hθ⟩
    rw [Matrix.mul_smul, Matrix.smul_mul] at hu
    exact smul_right_injective _ Complex.I_ne_zero hu
  choose u v huv hu hθ using key
  obtain ⟨G, hGat, hG⟩ := exists_mat_at hcm B.emb (fun w => u w - 1)
  obtain ⟨H, hHat, hH⟩ := exists_mat_at hcm B.emb (fun w => v w - 1)
  have hmap1 : ∀ w, (1 : Matrix (Fin n) (Fin n) (AE F E)).map (piInf (B.emb w)) = 1 :=
    fun w => Matrix.map_one _ (map_zero _) (map_one _)
  have hgmap : ∀ w, (1 + G).map (piInf (B.emb w)) = u w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hG]; abel
  have hhmap : ∀ w, (1 + H).map (piInf (B.emb w)) = v w := by
    intro w; rw [Matrix.map_add _ (map_add _), hmap1, hH]; abel
  have hgh : (1 + G) * (1 + H) = 1 := by
    have h0 : (1 + G) * (1 + H) - 1 = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G) * (1 + H) - 1 = G + H + G * H := by noncomm_ring
        rw [e]; exact at_add (at_add hGat hHat) (at_mul_left hGat H)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, hgmap, hhmap, hmap1, huv, sub_self]
    exact sub_eq_zero.1 h0
  have hhg : (1 + H) * (1 + G) = 1 := (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).1 hgh
  let g0 : GL (Fin n) (AE F E) := ⟨1 + G, 1 + H, hgh, hhg⟩
  have hmem : g0 ∈ UG (cA σ) (incM F X.J) := by
    show (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) = incM F X.J
    have h0 : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J = 0 := by
      apply mat_eq_zero hcm B.emb
      · have e : (1 + G)ᵀ * incM F X.J * (1 + G).map (cA σ) - incM F X.J =
            Gᵀ * incM F X.J + incM F X.J * G.map (cA σ) + Gᵀ * incM F X.J * G.map (cA σ) := by
          rw [Matrix.map_add _ (map_add _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_add, Matrix.transpose_one]
          noncomm_ring
        rw [e]
        exact at_add (at_add (at_mul_left (at_transpose hGat) _) (at_mul_right (at_map_cA σ hGat) _))
          (at_mul_right (at_map_cA σ hGat) _)
      · intro w
        rw [Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_cA_piInf hcm, hgmap,
          incM_map_piInf, hu, sub_self]
    exact sub_eq_zero.1 h0
  refine ⟨⟨g0, hmem⟩, ?_, fun w => ?_⟩
  · show At (evI F) ((1 + G) - 1)
    rw [add_sub_cancel_left]; exact hGat
  · show (1 + G).map (piInf (B.emb w)) * X.θ w = Y.θ w * (1 + G).map (piInf (B.emb w))
    rw [hgmap]; exact hθ w

end GlobalTheory.CartanConjSkew
