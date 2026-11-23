import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasHermitianSignatureComplementHyperbolicPlane

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.SkewPlaneSig

open Matrix

theorem hasSig_skew_complement : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → ∀ P : Matrix (Fin n₁) (Fin n) E, P * H.ι = 1 → ∀ w, HasSig (Complex.I • W₁.J.map (B.emb w).1) (r - 1) (s - 1) := by
  intro F E _ _ _ _ _ σ B hB n n₁ W W₁ H i₀ i₁ r s hW hH P hP w
  set τ : E →+* ℂ := (B.emb w).1 with hτ
  have hcm : ∀ z : E, τ (σ z) = star (τ z) := fun z => hB.cm.2.2.2 τ z
  set J' : Matrix (Fin n) (Fin n) ℂ := W.J.map τ with hJ'
  set X : Fin n → ℂ := fun i => τ (H.x i) with hX
  set Y0 : Fin n → ℂ := fun i => τ (H.y i) with hY0
  set ι' : Matrix (Fin n) (Fin n₁) ℂ := H.ι.map τ with hι'
  have hform : ∀ a b : Fin n → E, τ (form σ W.J a b) = (fun i => τ (a i)) ⬝ᵥ J' *ᵥ star (fun i => τ (b i)) := by
    intro a b
    have hs : (star fun i => τ (b i)) = τ ∘ fun i => σ (b i) := by ext i; simp [hcm]
    rw [hs, form, RingHom.map_dotProduct]
    show (τ ∘ a) ⬝ᵥ _ = (τ ∘ a) ⬝ᵥ _
    congr 1
    ext i
    exact RingHom.map_mulVec τ W.J _ i
  have hsm : ∀ u v : Fin n → ℂ, u ⬝ᵥ (Complex.I • J') *ᵥ v = Complex.I * (u ⬝ᵥ J' *ᵥ v) := by
    intro u v; rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hst : star (Complex.I • Y0) = (-Complex.I) • star Y0 := by
    rw [star_smul]; congr 1; simp [Complex.star_def]
  have hXX : X ⬝ᵥ (Complex.I • J') *ᵥ star X = 0 := by
    rw [hsm, ← hform, hH.xx, map_zero, mul_zero]
  have hYY : (Complex.I • Y0) ⬝ᵥ (Complex.I • J') *ᵥ star (Complex.I • Y0) = 0 := by
    rw [hsm, hst, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, ← hform, hH.yy]; simp
  have hXY : X ⬝ᵥ (Complex.I • J') *ᵥ star (Complex.I • Y0) = 1 := by
    rw [hsm, hst, Matrix.mulVec_smul, dotProduct_smul, ← hform, hH.xy]; simp
  have hMh : (Complex.I • J')ᴴ = Complex.I • J' := by
    ext i j
    have h := hW.skew i j
    have h2 : star (τ (W.J j i)) = - τ (W.J i j) := by rw [← hcm, h, map_neg]
    simp [conjTranspose_apply, hJ', h2, Complex.star_def]
  have hιv : ∀ b : Fin n → E, (∀ u, form σ W.J (H.ι *ᵥ u) b = 0) →
      ι'ᵀ *ᵥ ((Complex.I • J') *ᵥ star (fun i => τ (b i))) = 0 := by
    intro b hb
    ext j
    have h1 := congrArg τ (hb (Pi.single j 1))
    rw [map_zero, hform, Matrix.mulVec_single_one] at h1
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
    convert mul_zero Complex.I using 2
    rw [← h1]
    simp [Matrix.mulVec, hι', dotProduct]
  have hιX : ι'ᵀ *ᵥ ((Complex.I • J') *ᵥ star X) = 0 := hιv H.x fun u => (hH.orth u).1
  have hιY : ι'ᵀ *ᵥ ((Complex.I • J') *ᵥ star (Complex.I • Y0)) = 0 := by
    rw [hst, Matrix.mulVec_smul, Matrix.mulVec_smul, hιv H.y fun u => (hH.orth u).2, smul_zero]
  have hPι : P.map τ * ι' = 1 := by
    rw [hι', ← Matrix.map_mul, hP, Matrix.map_one _ (map_zero τ) (map_one τ)]
  have hc := GlobalTheory.PlaneSig.hasSig_complement_plane n n₁ (Complex.I • J') X (Complex.I • Y0) ι' (P.map τ) r s hH.rank hMh
    hXX hYY hXY hιX hιY hPι (hW.sig w)
  have hg : ι'ᵀ * (Complex.I • J') * ι'.map star = Complex.I • W₁.J.map τ := by
    have hs : ι'.map star = (H.ι.map σ).map τ := by ext i j; simp [hι', hcm]
    rw [Matrix.mul_smul, Matrix.smul_mul, hs, hι', hJ', ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, hH.gram]
  rwa [hg] at hc

end GlobalTheory.SkewPlaneSig
