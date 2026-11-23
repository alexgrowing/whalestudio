import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameDualGram

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.LeviFrame

theorem levi_unit_alg {R : Type} [CommRing R] (c : R →+* R) {d d₁ : ℕ} (Jd : Matrix (Fin d) (Fin d) R)
    (J₁ : Matrix (Fin d₁) (Fin d₁) R) (I : Matrix (Fin d) (Fin d₁) R) (P : Matrix (Fin d₁) (Fin d) R)
    (H : Matrix (Fin d₁) (Fin d₁) R) (hPI : P * I = 1) (hc : Iᵀ * Jd = J₁ * P.map c)
    (hd : Jd * I.map c = Pᵀ * J₁) (hH : Hᵀ * J₁ * H.map c = J₁) :
    (1 + I * ((H - 1) * P))ᵀ * Jd * (1 + I * ((H - 1) * P)).map c = Jd := by
  set D := H - 1 with hDdef
  have hD : Dᵀ * J₁ + J₁ * D.map c + Dᵀ * (J₁ * D.map c) = 0 := by
    have e1 : Dᵀ = Hᵀ - 1 := by simp [D, Matrix.transpose_sub]
    have e2 : D.map c = H.map c - 1 := by
      simp only [D]; rw [Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c)]
    rw [e1, e2]
    have : (Hᵀ - 1) * J₁ + J₁ * (H.map c - 1) + (Hᵀ - 1) * (J₁ * (H.map c - 1)) = Hᵀ * J₁ * H.map c - J₁ := by
      noncomm_ring
    rw [this, hH, sub_self]
  have hPIc : P.map c * I.map c = 1 := by
    rw [← Matrix.map_mul, hPI, Matrix.map_one _ (map_zero c) (map_one c)]
  have hc' : ∀ X : Matrix (Fin d) (Fin d) R, Iᵀ * (Jd * X) = J₁ * (P.map c * X) := fun X => by
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc]
  have hd' : ∀ X : Matrix (Fin d₁) (Fin d) R, Jd * (I.map c * X) = Pᵀ * (J₁ * X) := fun X => by
    rw [← Matrix.mul_assoc, hd, Matrix.mul_assoc]
  have hp' : ∀ X : Matrix (Fin d₁) (Fin d) R, P.map c * (I.map c * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPIc, Matrix.one_mul]
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.map_add _ (map_add c), Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_mul, Matrix.map_mul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hc', hd', hp', hc]
  have key : Pᵀ * ((Dᵀ * J₁ + J₁ * D.map c + Dᵀ * (J₁ * D.map c)) * P.map c) = 0 := by
    rw [hD, Matrix.zero_mul, Matrix.mul_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc] at key
  have := congrArg (Jd + ·) key
  simp only [add_zero] at this
  refine Eq.trans ?_ this; abel

theorem levi_inv_alg {R : Type} [CommRing R] {d d₁ : ℕ} (I : Matrix (Fin d) (Fin d₁) R) (P : Matrix (Fin d₁) (Fin d) R)
    (H K : Matrix (Fin d₁) (Fin d₁) R) (hPI : P * I = 1) (hHK : H * K = 1) :
    (1 + I * ((H - 1) * P)) * (1 + I * ((K - 1) * P)) = 1 := by
  have hp' : ∀ X : Matrix (Fin d₁) (Fin d) R, P * (I * X) = X := fun X => by
    rw [← Matrix.mul_assoc, hPI, Matrix.one_mul]
  have hk : (H - 1) + (K - 1) + (H - 1) * (K - 1) = 0 := by
    have : (H - 1) + (K - 1) + (H - 1) * (K - 1) = H * K - 1 := by noncomm_ring
    rw [this, hHK, sub_self]
  have key : I * (((H - 1) + (K - 1) + (H - 1) * (K - 1)) * P) = 0 := by rw [hk, Matrix.zero_mul, Matrix.mul_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hp']
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc] at key
  have := congrArg ((1 : Matrix (Fin d) (Fin d) R) + ·) key
  simp only [add_zero] at this
  refine Eq.trans ?_ this; abel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem frame_facts (σ : E →ₐ[F] E) (B : Base F E) {d : ℕ} (W : Spc F E d) {r s d₁ : ℕ} (W₁ : Spc F E d₁)
    (H' : Plane E d d₁) {i₀ i₁ : ℕ} (hσ : IsCMExt F E σ) (hW : W.IsSkew σ B r s)
    (hH : H'.IsAdapted σ B W W₁ i₀ i₁) : ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧ π *ᵥ H'.x = 0 ∧
      π *ᵥ H'.y = 0 ∧ H'.ιᵀ * W.J = W₁.J * π.map σ ∧ W.J * H'.ι.map σ = πᵀ * W₁.J := by
  obtain ⟨π, hπι, hF, -⟩ := GlobalTheory.PlaneFrame.frame_dual_gram F E σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH
  have hsk := GlobalTheory.PlaneFrame.form_skew hσ hW.skew
  set a : Fin d → E := W.J *ᵥ fun i => σ (H'.y i) with ha
  set b : Fin d → E := W.J *ᵥ fun i => σ (H'.x i) with hb
  have hax : a ⬝ᵥ H'.x = 1 := by rw [dotProduct_comm]; exact hH.xy
  have hbx : b ⬝ᵥ H'.x = 0 := by rw [dotProduct_comm]; exact hH.xx
  have hay : a ⬝ᵥ H'.y = 0 := by rw [dotProduct_comm]; exact hH.yy
  have hby : b ⬝ᵥ H'.y = -1 := by
    rw [dotProduct_comm]; show form σ W.J H'.y H'.x = -1
    rw [hsk, hH.xy, map_one]
  have hker : ∀ v, H'.ι *ᵥ (π *ᵥ v) = 0 → π *ᵥ v = 0 := fun v hv => by
    rw [← Matrix.one_mulVec (π *ᵥ v), ← hπι, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have hπx : π *ᵥ H'.x = 0 := by
    apply hker
    have := congrArg (· *ᵥ H'.x) hF
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, hax, hbx, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, MulOpposite.op_one, one_smul, MulOpposite.op_zero, zero_smul, sub_zero] at this
    simpa using this
  have hπy : π *ᵥ H'.y = 0 := by
    apply hker
    have := congrArg (· *ᵥ H'.y) hF
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.vecMulVec_mulVec, hay, hby, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, MulOpposite.op_zero, zero_smul, zero_add] at this
    simpa using this

  have hιv : ∀ v : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) v = 0) → H'.ιᵀ *ᵥ (W.J *ᵥ fun i => σ (v i)) = 0 := by
    intro v hv
    ext j
    have := hv (Pi.single j 1)
    simp only [form, Matrix.mulVec_single_one] at this
    rw [Matrix.mulVec_transpose]
    simpa [Matrix.vecMul, dotProduct, Matrix.transpose_apply, mul_comm] using this
  have hvι : ∀ v : Fin d → E, (∀ u, form σ W.J v (H'.ι *ᵥ u) = 0) → v ᵥ* (W.J * H'.ι.map σ) = 0 := by
    intro v hv
    ext j
    have := hv (Pi.single j 1)
    simp only [form, Matrix.mulVec_single_one] at this
    rw [← Matrix.vecMul_vecMul]
    simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, Finset.mul_sum,
      Finset.sum_mul] at this ⊢
    rw [Finset.sum_comm]
    simpa [mul_assoc] using this
  have hιb : H'.ιᵀ *ᵥ b = 0 := hιv _ fun u => (hH.orth u).1
  have hιa : H'.ιᵀ *ᵥ a = 0 := hιv _ fun u => (hH.orth u).2
  have hxι : H'.x ᵥ* (W.J * H'.ι.map σ) = 0 := hvι _ fun u => by rw [hsk, (hH.orth u).1, map_zero, neg_zero]
  have hyι : H'.y ᵥ* (W.J * H'.ι.map σ) = 0 := hvι _ fun u => by rw [hsk, (hH.orth u).2, map_zero, neg_zero]
  refine ⟨π, hπι, hπx, hπy, ?_, ?_⟩
  · let σR : E →+* E := σ.toRingHom
    have hFσ : Matrix.vecMulVec (fun i => σ (H'.x i)) (fun i => σ (a i)) + H'.ι.map σR * π.map σR -
        Matrix.vecMulVec (fun i => σ (H'.y i)) (fun i => σ (b i)) = 1 := by
      have := congrArg (RingHom.mapMatrix σR) hF
      rw [map_sub, map_add, map_one, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
        Matrix.map_mul] at this
      rw [← this]
      congr 1 <;> [congr 1; skip] <;> ext i j <;> simp [Matrix.vecMulVec, σR]
    calc H'.ιᵀ * W.J = H'.ιᵀ * W.J * 1 := (Matrix.mul_one _).symm
      _ = W₁.J * π.map σ := by
        rw [← hFσ, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_vecMulVec, Matrix.mul_vecMulVec,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
        rw [show (W.J *ᵥ fun i => σ (H'.x i)) = b from rfl, show (W.J *ᵥ fun i => σ (H'.y i)) = a from rfl, hιb, hιa]
        rw [← Matrix.mul_assoc, show H'.ι.map σR = H'.ι.map σ from rfl, hH.gram]
        simp [Matrix.vecMulVec, σR]
  · have hFt : Matrix.vecMulVec a H'.x + πᵀ * H'.ιᵀ - Matrix.vecMulVec b H'.y = 1 := by
      have := congrArg Matrix.transpose hF
      rwa [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_vecMulVec, Matrix.transpose_vecMulVec,
        Matrix.transpose_mul, Matrix.transpose_one] at this
    calc W.J * H'.ι.map σ = 1 * (W.J * H'.ι.map σ) := (Matrix.one_mul _).symm
      _ = πᵀ * W₁.J := by
        rw [← hFt, Matrix.sub_mul, Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.vecMulVec_mul, hxι, hyι,
          Matrix.mul_assoc, ← Matrix.mul_assoc H'.ιᵀ, hH.gram]
        simp [Matrix.vecMulVec]

theorem incM_map_cA (σ : E →ₐ[F] E) {m n : Type} (M : Matrix m n E) :
    (incM F M).map (cA σ) = incM F (M.map σ) := by
  ext i j; simp [incM, cA, inclR]

theorem incM_mulVec_incV {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) (v : Fin n → E) :
    incM F M *ᵥ incV F v = incV F (M *ᵥ v) := by
  ext i; simp only [incM, incV]; exact (RingHom.map_mulVec _ M v i).symm

theorem exists_levi_of_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d : ℕ)
    (W : Spc F E d) (r s d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s →
    H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ h₁ : UA σ W₁.J, ∃ m : UA σ W.J, IsLevi H' 1 h₁ m := by
  intro F E _ _ _ _ _ σ B d W r s d₁ W₁ H' i₀ i₁ hσ hW hH h₁
  obtain ⟨π, hπι, hπx, hπy, hc, hd⟩ := frame_facts σ B W W₁ H' hσ hW hH
  let c : AE F E →+* AE F E := (cA σ).toRingHom
  have hPI : incM F π * incM F H'.ι = 1 := by
    simp only [incM]; rw [← Matrix.map_mul, hπι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hcM : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map c := by
    rw [show (incM F π).map c = (incM F π).map (cA σ) from rfl, incM_map_cA]
    simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, hc, Matrix.map_mul]
  have hdM : incM F W.J * (incM F H'.ι).map c = (incM F π)ᵀ * incM F W₁.J := by
    rw [show (incM F H'.ι).map c = (incM F H'.ι).map (cA σ) from rfl, incM_map_cA]
    simp only [incM]; rw [← Matrix.transpose_map, ← Matrix.map_mul, hd, Matrix.map_mul]
  have hU : (mat h₁)ᵀ * incM F W₁.J * (mat h₁).map c = incM F W₁.J := h₁.2
  have hHK : mat h₁ * mat h₁⁻¹ = 1 := by
    show ((h₁ : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) *
      (((h₁⁻¹ : UA σ W₁.J) : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hKH : mat h₁⁻¹ * mat h₁ = 1 := by
    show (((h₁⁻¹ : UA σ W₁.J) : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) *
      ((h₁ : GL (Fin d₁) (AE F E)) : Matrix (Fin d₁) (Fin d₁) (AE F E)) = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  let g : GL (Fin d) (AE F E) :=
    ⟨1 + incM F H'.ι * ((mat h₁ - 1) * incM F π), 1 + incM F H'.ι * ((mat h₁⁻¹ - 1) * incM F π),
      levi_inv_alg _ _ _ _ hPI hHK, levi_inv_alg _ _ _ _ hPI hKH⟩
  have hg : g ∈ UG (cA σ) (incM F W.J) :=
    levi_unit_alg c (incM F W.J) (incM F W₁.J) (incM F H'.ι) (incM F π) (mat h₁) hPI hcM hdM hU
  refine ⟨⟨g, hg⟩, ?_, ?_, ?_⟩
  · show (1 + incM F H'.ι * ((mat h₁ - 1) * incM F π)) *ᵥ incV F H'.x = ((1 : (AE F E)ˣ) : AE F E) • incV F H'.x
    rw [Units.val_one, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, incM_mulVec_incV, hπx, show incV F (0 : Fin d₁ → E) = 0 from funext fun _ => map_zero _,
      Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  · show (1 + incM F H'.ι * ((mat h₁ - 1) * incM F π)) *ᵥ incV F H'.y =
      cA σ (((1 : (AE F E)ˣ)⁻¹ : (AE F E)ˣ) : AE F E) • incV F H'.y
    rw [inv_one, Units.val_one, map_one, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, incM_mulVec_incV, hπy, show incV F (0 : Fin d₁ → E) = 0 from funext fun _ => map_zero _,
      Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero]
  · show (1 + incM F H'.ι * ((mat h₁ - 1) * incM F π)) * incM F H'.ι = incM F H'.ι * mat h₁
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_assoc, hPI, Matrix.mul_one, Matrix.mul_sub,
      Matrix.mul_one, add_sub_cancel]

end GlobalTheory.LeviFrame
