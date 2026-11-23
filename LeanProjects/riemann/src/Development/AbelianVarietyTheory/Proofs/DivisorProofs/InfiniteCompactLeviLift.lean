import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompIsotropicVector
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviKInf

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_map_piInf {w : InfinitePlace F} (τ : EmbOver E w) {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) :
    (incM F A).map (piInf τ) = A.map τ.1 := by
  ext i j
  exact GlobalTheory.IwaAdelicIso.piInf_inclR τ (A i j)

theorem frame_id (hσ : ∀ z, σ (σ z) = z) {B : Base F E} {d d₁ r s : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    (hW : W.IsSkew σ B r s) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (π : Matrix (Fin d₁) (Fin d) E) (p1 : π * H'.ι = 1) (p4 : π *ᵥ H'.x = 0) (p5 : π *ᵥ H'.y = 0) :
    Matrix.of (fun i j => H'.x i * (W.J *ᵥ fun k => σ (H'.y k)) j) + H'.ι * π -
      Matrix.of (fun i j => H'.y i * (W.J *ᵥ fun k => σ (H'.x k)) j) = 1 := by
  obtain ⟨hdec, -⟩ := GlobalTheory.LeviAdapted.decomp hW hA
  set Q := Matrix.of (fun i j => H'.x i * (W.J *ᵥ fun k => σ (H'.y k)) j) + H'.ι * π -
      Matrix.of (fun i j => H'.y i * (W.J *ᵥ fun k => σ (H'.x k)) j) with hQ
  have hQv : ∀ v, Q *ᵥ v = form σ W.J v H'.y • H'.x + H'.ι *ᵥ (π *ᵥ v) - form σ W.J v H'.x • H'.y := by
    intro v
    funext i
    simp only [hQ, form, sub_mulVec, add_mulVec, ← mulVec_mulVec, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    congr 2
    · simp [mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
    · simp [mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  have hyx : form σ W.J H'.y H'.x = -1 := by
    rw [GlobalTheory.LeviAdapted.form_swap hσ hW.skew, hA.xy, map_one]
  have hxx := hA.xx
  have hyy := hA.yy
  have hfix : ∀ v, Q *ᵥ v = v := by
    intro v
    obtain ⟨a, b, u, rfl⟩ := hdec v
    have hπv : π *ᵥ (a • H'.x + H'.ι *ᵥ u + b • H'.y) = u := by
      rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, p4, p5, mulVec_mulVec, p1, one_mulVec]; simp
    have f1 : form σ W.J (a • H'.x + H'.ι *ᵥ u + b • H'.y) H'.y = a := by
      rw [GlobalTheory.LeviAdapted.form_add_left, GlobalTheory.LeviAdapted.form_add_left, GlobalTheory.LeviAdapted.form_smul_left,
        GlobalTheory.LeviAdapted.form_smul_left, hA.xy, (hA.orth u).2, hyy]; ring
    have f2 : form σ W.J (a • H'.x + H'.ι *ᵥ u + b • H'.y) H'.x = -b := by
      rw [GlobalTheory.LeviAdapted.form_add_left, GlobalTheory.LeviAdapted.form_add_left, GlobalTheory.LeviAdapted.form_smul_left,
        GlobalTheory.LeviAdapted.form_smul_left, hxx, (hA.orth u).1, hyx]; ring
    rw [hQv, hπv, f1, f2, neg_smul, sub_neg_eq_add]
  ext i j
  have := congrFun (hfix (Pi.single j 1)) i
  rw [mulVec_single_one] at this
  simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this

end GlobalTheory.LeviKInf

namespace GlobalTheory.LeviKInf

open Matrix

theorem proj_comm {d d₁ : ℕ} (θ : Matrix (Fin d) (Fin d) ℂ) (θ₁ : Matrix (Fin d₁) (Fin d₁) ℂ)
    (ι : Matrix (Fin d) (Fin d₁) ℂ) (π : Matrix (Fin d₁) (Fin d) ℂ) (x y r r' : Fin d → ℂ) (c : ℂ)
    (hid : Matrix.of (fun i j => x i * r j) + ι * π - Matrix.of (fun i j => y i * r' j) = 1)
    (hθθ : θ * θ = 1) (hθι : θ * ι = ι * θ₁) (hc : c ≠ 0) (hy : y = c • θ *ᵥ x) (hπι : π * ι = 1)
    (hπx : π *ᵥ x = 0) (hπy : π *ᵥ y = 0) : π * θ = θ₁ * π := by
  have hθx : θ *ᵥ x = c⁻¹ • y := by rw [hy, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hθy : θ *ᵥ y = c • x := by rw [hy, mulVec_smul, mulVec_mulVec, hθθ, one_mulVec]
  have h1 : (π * θ) *ᵥ x = 0 := by rw [← mulVec_mulVec, hθx, mulVec_smul, hπy, smul_zero]
  have h2 : (π * θ) *ᵥ y = 0 := by rw [← mulVec_mulVec, hθy, mulVec_smul, hπx, smul_zero]
  have hA : ∀ (M : Matrix (Fin d₁) (Fin d) ℂ) (v w : Fin d → ℂ), M *ᵥ v = 0 →
      M * Matrix.of (fun i j => v i * w j) = 0 := by
    intro M v w hM
    ext k j
    have := congrFun hM k
    simp only [mulVec, dotProduct] at this
    simp [Matrix.mul_apply, ← mul_assoc, ← Finset.sum_mul, this]
  calc π * θ = π * θ * 1 := (Matrix.mul_one _).symm
    _ = π * θ * (Matrix.of (fun i j => x i * r j) + ι * π - Matrix.of (fun i j => y i * r' j)) := by rw [hid]
    _ = θ₁ * π := by
      rw [Matrix.mul_sub, Matrix.mul_add, hA _ _ _ h1, hA _ _ _ h2, zero_add, sub_zero, ← Matrix.mul_assoc,
        Matrix.mul_assoc π, hθι, ← Matrix.mul_assoc, hπι, Matrix.one_mul]

theorem ext_comm {d d₁ : ℕ} (θ : Matrix (Fin d) (Fin d) ℂ) (θ₁ : Matrix (Fin d₁) (Fin d₁) ℂ)
    (ι : Matrix (Fin d) (Fin d₁) ℂ) (π : Matrix (Fin d₁) (Fin d) ℂ) (k : Matrix (Fin d₁) (Fin d₁) ℂ)
    (hθι : θ * ι = ι * θ₁) (hπθ : π * θ = θ₁ * π) (hk : Commute k θ₁) :
    Commute (1 + ι * (k - 1) * π) θ := by
  have hk' : Commute (k - 1) θ₁ := hk.sub_left (Commute.one_left _)
  show (1 + ι * (k - 1) * π) * θ = θ * (1 + ι * (k - 1) * π)
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, hπθ, ← Matrix.mul_assoc,
    Matrix.mul_assoc ι, hk'.eq, ← Matrix.mul_assoc ι, ← hθι]
  simp only [Matrix.mul_assoc]

end GlobalTheory.LeviKInf

namespace GlobalTheory.LeviKInf

open Matrix GlobalTheory.LeviUnitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_mulVec_zero (τ : E →+* ℂ) {k l : ℕ} (π : Matrix (Fin k) (Fin l) E) (z : Fin l → E) (hz : π *ᵥ z = 0) :
    π.map τ *ᵥ (fun i => τ (z i)) = 0 := by
  funext i
  have := RingHom.map_mulVec τ π z i
  rw [hz] at this
  simpa [Function.comp_def] using this.symm

theorem exists_kInf_isLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
      ∀ k₁ ∈ KInf σ G₁.W B.emb, ∃ k ∈ KInf σ G.W B.emb, IsLevi H' 1 k₁ k := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC hB hG hG₁ k₁ hk₁
  have hσ : ∀ z, σ (σ z) = z := GlobalTheory.LeviTorus.sigma_invol hB.cm
  have hW := hG.hW
  have hW₁ := hG₁.hW
  have hA := hC.hH'
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := GlobalTheory.LeviUnitary.exists_proj hB hW hW₁ hA
  have hid := frame_id hσ hW hA π p1 p4 p5
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : incM F G.W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F G₁.W.J := by
    rw [incM_conj, ← incM_mul, p2, incM_mul]; rfl
  have q3 : (incM F H'.ι)ᵀ * incM F G.W.J = incM F G₁.W.J * (incM F π).map (cA σ).toRingHom := by
    rw [incM_conj, ← incM_mul, ← p3, incM_mul]; rfl
  have hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat k₁ - 1) * incM F π) *ᵥ incV F z = incV F z := by
    intro z hz
    have h0 : incV F (0 : Fin (a + b) → E) = 0 := by funext i; exact map_zero _
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat k₁ - 1) * incM F π, 1 + incM F H'.ι * ((k₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩,
    ⟨?_, fun w => ?_⟩, ?_, ?_, ?_⟩
  · rw [ext_mul q1, mat, Units.mul_inv]; simp
  · rw [ext_mul q1, mat, Units.inv_mul]; simp
  · exact ext_unitary (cA σ).toRingHom q1 q2 q3 k₁.2
  · show At (evI F) ((1 + incM F H'.ι * (mat k₁ - 1) * incM F π) - 1)
    rw [add_sub_cancel_left]
    intro u hu
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hk₁.1 u hu, Matrix.mul_zero, Matrix.zero_mul]
  · set τ : E →+* ℂ := (B.emb w).1 with hτ
    show Commute ((1 + incM F H'.ι * (mat k₁ - 1) * incM F π).map (piInf (B.emb w))) (G.W.θ w)
    have hm : (1 + incM F H'.ι * (mat k₁ - 1) * incM F π).map (piInf (B.emb w)) =
        1 + H'.ι.map τ * ((mat k₁).map (piInf (B.emb w)) - 1) * π.map τ := by
      rw [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub _),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), incM_map_piInf,
        incM_map_piInf]
    rw [hm]
    obtain ⟨hθι, c, hc, hy⟩ := hA.cartan w
    have hidw : Matrix.of (fun i j => τ (H'.x i) * τ ((G.W.J *ᵥ fun k => σ (H'.y k)) j)) + H'.ι.map τ * π.map τ -
        Matrix.of (fun i j => τ (H'.y i) * τ ((G.W.J *ᵥ fun k => σ (H'.x k)) j)) = 1 := by
      rw [← Matrix.map_one τ (map_zero τ) (map_one τ), ← hid]
      ext i j
      simp [Matrix.mul_apply, map_sum, map_mul]
    have hπι : π.map τ * H'.ι.map τ = 1 := by
      rw [← Matrix.map_mul, p1, Matrix.map_one _ (map_zero τ) (map_one τ)]
    have hπθ := proj_comm (G.W.θ w) (G₁.W.θ w) (H'.ι.map τ) (π.map τ) _ _ _ _ c hidw (hW.cartan w).1 hθι hc hy hπι
      (map_mulVec_zero τ π _ p4) (map_mulVec_zero τ π _ p5)
    exact ext_comm _ _ _ _ _ hθι hπθ (hk₁.2 w)
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat k₁ - 1) * incM F π) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

end GlobalTheory.LeviKInf

end
