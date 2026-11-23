import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.KLeviReal

open Matrix GlobalTheory.LeviUnitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_incl_real {w : InfinitePlace F} (τ : EmbOver E w) (x : E) : piInf τ (inclR (F := F) (AF F) x) = τ.1 x := by
  simp [piInf, inclR, compInf, infEmb_tmul]

theorem one_eq_decomp (hcm : IsCMExt F E σ) {B : Base F E} {d d₁ r s : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    (hW : W.IsSkew σ B r s) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    {π : Matrix (Fin d₁) (Fin d) E} (p1 : π * H'.ι = 1) (p4 : π *ᵥ H'.x = 0) (p5 : π *ᵥ H'.y = 0) :
    (1 : Matrix (Fin d) (Fin d) E) = vecMulVec H'.x (W.J *ᵥ fun i => σ (H'.y i)) + H'.ι * π
      - vecMulVec H'.y (W.J *ᵥ fun i => σ (H'.x i)) := by
  have hσ := GlobalTheory.LeviTorus.sigma_invol hcm
  obtain ⟨hdec, -⟩ := GlobalTheory.LeviAdapted.decomp hW hA
  have hv : ∀ v : Fin d → E, (vecMulVec H'.x (W.J *ᵥ fun i => σ (H'.y i)) + H'.ι * π
      - vecMulVec H'.y (W.J *ᵥ fun i => σ (H'.x i))) *ᵥ v = v := by
    intro v
    obtain ⟨a, b, u, rfl⟩ := hdec v
    have e1 : ∀ z v : Fin d → E, (W.J *ᵥ fun i => σ (z i)) ⬝ᵥ v = form σ W.J v z := fun z v => by
      simp only [form]; exact dotProduct_comm _ _
    have fy : form σ W.J (a • H'.x + H'.ι *ᵥ u + b • H'.y) H'.y = a := by
      rw [GlobalTheory.LeviAdapted.form_add_left, GlobalTheory.LeviAdapted.form_add_left, GlobalTheory.LeviAdapted.form_smul_left,
        GlobalTheory.LeviAdapted.form_smul_left, hA.xy, hA.yy, (hA.orth u).2]; ring
    have fx : form σ W.J (a • H'.x + H'.ι *ᵥ u + b • H'.y) H'.x = -b := by
      rw [GlobalTheory.LeviAdapted.form_add_left, GlobalTheory.LeviAdapted.form_add_left, GlobalTheory.LeviAdapted.form_smul_left,
        GlobalTheory.LeviAdapted.form_smul_left, hA.xx, (hA.orth u).1, GlobalTheory.LeviAdapted.form_swap hσ hW.skew H'.y H'.x, hA.xy,
        map_one]; ring
    have pv : π *ᵥ (a • H'.x + H'.ι *ᵥ u + b • H'.y) = u := by
      rw [mulVec_add, mulVec_add, mulVec_smul, mulVec_smul, p4, p5, mulVec_mulVec, p1, one_mulVec]; simp
    rw [sub_mulVec, add_mulVec, vecMulVec_mulVec, vecMulVec_mulVec, ← mulVec_mulVec, pv, e1, e1, fy, fx]
    simp only [op_smul_eq_smul, neg_smul, sub_neg_eq_add]
  exact (Matrix.ext_of_mulVec_single fun j => by rw [hv, one_mulVec]).symm

theorem proj_cartan (hcm : IsCMExt F E σ) {B : Base F E} {d d₁ r s : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁}
    (hW : W.IsSkew σ B r s) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    {π : Matrix (Fin d₁) (Fin d) E} (p1 : π * H'.ι = 1) (p4 : π *ᵥ H'.x = 0) (p5 : π *ᵥ H'.y = 0) (w : InfinitePlace F) :
    π.map (B.emb w).1 * W.θ w = W₁.θ w * π.map (B.emb w).1 := by
  set f : E →+* ℂ := (B.emb w).1 with hf
  set θ := W.θ w
  set θ₁ := W₁.θ w
  have hId := congrArg f.mapMatrix (one_eq_decomp hcm hW hA p1 p4 p5)
  have mv : ∀ a b : Fin d → E, f.mapMatrix (vecMulVec a b) = vecMulVec (fun i => f (a i)) (fun i => f (b i)) :=
    fun a b => by ext i j; simp [vecMulVec_apply]
  rw [map_one, map_sub, map_add, mv, mv, RingHom.mapMatrix_apply, Matrix.map_mul] at hId
  have mvec : ∀ {k : ℕ} (M : Matrix (Fin k) (Fin d) E) (v : Fin d → E), M.map f *ᵥ (fun i => f (v i)) = fun i => f ((M *ᵥ v) i) :=
    fun M v => by funext i; rw [RingHom.map_mulVec]; rfl
  have hπx : π.map f *ᵥ (fun i => f (H'.x i)) = 0 := by rw [mvec, p4]; funext i; simp
  have hπy : π.map f *ᵥ (fun i => f (H'.y i)) = 0 := by rw [mvec, p5]; funext i; simp
  have hπι : π.map f * H'.ι.map f = 1 := by rw [← Matrix.map_mul, p1]; exact Matrix.map_one _ (map_zero f) (map_one f)
  obtain ⟨hθι, c, hc, hy⟩ := hA.cartan w
  rw [← hf] at hθι hy
  have hθθ : θ * θ = 1 := (hW.cartan w).1
  have hθx : θ *ᵥ (fun i => f (H'.x i)) = c⁻¹ • (fun i => f (H'.y i)) := by
    rw [hy, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hθy : θ *ᵥ (fun i => f (H'.y i)) = c • (fun i => f (H'.x i)) := by
    rw [hy, mulVec_smul, mulVec_mulVec, hθθ, one_mulVec]
  calc π.map f * θ = π.map f * θ * 1 := (Matrix.mul_one _).symm
    _ = θ₁ * π.map f := by
      rw [hId, Matrix.mul_sub, Matrix.mul_add, mul_vecMulVec, mul_vecMulVec, ← mulVec_mulVec, ← mulVec_mulVec, hθx, hθy,
        mulVec_smul, mulVec_smul, hπx, hπy, smul_zero, smul_zero, zero_vecMulVec, zero_vecMulVec, zero_add, sub_zero, Matrix.mul_assoc, ← Matrix.mul_assoc θ, hθι, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hπι, Matrix.one_mul]

theorem exists_kInf_isLevi_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s : ℕ), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ k₁ ∈ KInf σ W₁ B.emb, ∃ k ∈ KInf σ W B.emb, IsLevi H' 1 k₁ k := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s hcm hW hA h₁ hk₁
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := GlobalTheory.LeviAdapted.exists_proj hcm hW hA
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J := by
    rw [incM_conj, ← incM_mul, p2, incM_mul]; rfl
  have q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom := by
    rw [incM_conj, ← incM_mul, ← p3, incM_mul]; rfl
  have hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z := by
    intro z hz
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; exact map_zero _
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩,
    ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [ext_mul q1, mat, Units.mul_inv]; simp
  · rw [ext_mul q1, mat, Units.inv_mul]; simp
  · exact ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2
  · intro u hu
    show u • (1 + incM F H'.ι * (mat h₁ - 1) * incM F π - 1) = 0
    rw [add_sub_cancel_left, ← Matrix.smul_mul, ← Matrix.mul_smul, hk₁.1 u hu, Matrix.mul_zero, Matrix.zero_mul]
  · intro w
    set f : E →+* ℂ := (B.emb w).1 with hf
    have hinc : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (incM F A).map (piInf (B.emb w)) = A.map f := fun A => by
      ext i j; simp [incM, piInf_incl_real, hf]
    have hK : Commute ((mat h₁).map (piInf (B.emb w))) (W₁.θ w) := hk₁.2 w
    set K := (mat h₁).map (piInf (B.emb w))
    have hm : (1 + incM F H'.ι * (mat h₁ - 1) * incM F π).map (piInf (B.emb w)) = 1 + H'.ι.map f * (K - 1) * π.map f := by
      have e : ∀ A : Matrix (Fin d) (Fin d) (AE F E), A.map (piInf (B.emb w)) = (piInf (B.emb w)).mapMatrix A :=
        fun A => rfl
      have e1 : ∀ A : Matrix (Fin d₁) (Fin d₁) (AE F E), A.map (piInf (B.emb w)) = (piInf (B.emb w)).mapMatrix A :=
        fun A => rfl
      rw [e, map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul, e1 (mat h₁ - 1), map_sub, map_one,
        RingHom.mapMatrix_apply, hinc, hinc]
    show Commute ((1 + incM F H'.ι * (mat h₁ - 1) * incM F π).map (piInf (B.emb w))) (W.θ w)
    rw [hm]
    have hπ := proj_cartan hcm hW hA p1 p4 p5 w
    have hθι := (hA.cartan w).1
    have hK1 : (K - 1) * W₁.θ w = W₁.θ w * (K - 1) := by rw [Matrix.sub_mul, Matrix.mul_sub, hK.eq, Matrix.one_mul, Matrix.mul_one]
    show (1 + H'.ι.map f * (K - 1) * π.map f) * W.θ w = W.θ w * (1 + H'.ι.map f * (K - 1) * π.map f)
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
    congr 1
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hπ, ← Matrix.mul_assoc (K - 1), hK1, Matrix.mul_assoc, ← Matrix.mul_assoc (H'.ι.map f),
      ← hf, ← hθι, Matrix.mul_assoc, Matrix.mul_assoc]
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

end GlobalTheory.KLeviReal

end
