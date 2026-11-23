import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfSeparable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SesqAsym
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AntidiagTwistedNorm
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMulSelf
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PhiMulTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SigBasisApply
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section

namespace GlobalTheory.GramTwistNorm

open GlobalTheory.UnitLemma

theorem phi_map (a : ℕ) {R : Type} [CommRing R] (c : R →+* R) :
    (GlobalTheory.Tw.Phi a R).map c = GlobalTheory.Tw.Phi a R := by
  ext i j
  simp only [Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem phi_mul_self (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) :=
  _root_.UpperTheory.Reformulated.B.Yzd3.phi_mul_self a

theorem phi_mul_transpose (a : ℕ) {R : Type} [CommRing R] :
    GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R)ᵀ = 1 :=
  _root_.UpperTheory.Reformulated.B.Yzd2.phi_mul_transpose a

theorem herm_sum_left {K : UQ} (B : InvAlg K) (β : B.A) {ι : Type} (s : Finset ι) (v : ι → K.E)
    (x : ι → B.A) (z : B.A) :
    B.herm β (∑ i ∈ s, v i • x i) z = ∑ i ∈ s, v i * B.herm β (x i) z := by
  simp only [InvAlg.herm, Finset.mul_sum, Finset.sum_mul, map_sum, mul_smul_comm, smul_mul_assoc,
    map_smul, smul_eq_mul]

theorem herm_sum_right {K : UQ} (B : InvAlg K) (β y : B.A) {ι : Type} (s : Finset ι) (r : ι → K.E)
    (x : ι → B.A) :
    B.herm β y (∑ i ∈ s, r i • x i) = ∑ i ∈ s, K.c (r i) * B.herm β y (x i) := by
  simp only [InvAlg.herm, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, RingEquiv.map_mul B.σ, B.σ_alg, ← Algebra.smul_def, mul_smul_comm, map_smul, smul_eq_mul]

theorem gram_det_ne_zero {K : UQ} (B : InvAlg K) (hsep : B.P.Separable) (β : B.Aˣ) {a : ℕ}
    (b : Module.Basis (Fin a) K.E B.A) :
    (Matrix.of fun i j => B.herm β (b i) (b j)).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  set y := ∑ i, v i • b i with hy
  have hy0 : y ≠ 0 := by
    intro hy'
    apply hv0
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent v hy' i
  have hyb : ∀ j, B.herm β y (b j) = 0 := by
    intro j
    have := congrFun hv j
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply] at this
    rw [hy, herm_sum_left]
    exact this
  have hyz : ∀ z, B.herm β y z = 0 := by
    intro z
    rw [← b.sum_repr z, herm_sum_right]
    simp [hyb]
  have hβy : (β : B.A) * y = 0 := by
    apply GlobalTheory.UnitLemma.PairClass.trace_nondeg K.E B.A B.g hsep
    intro w
    have := hyz (B.σ w)
    simp only [InvAlg.herm, B.σ_σ] at this
    exact this
  exact hy0 ((Units.mul_right_eq_zero β).1 hβy)

theorem gram_map_conj {K : UQ} (B : InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L)
    (hec : ∀ x, e (K.c x) = c (e x)) (a : ℕ) (β : B.A)
    (hβ : B.σ β = β * ((-1) ^ (a - 1) * B.g)) (b : Module.Basis (Fin a) K.E B.A) :
    ((Matrix.of fun i j => B.herm β (b i) (b j)).map e).map c =
      ((-1 : L) ^ (a - 1)) • (((Matrix.of fun i j => B.herm β (b i) (b j)).map e)ᵀ *
        (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e) :=
  _root_.GlobalTheory.ScalarSigmaBasis.main B L e c hec a β hβ b

theorem gram_twisted_norm_charpoly : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [Field L] (e : K.E ≃+* L) (c : L →+* L), (∀ x, e (K.c x) = c (e x)) → (∀ x, c (c x) = x) → ∀ (a : ℕ) (Q : L[X]), B.P = Q.map e.symm.toRingHom → Q.Separable → Q.natDegree = a → ∀ β : B.Aˣ, B.σ (β : B.A) = β * ((-1) ^ (a - 1) * B.g) → ∀ b : Module.Basis (Fin a) K.E B.A, IsUnit (Matrix.of fun i j => e (B.herm β (b i) (b j))).det ∧ ∀ δ : GL (Fin a) L, ((δ.val * GlobalTheory.Tw.Phi a L)⁻¹)ᵀ = (Matrix.of fun i j => e (B.herm β (b i) (b j))) → (δ * thetaGL a c δ).val.charpoly = Q := by
  intro K B L _ e c hec hcc a Q hPQ hQs hQd β hβ b
  set S : Matrix (Fin a) (Fin a) K.E := Matrix.of fun i j => B.herm β (b i) (b j) with hS
  have hG : (Matrix.of fun i j => e (B.herm β (b i) (b j))) = S.map e := rfl
  have hsep : B.P.Separable := by rw [hPQ]; exact hQs.map
  rw [hG]
  refine ⟨?_, ?_⟩
  · have hdet : (S.map e).det = e S.det := by
      rw [show S.map e = (e : K.E →+* L).mapMatrix S from rfl, ← RingHom.map_det]
      rfl
    rw [hdet, isUnit_iff_ne_zero]
    exact (map_ne_zero e).2 (gram_det_ne_zero B hsep β b)
  · intro δ hδ
    set G := S.map e with hGdef
    set P := (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e with hP
    set Φ := GlobalTheory.Tw.Phi a L with hΦ
    have hGc : G.map c = ((-1 : L) ^ (a - 1)) • (Gᵀ * P) := gram_map_conj B L e c hec a β hβ b
    have hinv : (δ⁻¹).val = Φ * Gᵀ := by
      have h1 : (δ.val * Φ)⁻¹ = Gᵀ := by rw [← hδ, Matrix.transpose_transpose]
      have hΦinv : Φ⁻¹ = Φᵀ := Matrix.inv_eq_right_inv (phi_mul_transpose a)
      rw [Matrix.mul_inv_rev, hΦinv, ← Matrix.coe_units_inv] at h1
      calc (δ⁻¹).val = Φ * Φᵀ * (δ⁻¹).val := by rw [hΦ, phi_mul_transpose, Matrix.one_mul]
        _ = Φ * Gᵀ := by rw [Matrix.mul_assoc, h1]
    have hθ : (thetaGL a c δ).val = Φ * ((δ⁻¹).val.map c)ᵀ * Φᵀ := rfl
    have hΦΦ : Φᵀ * Φᵀ = ((-1 : L) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) L) := by
      rw [← Matrix.transpose_mul, hΦ, phi_mul_self, Matrix.transpose_smul, Matrix.transpose_one]
    have hδΦ : δ.val * Φ * Gᵀ = 1 := by rw [Matrix.mul_assoc, ← hinv, Units.mul_inv]
    have key : (δ * thetaGL a c δ).val = P := by
      rw [Units.val_mul, hθ, hinv, Matrix.map_mul, hΦ, phi_map, ← hΦ, Matrix.transpose_mul,
        Matrix.transpose_map, Matrix.transpose_transpose, hGc]
      calc δ.val * (Φ * ((-1 : L) ^ (a - 1) • (Gᵀ * P) * Φᵀ) * Φᵀ)
          = ((-1 : L) ^ (a - 1)) • ((δ.val * Φ * Gᵀ) * P * (Φᵀ * Φᵀ)) := by
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = P := by
            rw [hδΦ, hΦΦ, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow,
              neg_one_mul, neg_neg, one_pow, one_smul]
    rw [key, hP, show (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map e =
      (LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g)).map (e : K.E →+* L) from rfl,
      Matrix.charpoly_map, LinearMap.charpoly_toMatrix]
    change B.P.map (e : K.E →+* L) = Q
    rw [hPQ, Polynomial.map_map]
    have : (e : K.E →+* L).comp e.symm.toRingHom = RingHom.id L := by
      ext x; simp
    rw [this, Polynomial.map_id]

end GlobalTheory.GramTwistNorm
