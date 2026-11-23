import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetGramOfHermitianSelfDualLatticeSpace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.StdPairLoc
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

noncomputable section

namespace GlobalTheory.IsoCoord

open Matrix

section Lin
variable {R : Type} [CommRing R]

theorem vecMulVec_mulVec {m n k l : Type} [Fintype n] [Fintype l] (A : Matrix m n R) (C : Matrix k l R)
    (p : n → R) (q : l → R) : vecMulVec (A *ᵥ p) (C *ᵥ q) = A * vecMulVec p q * Cᵀ := by
  ext i j
  simp only [vecMulVec_apply, mulVec, dotProduct, mul_apply, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem map_vecMulVec {S : Type} [CommRing S] {m n : Type} (f : R →+* S) (p : m → R) (q : n → R) :
    (vecMulVec p q).map f = vecMulVec (fun i => f (p i)) (fun j => f (q j)) := by
  ext i j; simp [vecMulVec_apply]

end Lin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_incl {v : Pl F} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (F := F) (AF F) x) = τ x := by
  change splitProj τ (compFin F E v ((1 : AF F) ⊗ₜ[F] x)) = τ x
  simp [compFin]

theorem exists_vec_comps {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (v : Pl F) (τ : E →ₐ[F] Fv F v) {m : Type}
    (p₀ p₁ : m → Fv F v) :
    ∃ z : m → AE F E, At (evFin F v) z ∧ (fun i => piW τ (z i)) = p₀ ∧ (fun i => piW (τ.comp σ) (z i)) = p₁ := by
  obtain ⟨u, hu, h0, h1⟩ := GlobalTheory.SplitComps.exists_mat_comps hcm v τ (Matrix.of fun i (_ : Unit) => p₀ i)
    (Matrix.of fun i (_ : Unit) => p₁ i)
  refine ⟨fun i => u i (), fun a ha => ?_, ?_, ?_⟩
  · have := hu a ha; funext i; exact congrFun (congrFun this i) ()
  · funext i; exact congrFun (congrFun h0 i) ()
  · funext i; exact congrFun (congrFun h1 i) ()

theorem at_vecMulVec_right {v : Pl F} {m n : Type} (p : m → AE F E) {z : n → AE F E} (hz : At (evFin F v) z) :
    At (evFin F v) (vecMulVec p z) := by
  intro a ha
  ext i j
  have := congrFun (hz a ha) j
  simp only [Matrix.smul_apply, vecMulVec_apply, Matrix.zero_apply, Pi.smul_apply, Pi.zero_apply] at this ⊢
  rw [← mul_smul_comm, this, mul_zero]

theorem at_vecMulVec_left {v : Pl F} {m n k : Type} [Fintype k] (M : Matrix m k (AE F E)) {y : k → AE F E}
    (hy : At (evFin F v) y) (q : n → AE F E) :
    At (evFin F v) (vecMulVec (M *ᵥ y) q) := by
  intro a ha
  ext i j
  have h := hy a ha
  simp only [Matrix.smul_apply, vecMulVec_apply, Matrix.zero_apply]
  rw [← smul_mul_assoc]
  have : a • (M *ᵥ y) i = (M *ᵥ (a • y)) i := by rw [mulVec_smul]; rfl
  rw [this, h, mulVec_zero, Pi.zero_apply, zero_mul]

end GlobalTheory.IsoCoord

namespace GlobalTheory.IsoCoord
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.IsoCoord

namespace GlobalTheory.IsoCoord
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_sig {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem form_swap {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (ε : E)
    (hJ : ∀ i j, σ (J j i) = ε * J i j) (x y : Fin n → E) : σ (form σ J x y) = ε * form σ J y x := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, sig_sig hcm, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem dot_form {v : Pl F} (t : E →ₐ[F] Fv F v) (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (y z : Fin n → E) :
    (fun r => t (y r)) ⬝ᵥ (J.map t *ᵥ fun r => t (σ (z r))) = t (form σ J y z) := by
  simp [form, dotProduct, mulVec, map_sum, map_mul]

end GlobalTheory.IsoCoord

namespace GlobalTheory.IsoCoord
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem piW_incV {v : Pl F} (τ : E →ₐ[F] Fv F v) {n : ℕ} (x : Fin n → E) :
    (fun i => piW τ (incV F x i)) = fun i => τ (x i) := funext fun i => piW_incl τ (x i)

theorem piW_mulVec {v : Pl F} (τ : E →ₐ[F] Fv F v) {n m : ℕ} (M : Matrix (Fin n) (Fin m) E) (y : Fin m → AE F E) :
    (fun i => piW τ ((incM F M *ᵥ y) i)) = M.map τ *ᵥ fun k => piW τ (y k) := by
  funext i
  simp [mulVec, dotProduct, map_sum, map_mul, incM, piW_incl]

def ein {K : Type} [Zero K] {b : ℕ} (s : Fin b → K) : Fin (b + 2) → K := Fin.cons 0 (Fin.snoc (α := fun _ => K) s 0)

end GlobalTheory.IsoCoord

namespace GlobalTheory.IsoCoord
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem det_map_ne_zero {v : Pl F} (t : E →ₐ[F] Fv F v) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (h : J.det ≠ 0) :
    (J.map t).det ≠ 0 := by
  rw [show (J.map t).det = (t : E →+* Fv F v) J.det from (RingHom.map_det _ _).symm]
  exact fun h0 => h ((t : E →+* Fv F v).injective (by rw [map_zero]; exact h0))

theorem det_ne_zero_skew {σ : E →ₐ[F] E} {B : Base F E} {n : ℕ} {X : Spc F E n} {r s : ℕ} (h : X.IsSkew σ B r s) :
    X.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have h1 := GlobalTheory.det_ne_zero_of_hasSig (h.sig w)
  rw [Matrix.det_smul] at h1
  intro h0
  apply h1
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem orth_col {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {H : Plane E n n₁} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {i₀ i₁ : ℕ} (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) (k : Fin n₁) :
    form σ Y.J (fun r => H.ι r k) H.x = 0 ∧ form σ Y.J (fun r => H.ι r k) H.y = 0 := by
  have e : H.ι *ᵥ Pi.single k 1 = fun r => H.ι r k := by rw [mulVec_single_one]; rfl
  have := hH.orth (Pi.single k 1)
  rwa [e] at this

theorem gram_form {σ : E →ₐ[F] E} {n m : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin m) E) (k' k : Fin m) :
    form σ J (fun r => ι r k') (fun r => ι r k) = (ιᵀ * J * ι.map σ) k' k := by
  simp only [form, dotProduct, mulVec, mul_apply, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum]
  first
  | exact Finset.sum_comm.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  | exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.IsoCoord

namespace GlobalTheory.IsoCoord
open Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.IsoCoord
