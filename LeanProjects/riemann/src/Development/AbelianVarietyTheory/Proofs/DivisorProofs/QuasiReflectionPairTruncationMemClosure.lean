import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMemSUAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureDivMem
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.SUPair
open Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def wv (x : Fin M → E) : Fin M → E := Matrix.vecMul (fun i => σ (x i)) J

theorem hE_eq (x v : Fin M → E) : hE σ J x v = wv σ J x ⬝ᵥ v := by
  simp only [hE, Formalism.UG.hform, wv, Matrix.vecMul, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem qr_eq (x : Fin M → E) (u : E) :
    GlobalTheory.SUAssemble.qr σ J x u = 1 + ((u - 1) / hE σ J x x) • Matrix.vecMulVec x (wv σ J x) := rfl

theorem qr_mulVec (x : Fin M → E) (u : E) (v : Fin M → E) :
    GlobalTheory.SUAssemble.qr σ J x u *ᵥ v = v + ((u - 1) / hE σ J x x * hE σ J x v) • x := by
  rw [qr_eq, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp only [hE_eq, op_smul_eq_smul, smul_smul]

theorem hE_sub_left (a b v : Fin M → E) : hE σ J (a - b) v = hE σ J a v - hE σ J b v := by
  simp [hE, Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]
theorem hE_smul_left (t : E) (a v : Fin M → E) : hE σ J (t • a) v = σ t * hE σ J a v := by
  simp [hE, Formalism.UG.hform, Finset.mul_sum, mul_assoc]
theorem hE_sub_right (a b v : Fin M → E) : hE σ J v (a - b) = hE σ J v a - hE σ J v b := by
  simp [hE, Formalism.UG.hform, mul_sub, Finset.sum_sub_distrib]
theorem hE_smul_right (t : E) (a v : Fin M → E) : hE σ J v (t • a) = t * hE σ J v a := by
  simp [hE, Formalism.UG.hform, Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem Q_mul_Q (x : Fin M → E) :
    Matrix.vecMulVec x (wv σ J x) * Matrix.vecMulVec x (wv σ J x) = hE σ J x x • Matrix.vecMulVec x (wv σ J x) := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, hE_eq, dotProduct, Finset.sum_mul]
  refine Finset.sum_congr rfl fun _ _ => by ring

theorem cT_Q_mul (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) :
    Formalism.UG.cT (σ : E →+* E) (Matrix.vecMulVec x (wv σ J x)) * J = J * Matrix.vecMulVec x (wv σ J x) := by
  ext i j
  simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.vecMulVec_apply, wv,
    Matrix.vecMul, dotProduct, map_mul, map_sum, AlgHom.coe_toRingHom, hσ, hJ]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end GlobalTheory.SUPair

namespace GlobalTheory.SUPair
open Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem hE_self (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem qr_one (x : Fin M → E) : GlobalTheory.SUAssemble.qr σ J x 1 = 1 := by
  rw [qr_eq, sub_self, zero_div, zero_smul, add_zero]

theorem qr_mul_qr (x : Fin M → E) (hx : hE σ J x x ≠ 0) (a b : E) :
    GlobalTheory.SUAssemble.qr σ J x a * GlobalTheory.SUAssemble.qr σ J x b = GlobalTheory.SUAssemble.qr σ J x (a * b) := by
  rw [qr_eq, qr_eq, qr_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Q_mul_Q, smul_add]
  have : (a * b - 1) / hE σ J x x = (a - 1) / hE σ J x x + (b - 1) / hE σ J x x +
      (a - 1) / hE σ J x x * ((b - 1) / hE σ J x x * hE σ J x x) := by
    field_simp; ring
  rw [this]
  module

theorem cT_qr (x : Fin M → E) (u : E) :
    Formalism.UG.cT (σ : E →+* E) (GlobalTheory.SUAssemble.qr σ J x u) =
      1 + σ ((u - 1) / hE σ J x x) • Formalism.UG.cT (σ : E →+* E) (Matrix.vecMulVec x (wv σ J x)) := by
  rw [qr_eq]
  ext i j
  simp [Formalism.UG.cT, Matrix.one_apply, eq_comm]

theorem qr_unitary (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E)
    (hx : hE σ J x x ≠ 0) (u : E) (hu : u * σ u = 1) :
    Formalism.UG.cT (σ : E →+* E) (GlobalTheory.SUAssemble.qr σ J x u) * J * GlobalTheory.SUAssemble.qr σ J x u = J := by
  rw [cT_qr]
  rw [qr_eq]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, cT_Q_mul σ J hσ hJ, Matrix.mul_assoc, Q_mul_Q, smul_add]
  have hs : σ ((u - 1) / hE σ J x x) = (σ u - 1) / hE σ J x x := by
    rw [map_div₀, map_sub, map_one, hE_self σ J hσ hJ]
  rw [hs]
  have : (u - 1) / hE σ J x x * ((σ u - 1) / hE σ J x x * hE σ J x x) =
      -((σ u - 1) / hE σ J x x) - (u - 1) / hE σ J x x := by
    field_simp; linear_combination hu
  rw [this]
  module

theorem det_qr (x : Fin M → E) (hx : hE σ J x x ≠ 0) (u : E) : (GlobalTheory.SUAssemble.qr σ J x u).det = u := by
  rw [qr_eq, ← Matrix.smul_vecMulVec, Matrix.vecMulVec_eq (ι := Unit),
    Matrix.det_one_add_replicateCol_mul_replicateRow, dotProduct_smul, ← hE_eq, smul_eq_mul, div_mul_cancel₀ _ hx]
  ring

end GlobalTheory.SUPair

namespace GlobalTheory.SUPair
open Matrix

section Grp
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

def qrU (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin M → E) (hx : hE σ J x x ≠ 0)
    (u : E) (hu : u * σ u = 1) : Formalism.UG.UJ (σ : E →+* E) J :=
  ⟨⟨GlobalTheory.SUAssemble.qr σ J x u, GlobalTheory.SUAssemble.qr σ J x (σ u),
    by rw [qr_mul_qr σ J x hx, hu, qr_one], by rw [qr_mul_qr σ J x hx, mul_comm, hu, qr_one]⟩,
    qr_unitary σ J hσ hJ x hx u hu⟩

end Grp

section Fix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

theorem trunc_fix (η : AF F) (hη : η * η = η) (g : Formalism.UG.UJ (σ : E →+* E) J) (v : Fin M → E)
    (hv : (g.1 : Matrix (Fin M) (Fin M) E) *ᵥ v = v) :
    ((HA.mat (AF F) σ J (GlobalTheory.SUAssemble.trunc σ J η hη g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) *ᵥ
      (fun i => inclR (AF F) (v i)) = fun i => inclR (AF F) (v i) := by
  rw [GlobalTheory.SUAssemble.mv_trunc]
  have h : GlobalTheory.SUAssemble.rmat (F := F) g.1 *ᵥ (fun i => inclR (AF F) (v i)) = fun i => inclR (AF F) (v i) := by
    funext i
    conv_rhs => rw [← hv]
    simp [GlobalTheory.SUAssemble.rmat, Matrix.mulVec, dotProduct, map_sum]
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, h, Matrix.one_mulVec, sub_self,
    smul_zero, add_zero]

end Fix

theorem trunc_pair_mem : (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ e₁ e₂ : Fin M → E, hE σ J e₁ e₂ = 0 → hE σ J e₁ e₁ ≠ 0 → hE σ J e₂ e₂ ≠ 0 → (∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J e₁ e₁ / hE σ J e₂ e₂)) = 0) → ∀ g ∈ SUAdelic σ J, (∀ v : Fin M → E, hE σ J e₁ v = 0 → hE σ J e₂ v = 0 → Matrix.mulVec ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) (fun i => inclR (AF F) (v i)) = (fun i => inclR (AF F) (v i))) → g ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h}) → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (ε : AF F), IsPlacesIdem S₁ S₂ ε → (S₁.Nonempty ∨ S₂.Nonempty) → ∀ (η : AF F) (hη : η * η = η) (x y z : Fin M → E) (u : E), u * σ u = 1 → hE σ J x x ≠ 0 → hE σ J y y ≠ 0 → hE σ J z z ≠ 0 → (hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J x x / hE σ J (z - (hE σ J x z / hE σ J x x) • x) (z - (hE σ J x z / hE σ J x x) • x))) = 0) → (hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z) ≠ 0 ∧ ∃ t : AF F ⊗[F] E, algebraMap (AF F) (AF F ⊗[F] E) ε * (t * sigR (AF F) σ t + inclR (AF F) (hE σ J z z / hE σ J (y - (hE σ J z y / hE σ J z z) • z) (y - (hE σ J z y / hE σ J z z) • z))) = 0) → ∃ p : Formalism.UG.UJ (σ : E →+* E) J, (p.1 : Matrix (Fin M) (Fin M) E) = GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J y (σ u) ∧ GlobalTheory.SUAssemble.trunc σ J η hη p ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} := by
  intro H F E _ _ _ _ _ σ hcm M J hJ S₁ S₂ ε hε hne η hη x y z u hu hx hy hz ⟨hz'n, t₁, ht₁⟩ ⟨hy'n, t₂, ht₂⟩
  have hσ : ∀ a, σ (σ a) = a := fun a => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hJ' : ∀ i j, σ (J j i) = J i j := hJ.1
  have hu' : σ u * σ (σ u) = 1 := by rw [hσ, mul_comm, hu]
  set S := {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, ∃ h ∈ SUSupp σ J ε, x = γ * h} with hS
  have h1 : (1 : HA (AF F) σ J) ∈ closure S := subset_closure ⟨1, (SURat σ J).one_mem, 1,
    (GlobalTheory.SUSuppSub.mem_SUSupp_iff σ J).2 ⟨(SUAdelic σ J).one_mem, by rw [GlobalTheory.SUSuppSub.mv_one, sub_self, smul_zero]⟩,
    by simp⟩
  have hmul : ∀ a ∈ closure S, ∀ b ∈ closure S, a * b ∈ closure S := by
    intro a ha b hb
    have hbi : b⁻¹ ∈ closure S := by
      simpa using GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε 1 h1 b hb
    simpa using GlobalTheory.SUSuppSub.closure_div_mem F E σ hcm M J hJ S₁ S₂ ε hε a ha b⁻¹ hbi
  let A := qrU σ J hσ hJ' x hx u hu
  let B := qrU σ J hσ hJ' y hy (σ u) hu'
  let C := qrU σ J hσ hJ' z hz (σ u) hu'
  let D := qrU σ J hσ hJ' z hz u hu
  refine ⟨A * B, rfl, ?_⟩
  have hCD : C * D = 1 := Subtype.ext (Units.ext (by
    show GlobalTheory.SUAssemble.qr σ J z (σ u) * GlobalTheory.SUAssemble.qr σ J z u = 1
    rw [qr_mul_qr σ J z hz, mul_comm, hu, qr_one]))
  have hAB : A * B = (A * C) * (D * B) := by
    rw [mul_assoc, ← mul_assoc C, hCD, one_mul]
  rw [hAB, map_mul]

  have hzv : ∀ v : Fin M → E, hE σ J x v = 0 →
      hE σ J (z - (hE σ J x z / hE σ J x x) • x) v = 0 → hE σ J z v = 0 := by
    intro v h1 h2
    rwa [hE_sub_left, hE_smul_left, h1, mul_zero, sub_zero] at h2
  have hyv : ∀ v : Fin M → E, hE σ J z v = 0 →
      hE σ J (y - (hE σ J z y / hE σ J z z) • z) v = 0 → hE σ J y v = 0 := by
    intro v h1 h2
    rwa [hE_sub_left, hE_smul_left, h1, mul_zero, sub_zero] at h2
  apply hmul
  · refine H F E σ hcm M J hJ S₁ S₂ ε hε hne x (z - (hE σ J x z / hE σ J x x) • x) ?_ hx hz'n ⟨t₁, ht₁⟩ _ ?_ ?_
    · rw [hE_sub_right, hE_smul_right, div_mul_cancel₀ _ hx, sub_self]
    · refine GlobalTheory.SUAssemble.trunc_mem_SUAdelic σ J η hη _ ?_
      show (GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J z (σ u)).det = 1
      rw [Matrix.det_mul, det_qr σ J x hx, det_qr σ J z hz, hu]
    · intro v h1 h2
      refine trunc_fix σ J η hη _ v ?_
      show (GlobalTheory.SUAssemble.qr σ J x u * GlobalTheory.SUAssemble.qr σ J z (σ u)) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec, qr_mulVec σ J z, hzv v h1 h2, mul_zero, zero_smul, add_zero, qr_mulVec σ J x, h1, mul_zero,
        zero_smul, add_zero]
  · refine H F E σ hcm M J hJ S₁ S₂ ε hε hne z (y - (hE σ J z y / hE σ J z z) • z) ?_ hz hy'n ⟨t₂, ht₂⟩ _ ?_ ?_
    · rw [hE_sub_right, hE_smul_right, div_mul_cancel₀ _ hz, sub_self]
    · refine GlobalTheory.SUAssemble.trunc_mem_SUAdelic σ J η hη _ ?_
      show (GlobalTheory.SUAssemble.qr σ J z u * GlobalTheory.SUAssemble.qr σ J y (σ u)).det = 1
      rw [Matrix.det_mul, det_qr σ J z hz, det_qr σ J y hy, hu]
    · intro v h1 h2
      refine trunc_fix σ J η hη _ v ?_
      show (GlobalTheory.SUAssemble.qr σ J z u * GlobalTheory.SUAssemble.qr σ J y (σ u)) *ᵥ v = v
      rw [← Matrix.mulVec_mulVec, qr_mulVec σ J y, hyv v h1 h2, mul_zero, zero_smul, add_zero, qr_mulVec σ J z, h1, mul_zero,
        zero_smul, add_zero]

end GlobalTheory.SUPair
