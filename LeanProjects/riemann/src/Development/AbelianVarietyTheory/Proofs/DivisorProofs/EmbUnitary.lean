import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmExtensionConjugationInvolutiveFixedField

noncomputable section

open Matrix
open scoped Quaternion

namespace GlobalTheory.PlaneSU

open Formalism.UG

section Emb

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def emb (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) (X : Matrix (Fin 2) (Fin 2) R) : Matrix n n R :=
  1 + A * (X - 1) * B

theorem emb_one (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R) : emb A B 1 = 1 := by
  simp [emb]

theorem emb_mul {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X Y : Matrix (Fin 2) (Fin 2) R) : emb A B (X * Y) = emb A B X * emb A B Y := by
  have e1 : X * Y - 1 = (X - 1) + (Y - 1) + (X - 1) * (Y - 1) := by noncomm_ring
  have e2 : A * (X - 1) * B * (A * (Y - 1) * B) = A * ((X - 1) * (Y - 1)) * B := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc B A, hBA, Matrix.one_mul]
  unfold emb
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, e2, e1,
    Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  abel

theorem det_emb {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} (hBA : B * A = 1)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).det = X.det := by
  unfold emb
  rw [Matrix.mul_assoc, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hBA, Matrix.mul_one, add_sub_cancel]

theorem emb_map {S : Type} [CommRing S] (f : R →+* S) (A : Matrix n (Fin 2) R) (B : Matrix (Fin 2) n R)
    (X : Matrix (Fin 2) (Fin 2) R) : (emb A B X).map f = emb (A.map f) (B.map f) (X.map f) := by
  simp [emb, Matrix.map_mul, Matrix.map_add, Matrix.map_sub, Matrix.map_one]

theorem cT_add (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P + Q) = cT c P + cT c Q := by
  ext i j; simp [cT]

theorem cT_sub (c : R →+* R) {m p : Type} (P Q : Matrix m p R) : cT c (P - Q) = cT c P - cT c Q := by
  ext i j; simp [cT]

theorem emb_unitary (c : R →+* R) {A : Matrix n (Fin 2) R} {B : Matrix (Fin 2) n R} {J : Matrix n n R}
    {H X : Matrix (Fin 2) (Fin 2) R} (hBA : B * A = 1) (h1 : cT c A * J = H * B) (h2 : J * A = cT c B * H)
    (hX : cT c X * H * X = H) : cT c (emb A B X) * J * emb A B X = J := by
  have hc : cT c (emb A B X) = 1 + cT c B * (cT c X - 1) * cT c A := by
    unfold emb
    rw [cT_add, cT_one, cT_mul, cT_mul, cT_sub, cT_one, Matrix.mul_assoc]
  set P := X - 1 with hP
  set P' := cT c X - 1 with hP'
  have key : H * P + P' * H + P' * H * P = 0 := by
    rw [hP, hP']
    calc H * (X - 1) + (cT c X - 1) * H + (cT c X - 1) * H * (X - 1) = cT c X * H * X - H := by noncomm_ring
      _ = 0 := by rw [hX, sub_self]
  have h1' : ∀ Z : Matrix n n R, cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h1'' : ∀ {k : Type} [Fintype k] (Z : Matrix n k R), cT c A * (J * Z) = H * (B * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h1, Matrix.mul_assoc]
  have h2' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), J * (A * Z) = cT c B * (H * Z) := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.mul_assoc]
  have hBA' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), B * (A * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hBA, Matrix.one_mul]
  rw [hc]
  unfold emb
  rw [← hP]
  have e : (1 + cT c B * P' * cT c A) * J * (1 + A * P * B) =
      J + cT c B * ((H * P + P' * H + P' * H * P) * B) := by
    have hAB' : ∀ {k : Type} (Z : Matrix (Fin 2) k R), cT c A * (cT c B * Z) = Z := fun Z => by
      rw [← Matrix.mul_assoc, ← cT_mul, hBA, cT_one, Matrix.one_mul]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc, h1, h1'', h2', hBA', hAB']
    abel
  rw [e, key, Matrix.zero_mul, Matrix.mul_zero, add_zero]

end Emb

section Quat

variable {S T : Type} [CommRing S] [CommRing T]

def qm (ι : S →+* T) (θ : T) {a b : S} (x : ℍ[S, a, b]) : Matrix (Fin 2) (Fin 2) T :=
  !![ι x.re + ι x.imI * θ, ι b * (ι x.imJ + ι x.imK * θ); ι x.imJ - ι x.imK * θ, ι x.re - ι x.imI * θ]

variable (ι : S →+* T) (θ : T) {a b : S}

theorem qm_one : qm ι θ (1 : ℍ[S, a, b]) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm]

theorem qm_sub (x y : ℍ[S, a, b]) : qm ι θ (x - y) = qm ι θ x - qm ι θ y := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_smul (r : S) (x : ℍ[S, a, b]) : qm ι θ (r • x) = ι r • qm ι θ x := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [qm] <;> ring

theorem qm_mul (hθ : θ * θ = ι a) (x y : ℍ[S, a, b]) : qm ι θ (x * y) = qm ι θ x * qm ι θ y := by
  ext i j
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  fin_cases i <;> fin_cases j <;> simp [qm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf <;> simp only [hθ2] <;> ring

theorem det_qm (hθ : θ * θ = ι a) (x : ℍ[S, a, b]) : (qm ι θ x).det = ι (GlobalTheory.QSA.nrm x) := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  simp [qm, Matrix.det_fin_two, GlobalTheory.QSA.nrm]
  ring_nf
  simp only [hθ2]
  ring

theorem qm_unitary (c : T →+* T) (hc : ∀ s, c (ι s) = ι s) (hcθ : c θ = -θ) (hθ : θ * θ = ι a)
    {h₁ h₂ : T} (hb : ι b * h₁ = -h₂) {x : ℍ[S, a, b]} (hx : GlobalTheory.QSA.nrm x = 1) :
    cT c (qm ι θ x) * Matrix.diagonal ![h₁, h₂] * qm ι θ x = Matrix.diagonal ![h₁, h₂] := by
  have hθ2 : θ ^ 2 = ι a := by rw [sq, hθ]
  have hn : ι x.re ^ 2 - ι a * ι x.imI ^ 2 - ι b * ι x.imJ ^ 2 + ι a * ι b * ι x.imK ^ 2 = 1 := by
    have := congrArg ι hx
    simp only [GlobalTheory.QSA.nrm, map_sub, map_add, map_mul, map_pow, map_one] at this
    exact this
  have hh2 : h₂ = -(ι b * h₁) := by rw [hb, neg_neg]
  subst hh2
  ext i j
  fin_cases i <;> fin_cases j
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination h₁ * hn
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf
  · simp [cT, qm, Matrix.mul_apply, Fin.sum_univ_two, hc, hcθ]
    ring_nf; simp only [hθ2]; linear_combination (-(ι b * h₁)) * hn

end Quat

section Plane

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [Field E] [Algebra F E] {M : ℕ}

def planeA (e₁ e₂ : Fin M → E) : Matrix (Fin M) (Fin 2) E := Matrix.of fun i k => ![e₁, e₂] k i

def planeH (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin 2) E :=
  Matrix.diagonal ![hE σ J e₁ e₁, hE σ J e₂ e₂]

def planeB (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (e₁ e₂ : Fin M → E) : Matrix (Fin 2) (Fin M) E :=
  Matrix.diagonal ![(hE σ J e₁ e₁)⁻¹, (hE σ J e₂ e₂)⁻¹] * cT (σ : E →+* E) (planeA e₁ e₂) * J

end Plane

end GlobalTheory.PlaneSU
