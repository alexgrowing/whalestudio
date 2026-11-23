import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd

noncomputable section

namespace GlobalTheory.ThK.ConeEuler

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE absEv unitFin ideleAt)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem idem_mul_one_sub {R : Type} [CommRing R] {ε : R} (hε : ε * ε = ε) : ε * (1 - ε) = 0 := by
  rw [mul_sub, mul_one, hε, sub_self]

theorem one_sub_idem {R : Type} [CommRing R] {ε : R} (hε : ε * ε = ε) : (1 - ε) * (1 - ε) = 1 - ε := by
  linear_combination hε

theorem idem_smul_mul {A : Type} [CommRing A] [Algebra (AF F) A] {ε : AF F} (hε : ε * ε = ε) (a b : A) :
    (ε • a + (1 - ε) • (1 : A)) * (ε • b + (1 - ε) • (1 : A)) = ε • (a * b) + (1 - ε) • (1 : A) := by
  simp only [Algebra.smul_def, mul_one]
  have he : algebraMap (AF F) A ε * algebraMap (AF F) A ε = algebraMap (AF F) A ε := by rw [← map_mul, hε]
  rw [map_sub, map_one]
  linear_combination (a * b - a - b + 1) * he

theorem idem_smul_mat_mul {A : Type} [CommRing A] [Algebra (AF F) A] {n : ℕ} {ε : AF F} (hε : ε * ε = ε)
    (G H : Matrix (Fin n) (Fin n) A) :
    (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) A)) * (ε • H + (1 - ε) • 1) = ε • (G * H) + (1 - ε) • 1 := by
  have h1 := idem_mul_one_sub hε
  have h2 := one_sub_idem hε
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add,
    smul_smul, hε, h1, h2, mul_comm (1 - ε) ε, zero_smul, add_zero, zero_add]

theorem idem_smul_unitary {A : Type} [CommRing A] [Algebra (AF F) A] (c : A →ₐ[AF F] A) {n : ℕ} {ε : AF F}
    (hε : ε * ε = ε) {G J : Matrix (Fin n) (Fin n) A} (hG : Gᵀ * J * G.map c = J) :
    (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) A))ᵀ * J * (ε • G + (1 - ε) • 1).map c = J := by
  have h1 := idem_mul_one_sub hε
  have h2 := one_sub_idem hε
  have hm : (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) A)).map c = ε • G.map c + (1 - ε) • 1 := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, map_add, map_smul]
    split_ifs <;> simp
  rw [hm, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_add,
    smul_smul, hε, h1, h2, mul_comm (1 - ε) ε, zero_smul, add_zero, zero_add]
  rw [hG, ← add_smul, add_sub_cancel, one_smul]

variable (E) in

def idemUnit (ε : AF F) (hε : ε * ε = ε) : (AE F E)ˣ →* (AE F E)ˣ where
  toFun l := ⟨ε • l.1 + (1 - ε) • 1, ε • (l⁻¹ : (AE F E)ˣ).1 + (1 - ε) • 1,
    by rw [idem_smul_mul hε, Units.mul_inv, ← add_smul, add_sub_cancel, one_smul],
    by rw [idem_smul_mul hε, Units.inv_mul, ← add_smul, add_sub_cancel, one_smul]⟩
  map_one' := Units.ext (by simp only [Units.val_one, Units.val_mk]; rw [← add_smul, add_sub_cancel, one_smul])
  map_mul' a b := Units.ext (by simp only [Units.val_mul, Units.val_mk]; rw [idem_smul_mul hε])

theorem val_idemUnit (ε : AF F) (hε : ε * ε = ε) (l : (AE F E)ˣ) :
    (idemUnit E ε hε l : AE F E) = ε • (l : AE F E) + (1 - ε) • 1 := rfl

variable (σ) in

def idemU {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ε : AF F) (hε : ε * ε = ε) : UA σ J →* UA σ J where
  toFun g := ⟨⟨ε • mat g + (1 - ε) • 1, ε • mat g⁻¹ + (1 - ε) • 1,
      by rw [idem_smul_mat_mul hε, GlobalTheory.StabHaar.mat_mul_inv, ← add_smul, add_sub_cancel, one_smul],
      by rw [idem_smul_mat_mul hε, show mat g⁻¹ * mat g = 1 from by
        rw [← GlobalTheory.StabHaar.mat_mul, inv_mul_cancel, GlobalTheory.StabHaar.mat_one], ← add_smul, add_sub_cancel, one_smul]⟩, idem_smul_unitary (cA σ) hε g.2⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    change ε • mat (1 : UA σ J) + (1 - ε) • 1 = 1
    rw [GlobalTheory.StabHaar.mat_one, ← add_smul, add_sub_cancel, one_smul]
  map_mul' a b := by
    apply Subtype.ext; apply Units.ext
    change ε • mat (a * b) + (1 - ε) • 1 = (ε • mat a + (1 - ε) • 1) * (ε • mat b + (1 - ε) • 1)
    rw [idem_smul_mat_mul hε, GlobalTheory.StabHaar.mat_mul]

def eFin (v : Pl F) : AF F := GlobalTheory.LatVac.liftV v 1

def eInf (F : Type) [Field F] [NumberField F] : AF F := realAd F 1

theorem eFin_idem (v : Pl F) : eFin v * eFin v = eFin v := by
  have h := GlobalTheory.LatVac.at_liftV v 1 (eFin v - 1) (by
    rw [eFin, map_sub, GlobalTheory.LatVac.evFin_liftV, map_one, sub_self])
  rw [smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
  exact h

theorem eInf_idem : eInf F * eInf F = eInf F := by
  have h := at_partInf (M := AF F) (1 : AF F) (eInf F - 1) (by
    rw [eInf, GlobalTheory.ArchUniq.evI_eq_evIHom, map_sub, map_one, ← GlobalTheory.ArchUniq.evI_eq_evIHom, evI_realAd_one, sub_self])
  simp only [partInf, smul_eq_mul, mul_one] at h
  unfold eInf at h ⊢
  rw [sub_mul, one_mul, sub_eq_zero] at h
  exact h

variable (E) in

def unitAt (v : Pl F) : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eFin v) (eFin_idem v)

variable (F E) in

def unitArch : (AE F E)ˣ →* (AE F E)ˣ := idemUnit E (eInf F) eInf_idem

variable (σ) in

def compAt {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) : UA σ J →* UA σ J := idemU σ J (eFin v) (eFin_idem v)

variable (σ) in

def compArch {n : ℕ} (J : Matrix (Fin n) (Fin n) E) : UA σ J →* UA σ J := idemU σ J (eInf F) eInf_idem

theorem mat_compAt {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl F) (g : UA σ J) :
    mat (compAt σ J v g) = eFin v • mat g + (1 - eFin v) • 1 := rfl

theorem mat_compArch {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : UA σ J) :
    mat (compArch σ J g) = eInf F • mat g + (1 - eInf F) • 1 := rfl

theorem compAt_mem {n : ℕ} {X : Spc F E n} (v : Pl F) (g : UA σ X.J) : compAt σ X.J v g ∈ UAt σ X (evFin F v) := by
  intro u hu
  have h := GlobalTheory.LatVac.at_liftV v 1 u hu
  rw [mat_compAt, show eFin v • mat g + (1 - eFin v) • (1 : Matrix (Fin _) (Fin _) (AE F E)) - 1 =
    eFin v • (mat g - 1) by rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eFin v = 0 from h, zero_smul]

theorem compArch_mem {n : ℕ} {X : Spc F E n} (g : UA σ X.J) : compArch σ X.J g ∈ UAt σ X (evI F) := by
  intro u hu
  have h := at_partInf (M := AF F) (1 : AF F) u hu
  simp only [partInf, smul_eq_mul, mul_one] at h
  rw [mat_compArch, show eInf F • mat g + (1 - eInf F) • (1 : Matrix (Fin _) (Fin _) (AE F E)) - 1 =
    eInf F • (mat g - 1) by rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eInf F = 0 from h, zero_smul]

theorem unitAt_mem (v : Pl F) (l : (AE F E)ˣ) : unitAt E v l ∈ idelesAt E (evFin F v) := by
  intro u hu
  have h := GlobalTheory.LatVac.at_liftV v 1 u hu
  change u • (eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1) = 0
  rw [show eFin v • (l : AE F E) + (1 - eFin v) • 1 - 1 = eFin v • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eFin v = 0 from h, zero_smul]

theorem unitArch_mem (l : (AE F E)ˣ) : unitArch F E l ∈ idelesAt E (evI F) := by
  intro u hu
  have h := at_partInf (M := AF F) (1 : AF F) u hu
  simp only [partInf, smul_eq_mul, mul_one] at h
  change u • (eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1) = 0
  rw [show eInf F • (l : AE F E) + (1 - eInf F) • 1 - 1 = eInf F • ((l : AE F E) - 1) by
    rw [sub_smul, one_smul, smul_sub]; abel, smul_smul]
  rw [show u * eInf F = 0 from h, zero_smul]

end GlobalTheory.ThK.ConeEuler
