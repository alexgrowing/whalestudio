import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocFrame.HomW

section Idem

variable {R L : Type} [CommRing R] [Field L] {n : ℕ} (ι : L →+ R) (hm : ∀ x y, ι (x * y) = ι x * ι y)
include hm

theorem map_mul_map (X Y : Matrix (Fin n) (Fin n) L) : X.map ι * Y.map ι = (X * Y).map ι := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, hm]

theorem e_mul (t : L) : ι 1 * ι t = ι t := by rw [← hm, one_mul]

theorem f_mul (t : L) : (1 - ι 1) * ι t = 0 := by rw [sub_mul, one_mul, e_mul ι hm, sub_self]

theorem ff : (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
  have := e_mul ι hm 1
  linear_combination this

theorem ef : ι 1 * (1 - ι 1) = 0 := by
  have := e_mul ι hm 1
  linear_combination -this

theorem f_smul_map (X : Matrix (Fin n) (Fin n) L) : (1 - ι 1) • X.map ι = 0 := by
  ext i j
  simp [Matrix.smul_apply, f_mul ι hm]

theorem f_smul_mul_map (Y : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin n) L) :
    (1 - ι 1) • (Y * X.map ι) = 0 := by
  rw [← Matrix.mul_smul, f_smul_map ι hm, Matrix.mul_zero]

theorem f_smul_map_mul (Y : Matrix (Fin n) (Fin n) R) (X : Matrix (Fin n) (Fin n) L) :
    (1 - ι 1) • (X.map ι * Y) = 0 := by
  rw [← Matrix.smul_mul, f_smul_map ι hm, Matrix.zero_mul]

theorem map_one' : (1 : Matrix (Fin n) (Fin n) L).map ι = ι 1 • (1 : Matrix (Fin n) (Fin n) R) := by
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

def Mm (K : Matrix (Fin n) (Fin n) L) : Matrix (Fin n) (Fin n) R := (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) R) + K.map ι

omit hm in
theorem Mm_def (K : Matrix (Fin n) (Fin n) L) : Mm ι K = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) R) + K.map ι := rfl

theorem Mm_mul (K K' : Matrix (Fin n) (Fin n) L) : Mm ι K * Mm ι K' = Mm ι (K * K') := by
  simp only [Mm_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ff ι hm,
    Matrix.one_mul, Matrix.mul_one, f_smul_map ι hm, map_mul_map ι hm, add_zero, zero_add]

theorem Mm_one : Mm ι (1 : Matrix (Fin n) (Fin n) L) = 1 := by
  rw [Mm_def, map_one' ι hm, ← add_smul, sub_add_cancel, one_smul]

theorem sandwich (Y : Matrix (Fin n) (Fin n) R) (K1 K2 K3 : Matrix (Fin n) (Fin n) L) :
    Mm ι K1 * ((1 - ι 1) • Y + K2.map ι) * Mm ι K3 = (1 - ι 1) • Y + (K1 * K2 * K3).map ι := by
  simp only [Mm_def, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, ff ι hm,
    Matrix.one_mul, Matrix.mul_one, f_smul_map ι hm, map_mul_map ι hm, f_smul_mul_map ι hm, f_smul_map_mul ι hm,
    add_zero, zero_add]

def toGL : GL (Fin n) L →* GL (Fin n) R where
  toFun g := ⟨Mm ι (g : Matrix (Fin n) (Fin n) L), Mm ι ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L),
    by rw [Mm_mul ι hm, Units.mul_inv, Mm_one ι hm], by rw [Mm_mul ι hm, Units.inv_mul, Mm_one ι hm]⟩
  map_one' := Units.ext (by show Mm ι ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1; rw [Units.val_one, Mm_one ι hm])
  map_mul' g g' := Units.ext (by
    show Mm ι ((g * g' : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Mm ι (g : Matrix (Fin n) (Fin n) L) * Mm ι (g' : Matrix (Fin n) (Fin n) L)
    rw [Units.val_mul, Mm_mul ι hm])

omit hm in
theorem Mm_transpose (K : Matrix (Fin n) (Fin n) L) : (Mm ι K)ᵀ = Mm ι Kᵀ := by
  simp only [Mm_def, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_map]

end Idem

section Core

variable {L : Type} [Field L] {n : ℕ}

theorem unit_core (σL : L →+* L) (δ : L) (hδ : δ ≠ 0) (T : Matrix (Fin n) (Fin n) L) (P : GL (Fin n) L)
    (JT h : Matrix (Fin n) (Fin n) L)
    (hJT : JT = -δ⁻¹ • ((P : Matrix (Fin n) (Fin n) L)ᵀ * T * (P : Matrix (Fin n) (Fin n) L).map σL)ᵀ)
    (hh : (h.map σL)ᵀ * JT * h = JT) :
    ((P : Matrix (Fin n) (Fin n) L) * h * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))ᵀ * T *
      ((P : Matrix (Fin n) (Fin n) L) * h * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map σL = T := by
  set Pm : Matrix (Fin n) (Fin n) L := (P : Matrix (Fin n) (Fin n) L)
  set Pi : Matrix (Fin n) (Fin n) L := ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  set G := Pmᵀ * T * Pm.map σL with hGdef
  have hPP : Pm * Pi = 1 := Units.mul_inv P
  have h1 : Piᵀ * Pmᵀ = 1 := by rw [← Matrix.transpose_mul, hPP, Matrix.transpose_one]
  have h2 : Pm.map σL * Pi.map σL = 1 := by rw [← Matrix.map_mul, hPP, Matrix.map_one _ (map_zero σL) (map_one σL)]
  have hGt : (h.map σL)ᵀ * Gᵀ * h = Gᵀ := by
    rw [hJT, Matrix.mul_smul, Matrix.smul_mul] at hh
    have := congrArg (fun M : Matrix (Fin n) (Fin n) L => (-δ) • M) hh
    simpa only [smul_smul, neg_mul_neg, mul_inv_cancel₀ hδ, one_smul] using this
  have hG : hᵀ * G * h.map σL = G := by
    have := congrArg Matrix.transpose hGt
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_transpose,
      ← Matrix.mul_assoc] at this
    exact this
  calc (Pm * h * Pi)ᵀ * T * (Pm * h * Pi).map σL
      = Piᵀ * (hᵀ * (Pmᵀ * T * Pm.map σL) * h.map σL) * Pi.map σL := by
        simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_assoc]
    _ = Piᵀ * (Pmᵀ * T * Pm.map σL) * Pi.map σL := by rw [← hGdef, hG]
    _ = (Piᵀ * Pmᵀ) * T * (Pm.map σL * Pi.map σL) := by simp only [Matrix.mul_assoc]
    _ = T := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

end Core

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L] {n : ℕ}

theorem e_smul_incM (v : Pl F) (ι : L →+ AE F E) (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
    (J : Matrix (Fin n) (Fin n) E) : ι 1 • incM F J = (tJ ι J).map ι := by
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, incM, tJ, smul_eq_mul]
  rw [pre_spec]
  apply (hAt _).1
  intro u hu
  have h1 : u • ι 1 = 0 := (hAt (ι 1)).2 ⟨1, rfl⟩ u hu
  rw [← smul_mul_assoc, h1, zero_mul]

theorem incM_split (v : Pl F) (ι : L →+ AE F E) (hAt : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z)
    (J : Matrix (Fin n) (Fin n) E) : incM F J = (1 - ι 1) • incM F J + (tJ ι J).map ι := by
  rw [← e_smul_incM v ι hAt, ← add_smul, sub_add_cancel, one_smul]

theorem Mm_cA (σ : E →ₐ[F] E) (σL : L →+* L) (ι : L →+ AE F E) (hσ : ∀ x, ι (σL x) = cA σ (ι x))
    (K : Matrix (Fin n) (Fin n) L) : (Mm ι K).map (cA σ) = Mm ι (K.map σL) := by
  have he : cA σ (ι 1) = ι 1 := by rw [← hσ, map_one]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Mm_def, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_sub, he, hσ]
  · simp [Mm_def, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_ne hij, hσ]

end Adelic

theorem homW : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] (σL : L →+* L) (δ : L)
    (ι : L →+ AE F E), δ ≠ 0 → (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      ∀ (P JT : GL (Fin n) L), (JT : Matrix (Fin n) (Fin n) L) = -δ⁻¹ • (GlobalTheory.InertLocFrame.gram σL ι P X.J)ᵀ →
      ∃ iW : Formalism.UG.UJ σL (JT : Matrix (Fin n) (Fin n) L) →* UA σ X.J, ∀ h,
        mat (iW h) = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) +
          ((P : Matrix (Fin n) (Fin n) L) * ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι := by
  intro F E _ _ _ _ _ σ v n X L _ σL δ ι hδ hAt hm hσ P JT hJT
  let φ : Formalism.UG.UJ σL (JT : Matrix (Fin n) (Fin n) L) →* GL (Fin n) L :=
    (MulAut.conj P).toMonoidHom.comp (Subgroup.subtype _)
  have hφ : ∀ h, ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (P : Matrix (Fin n) (Fin n) L) *
      ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    intro h
    simp [φ, MulAut.conj_apply, Units.val_mul]
  have hmem : ∀ h, (toGL ι hm).comp φ h ∈ UG (cA σ) (incM F X.J) := by
    intro h
    have hh : (((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JT : Matrix (Fin n) (Fin n) L) *
        ((h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = (JT : Matrix (Fin n) (Fin n) L) := h.2
    show (Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L))ᵀ * incM F X.J *
      (Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map (cA σ) = incM F X.J
    rw [Mm_transpose, Mm_cA σ σL ι hσ]
    conv_lhs => rw [incM_split v ι hAt X.J]
    rw [sandwich ι hm, hφ, unit_core σL δ hδ (tJ ι X.J) P JT _ hJT hh, ← incM_split v ι hAt X.J]
  refine ⟨((toGL ι hm).comp φ).codRestrict _ hmem, fun h => ?_⟩
  show Mm ι ((φ h : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = _
  rw [hφ, Mm_def]

end GlobalTheory.InertLocFrame.HomW
