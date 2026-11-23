import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.XmApply
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertLocHomV

open GlobalTheory.InertLocFrame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]

theorem one_sub_mul_eq_zero (ι : L →+ AE F E) (hmul : ∀ x y, ι (x * y) = ι x * ι y) (t : L) :
    (1 - ι 1) * ι t = 0 := by
  rw [sub_mul, one_mul, ← hmul, one_mul, sub_self]

theorem idem (ι : L →+ AE F E) (hmul : ∀ x y, ι (x * y) = ι x * ι y) :
    (1 - ι 1) * (1 - ι 1) = 1 - ι 1 := by
  rw [mul_sub, mul_one, one_sub_mul_eq_zero ι hmul, sub_zero]

theorem map_mul_map (ι : L →+ AE F E) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ}
    (X Y : Matrix (Fin n) (Fin n) L) : X.map ι * Y.map ι = (X * Y).map ι := by
  ext i j
  simp [Matrix.mul_apply, map_sum, hmul]

theorem smul_map_eq_zero (ι : L →+ AE F E) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ}
    (X : Matrix (Fin n) (Fin n) L) : (1 - ι 1) • X.map ι = 0 := by
  ext i j
  simp [smul_eq_mul, one_sub_mul_eq_zero ι hmul]

def Am {n : ℕ} (P g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L :=
  (P : Matrix (Fin n) (Fin n) L) * ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
    ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)

def Mg (ι : L →+ AE F E) {n : ℕ} (P g : GL (Fin n) L) : Matrix (Fin n) (Fin n) (AE F E) :=
  (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (Am P g).map ι

theorem Am_mul {n : ℕ} (P g g' : GL (Fin n) L) : Am P g * Am P g' = Am P (g * g') := by
  unfold Am
  calc _ = (P : Matrix (Fin n) (Fin n) L) * ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
        (((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L)) *
        ((g'⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        rw [Units.inv_mul, Matrix.mul_one, mul_inv_rev, Units.val_mul, Matrix.transpose_mul]
        simp only [Matrix.mul_assoc]

theorem Am_one {n : ℕ} (P : GL (Fin n) L) : Am P 1 = 1 := by
  simp [Am]

theorem Mg_mul (ι : L →+ AE F E) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ} (P g g' : GL (Fin n) L) :
    Mg ι P g * Mg ι P g' = Mg ι P (g * g') := by
  unfold Mg
  rw [add_mul, mul_add, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul, smul_smul,
    idem ι hmul, smul_map_eq_zero ι hmul, Matrix.mul_smul, Matrix.mul_one, smul_map_eq_zero ι hmul,
    map_mul_map ι hmul, Am_mul, add_zero, zero_add]

theorem Mg_one (ι : L →+ AE F E) {n : ℕ} (P : GL (Fin n) L) : Mg ι P 1 = 1 := by
  unfold Mg
  rw [Am_one]
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

def Phi (ι : L →+ AE F E) (hmul : ∀ x y, ι (x * y) = ι x * ι y) {n : ℕ} (P : GL (Fin n) L) :
    GL (Fin n) L →* GL (Fin n) (AE F E) where
  toFun g := ⟨Mg ι P g, Mg ι P g⁻¹, by rw [Mg_mul ι hmul, mul_inv_cancel, Mg_one],
    by rw [Mg_mul ι hmul, inv_mul_cancel, Mg_one]⟩
  map_one' := Units.ext (Mg_one ι P)
  map_mul' g g' := Units.ext (Mg_mul ι hmul P g g').symm

theorem key (σL : L →+* L) (ι : L →+ AE F E) {n : ℕ} (P JS g : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E)
    (hJ : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = gram σL ι P J)
    (hg : Formalism.UG.cT σL (g : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * g = JS) :
    (Am P g)ᵀ * tJ ι J * (Am P g).map σL = tJ ι J := by
  have hpp : ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul P
  have hpp' : (P : Matrix (Fin n) (Fin n) L) * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv P
  have hσp' : (P : Matrix (Fin n) (Fin n) L).map σL * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL = 1 := by
    rw [← Matrix.map_mul, hpp', Matrix.map_one _ (map_zero σL) (map_one σL)]
  have hKK : (JS : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = 1 := Units.mul_inv JS
  have hKK' : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul JS
  have hgg : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * (g : Matrix (Fin n) (Fin n) L) = 1 := Units.inv_mul g
  have huu : (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * ((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero σL) (map_one σL),
      Matrix.transpose_one]
  have hT : tJ ι J = ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL := by
    rw [hJ, gram]
    calc tJ ι J = (((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ * (P : Matrix (Fin n) (Fin n) L)ᵀ) * tJ ι J *
        ((P : Matrix (Fin n) (Fin n) L).map σL * ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL) := by
          rw [← Matrix.transpose_mul, hpp', Matrix.transpose_one, Matrix.one_mul, hσp', Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have hKi : ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
      (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ = ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
    have hg' : ((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JS : Matrix (Fin n) (Fin n) L) * g = JS := hg
    calc _ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ *
          ((JS : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by
            rw [hKK, Matrix.mul_one]
      _ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ *
          (((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ * (JS : Matrix (Fin n) (Fin n) L) * g *
            ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)) := by rw [hg']
      _ = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ * ((g : Matrix (Fin n) (Fin n) L).map σL)ᵀ) *
          (JS : Matrix (Fin n) (Fin n) L) * g * ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by
            simp only [Matrix.mul_assoc]
      _ = _ := by
            rw [huu, Matrix.mul_one, Matrix.mul_assoc ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L), hKK',
              Matrix.mul_one, hgg, Matrix.one_mul]
  calc (Am P g)ᵀ * tJ ι J * (Am P g).map σL
      = ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
        (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *
          ((P : Matrix (Fin n) (Fin n) L)ᵀ * tJ ι J * (P : Matrix (Fin n) (Fin n) L).map σL) *
          (((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL)ᵀ) *
        ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map σL := by
          simp only [Am, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.map_mul, Matrix.transpose_map,
            Matrix.mul_assoc]
    _ = tJ ι J := by rw [← gram, ← hJ, hKi, ← hT]

theorem mem (σ : E →ₐ[F] E) (v : Pl F) (σL : L →+* L) (ι : L →+ AE F E)
    (hsupp : ∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) (hmul : ∀ x y, ι (x * y) = ι x * ι y)
    (hσ : ∀ x, ι (σL x) = cA σ (ι x)) {n : ℕ} (P JS g : GL (Fin n) L) (J : Matrix (Fin n) (Fin n) E)
    (hJ : ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = gram σL ι P J)
    (hg : Formalism.UG.cT σL (g : Matrix (Fin n) (Fin n) L) * (JS : Matrix (Fin n) (Fin n) L) * g = JS) :
    (Mg ι P g)ᵀ * incM F J * (Mg ι P g).map (cA σ) = incM F J := by
  have hce : cA σ (ι 1) = ι 1 := by rw [← hσ, map_one]
  have hMT : (Mg ι P g)ᵀ = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + (Am P g)ᵀ.map ι := by
    simp [Mg, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_map]
  have hMc : (Mg ι P g).map (cA σ) =
      (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) + ((Am P g).map σL).map ι := by
    ext i j
    by_cases h : i = j <;> simp [Mg, h, Matrix.one_apply, ← hσ, hce]
  have hsplit : incM F J = (1 - ι 1) • incM F J + (tJ ι J).map ι := by
    ext i j
    have hex : ∃ x, ι x = ι 1 * inclR (F := F) (AF F) (J i j) := (hsupp _).1 (fun u hu => by
      rw [← smul_mul_assoc, (hsupp (ι 1)).2 ⟨1, rfl⟩ u hu, zero_mul])
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply, incM, tJ]
    rw [pre_spec ι hex]
    ring
  have h1 : (Am P g)ᵀ.map ι * incM F J = ((Am P g)ᵀ * tJ ι J).map ι := by
    calc (Am P g)ᵀ.map ι * incM F J = (Am P g)ᵀ.map ι * ((1 - ι 1) • incM F J + (tJ ι J).map ι) := by
          rw [← hsplit]
      _ = ((1 - ι 1) • (Am P g)ᵀ.map ι) * incM F J + (Am P g)ᵀ.map ι * (tJ ι J).map ι := by
          rw [Matrix.mul_add, Matrix.mul_smul, ← Matrix.smul_mul]
      _ = _ := by rw [smul_map_eq_zero ι hmul, Matrix.zero_mul, zero_add, map_mul_map ι hmul]
  have hL : (Mg ι P g)ᵀ * incM F J = (1 - ι 1) • incM F J + ((Am P g)ᵀ * tJ ι J).map ι := by
    rw [hMT, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, h1]
  have e1 : ((1 - ι 1) • incM F J) * ((1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E))) = (1 - ι 1) • incM F J := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, idem ι hmul]
  have e2 : ((1 - ι 1) • incM F J) * ((Am P g).map σL).map ι = 0 := by
    rw [Matrix.smul_mul, ← Matrix.mul_smul, smul_map_eq_zero ι hmul, Matrix.mul_zero]
  have e3 : ((Am P g)ᵀ * tJ ι J).map ι * ((1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E))) = 0 := by
    rw [Matrix.mul_smul, Matrix.mul_one, smul_map_eq_zero ι hmul]
  rw [hL, hMc, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, e1, e2, e3, map_mul_map ι hmul,
    key σL ι P JS g J hJ hg, add_zero, zero_add, ← hsplit]

theorem exists_homV : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : Pl F) (n : ℕ) (X : Spc F E n) (L : Type) [Field L] (σL : L →+* L)
    (ι : L →+ AE F E), (∀ z : AE F E, At (evFin F v) z ↔ ∃ x, ι x = z) → (∀ x y, ι (x * y) = ι x * ι y) → (∀ x, ι (σL x) = cA σ (ι x)) →
      ∀ (P JS : GL (Fin n) L), ((JS⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = GlobalTheory.InertLocFrame.gram σL ι P X.J →
      ∃ iV : Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L) →* UA σ X.J, ∀ g,
        mat (iV g) = (1 - ι 1) • (1 : Matrix (Fin n) (Fin n) (AE F E)) +
          ((P : Matrix (Fin n) (Fin n) L) * (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)ᵀ *
            ((P⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)).map ι := by
  intro F E _ _ _ _ _ σ v n X L _ σL ι hsupp hmul hσ P JS hJ
  exact ⟨((Phi ι hmul P).comp (Formalism.UG.UJ σL (JS : Matrix (Fin n) (Fin n) L)).subtype).codRestrict
    (UG (cA σ) (incM F X.J)) (fun g => mem σ v σL ι hsupp hmul hσ P JS g.1 X.J hJ g.2), fun g => rfl⟩

end GlobalTheory.InertLocHomV

end
