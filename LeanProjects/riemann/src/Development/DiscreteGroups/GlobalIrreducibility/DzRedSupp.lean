import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne
import Development.DiscreteGroups.GlobalIrreducibility.DzLcFin
import Development.DiscreteGroups.GlobalIrreducibility.DzLcIso
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.GLp GlobalTheory.GLq GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Whittaker GroundTheory.Automorphic

namespace DiscreteGroups.sglob.DzRed

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Conj

variable {F : Type} [Field F] {n : ℕ}

theorem conj_apply (δ : Fin n → Fˣ) (u : GL (Fin n) F) (a b : Fin n) :
    ((Iwasawa.diagGL F n δ * u * (Iwasawa.diagGL F n δ)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a b =
      (δ a : F) * (u : Matrix (Fin n) (Fin n) F) a b * (δ b : F)⁻¹ := by
  rw [show (Iwasawa.diagGL F n δ)⁻¹ = Iwasawa.diagGL F n δ⁻¹ from (map_inv _ _).symm, Units.val_mul,
    Units.val_mul, Iwasawa.coe_diagGL, Iwasawa.coe_diagGL, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp

theorem conj_mem_unipB (δ : Fin n → Fˣ) {u : GL (Fin n) F} (hu : u ∈ unipB F (Fin n)) :
    Iwasawa.diagGL F n δ * u * (Iwasawa.diagGL F n δ)⁻¹ ∈ unipB F (Fin n) := by
  rw [mem_unipB] at hu ⊢
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · rw [conj_apply, hu.1 a b hab]; simp
  · rw [conj_apply, hu.2 a]; simp

theorem superDiag_conj (δ : Fin n → Fˣ) (u : GL (Fin n) F) :
    superDiag (Iwasawa.diagGL F n δ * u * (Iwasawa.diagGL F n δ)⁻¹) =
      ∑ a : Fin n, ∑ b : Fin n with b.val = a.val + 1,
        (δ a : F) * (u : Matrix (Fin n) (Fin n) F) a b * (δ b : F)⁻¹ := by
  unfold superDiag
  simp_rw [conj_apply]

def tv (a b : Fin n) (hab : a ≠ b) (c : F) : GL (Fin n) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection a b c)
    (by rw [Matrix.det_transvection_of_ne a b hab c]; exact one_ne_zero)

theorem tv_apply (a b : Fin n) (hab : a ≠ b) (c : F) (x y : Fin n) :
    (tv a b hab c : Matrix (Fin n) (Fin n) F) x y =
      (1 : Matrix (Fin n) (Fin n) F) x y + if x = a ∧ y = b then c else 0 := by
  show Matrix.transvection a b c x y = _
  by_cases h : x = a ∧ y = b
  · obtain ⟨rfl, rfl⟩ := h
    simp [Matrix.transvection]
  · simp only [Matrix.transvection, Matrix.add_apply, h, if_false]
    congr 1
    rw [Matrix.single_apply, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)]

theorem tv_mem_unipB (a b : Fin n) (hab : a < b) (c : F) : tv a b hab.ne c ∈ unipB F (Fin n) := by
  rw [mem_unipB]
  refine ⟨fun x y hxy => ?_, fun x => ?_⟩
  · rw [tv_apply, Matrix.one_apply_ne (ne_of_gt hxy)]
    have : ¬ (x = a ∧ y = b) := by rintro ⟨rfl, rfl⟩; exact absurd (hxy.trans hab) (lt_irrefl _)
    simp [this]
  · rw [tv_apply, Matrix.one_apply_eq]
    have : ¬ (x = a ∧ x = b) := by rintro ⟨rfl, h⟩; exact hab.ne h
    simp [this]

theorem conj_tv (δ : Fin n → Fˣ) (a b : Fin n) (hab : a ≠ b) (c : F) :
    Iwasawa.diagGL F n δ * tv a b hab c * (Iwasawa.diagGL F n δ)⁻¹ = tv a b hab ((δ a : F) * c * (δ b : F)⁻¹) := by
  refine Units.ext (Matrix.ext fun x y => ?_)
  rw [conj_apply, tv_apply, tv_apply]
  by_cases hxy : x = y
  · subst hxy
    have : ¬ (x = a ∧ x = b) := by rintro ⟨rfl, h⟩; exact hab h
    simp [this]
  · rw [Matrix.one_apply_ne hxy]
    by_cases h : x = a ∧ y = b
    · obtain ⟨rfl, rfl⟩ := h; simp
    · simp [h]

theorem superDiag_tv (a b : Fin n) (hb : b.val = a.val + 1) (c : F) :
    superDiag (tv a b (fun h => by rw [h] at hb; omega) c) = c := by
  unfold superDiag
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · rw [tv_apply, Matrix.one_apply_ne (fun h => by rw [h] at hb; omega)]; simp
    · intro y _ hy
      rw [tv_apply, Matrix.one_apply_ne (fun h => by subst h; simp_all)]
      simp [hy]
    · intro h; exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ b, hb⟩) h
  · intro x _ hx
    refine Finset.sum_eq_zero fun y hy => ?_
    have hy' := (Finset.mem_filter.1 hy).2
    rw [tv_apply, Matrix.one_apply_ne (fun h => by subst h; omega)]
    simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

end Conj

end DiscreteGroups.sglob.DzRed
