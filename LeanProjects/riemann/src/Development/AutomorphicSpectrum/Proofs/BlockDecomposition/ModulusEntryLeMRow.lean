import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntInd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerTemperedBoundDetOne
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaCoordinatesBoundedRegion
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 GlobalTheory.CompanionTheory.SphTheta
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.SphTheta.RowIwasawa

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem modulus_add_le_sup (x y : F) : modulus (x + y) ≤ max (modulus x) (modulus y) := by
  have h := GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max x y
  exact_mod_cast h

theorem modulus_mRow (g : GL (Fin 2) F) :
    modulus (mRow g) = max (modulus (g.val 1 0)) (modulus (g.val 1 1)) := by
  unfold mRow
  split_ifs with h
  · exact (max_eq_right h.le).symm
  · exact (max_eq_left (not_lt.1 h)).symm

theorem mRow_ne_zero (g : GL (Fin 2) F) : mRow g ≠ 0 := by
  intro h0
  have hm : max (modulus (g.val 1 0)) (modulus (g.val 1 1)) = 0 := by
    rw [← modulus_mRow, h0, modulus_zero]
  have hc : g.val 1 0 = 0 := modulus_eq_zero.1
    (le_antisymm (hm ▸ le_max_left _ _) zero_le')
  have hd : g.val 1 1 = 0 := modulus_eq_zero.1
    (le_antisymm (hm ▸ le_max_right _ _) zero_le')
  have hdet : (g.val).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  apply hdet
  rw [Matrix.det_fin_two, hc, hd]
  ring

theorem modulus_entry_le_mRow (g : GL (Fin 2) F) (j : Fin 2) :
    modulus (g.val 1 j) ≤ modulus (mRow g) := by
  rw [modulus_mRow]
  fin_cases j
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem modulus_comb_le {u v s t : F} {B : NNReal} (hu : modulus u ≤ B) (hv : modulus v ≤ B)
    (hs : s ∈ 𝒪[F]) (ht : t ∈ 𝒪[F]) : modulus (u * s + v * t) ≤ B := by
  refine (modulus_add_le_sup _ _).trans (max_le ?_ ?_)
  · rw [modulus_mul]
    exact (mul_le_of_le_one_right' (modulus_le_one_iff.2 hs)).trans hu
  · rw [modulus_mul]
    exact (mul_le_of_le_one_right' (modulus_le_one_iff.2 ht)).trans hv

theorem modulus_mRow_mul_le (g k : GL (Fin 2) F) (hk : ∀ i j, k.val i j ∈ 𝒪[F]) :
    modulus (mRow (g * k)) ≤ modulus (mRow g) := by
  have key : ∀ j, modulus ((g * k).val 1 j) ≤ modulus (mRow g) := fun j => by
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact modulus_comb_le (modulus_entry_le_mRow g 0) (modulus_entry_le_mRow g 1) (hk 0 j) (hk 1 j)
  rw [modulus_mRow]
  exact max_le (key 0) (key 1)

theorem modulus_mRow_mul (g k : GL (Fin 2) F) (hk : k ∈ GLnLocal.integralGL F 2) :
    modulus (mRow (g * k)) = modulus (mRow g) := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  refine le_antisymm (modulus_mRow_mul_le g k h1) ?_
  have := modulus_mRow_mul_le (g * k) k⁻¹ h2
  rwa [mul_inv_cancel_right] at this

theorem modulus_det_mul [MeasurableSpace F] [BorelSpace F] (g k : GL (Fin 2) F) (hk : k ∈ GLnLocal.integralGL F 2) :
    modulus ((g * k).val).det = modulus (g.val).det := by
  rw [Units.val_mul, Matrix.det_mul, modulus_mul,
    GlobalTheory.CompanionTheory.GJTwo.WhB.modulus_det_integral hk, mul_one]

theorem exists_column (g : GL (Fin 2) F) :
    ∃ j, mRow g = g.val 1 j ∧ xRow g = g.val 0 j / g.val 1 j := by
  unfold mRow xRow
  split_ifs with h
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨0, rfl, rfl⟩

theorem modulus_sub_xRow_le (g : GL (Fin 2) F)
    (hD : modulus (g.val).det ≤ modulus (mRow g) ^ 2) (j : Fin 2) :
    modulus (g.val 0 j - xRow g * g.val 1 j) ≤ modulus (mRow g) := by
  have hm := mRow_ne_zero g
  have hpos : 0 < modulus (mRow g) := modulus_pos hm
  have hdiv : modulus ((g.val).det / mRow g) ≤ modulus (mRow g) := by
    rw [div_eq_mul_inv, modulus_mul, modulus_inv, ← div_eq_mul_inv, div_le_iff₀ hpos, ← sq]
    exact hD
  by_cases h : modulus (g.val 1 0) < modulus (g.val 1 1)
  · have hmd : mRow g = g.val 1 1 := by simp [mRow, h]
    have hxd : xRow g = g.val 0 1 / g.val 1 1 := by simp [xRow, h]
    have hd : g.val 1 1 ≠ 0 := hmd ▸ hm
    rw [hxd]
    fin_cases j
    · have e : g.val 0 0 - g.val 0 1 / g.val 1 1 * g.val 1 0 = (g.val).det / mRow g := by
        rw [hmd, Matrix.det_fin_two]
        field_simp
      simpa [e] using hdiv
    · have e : g.val 0 1 - g.val 0 1 / g.val 1 1 * g.val 1 1 = 0 := by
        field_simp
        ring
      simp [e]
  · have hmc : mRow g = g.val 1 0 := by simp [mRow, h]
    have hxc : xRow g = g.val 0 0 / g.val 1 0 := by simp [xRow, h]
    have hc : g.val 1 0 ≠ 0 := hmc ▸ hm
    rw [hxc]
    fin_cases j
    · have e : g.val 0 0 - g.val 0 0 / g.val 1 0 * g.val 1 0 = 0 := by
        field_simp
        ring
      simp [e]
    · have e : g.val 0 1 - g.val 0 0 / g.val 1 0 * g.val 1 1 = -((g.val).det / mRow g) := by
        rw [hmc, Matrix.det_fin_two]
        field_simp
        ring
      have : modulus (g.val 0 1 - g.val 0 0 / g.val 1 0 * g.val 1 1) ≤ modulus (mRow g) := by
        rw [e, GlobalTheory.CompanionTheory.LFCoords.modulus_neg_self]
        exact hdiv
      simpa using this

theorem xRow_mul_sub_mem (g k : GL (Fin 2) F) (hk : k ∈ GLnLocal.integralGL F 2)
    (hD : modulus (g.val).det ≤ modulus (mRow g) ^ 2) : xRow (g * k) - xRow g ∈ 𝒪[F] := by
  obtain ⟨h1, -⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  obtain ⟨j, hmj, hxj⟩ := exists_column (g * k)
  have hne : (g * k).val 1 j ≠ 0 := hmj ▸ mRow_ne_zero (g * k)
  have hmod : modulus ((g * k).val 1 j) = modulus (mRow g) := by
    rw [← hmj, modulus_mRow_mul g k hk]
  have hnum : (g * k).val 0 j - xRow g * (g * k).val 1 j =
      (g.val 0 0 - xRow g * g.val 1 0) * k.val 0 j +
        (g.val 0 1 - xRow g * g.val 1 1) * k.val 1 j := by
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hle : modulus ((g * k).val 0 j - xRow g * (g * k).val 1 j) ≤ modulus (mRow g) := by
    rw [hnum]
    exact modulus_comb_le (modulus_sub_xRow_le g hD 0) (modulus_sub_xRow_le g hD 1)
      (h1 0 j) (h1 1 j)
  have hx : xRow (g * k) - xRow g =
      ((g * k).val 0 j - xRow g * (g * k).val 1 j) * ((g * k).val 1 j)⁻¹ := by
    rw [hxj]
    field_simp
  rw [hx, ← modulus_le_one_iff, modulus_mul, modulus_inv, hmod]
  exact mul_inv_le_one_of_le₀ hle zero_le'

end

theorem iwasawa_lower_row : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F], ∀ (g k : GL (Fin 2) F), k ∈ GLnLocal.integralGL F 2 → mRow g ≠ 0 ∧ modulus ((g * k).val).det = modulus (g.val).det ∧ modulus (mRow (g * k)) = modulus (mRow g) ∧ (modulus (g.val).det ≤ modulus (mRow g) ^ 2 → xRow (g * k) - xRow g ∈ 𝒪[F]) := by
  intro F _ _ _ _ _ _ g k hk
  exact ⟨mRow_ne_zero g, modulus_det_mul g k hk, modulus_mRow_mul g k hk,
    xRow_mul_sub_mem g k hk⟩

end GlobalTheory.CompanionTheory.SphTheta.RowIwasawa
