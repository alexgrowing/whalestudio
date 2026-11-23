import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasCompactSupportDescend
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipMulMemCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDivZpowOrd
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.IwaCell

theorem exists_mem_cell : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℕ) (ϖ : kˣ), ord k ϖ = 1 → ∀ g : GL (Fin m) k, ∃ a : Fin m → ℤ, g ∈ GlobalTheory.IwaCell.cell ϖ a := by
  intro k _ _ _ _ m ϖ hϖ g
  obtain ⟨k₀, b, hb, hg⟩ := GlobalTheory.ValIwasawa.iwasawa 𝒪[k] k m g⁻¹
  have hg' : g = b⁻¹ * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹ := by
    rw [← _root_.mul_inv_rev, ← hg, inv_inv]
  set c := b⁻¹ with hc
  have hcT : c.val.BlockTriangular id := by
    have : c.val = b.val⁻¹ := by rw [hc, Matrix.coe_units_inv]
    rw [this]; exact Matrix.blockTriangular_inv_of_blockTriangular hb
  have hdet : c.val.det = ∏ i, c.val i i := Matrix.det_of_upperTriangular hcT
  have hd : ∀ i, c.val i i ≠ 0 := fun i h => by
    have := Matrix.GeneralLinearGroup.det_ne_zero c
    rw [hdet] at this
    exact this (Finset.prod_eq_zero (Finset.mem_univ i) h)
  let d : Fin m → kˣ := fun i => Units.mk0 _ (hd i)
  let a : Fin m → ℤ := fun i => ord k (d i)
  let e : Fin m → kˣ := fun i => d i / ϖ ^ a i
  have he : ∀ i, valuation k (e i : k) = 1 := fun i => by
    apply ord_eq_zero_iff.1
    simp only [e, div_eq_mul_inv, ← _root_.zpow_neg, ord_mul, ord_zpow, hϖ, a]
    ring
  have hde : d = (fun i => ϖ ^ a i) * e := by
    funext i; simp [e]
  let u := c * (diagT k (Fin m) d)⁻¹
  have hu : u ∈ unipB k (Fin m) := by
    rw [mem_unipB]
    have hval : u.val = c.val * diagonal (fun i => (((d i)⁻¹ : kˣ) : k)) := by
      simp only [u, ← map_inv, Units.val_mul, val_diagT, Pi.inv_apply]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hval, mul_diagonal, hcT hij, zero_mul]
    · rw [hval, mul_diagonal]; simp [d, mul_inv_cancel₀ (hd i)]
  refine ⟨a, u, hu, diagT k (Fin m) e * (GeneralLinearGroup.map (algebraMap 𝒪[k] k) k₀)⁻¹,
    mul_mem (GlobalTheory.LocalCartan.diagT_mem_KO he) (inv_mem ⟨k₀, rfl⟩), ?_⟩
  rw [hg', tD, ← mul_assoc, mul_assoc u, ← map_mul, ← hde]
  simp [u]

end GlobalTheory.IwaCell
