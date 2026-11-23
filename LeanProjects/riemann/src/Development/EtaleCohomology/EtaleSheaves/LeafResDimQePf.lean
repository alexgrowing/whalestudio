import Development.EtaleCohomology.EtaleSheaves.LeafCoordsPointResPfY

noncomputable section
namespace LateralTheory.E.LeafResDimQePf
open LateralTheory.E.LeafCoordsPointResPf
open scoped TensorProduct

theorem LeafResDimQe_of : LeafResDimQe := by
  intro d e A B _ _ _ I hB hBI P _ hIP
  set K := P.ResidueField
  have hI : ∀ a ∈ I, algebraMap B K a = 0 := fun a ha => by
    rw [Ideal.algebraMap_residueField_eq_zero]; exact hIP ha
  letI : Algebra (B ⧸ I) K := (Ideal.Quotient.lift I (algebraMap B K) hI).toAlgebra
  have : IsScalarTower B (B ⧸ I) K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr
    (fun h => Ideal.IsPrime.ne_top ‹P.IsPrime› (eq_top_iff.mpr (h ▸ hIP)))
  have := hBI
  have := hBI.isStandardSmooth
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := A) (S := B ⧸ I) e
  have hf : Module.finrank (B ⧸ I) Ω[(B ⧸ I)⁄A] = e := Module.finrank_eq_of_rank_eq hr
  have : TensorProduct.CompatibleSMul B (B ⧸ I) K Ω[(B ⧸ I)⁄A] := ⟨fun r m n => by
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
    have h1 : (Ideal.Quotient.mk I b) • m = b • m := (algebraMap_smul (B ⧸ I) b m)
    have h2 : (Ideal.Quotient.mk I b) • n = b • n := (algebraMap_smul (B ⧸ I) b n)
    rw [h1, h2, TensorProduct.smul_tmul]⟩
  rw [← (TensorProduct.equivOfCompatibleSMul B (B ⧸ I) K K Ω[(B ⧸ I)⁄A]).finrank_eq,
    Module.finrank_baseChange, hf]

end LateralTheory.E.LeafResDimQePf
