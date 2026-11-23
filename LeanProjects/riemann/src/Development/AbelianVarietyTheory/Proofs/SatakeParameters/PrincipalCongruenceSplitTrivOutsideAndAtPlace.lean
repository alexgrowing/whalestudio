import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CongruenceElementDecompose
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CongSplitBoth

open GlobalTheory.IdemSplit GlobalTheory.CongSplit

theorem split_cong_at_place : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (κ : GAf L n), NG.Cong L n N κ → ∃ x y : GAf L n, TrivOutside {v} x ∧ TrivOutside {v}ᶜ y ∧ NG.Cong L n N x ∧ NG.Cong L n N y ∧ κ = x * y := by
  intro L _ _ _ n N v κ hc
  set e := idemAt L v with he_def
  have he : e * e = e := idemAt_mul_self L v
  have he' : (1 - e) * (1 - e) = 1 - e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  have hσ : conjAL L e = e := conjAL_idemAt L v
  have hσ' : conjAL L (1 - e) = 1 - e := by rw [map_sub, map_one, hσ]
  have hei : e ∈ ALint L := idemAt_mem L v
  have hei' : 1 - e ∈ ALint L := Subring.sub_mem _ (one_mem _) hei
  refine ⟨gaFold he hσ κ, gaFold he' hσ' κ, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    have hw' : w ≠ v := by simpa using hw
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add, map_mul, map_mul, map_sub, map_one,
      compAt_idemAt_ne L v hw', compAt_one_apply]
    simp
  · intro w hw
    have hw' : w = v := by simpa using hw
    subst hw'
    ext i j
    rw [Matrix.map_apply, gaFold_val, fold_apply, map_add, map_mul, map_mul, map_sub, map_one,
      compAt_one_apply]
    simp [he_def, compAt_idemAt_self]
  · refine ⟨gaFold_mem_Umax L he hσ hei κ hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨e * y, Subring.mul_mem _ hei hy, ?_⟩
    rw [gaFold_val, fold_apply]
    linear_combination e * hEq
  · refine ⟨gaFold_mem_Umax L he' hσ' hei' κ hc.1, fun i j => ?_⟩
    obtain ⟨y, hy, hEq⟩ := hc.2 i j
    refine ⟨(1 - e) * y, Subring.mul_mem _ hei' hy, ?_⟩
    rw [gaFold_val, fold_apply, sub_sub_cancel]
    linear_combination (1 - e) * hEq
  · apply Subtype.ext; apply Units.ext
    show (κ.1 : Matrix (Fin n) (Fin n) (AL L)) = fold e _ * fold (1 - e) _
    rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]

end GlobalTheory.CongSplitBoth
