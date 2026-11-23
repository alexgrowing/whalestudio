import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRFiltrationLaws

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.Per.TiedField

theorem exists_inv_filD {l : ℕ} [Fact l.Prime] (x : Per.BdR l) (h0 : x ∈ Per.FilD l 0)
    (h1 : x ∉ Per.FilD l 1) : ∃ y ∈ Per.FilD l 0, x * y = 1 := by
  obtain ⟨-, hone, -, -, -, -, hlast⟩ := GlobalTheory.MemLoc.filD_laws l
  obtain ⟨-, hker, hunit, -, -⟩ := GlobalTheory.MemLoc.thetaD_props l
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.FilLaws.exists_isEps l
  obtain ⟨z, hz⟩ := (GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l e he 0 x).1 h0
  rw [neg_zero, Int.toNat_zero, pow_zero, pow_zero, mul_one, one_mul] at hz
  subst hz
  have hz1 : Per.θD l z ≠ 0 := fun h => h1 ((hlast 1 z).2 ((hker z).1 h))
  obtain ⟨w, hw⟩ := (hunit z hz1).exists_right_inv
  refine ⟨algebraMap (Per.BdRp l) (Per.BdR l) w, ?_, by rw [← map_mul, hw, map_one]⟩
  have := Submodule.smul_mem _ w hone
  rwa [Algebra.smul_def, mul_one] at this

theorem tied_field : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    IsField P.R.BdR ∧ IsDomain P.R.B ∧ Function.Injective P.ιB ∧ Function.Injective P.φB ∧
      ∀ (K : FinExt l) (x : P.R.BdR), x ∈ (P.PD K).Fil 0 → x ∉ (P.PD K).Fil 1 →
        ∃ y ∈ (P.PD K).Fil 0, x * y = 1 := by
  intro l _ P AI T
  have hF : IsField P.R.BdR := T.eD.toMulEquiv.isField (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.1
  obtain ⟨K₁⟩ : Nonempty (FinExt l) := ⟨⟨⊥, inferInstance⟩⟩
  have hι : Function.Injective P.ιB := fun a b h =>
    (P.PD K₁).ι_inj (by rw [P.PD_ι, P.PD_ι]; exact h)
  have hφ : Function.Injective P.φB := fun a b h =>
    (P.PD K₁).φ_inj (by rw [P.PD_φ, P.PD_φ]; exact h)
  refine ⟨hF, ?_, hι, hφ, fun K x h0 h1 => ?_⟩
  · have := hF.isDomain
    exact hι.isDomain (P.ιB : P.R.B →+* P.R.BdR)
  · obtain ⟨y, hy, hxy⟩ := exists_inv_filD (T.eD x) ((T.fil K 0 x).1 h0) (fun h => h1 ((T.fil K 1 x).2 h))
    refine ⟨T.eD.symm y, (T.fil K 0 _).2 (by rwa [RingEquiv.apply_symm_apply]), T.eD.injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply, hxy, map_one]

end GlobalTheory.Per.TiedField
