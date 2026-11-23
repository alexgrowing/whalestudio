import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.MM

namespace GlobalTheory.CompanionTheory.MM.LatCO

theorem matV_mul {D : D7} {n : ℕ} (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F))
    (a b : Matrix (Fin n) (Fin n) (AE D)) :
    PositivityTheory.SiegelWeilFormula.Gen.matV v (a * b) =
      PositivityTheory.SiegelWeilFormula.Gen.matV v a * PositivityTheory.SiegelWeilFormula.Gen.matV v b := by
  unfold PositivityTheory.SiegelWeilFormula.Gen.matV
  exact Matrix.map_mul (f := (Algebra.TensorProduct.map
    ((HeckeCharacterZeroLocus.SiegelWeilU.evalV D.host.F v).comp (HeckeCharacterZeroLocus.SiegelWeilU.sndA D.host.F)) (AlgHom.id D.host.F D.host.E)))

theorem matV_one {D : D7} {n : ℕ} (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) :
    PositivityTheory.SiegelWeilFormula.Gen.matV v (1 : Matrix (Fin n) (Fin n) (AE D)) = 1 := by
  unfold PositivityTheory.SiegelWeilFormula.Gen.matV
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem isCO_std {D : D7} {n : ℕ} (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)) :
    PositivityTheory.SiegelWeilFormula.Gen.IsCO (latLoc D.host.F (stdLattice D.host.E n) v).toAddSubgroup := by
  have e : (((latLoc D.host.F (stdLattice D.host.E n) v).toAddSubgroup : AddSubgroup _) :
      Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) =
      Set.univ.pi fun _ => (intLoc D.host.F D.host.E v : Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
    ext y
    simpa using (mem_latLoc_stdLattice (F := D.host.F) (E := D.host.E) (n := n) (v := v) (y := y))
  obtain ⟨hc, ho⟩ := GlobalTheory.ThK.isCompact_isOpen_intLoc (F := D.host.F) (E := D.host.E) v
  refine ⟨?_, ?_⟩
  · rw [e]; exact isOpen_set_pi Set.finite_univ fun _ _ => ho
  · rw [e]; exact isCompact_univ_pi fun _ => hc

end GlobalTheory.CompanionTheory.MM.LatCO

namespace GlobalTheory.CompanionTheory.MM

theorem latAt_isCO : ∀ (D : D7) (n : ℕ) (h : GL (Fin n) (AE D))
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F)),
    PositivityTheory.SiegelWeilFormula.Gen.IsCO (latAt h.1 v) := by
  intro D n h v
  haveI : IsTopologicalRing (HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) :=
    GlobalTheory.Doubling.isTopologicalRing_tens
  set M := PositivityTheory.SiegelWeilFormula.Gen.matV v h.1 with hM
  set M' := PositivityTheory.SiegelWeilFormula.Gen.matV v (h⁻¹).1 with hM'
  have h1 : M * M' = 1 := by
    rw [hM, hM', ← LatCO.matV_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, LatCO.matV_one]
  have h2 : M' * M = 1 := by
    rw [hM, hM', ← LatCO.matV_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, LatCO.matV_one]
  let φ : (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) ≃ₜ
      (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E) :=
    { toFun := fun y => M *ᵥ y
      invFun := fun y => M' *ᵥ y
      left_inv := fun y => by simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
      right_inv := fun y => by simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
      continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
      continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id }
  have e : ((latAt h.1 v : AddSubgroup _) : Set (Fin n → HeckeCharacterZeroLocus.SiegelWeilU.Fv D.host.F v ⊗[D.host.F] D.host.E)) =
      φ '' ((latLoc D.host.F (stdLattice D.host.E n) v).toAddSubgroup : AddSubgroup _) := by
    ext y
    simp only [latAt, AddSubgroup.coe_map, Set.mem_image]
    rfl
  obtain ⟨ho, hc⟩ := LatCO.isCO_std (D := D) (n := n) v
  refine ⟨?_, ?_⟩
  · rw [e]; exact φ.isOpenMap _ ho
  · rw [e]; exact hc.image φ.continuous

end GlobalTheory.CompanionTheory.MM
