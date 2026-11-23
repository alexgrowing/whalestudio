import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffOfContinuousOneParameter

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.ArchCancel

theorem eq_of_tens_eq : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (r : (κ → AF F) → ℂ),
    (∀ x z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z → r (x + z) = r x) → (∃ x, r x ≠ 0) →
    ∀ f₁ f₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₂ r → f₁ = f₂ := by
  intro F _ _ κ _ r hr hne f₁ f₂ h
  obtain ⟨x₀, hx₀⟩ := hne
  refine DFunLike.ext f₁ f₂ fun y => ?_
  let z : κ → AF F := fun i =>
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)), 0)
  have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
    intro u hu
    funext i
    have hu1 : u.1 = 0 := by
      have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
      exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
    show u * z i = 0
    refine Prod.ext ?_ ?_
    · show u.1 * (z i).1 = 0
      rw [hu1, zero_mul]
    · show u.2 * (z i).2 = 0
      show u.2 * 0 = 0
      rw [mul_zero]
  have hev : (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x₀ + z) i)) = y := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x₀ i).1 +
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i))) = y i
    rw [map_add, RingEquiv.apply_symm_apply]
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i) + (y i - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i)) = y i
    exact add_sub_cancel _ _
  have h2 := congrFun h (x₀ + z)
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens] at h2
  rw [hev, hr x₀ z hz] at h2
  exact mul_right_cancel₀ hx₀ h2

end GlobalTheory.ArchCancel
