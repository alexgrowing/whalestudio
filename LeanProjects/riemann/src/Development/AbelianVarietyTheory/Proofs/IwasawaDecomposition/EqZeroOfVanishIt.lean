import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IoUniq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TprodEqZeroOfKFinOff
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.KFiniteSpanLeSpanRealIntertwinerValues
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.StepUniq

open Classical in

theorem eq_zero_of_vanish_it : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (t : T) (k : ℕ), k + 1 < D.R.m → ∀ u : MMap (R.MY k), Formalism.IndefR.Eqv.ContAt (R.MY k) u → (∀ φ w, PiTensorProduct.lift u (R.ItY k φ w) = 0) → u = 0 := by
  intro hDS hHC D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH t k hk u hc hv
  have hB := hP.char.base
  have hCh : R.toRealDat.IsChain := RealDat.chain_of_weak hB.chain hH.aux.ex
  have hok := GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A3.A Ks R.toRealDat hB.lev hB.models.inf hCh.ωY hCh.ωX hCh.vY hCh.vX
  obtain ⟨hw, hvv⟩ := hok.1 t ⟨k, by omega⟩ hk
  have hIt := hCh.ItY t k hk
  have hle := GlobalTheory.ItOnto.kfinSpan_le_span_it hDS hHC D _ _ _ _ (R.MY k) (R.MY (k + 1)) R.θ R.ψ _ _
    (R.ωY t k) (R.vY t k) (R.ItY k) hB.models.inf hw hvv hIt
  have hx : ∀ x, (LinearMap.proj x : (GA D (Yc D k) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ PiTensorProduct.lift u = 0 := by
    intro x
    refine GlobalTheory.Core.Mi.eq_zero_of_sepCont hHC D _ _ (R.MY k) _ ?_ ?_
    · intro τ v
      obtain ⟨ℓ, hℓ, he⟩ := hc τ v x
      refine ⟨ℓ, hℓ, fun w => ?_⟩
      rw [he w]
      simp [PiTensorProduct.lift.tprod]
    · intro v hv'
      have hmem := hle (Submodule.subset_span ⟨v, fun τ => Submodule.subset_span (hv' τ), rfl⟩)
      have hker : Submodule.span ℂ {w | ∃ P, ∃ y ∈ Submodule.span ℂ {w | ∃ v, (∀ τ, ((v τ : (R.MY (k + 1)).sm τ) :
          (R.MY (k + 1)).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin (R.MY (k + 1)) τ) ∧ w = PiTensorProduct.tprod ℂ v},
            w = (R.ItY k P) y} ≤ LinearMap.ker ((LinearMap.proj x : (GA D (Yc D k) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ
              PiTensorProduct.lift u) := by
        rw [Submodule.span_le]
        rintro _ ⟨P, y, -, rfl⟩
        simp [hv P y]
      exact hker hmem
  have h0 : PiTensorProduct.lift u = 0 := by
    ext v x
    have := congrArg (fun Λ => Λ (PiTensorProduct.tprod ℂ v)) (hx x)
    simpa using this
  have : u = PiTensorProduct.lift.symm (PiTensorProduct.lift u) := by simp
  rw [this, h0, map_zero]

end GlobalTheory.Mem.R3.StepUniq
