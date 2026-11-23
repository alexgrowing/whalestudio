import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProofStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionUnitaryAndConjugationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryTransvectionEqLeviUnipotentProductStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Unf

theorem transvTrivial_of_descent (D : D7) (hD : Descent D) : GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvTrivial D := by
  intro S S₀ T ρ d ψ χS χT om hom μ 𝓕 hμ a v hv u hu x hx f hf
  obtain ⟨om₀, hom₀⟩ := (hD ψ S T χS χT om hom).1 S₀ ρ d
  obtain ⟨m, b, c, rfl, hdet, hk⟩ := GlobalTheory.T.unitaryTransvection_eq_leviUnipotentProduct D S S₀ ρ d _ v hv u hu
  obtain ⟨h1, h2, h3⟩ := hk T x hx
  have F := fun g hg => GlobalTheory.T.mixedModelFormulasWittSource_proof D ψ S S₀ T ρ d χS χT om om₀ hom hom₀ μ 𝓕 hμ g hg
  have hc := hom.om_pres (d.nC c, 1) f hf
  have hb := hom.om_pres (d.nB b, 1) _ hc
  have e : om (d.levi m * d.nB b * d.nC c, 1) f = om (d.levi m, 1) (om (d.nB b, 1) (om (d.nC c, 1) f)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, Prod.mk_mul_mk, Prod.mk_mul_mk,
      mul_one, mul_one]
  have hq : symplOH S T (d.extX T x) (d.extY T (x ⬝ c.1)) = 0 := h3
  rw [e, (F _ hb).levi, h1, (F _ hc).unip, h2, GlobalTheory.MixPer.heisO_zero, (F _ hf).centre, hq, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet]
  simp

theorem transvLemma_of_descent : ∀ D : D7, Descent D → GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvLemma D := fun D hD =>
  ⟨(GlobalTheory.T.unitaryTransvection_unitary_and_conjugation D).1, (GlobalTheory.T.unitaryTransvection_unitary_and_conjugation D).2, transvTrivial_of_descent D hD⟩

end GlobalTheory.Unf
