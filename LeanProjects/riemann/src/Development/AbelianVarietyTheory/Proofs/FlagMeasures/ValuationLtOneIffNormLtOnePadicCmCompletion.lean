import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys Formalism.MainNotions.ArithmeticCylinders
attribute [local instance] GlobalTheory.TypeRec.factG GlobalTheory.LabPin.instCM
open GlobalTheory.LabPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Filter Topology

namespace GlobalTheory.SlocVal

theorem tendsto_pow_map {A B : Type} [Ring A] [TopologicalSpace A] [Ring B] [TopologicalSpace B]
    (f : A →+* B) (hf : Continuous f) {x : A} (hx : Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => f x ^ n) atTop (𝓝 0) := by
  have h := (hf.tendsto 0).comp hx
  rw [map_zero] at h
  simpa [Function.comp_def, map_pow] using h

theorem continuous_symm {A B : Type} [Field A] [TopologicalSpace A] [IsTopologicalRing A]
    [SigmaCompactSpace A] [Field B] [TopologicalSpace B] [IsTopologicalRing B] [BaireSpace B]
    [T2Space B] (e : A ≃+* B) (he : Continuous e) : Continuous e.symm := by
  have ho : IsOpenMap e :=
    AddMonoidHom.isOpenMap_of_sigmaCompact e.toAddEquiv.toAddMonoidHom e.surjective he
  exact e.toEquiv.continuous_symm_iff.2 ho

end GlobalTheory.SlocVal

open GlobalTheory.SlocVal in

theorem GlobalTheory.valuation_lt_one_iff_norm_lt_one_of_continuous : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (g : ℕ) [Fact g.Prime] (i : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L) (j : ℚ_[g] ≃+* s.w.adicCompletion L), Continuous i → Continuous j → ∀ z : s.v.adicCompletion (maximalRealSubfield L), Valued.v z < 1 ↔ ‖j.symm (i z)‖ < 1 := by
  intro L _ _ _ s g _ i j hi hj z
  have := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion (maximalRealSubfield L) s.v
  have hj' : Continuous j.symm := continuous_symm j hj
  have hi' : Continuous i.symm := continuous_symm i hi
  have hφ : Continuous (i.trans j.symm) := hj'.comp hi
  have hψ : Continuous (i.trans j.symm).symm := hi'.comp hj
  have hz : Valued.v z < 1 ↔ ‖z‖ < 1 := (Valued.toNormedField.norm_lt_one_iff).symm
  rw [hz, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
  constructor
  · intro h
    exact tendsto_pow_map (i.trans j.symm).toRingHom hφ h
  · intro h
    have := tendsto_pow_map (i.trans j.symm).symm.toRingHom hψ h
    simpa using this
