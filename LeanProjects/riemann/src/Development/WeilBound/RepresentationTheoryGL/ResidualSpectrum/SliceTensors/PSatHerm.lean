import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLExistsLocalComponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterGLStarEqInvOfUnitarisableStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.CuspDiscrete

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace PositivityTheory.Rg.Rs

namespace SatakeHermitian

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem isUnitarisable_locRepD {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V)
    (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.LGrp.IsUnitarisable (GlobalTheory.DiscLocEx.locRepD hV.stable w) := by
  letI : MeasurableSpace (GA E N) := borel _
  haveI : BorelSpace (GA E N) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin N → Fin N → Ad E))
  haveI : LocallyCompactSpace (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GA E N) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin N → Fin N → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin N) (Fin N) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E N) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := GlobalTheory.DiscreteUnit.countable_latticeGL (E := E) (N := N)
  haveI : Infinite (w.adicCompletion E) := .of_injective _ (algebraMap E _).injective
  refine GlobalTheory.DiscreteUnit.isUnitarisable_of_embedding (Γ := latticeGL E N) (GlobalTheory.DiscLocEx.locRepD hV.stable w)
    (fun g => finGL E N (locGL E N w g)) (fun g => ?_)
    ((Sm E N).subtype.comp V.subtype) (Subtype.val_injective.comp Subtype.val_injective)
    (fun v => GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E N v.1 (hV.aut _ v.2).level)
    (fun v => GlobalTheory.DiscreteUnit.left_latticeGL (hV.aut _ v.2) (hV.sqInt _ v.2)) (fun v => (hV.sqInt _ v.2).2)
    fun g v x => rfl
  exact GlobalTheory.DiscreteUnit.modular_eq_one ((finGL E N).comp (locGL E N w))
    (fun g => (congrArg (finGL E N) (GlobalTheory.DiscreteUnit.cornerGL_transInv (sLoc E w) g)).trans
      (GlobalTheory.DiscreteUnit.cornerGL_transInv (sFin E) _)) g

theorem herm_of_star {B : Multiset ℂˣ} (h : B.map star = B.map (·⁻¹)) : B.map (fun b => (star b)⁻¹) = B := by
  have e := congrArg (Multiset.map (fun b : ℂˣ => b⁻¹)) h
  rw [Multiset.map_map, Multiset.map_map] at e
  simpa [Function.comp_def] using e

theorem herm_of_isSatVec {N : ℕ} {V : Submodule ℂ (Sm E N)} (hV : IsDiscrete V) {w : HeightOneSpectrum (𝓞 E)}
    {B : Multiset ℂˣ} {φ : Sm E N} (hφ : φ ∈ V)
    (h : GlobalTheory.LFun.IsSatVecGL w ((finRep E N).comp (locGL E N w)) φ B) : B.map (fun b => (star b)⁻¹) = B := by
  have h' : GlobalTheory.LFun.IsSatVecGL w (GlobalTheory.DiscLocEx.locRepD hV.stable w) ⟨φ, hφ⟩ B :=
    GlobalTheory.LFun.IsSatVecGL.of_map (ρ' := (finRep E N).comp (locGL E N w)) V.subtype (fun _ _ => rfl)
      Subtype.val_injective h
  exact herm_of_star (GlobalTheory.T.satakeParameterGL_star_eq_inv_of_unitarisable E w N V _ _ B (isUnitarisable_locRepD hV w) h')

end SatakeHermitian

open SatakeHermitian in
theorem satHerm_holds : SatHerm := by
  intro E _ _ _ N w B
  refine ⟨fun V hV hS => ?_, fun π hN hu hn hB => ?_⟩
  · obtain ⟨φ, hφ, h⟩ := hS.1
    exact herm_of_isSatVec hV hφ h
  · have hD : IsDiscrete π.V := PositivityTheory.RSHS.L1.cuspDiscrete E N hN π hu hn
    obtain ⟨x, hx⟩ := GlobalTheory.LFun.HasSatGL.exists_vec hB
    have h1 := hx.map (ρ' := (finRep E N).comp (locGL E N w)) π.V.subtype (fun _ _ => rfl)
      (fun e => hx.1 (Subtype.ext e))
    exact herm_of_isSatVec hD x.2 h1

end PositivityTheory.Rg.Rs

end
