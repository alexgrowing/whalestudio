import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Clause3Asc
import Development.WeilBound.CoreStatements.AutomorphicKernels.ResidualSpectrumHilbertSum.ResidualSpectrumTensors.LocalComponentGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteAutomorphicRepGLLocalComponentIsUnitaris
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.IwasawaCompletion.SpehCosocleUc
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.BernsteinExponentBounds.ExpBound
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.IsGenericOfEquiv
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.SegmentJacquetSubquotients.SegmentRepresentation
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.GenericUnlinkedGLOfSegRep2
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.LanglandsMultisegmentsOfSeg

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.Rs.C3

theorem isSpeh_of_quot {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (GL (Fin N) k) V}
    (hi : ρ.IsIrreducible) (x : GlobalTheory.LocGL.IrrGL k) (d : ℕ)
    (hd : ∑ i, (GlobalTheory.LocGL.spehFactor x d i).1 = N)
    (hc : ∃ (W : Type) (_ : AddCommGroup W) (_ : Module ℂ W) (τ : Representation ℂ (GL (Fin N) k) W),
      GlobalTheory.LocGL.IsCosocle τ (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd))
    (f : (GlobalTheory.LocGL.prodIrr (GlobalTheory.LocGL.spehFactor x d) hd).IntertwiningMap ρ) (hf : Function.Surjective f) :
    GlobalTheory.LocGL.IsSpeh x d ρ := by
  obtain ⟨W, _, _, τ, hτ⟩ := hc
  obtain ⟨e⟩ := hτ.equiv_of_surjective hi f hf
  exact ⟨hd, hτ.of_equiv e.symm (.refl _)⟩

theorem charZero_completion {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

theorem clause3Asc_of (hL : LocSub) (hD : LocDual) (hG : PositivityTheory.RgUd.Exp.GenUnitCC)
    (hSC : GlobalTheory.Published.StandardCosocleGL) : Clause3Asc := by
  intro E _ _ _ N a d V π hN hV hu hn hasc w σ σ' hσ hσ'
  obtain ⟨hd, f, hf⟩ := hL E N a d V π hN hV hasc w σ σ' hσ hσ'
  obtain ⟨hg, hun⟩ := PositivityTheory.RSHS.LocalComponentGL.generic_unitarisable hu hn hσ
  have hU' : IsUnitarisable σ'.ρ := GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E N V hV w σ' hσ'
  have := charZero_completion (E := E) w
  obtain ⟨hd', g, hg'⟩ := hD _ N d _ σ' hun hU' hd f hf
  exact isSpeh_of_quot σ'.irred _ d hd' (UC.spehCosocle_uc hG hSC _ hg hun d hd') g hg'

theorem clause3Asc_holds (hL : LocSub) (hD : LocDual) : Clause3Asc :=
  have hZ := PositivityTheory.RgGu.segmentRepresentation
  clause3Asc_of hL hD
    (PositivityTheory.RgUd.Exp.genUnitCCOf (fun k _ _ _ _ => PositivityTheory.RgUd.expBound k) (GlobalTheory.RgGu.genericUnlinkedGL_of_segRep2 hZ))
    (PositivityTheory.Exh.standardCosocleGL_of_seg hZ)

end PositivityTheory.Rg.Rs.C3

end
