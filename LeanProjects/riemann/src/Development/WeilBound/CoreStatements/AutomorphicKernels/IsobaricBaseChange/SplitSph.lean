import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.FixedVectorVanishing.FixedEqZeroOfMemISup

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace GlobalTheory.PfBCI

namespace SplitSph

section Abstract

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem isIrreducible_comp_surj {H : Type} [Group H] (σ : Representation ℂ H W) (p : G →* H)
    (hp : Function.Surjective p) (hσ : σ.IsIrreducible) : Representation.IsIrreducible (σ.comp p) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 hσ
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun Y hY => h1 Y fun g v hv => ?_⟩
  obtain ⟨x, rfl⟩ := hp g
  exact hY x v hv

end Abstract

end SplitSph

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem split_spherical {π : Submodule ℂ (UA E n → ℂ)} (hπ : IsAutRepU π) {w : HeightOneSpectrum (𝓞 E)} (hs : IsSplitAt w)
    (P : SmIrr (GL (Fin n) (w.adicCompletion E)))
    (hc : IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ) (hu : IsUnramU π w) :
    GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w n) :=
  PositivityTheory.Rg.BcB.Loc.split_spherical2 hπ hs P hc hu

end GlobalTheory.PfBCI

end
