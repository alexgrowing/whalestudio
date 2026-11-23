import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.UnlLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TameSuppUniqueHolds
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo
import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.Outright
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProduct
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredity

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.Gal.TypesAndIwahori

theorem unlinked_of_typeVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N c : ℕ) (d : Fin c → ℕ) (hd : ∑ b, d b = N) (hpos : ∀ b, 0 < d b) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) (hg : IsGeneric π)
    (θ : Fin c → 𝓀[k]ˣ →* ℂˣ) (hθ : Function.Injective θ) (hv : HasTypeVec π (stdBlocks d hd) θ)
    (s : Multiset (IrrGL k)) (hS : HasSupport π s) : GlobalTheory.RoadU.Unlinked s :=
  unlinked_of_tameSphProd loc_holds GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds PositivityTheory.Exh.langlandsMultisegments_holds
    PositivityTheory.Exh.standardCosocleGL_holds
    (GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity _ (GlobalTheory.CompanionTheory.Rodier.whitHeredity _)) hg hθ
    (topB_holds k N c d hd hpos V π hs hi θ hθ hv) hS

end UpperTheory.Gal.TypesAndIwahori
