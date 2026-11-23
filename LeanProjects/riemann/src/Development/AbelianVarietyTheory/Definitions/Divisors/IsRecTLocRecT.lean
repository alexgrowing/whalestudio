import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CuspRep.ParLawsT

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

def locRecT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) : IrrGL (w.adicCompletion E) → WD h :=
  (hT E Ω A w h).choose

theorem isRecT_locRecT (hT : UpperTheory.Zero.LLC.RecTExists) (h : IsPlaceOver A w) :
    UpperTheory.Zero.LLC.IsRecT h (locRecT hT h) :=
  (hT E Ω A w h).choose_spec

variable [IsTotallyComplex E]

def locParT (hT : UpperTheory.Zero.LLC.RecTExists) (π : CG E a) (h : IsPlaceOver A w) : WD h :=
  locRecT hT h ⟨a, ParLaws.toCl (π.loc w)⟩

end GlobalTheory.CuspRep.ParLawsT

namespace GlobalTheory.CuspRep.ParLawsT

open Formalism.BasicNotions

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R} {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

def locGT (hT : UpperTheory.Zero.LLC.RecTExists) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a) (w : PlE H) :
    WD (pl.2 w) :=
  haveI := host_isCMField H; locParT hT π.1 (pl.2 w)

end GlobalTheory.CuspRep.ParLawsT

end
