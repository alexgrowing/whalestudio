import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.QuadraticInductionGL2Alt

noncomputable section

open NumberField GlobalTheory.CuspRep UpperTheory.V.Z.Bc

namespace UpperTheory.V.Z.Inf

def InfOfLC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ (P : CuspSub K (2 * 2)) (π : CuspSub M 2), IndSys (CG.mk π).HasSat (CG.mk P).HasSat →
    ∀ (τ τ' : M →+* ℂ) (m m' : Multiset ℂ), τ ≠ τ' → τ.comp (algebraMap K M) = τ'.comp (algebraMap K M) →
      π.HasInfChar τ m → π.HasInfChar τ' m' → P.HasInfChar (τ.comp (algebraMap K M)) (m + m')

def IndWeakC : Prop :=
  ∀ (K M : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field M] [NumberField M] [IsTotallyComplex M] [Algebra K M],
    Module.finrank K M = 2 → ∀ π : CuspSub M 2, MixWtC K π → ∃ P : CuspSub K (2 * 2), IndSys (CG.mk π).HasSat (CG.mk P).HasSat

end UpperTheory.V.Z.Inf
