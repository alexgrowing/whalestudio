import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import CompanionTheory.EightfoldTheory.ZeroLevelTheory.LocalLanglands.Imports
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

section Laws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem lawsT_iff (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (rc : IrrGL (w.adicCompletion E) → WD h) : LawsT a ha rc ↔ UpperTheory.Zero.LLC.LawsT a ha rc :=
  ⟨fun H => ⟨H.1, H.2, H.3, H.4, H.5, H.6, H.7, H.8, H.9, H.10, H.11, H.12⟩,
   fun H => ⟨H.1, H.2, H.3, H.4, H.5, H.6, H.7, H.8, H.9, H.10, H.11, H.12⟩⟩

theorem isRecT_iff (rc : IrrGL (w.adicCompletion E) → WD h) : IsRecT h rc ↔ UpperTheory.Zero.LLC.IsRecT h rc :=
  ⟨fun ⟨a, ha, H⟩ => ⟨a, ha, (lawsT_iff a ha rc).1 H⟩, fun ⟨a, ha, H⟩ => ⟨a, ha, (lawsT_iff a ha rc).2 H⟩⟩

end Laws

end GlobalTheory.RecT
