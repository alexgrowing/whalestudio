import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapInjectiveBijectiveNorms
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.HerrCohomologyExtensions
import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator

noncomputable section

namespace Formalism.MainNotions.HerrComplexNaturality

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

def FN (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.adm9 D HW F

def HerrNaturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm17 D HW F

def AdmNat (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F

def HerrNaturalityTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmNat D HW F → HerrNaturality D HW F

theorem herr_naturality_theorem_holds (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrNaturalityTheorem D HW F := by
  intro h l _ K s LL g
  refine ⟨(h l K s LL g).2.2, ?_⟩
  intro hg T T' f pr pr' hp
  have h1 := (h l K s LL g).1 hg T
  exact (h1.2.2 T' f pr pr' hp).symm

theorem herr_naturality_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrNaturality D HW F ↔ Formalism.MainNotions.HerrCohomologyExtensions.adm18 D HW F := Iff.rfl

def HerrExtensionClass (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := Formalism.MainNotions.RamifiedCoefficientChains.adm16 D HW F

def AdmExt (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := FN D HW F ∧ Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.WachCharacterisation D HW F

def HerrExtensionTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExt D HW F → HerrExtensionClass D HW F

theorem herr_extension_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : HerrExtensionClass D HW F ↔ Formalism.MainNotions.HerrCohomologyExtensions.adm16 D HW F := Iff.rfl

def HerrExtensionUpToUnit (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    Formalism.MainNotions.ElementDenominator.coreHerrExt ((HW l).W K s LL h) ∧ Formalism.MainNotions.ElementDenominator.coreHerrExtΔ ((HW l).W K s LL h)

def AdmExtU (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := HerrExtensionClass D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.WachLatticeFreeGlobal D HW F ∧ Formalism.MainNotions.DeltaInvariantLattices.ConclusionE D HW F

def HerrExtensionUnitTheorem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop := AdmExtU D HW F → HerrExtensionUpToUnit D HW F

theorem herr_class_maps_of_naturality (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h1 : HerrNaturality D HW F) (h2 : HerrExtensionUpToUnit D HW F) : Formalism.MainNotions.ElementDenominator.HerrClassMapsLocal D HW F :=
  fun l _ K s LL h => ⟨(h1 l K s LL h).1, (h1 l K s LL h).2, (h2 l K s LL h).1, (h2 l K s LL h).2⟩

theorem herr_class_maps_iff (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Formalism.MainNotions.ElementDenominator.HerrClassMapsLocal D HW F ↔ HerrNaturality D HW F ∧ HerrExtensionUpToUnit D HW F :=
  ⟨fun H => ⟨fun l _ K s LL h => ⟨(H l K s LL h).1, (H l K s LL h).2.1⟩,
    fun l _ K s LL h => (H l K s LL h).2.2⟩, fun H => herr_class_maps_of_naturality D HW F H.1 H.2⟩

end Formalism.MainNotions.HerrComplexNaturality
