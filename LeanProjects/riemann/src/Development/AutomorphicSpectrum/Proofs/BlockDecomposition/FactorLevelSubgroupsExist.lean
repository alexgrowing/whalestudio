import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.FmTools
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinsumOutOfLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelFamInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPairProjection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfIsOpen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsBisExtra
open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.CG
open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.F.FA
open scoped Classical
open GlobalTheory.CompanionTheory.FinActS

noncomputable section

namespace GlobalTheory.CompanionTheory.PositionTest

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem eventually_factor {S : Set (Pl E)} {P : Slot S → Prop}
    (h₁ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S, P (Sum.inl ⟨w, hw⟩))
    (h₂ : ∀ᶠ w : Pl E in cofinite, ∀ hw : w ∈ S ∧ IsSplitAt w, P (Sum.inr ⟨w, hw⟩)) :
    ∀ᶠ i : Slot S in cofinite, P i := by
  have f₁ := Filter.eventually_cofinite.1 h₁
  have f₂ := Filter.eventually_cofinite.1 h₂
  refine Filter.eventually_cofinite.2 ?_
  refine (((f₁.preimage (Subtype.val_injective (p := fun w => w ∈ S)).injOn).image Sum.inl).union
    ((f₂.preimage (Subtype.val_injective (p := fun w => w ∈ S ∧ IsSplitAt w)).injOn).image Sum.inr)).subset ?_
  rintro (⟨w, hw⟩ | ⟨w, hw⟩) hi
  · exact Or.inl ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩
  · exact Or.inr ⟨⟨w, hw⟩, fun h => hi (h hw), rfl⟩

def localLevel {S : Set (Pl E)} (L₁ L₂ : ∀ w : Pl E, Subgroup (GLw a w × GLw b w)) :
    ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl)
  | .inl w => L₁ w.1
  | .inr w => L₂ w.1

theorem exists_factor_level₂ {S : Set (Pl E)} {φ₁ φ₂ : ∀ w : Pl E, LF a b w} (h₁ : IsTestP φ₁) (h₂ : IsTestP φ₂) :
    ∃ L : ∀ i : Slot S, Subgroup (GLw a i.pl × GLw b i.pl),
      (∀ i, IsOpen (L i : Set (GLw a i.pl × GLw b i.pl))) ∧ (∀ᶠ i in cofinite, L i = K2 a b i.pl) ∧
      (∀ i, ∀ k ∈ L i, ∀ x, sf φ₁ φ₂ i (x * k) = sf φ₁ φ₂ i x) ∧
      (∀ i : Slot S, HasCompactSupport (sf φ₁ φ₂ i)) ∧
      ∀ᶠ i : Slot S in cofinite, sf φ₁ φ₂ i = (K2 a b i.pl : Set (GLw a i.pl × GLw b i.pl)).indicator 1 := by
  obtain ⟨L₁, o₁, e₁, i₁⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₁
  obtain ⟨L₂, o₂, e₂, i₂⟩ := GlobalTheory.CompanionTheory.FinLevelTw.exists_level_of_test h₂
  have c₁ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₁
  have c₂ := GlobalTheory.CompanionTheory.FinTestTw.eventually_eq_indicator h₂
  refine ⟨localLevel L₁ L₂, ?_, ?_, ?_, ?_, ?_⟩
  · rintro (w | w)
    · exact o₁ w.1
    · exact o₂ w.1
  · exact eventually_factor (e₁.mono fun w h _ => h) (e₂.mono fun w h _ => h)
  · rintro (w | w) k hk x
    · exact (i₁ w.1 k hk x).2
    · exact (i₂ w.1 k hk x).2
  · rintro (w | w)
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₁ w.1
    · exact GlobalTheory.CompanionTheory.FinTestTw.hasCompactSupport_loc h₂ w.1
  · exact eventually_factor (c₁.mono fun w h _ => h) (c₂.mono fun w h _ => h)

end GlobalTheory.CompanionTheory.PositionTest

end
