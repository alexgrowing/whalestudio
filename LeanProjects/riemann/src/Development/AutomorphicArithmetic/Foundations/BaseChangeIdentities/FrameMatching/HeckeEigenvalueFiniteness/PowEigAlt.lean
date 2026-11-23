import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameL
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.Target

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
  PositivityTheory.Rg.BcB.F.Choice PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcN.F2
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence

def LocC : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ι : Type) [Fintype ι] (a : ι → ℕ)
  (Z : ∀ i, Set ((Fin (a i) → ℂˣ) × (Fin (n - a i) → ℂˣ))) (ξ : Fin n → ℂˣ), (∀ i, a i ≤ n) → (∀ i, (Z i).Finite) → PositivityTheory.Rg.BcB.N3.Mono ξ →
  ∃ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n 2) ∧ evalGL c (chiN w ξ) = 1 ∧
    ∀ i (s : Finset (Fin (n / 2))) (h : LocData.admitted n (a i) s) (ξa : Fin (a i) → ℂˣ) (ξb : Fin (n - a i) → ℂˣ), (ξa, ξb) ∈ Z i →
      (c.sum fun x t => t * (-qh w) ^ (-vRes n (a i) (lOf x) s) * ev2 w ξa ξb (restr x _ h.2.1) (restr x _ h.2.2)) ≠ 0 →
      PositivityTheory.Rg.BcB.N3.Mono ξa ∧ PositivityTheory.Rg.BcB.N3.Mono ξb ∧
        (Finset.univ.val.map ξa).map (· * (-1 : ℂˣ) ^ (n - a i)) + (Finset.univ.val.map ξb).map (· * (-1 : ℂˣ) ^ a i) =
          Finset.univ.val.map ξ

def LocE : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w →
  ∀ (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n →
  GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) (K'.subgroupOf (UL n w)) →
  ∀ σ : SmIrr (UL n w), fixed σ.ρ (K'.subgroupOf (UL n w)) ≠ ⊥ → ∀ (k : ℕ) (D : Fin k → Pre E n),
  ∃ (e : GLw n w → ℂ) (P : SmIrr (GLw n w)), IsHk K' e ∧ IsHecke (K'.subgroupOf (UL n w)) (fun y => e y.1) ∧
    (∀ π : Submodule ℂ (UA E n → ℂ), IsCompU π w σ → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ) ∧
    (∃ y : fixed σ.ρ (K'.subgroupOf (UL n w)), y ≠ 0 ∧ locOp σ (K'.subgroupOf (UL n w)) (fun y => e y.1) y = y) ∧
    ∀ j, ∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (D j) w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0

def MuVal : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ w : Pl E, ¬ IsSplitAt w → ∀ k : ℕ, (μ ^ k).val w = (-1 : ℂˣ) ^ k

def PowEig : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (σ : SmIrr (UL n w))
  (K' : Subgroup (UL n w)), GlobalTheory.BCT.IsLevel (MonoidHom.id _) (KL n w) K' → ∀ g : UL n w → ℂ, IsHecke K' g →
    ∀ y : fixed σ.ρ K', locOp σ K' g y = y → ∀ m : ℕ, locOp σ K' (U.lpow K' g m) y = y

end UpperTheory.HeckeLevelFrameExistence

end
