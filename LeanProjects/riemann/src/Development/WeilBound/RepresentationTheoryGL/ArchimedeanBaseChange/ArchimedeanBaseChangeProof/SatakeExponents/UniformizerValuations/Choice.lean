import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameReading.JoinType
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.PeakCone

noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.One PositivityTheory.Rg.BcB.F.F5
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail
open scoped Classical TensorProduct
set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Choice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

structure Shuf (n : ℕ) where
  a : ℕ
  b : ℕ
  e : Fin a ⊕ Fin b ≃ Fin n
  monoL : StrictMono fun i : Fin a => e (Sum.inl i)
  monoR : StrictMono fun j : Fin b => e (Sum.inr j)
  eps : Fin n → ℂˣ

def resL (s : Shuf n) (x : Fin n → ℤ) : Fin s.a → ℤ := fun i => x (s.e (Sum.inl i))
def resR (s : Shuf n) (x : Fin n → ℤ) : Fin s.b → ℤ := fun j => x (s.e (Sum.inr j))

def qU (w : Pl E) (k : ℤ) : ℂˣ := if h : (qh w : ℂ) ≠ 0 then Units.mk0 _ h ^ k else 1

def chiOf (w : Pl E) (s : Shuf n) (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ) : Fin n → ℂˣ :=
  fun k => s.eps k * Sum.elim (fun i => ξa i * qU w ((s.a : ℤ) - 1 - 2 * (i : ℕ)))
    (fun j => ξb j * qU w ((s.b : ℤ) - 1 - 2 * (j : ℕ))) (s.e.symm k)

def ChiEval : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (s : Shuf n)
  (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ) (x : Fin n → ℤ),
  ((∏ k, s.eps k ^ x k : ℂˣ) : ℂ) * ev2 w ξa ξb (resL s x) (resR s x) = ((∏ k, chiOf w s ξa ξb k ^ x k : ℂˣ) : ℂ)

def GapRes : Prop := ∀ (n : ℕ) (s : Shuf n) (x : Fin n → ℤ), x ∈ coneGL n 2 → Gap (resL s x) ∧ Gap (resR s x)

def ChoiceT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (ι : Type) [Fintype ι]
  (s : ι → Shuf n) (Z : ∀ i, Set ((Fin (s i).a → ℂˣ) × (Fin (s i).b → ℂˣ))) (α : Fin n → ℂˣ), (∀ i, (Z i).Finite) →
  ∃ c : (Fin n → ℤ) →₀ ℂ, (↑c.support ⊆ coneGL n 2) ∧ evalGL c α = 1 ∧
    ∀ i, ∀ p ∈ Z i, (c.sum fun x a => a * ((∏ k, (s i).eps k ^ x k : ℂˣ) : ℂ) *
        ev2 w p.1 p.2 (resL (s i) x) (resR (s i) x)) ≠ 0 → chiOf w (s i) p.1 p.2 = α

def TargetOK (w : Pl E) (s : Shuf n) (ξa : Fin s.a → ℂˣ) (ξb : Fin s.b → ℂˣ) (α : Fin n → ℂˣ) : Prop :=
  chiOf w s ξa ξb = α

def ChoiceS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (GLw n w)),
  IsOpen (K' : Set (GLw n w)) → IsCompact (K' : Set (GLw n w)) → ∀ P : SmIrr (GLw n w), (∃ v ∈ fixed P.ρ K', v ≠ 0) →
  ∀ (k : ℕ) (D : Fin k → Pre E n),
  ∃ e : GLw n w → ℂ, IsHk K' e ∧ (∃ v₀ ∈ fixed P.ρ K', ∃ l : _ →ₗ[ℂ] ℂ, l v₀ = 1 ∧ ∀ v ∈ fixed P.ρ K', hk P.ρ K' e v = l v • v₀) ∧
    ∀ j, ∀ τ : SmIrr (GLw n w), GlobalTheory.SmGL.IsSubquotient τ.ρ (prodAt (D j) w) → IsEmpty (τ.ρ.Equiv P.ρ) →
      ∀ v ∈ fixed τ.ρ K', hk τ.ρ K' e v = 0

def ChoiceM : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (GLw n w))
  (k : ℕ) (D : Fin k → Pre E n), (∀ j, FiniteDimensional ℂ (fixed (prodAt (D j) w) K')) →
  ∃ m : ℕ, ∀ j, Module.finrank ℂ (fixed (prodAt (D j) w) K') < m

def ChoiceTOf : Prop := PeakCone → ChiEval → GapRes → ChoiceT

end PositivityTheory.Rg.BcB.F.Choice

end
