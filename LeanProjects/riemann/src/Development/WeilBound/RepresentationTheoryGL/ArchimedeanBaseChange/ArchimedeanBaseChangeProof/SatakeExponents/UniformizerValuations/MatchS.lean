import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.MS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def gpow {w : Pl E} (f : GLw n w → ℂ) : ℕ → GLw n w → ℂ
  | 0 => f
  | N + 1 => gconv f (gpow f N)

def mpow {w : Pl E} (X : Finset (GLw n w)) (Φ : GLw n w → GLw n w → GLw a w × GLw b w → ℂ) :
    ℕ → GLw n w → GLw n w → GLw a w × GLw b w → ℂ
  | 0 => Φ
  | N + 1 => fun x z m => ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (Φ x y) (mpow X Φ N y z) m

def splitPlaceMackeyTraceTwist (h : a + b = n) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ) (X : Finset (GLw n w)) (f : GLw n w → ℂ) (N : ℕ)
    (m : GLw a w × GLw b w) : ℂ :=
  (μ ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) *
    (((X.card : ℂ))⁻¹ * ∑ x ∈ X, mpow X (phi3 h w f) N x x m)

def SplitPlaceConstantTermPowers : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n →
    (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') →
    ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') →
    ∀ f : GLw n w → ℂ, IsHk K' f → ∀ (N : ℕ) (m : GLw a w × GLw b w),
      ct h w (gpow f N) m = ((X.card : ℂ))⁻¹ * ∑ x ∈ X, mpow X (phi3 h w f) N x x m

def MatchSplitPlace : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n a : ℕ) (w : Pl E), IsSplitAt w →
    (∀ g : GLw n w, g ∈ UL n w) → ∀ (μ : (w.adicCompletion E)ˣ →* ℂˣ) (K' : Subgroup (GLw n w)),
    IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') →
    IsLevel (MonoidHom.id _) (KL n w) (K'.subgroupOf (UL n w)) →
    ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') →
    ∀ f : GLw n w → ℂ, IsHk K' f → ∀ (ha : a ≤ n) (N : ℕ),
      Match n a (n - a) w μ (fun u : UL n w => gpow f N (u : GLw n w)) (splitPlaceMackeyTraceTwist (Nat.add_sub_cancel' ha) w μ X f N)

end PositivityTheory.Rg.BcB.F.MS

end
