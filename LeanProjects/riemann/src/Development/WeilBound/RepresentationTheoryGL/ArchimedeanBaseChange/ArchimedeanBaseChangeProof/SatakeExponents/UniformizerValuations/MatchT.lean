import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.SymIdx
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ExistsEigv

noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.MT

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

open PositivityTheory.Rg.BcB.F.Eig (lconv)
open PositivityTheory.Rg.BcB.F.U (lpow lone)
open PositivityTheory.Rg.BcN.F2 (mconv)
open Formalism.UG (ordL)

def lone2 (a b : ℕ) (w : Pl E) : GLw a w × GLw b w → ℂ :=
  (((iwGL a w).prod (iwGL b w) : Subgroup (GLw a w × GLw b w)) : Set (GLw a w × GLw b w)).indicator
    fun _ => ((((iwGL a w).prod (iwGL b w)).relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : ℕ) : ℂ)

def mpow (w : Pl E) (f : GLw a w × GLw b w → ℂ) : ℕ → GLw a w × GLw b w → ℂ
  | 0 => lone2 a b w
  | k + 1 => mconv f (mpow w f k)

def admitted (n a : ℕ) (s : Finset (Fin (n / 2))) : Prop :=
  s.card = a / 2 ∧ sᶜ.card = (n - a) / 2 ∧ a % 2 + (n - a) % 2 = n % 2 ∧
    (symIdx n (a % 2 = 1) s).card = a ∧ (symIdx n ((n - a) % 2 = 1) sᶜ).card = n - a

def entT (n : ℕ) (w : Pl E) (ϖ : (w.adicCompletion E)ˣ) (a : ℕ) {J : Type} [Fintype J] (c : J → ℂ) (x : J → Fin n → ℤ)
    (s : Finset (Fin (n / 2))) (y : GLw a w × GLw (n - a) w) : ℂ :=
  if h : admitted n a s then
    ∑ j, c j * (-qh w) ^ (-vRes n a (lOf (x j)) s) *
      dcos a w (tdiag ϖ (restr (x j) _ h.2.2.2.1)) y.1 * dcos (n - a) w (tdiag ϖ (restr (x j) _ h.2.2.2.2)) y.2
  else 0

def cR (n a : ℕ) (w : Pl E) (b : GLw n w) : ℂ :=
  (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ * ((iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) : ℕ) *
    ((iwGL (n - a) w).relIndex (GlobalTheory.LFun.KGL w (n - a)) : ℕ)

def MatchT : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ w : Pl E, ¬ IsSplitAt w → ∀ (n a : ℕ), a ≤ n → ∀ (b : GLw n w), IsWitt n w b →
    ∀ ϖ : (w.adicCompletion E)ˣ, IsUnifAt ϖ → ∀ (J : Type) [Fintype J] (c : J → ℂ) (x : J → Fin n → ℤ),
      (∀ j, StrictAnti (x j) ∧ Cone (lOf (x j))) → ∀ k : ℕ, 1 ≤ k →
      Match n a (n - a) w 1 (lpow (iwU n w b) (fun γ => ∑ j, c j * fU n w b ϖ (lOf (x j)) γ) k)
        (fun y => cR n a w b ^ k * ∑ s, mpow w (entT n w ϖ a c x s) k y)

def FUMul : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ (n : ℕ) (b : GLw n w),
    IsWitt n w b → ∀ ϖ : (w.adicCompletion E)ˣ, IsUnifAt ϖ → ∀ l l' : Fin (n / 2) → ℤ, Cone l → Cone l' →
      lconv (fU n w b ϖ l) (fU n w b ϖ l') = fun γ => (((iwU n w b).relIndex (KL n w) : ℕ) : ℂ)⁻¹ * fU n w b ϖ (l + l') γ

def DcosMul : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (ϖ : (w.adicCompletion E)ˣ), IsUnifAt ϖ →
    ∀ (a b : ℕ) (x x' : Fin a → ℤ) (y y' : Fin b → ℤ), Antitone x → Antitone x' → Antitone y → Antitone y' →
      mconv (fun m : GLw a w × GLw b w => dcos a w (tdiag ϖ x) m.1 * dcos b w (tdiag ϖ y) m.2)
        (fun m => dcos a w (tdiag ϖ x') m.1 * dcos b w (tdiag ϖ y') m.2) =
      fun m => ((((iwGL a w).prod (iwGL b w)).relIndex ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)) : ℕ) : ℂ)⁻¹ *
        (dcos a w (tdiag ϖ (x + x')) m.1 * dcos b w (tdiag ϖ (y + y')) m.2)

def MatchLin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (w : Pl E) (μ : (w.adicCompletion E)ˣ →* ℂˣ)
    (J : Type) [Fintype J] (c : J → ℂ) (f : J → UL n w → ℂ) (φ : J → GLw a w × GLw b w → ℂ),
    (∀ j, Continuous (f j) ∧ HasCompactSupport (f j) ∧ Continuous (φ j) ∧ HasCompactSupport (φ j)) →
    (∀ j, Match n a b w μ (f j) (φ j)) → Match n a b w μ (fun γ => ∑ j, c j * f j γ) (fun y => ∑ j, c j * φ j y)

def MatchTOf : Prop := M4 → FUMul → DcosMul → MatchLin → MatchT

def CtMul : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w →
    ∀ μ : (w.adicCompletion E)ˣ →* ℂˣ, (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) →
    ∀ f g : UL n w → ℂ, IsHecke (KL n w) f → IsHecke (KL n w) g →
      ctMu (Nat.add_sub_cancel' ha) w μ (lconv f g) =
        mconv (ctMu (Nat.add_sub_cancel' ha) w μ f) (ctMu (Nat.add_sub_cancel' ha) w μ g)

def MatchSplit : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a : ℕ) (ha : a ≤ n) (w : Pl E), IsSplitAt w →
    ∀ μ : (w.adicCompletion E)ˣ →* ℂˣ, (∀ u : (w.adicCompletion E)ˣ, ordL (u : w.adicCompletion E) = 0 → μ u = 1) →
    ∀ f : UL n w → ℂ, IsHecke (KL n w) f → ∀ k : ℕ, 1 ≤ k →
      Match n a (n - a) w μ (lpow (KL n w) f k) (mconv (ctMu (Nat.add_sub_cancel' ha) w μ f)
        (Nat.rec (ctMu (Nat.add_sub_cancel' ha) w μ (lone (KL n w))) (fun _ g => mconv (ctMu (Nat.add_sub_cancel' ha) w μ f) g) (k - 1)))

def MatchSplitOf : Prop := M3 → CtMul → MatchSplit

end PositivityTheory.Rg.BcB.F.MT

end
