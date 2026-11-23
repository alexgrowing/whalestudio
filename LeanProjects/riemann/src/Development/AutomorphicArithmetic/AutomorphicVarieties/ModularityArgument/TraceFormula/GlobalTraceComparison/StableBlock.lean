import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.BindPow
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison

def RunC : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    (∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ w : Pl E, ¬ IsSplitAt w → IsUnramU σ w) ∧
      ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ),
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B) ∨
    ∃ D : CD E n, ¬ D.Has π ∧ ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

def G2s : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ lam : InfinitePlace E → DomWeight n, ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℕ) (l₁ : ∀ i, InfinitePlace E → DomWeight (a i))
    (l₂ : ∀ i, InfinitePlace E → DomWeight (n - a i)) (sg : ι → ℤˣ),
    (∀ i, a i ≤ n ∧ ∀ v, (infOfWeight (l₁ i v)).map (· + ((n - a i : ℕ) : ℂ) * (e v : ℂ) / 2) +
      (infOfWeight (l₂ i v)).map (· + (a i : ℂ) * (e v : ℂ) / 2) = infOfWeight (lam v)) ∧
    (∃ i, a i = n ∧ sg i = 1 ∧ ∀ j, a j = n → j = i) ∧ (∃ i, a i = 0 ∧ sg i = 1 ∧ ∀ j, a j = 0 → j = i) ∧
    ∀ S : Set (Pl E), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)) (f : ∀ w : Pl E, UL n w → ℂ)
      (φ : ∀ a (w : Pl E), GLw a w × GLw (n - a) w → ℂ), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
      GlobalTheory.BCT.IsTest (KL n) K' f → (∀ a ≤ n, IsTestP (φ a) ∧ ∀ w ∈ S, Match n a (n - a) w (μ.loc w) (f w) (φ a w)) →
      geomU S lam f = ∑ i, ((sg i : ℤ) : ℂ) * geomSt2 S (l₁ i) (l₂ i) (φ (a i))

def MuEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∃ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e

def MatchUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∀ n a b : ℕ, a + b = n →
  Match n a b w 1 ((KL n w : Set (UL n w)).indicator 1) ((K2 a b w : Set _).indicator 1)

def MatchSplit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), IsSplitAt w → ∀ (n a b : ℕ) (h : a + b = n) (μ : HChar E) (f : UL n w → ℂ),
  Lc (KL n w) f → Lc (K2 a b w) (ctMu h w (μ.loc w) f) ∧ Match n a b w (μ.loc w) f (ctMu h w (μ.loc w) f)

def EndoBlock : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ), 1 ≤ a + b → ∀ S : Set (Pl E), IsSection S →
  ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (Z : Finset (Pl E)), SplitIn S Z →
    ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w ∈ Z, Lc (K2 a b w) (φ w)) → (∃ w ∈ Z, RegAt2 a b w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D₁ : J → CD E a) (D₂ : J → CD E b) (B₁ B₂ : J → Pl E → Multiset ℂˣ),
      (∀ j w, Off Z w → (D₁ j).Sat w (B₁ j w) ∧ (D₂ j).Sat w (B₂ j w)) ∧
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (ρ : ℝ), 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) (B₂ j)‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k)

def StableBlock : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∃ l₁ : InfinitePlace E → DomWeight n,
    ∀ (l₂ : InfinitePlace E → DomWeight 0) (S : Set (Pl E)), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
    ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, c ≠ 0 ∧
    ∀ φ : ∀ w : Pl E, GLw n w × GLw 0 w → ℂ, (∀ w ∈ Z, Lc (K2 n 0 w) (φ w)) → (∃ w ∈ Z, RegAt2 n 0 w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D : J → CD E n) (B₁ : J → Pl E → Multiset ℂˣ),
      (∀ j, ¬ (D j).Has π ∧ ∀ w, Off Z w → (D j).Sat w (B₁ j w)) ∧
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (ρ : ℝ), 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) 0‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) -
          c * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)) * val T e₁ e₂ B 0 ^ k

def CuspRead : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (bad : Set (Pl E)) (m₀ : (E →+* ℂ) → Multiset ℂ) (X : Set (CuspSub E N)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  FiniteDimensional ℂ W → bad.Finite → (∀ w ∉ bad, ∀ k ∈ KGL w N, locGL E N w k ∈ K) → X.Subsingleton →
  (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) →
  ∃ (J : Type) (_ : Fintype J) (D : J → CD E N) (C : J → Pl E → Multiset ℂˣ),
    (∀ j, (∀ π ∈ X, ¬ (D j).Has π) ∧ ∀ w ∉ bad, (D j).Sat w (C j w)) ∧
    ∀ (φ : ℕ → Sm E N) (m : ℕ → (E →+* ℂ) → Multiset ℂ) (B : ℕ → Pl E → Multiset ℂˣ),
      (∀ k, φ k ≠ 0 ∧ IsAutForm (φ k) ∧ PositivityTheory.Rg.BcB.SpectralAccumulation.TypeB K W (φ k) ∧ Cj.S.HasCap (φ k) (m k) ∧
        (∀ w ∉ bad, IsSatVecGL w (Cj.S.fL N w) (φ k) (B k w)) ∧
        ∀ π ∈ X, ∀ ψ ∈ π.V, ∀ z : ℂ, ¬ ∀ g, (φ k).1 g = ψ.1 g * Complex.exp (z * PositivityTheory.Rg.BcB.logAbs g.val.det)) →
      (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (m k τ) (m₀ τ)) →
      ∃ (j : J) (s : ℕ → ℕ), StrictMono s ∧ ∀ w ∉ bad, ∀ i : ℕ,
        Tendsto (fun k => satEig (qV E w) N (B (s k) w) i) atTop (𝓝 (satEig (qV E w) N (C j w) i))

def Peak : Prop := ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (H : Type) [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] (R : B →⋆ₐ[ℂ] (H →L[ℂ] H)) (A : StarSubalgebra ℂ B) (p : A →⋆ₐ[ℂ] ℂ) (a₀ : A) (x : B)
  (ρ : ℝ), p a₀ = 1 → 0 < ρ →
  (∀ s : B →⋆ₐ[ℂ] ℂ, (∀ y, ‖s y‖ ≤ ‖R y‖) → (∀ a : A, s a = p a) → ‖s x‖ < ρ) →
  ∃ g : A, p g = 1 ∧ ‖R (x * (g * a₀ : A))‖ < ρ

def Asm : Prop := USide → G2s → MuEx → MatchUnit → MatchSplit → EndoBlock → StableBlock → RunC

end UpperTheory.V.Z.Tf.GlobalTraceComparison
