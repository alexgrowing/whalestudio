import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.StableBlock
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntZero

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def CD.Inf (D : CD E n) (m : (E →+* ℂ) → Multiset ℂ) : Prop := ∀ τ, ∑ i, (D.P i).infChar τ = m τ

def CD.Reg (D : CD E n) : Prop := ∀ τ, ∃ lam : DomWeight n, ∑ i, (D.P i).infChar τ = infOfWeight lam

example : (CD.nil E).Inf fun _ => 0 := fun _ => rfl

def mW (l : InfinitePlace E → DomWeight n) : (E →+* ℂ) → Multiset ℂ :=
  PositivityTheory.Rg.BcB.CG.mOf fun v => PositivityTheory.RgBcC.infOf (l v).w

def dEx (p : Fin (a + 1) × Fin (b + 1)) : Ex (Fin (a + 1) × Fin (b + 1)) :=
  .add (.mul (.gen (Fin.last a, Fin.last b)) (.gen p)) (.smul (-1) (.gen (p.1.rev, p.2.rev)))

inductive U1 : Ex (Fin (a + 1) × Fin (b + 1)) → Prop
  | one : U1 .one
  | step (c : ℂ) (p : Fin (a + 1) × Fin (b + 1)) : U1 (.add .one (.smul c (dEx p)))
  | mul {x y} : U1 x → U1 y → U1 (.mul x y)

theorem U1.pow {x : Ex (Fin (a + 1) × Fin (b + 1))} (h : U1 x) : ∀ k, U1 (x.pow k)
  | 0 => .one
  | k + 1 => .mul (h.pow k) h

def RunTh : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
    (∃ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ ∧ (∀ w : Pl E, ¬ IsSplitAt w → IsUnramU σ w) ∧
      ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ),
        IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ HasSatGL w τ.ρ B ∧ (CG.mk π).HasSat w B) ∨
    ∃ D : CD E n, ¬ D.Has π ∧ D.Reg ∧ (∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∃ B, D.Sat w B ∧ inv B = B) ∧
      ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

def EndoBlockG : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ), 1 ≤ a + b → ∀ S : Set (Pl E), IsSection S →
  ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (Z : Finset (Pl E)), SplitIn S Z →
    ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w ∈ Z, Lc (K2 a b w) (φ w)) → (∃ w ∈ Z, RegAt2 a b w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D₁ : J → CD E a) (D₂ : J → CD E b) (B₁ B₂ : J → Pl E → Multiset ℂˣ),
      (∀ j w, Off Z w → (D₁ j).Sat w (B₁ j w) ∧ (D₂ j).Sat w (B₂ j w)) ∧
      (∀ j, (D₁ j).Inf (mW l₁) ∧ (D₂ j).Inf (mW l₂)) ∧
      ∀ T : Finset (Pl E), (∀ w ∈ T, w ∈ S) → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (ρ : ℝ),
        (∀ w ∈ T, ¬ IsSplitAt w → e₂ w = .one) → 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) (B₂ j)‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k)

def StableBlockG : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∃ l₁ : InfinitePlace E → DomWeight n,
    ∀ (l₂ : InfinitePlace E → DomWeight 0) (S : Set (Pl E)), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
    ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, c ≠ 0 ∧
    ∀ φ : ∀ w : Pl E, GLw n w × GLw 0 w → ℂ, (∀ w ∈ Z, Lc (K2 n 0 w) (φ w)) → (∃ w ∈ Z, RegAt2 n 0 w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D : J → CD E n) (B₁ : J → Pl E → Multiset ℂˣ),
      (∀ j, ¬ (D j).Has π ∧ ∀ w, Off Z w → (D j).Sat w (B₁ j w)) ∧ (∀ j, (D j).Inf (mW l₁)) ∧
      ∀ T : Finset (Pl E), (∀ w ∈ T, w ∈ S) → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (ρ : ℝ),
        (∀ w ∈ T, ¬ IsSplitAt w → e₂ w = .one) → 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) 0‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) -
          c * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)) * val T e₁ e₂ B 0 ^ k

def EndoBlockS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ), 1 ≤ a + b → ∀ S : Set (Pl E), IsSection S →
  ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (Z : Finset (Pl E)), SplitIn S Z →
    ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w ∈ Z, Lc (K2 a b w) (φ w)) → (∃ w ∈ Z, RegAt2 a b w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D₁ : J → CD E a) (D₂ : J → CD E b) (B₁ B₂ : J → Pl E → Multiset ℂˣ),
      (∀ j w, Off Z w → (D₁ j).Sat w (B₁ j w) ∧ (D₂ j).Sat w (B₂ j w)) ∧
      (∀ j, (D₁ j).Inf (mW l₁) ∧ (D₂ j).Inf (mW l₂)) ∧
      (∀ j w, ¬ IsSplitAt w → inv (B₁ j w) = B₁ j w ∧ inv (B₂ j w) = B₂ j w) ∧
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (ρ : ℝ), 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) (B₂ j)‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k)

def StableBlockS : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∃ l₁ : InfinitePlace E → DomWeight n,
    ∀ (l₂ : InfinitePlace E → DomWeight 0) (S : Set (Pl E)), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
    ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, c ≠ 0 ∧
    ∀ φ : ∀ w : Pl E, GLw n w × GLw 0 w → ℂ, (∀ w ∈ Z, Lc (K2 n 0 w) (φ w)) → (∃ w ∈ Z, RegAt2 n 0 w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D : J → CD E n) (B₁ : J → Pl E → Multiset ℂˣ),
      (∀ j, ¬ (D j).Has π ∧ ∀ w, Off Z w → (D j).Sat w (B₁ j w)) ∧ (∀ j, (D j).Inf (mW l₁)) ∧
      (∀ j w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w) ∧
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (ρ : ℝ), 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) 0‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) -
          c * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)) * val T e₁ e₂ B 0 ^ k

def CuspReadI : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (bad : Set (Pl E)) (m₀ : (E →+* ℂ) → Multiset ℂ) (X : Set (CuspSub E N)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  FiniteDimensional ℂ W → bad.Finite → (∀ w ∉ bad, ∀ k ∈ KGL w N, locGL E N w k ∈ K) → X.Subsingleton →
  (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) →
  ∃ (J : Type) (_ : Fintype J) (D : J → CD E N) (C : J → Pl E → Multiset ℂˣ),
    (∀ j, (∀ π ∈ X, ¬ (D j).Has π) ∧ ∀ w ∉ bad, (D j).Sat w (C j w)) ∧ (∀ j, (D j).Inf m₀) ∧
    ∀ (φ : ℕ → Sm E N) (m : ℕ → (E →+* ℂ) → Multiset ℂ) (B : ℕ → Pl E → Multiset ℂˣ),
      (∀ k, φ k ≠ 0 ∧ IsAutForm (φ k) ∧ PositivityTheory.Rg.BcB.SpectralAccumulation.TypeB K W (φ k) ∧ Cj.S.HasCap (φ k) (m k) ∧
        (∀ w ∉ bad, IsSatVecGL w (Cj.S.fL N w) (φ k) (B k w)) ∧
        ∀ π ∈ X, ∀ ψ ∈ π.V, ∀ z : ℂ, ¬ ∀ g, (φ k).1 g = ψ.1 g * Complex.exp (z * PositivityTheory.Rg.BcB.logAbs g.val.det)) →
      (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (m k τ) (m₀ τ)) →
      ∃ (j : J) (s : ℕ → ℕ), StrictMono s ∧ ∀ w ∉ bad, ∀ i : ℕ,
        Tendsto (fun k => satEig (qV E w) N (B (s k) w) i) atTop (𝓝 (satEig (qV E w) N (C j w) i))

def StUnit : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ w : Pl E, ¬ IsSplitAt w →
  ∀ (a b : ℕ) (e : Ex (Fin (a + 1) × Fin (b + 1))), U1 e → ∀ Q₁ Q₂ : (w.adicCompletion E)[X], Q₁.Separable → Q₂.Separable →
    stTw2 a b w Q₁ Q₂ (fn2 a b w e) = stTw2 a b w Q₁ Q₂ ((K2 a b w : Set _).indicator 1)

def EvaluationAtUnitaryOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a b : ℕ) (e : Ex (Fin (a + 1) × Fin (b + 1))), U1 e →
  ∀ B₁ B₂ : Multiset ℂˣ, B₁.card = a → B₂.card = b → inv B₁ = B₁ → inv B₂ = B₂ → ev2 a b w e B₁ B₂ = 1

def SeparatesUnitaryOne : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a b : ℕ) (B₁ B₂ : Multiset ℂˣ), B₁.card = a → B₂.card = b →
  ¬ (inv B₁ = B₁ ∧ inv B₂ = B₂) → ∃ e, U1 e ∧ ev2 a b w e B₁ B₂ = 0

def Enlarge : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ) (S : Set (Pl E)), IsSection S →
  ∀ Z T : Finset (Pl E), SplitIn S Z → SplitIn S T → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)))
    (I : Type) [Finite I] (u : I → Pl E) (C₁ C₂ : I → Pl E → Multiset ℂˣ),
    (∀ i, ¬ IsSplitAt (u i) ∧ (C₁ i (u i)).card = a ∧ (C₂ i (u i)).card = b ∧ ¬ (inv (C₁ i (u i)) = C₁ i (u i) ∧ inv (C₂ i (u i)) = C₂ i (u i))) →
    ∃ (T' : Finset (Pl E)) (e₁' e₂' : Pl E → Ex (Fin (a + 1) × Fin (b + 1))), (∀ w ∈ T', w ∈ S) ∧ Disjoint T' Z ∧
      (∀ w ∈ T', ¬ IsSplitAt w → e₂' w = .one) ∧ (∀ i, val T' e₁' e₂' (C₁ i) (C₂ i) = 0) ∧
      (∀ B₁ B₂ : Pl E → Multiset ℂˣ,
        (∀ i, (B₁ (u i)).card = a ∧ (B₂ (u i)).card = b ∧ inv (B₁ (u i)) = B₁ (u i) ∧ inv (B₂ (u i)) = B₂ (u i)) →
        val T' e₁' e₂' B₁ B₂ = val T e₁ e₂ B₁ B₂) ∧
      ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ) (k : ℕ),
        geomSt2 S l₁ l₂ (fam Z T' φ e₁' e₂' k) = geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k)

def MWAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → DomWeight n) (v : InfinitePlace E),
  mW l v.embedding = infOfWeight (l v) ∧ mW l (ComplexEmbedding.conjugate v.embedding) = (infOfWeight (l v)).map Neg.neg

def DualWt : Prop := ∀ (n : ℕ) (lam : DomWeight n), ∃ lam' : DomWeight n, infOfWeight lam' = (infOfWeight lam).map Neg.neg

def MuInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  (∀ w : Pl E, ¬ IsSplitAt w → μ.val w = -1) ∧ ∀ (N k : ℕ) (P : CG E N) (v : InfinitePlace E),
    (P.twist (μ ^ k)).infChar v.embedding = (P.infChar v.embedding).map (· + (k : ℂ) * (e v : ℂ) / 2) ∧
    (P.twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
      (P.infChar (ComplexEmbedding.conjugate v.embedding)).map (· - (k : ℂ) * (e v : ℂ) / 2)

def PartNorm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → ∀ D : CD E n, D.Reg →
    (∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B) →
    ∀ i, ∃ P : CuspSub E (D.N i), CG.mk P = D.P i ∧ GlobalTheory.DiscSpec.IsNormalised P ∧ P.IsUnitary

def AsmTh : Prop := USide → G2s → MuEx → MatchUnit → MatchSplit → EndoBlockS → StableBlockS → RunTh

end UpperTheory.V.Z.Tf.GlobalTraceComparison
