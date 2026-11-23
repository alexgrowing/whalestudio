import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.StableBlock

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def famU (Z T : Finset (Pl E)) (f : ∀ w : Pl E, GLw n w → ℂ) (e₁ e₂ : Pl E → Ex (Fin (n + 1))) (k : ℕ) (w : Pl E) :
    UL n w → ℂ :=
  if w ∈ Z then fun x => f w x.1 else if w ∈ T then fun x => fn1 n w (((e₁ w).pow k).mul ((e₂ w).pow k)) x.1
  else (KL n w : Set _).indicator 1

def val1 (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (n + 1))) (B : Pl E → Multiset ℂˣ) : ℂ :=
  ∏ w ∈ T, ev1 n w (e₁ w) (B w) * ev1 n w (e₂ w) (inv (B (cPl w)))

def un (μ : HChar E) (a b : ℕ) (w : Pl E) (B₁ B₂ : Multiset ℂˣ) : Multiset ℂˣ :=
  B₁.map (· * μ.val w ^ b) + B₂.map (· * μ.val w ^ a)

def ct0 (μ : HChar E) {a b : ℕ} (h : a + b = n) (f : ∀ w : Pl E, GLw n w → ℂ) (w : Pl E) : GLw a w × GLw b w → ℂ :=
  ctMu h w (μ.loc w) fun x : UL n w => f w x.1

def ExAct : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (e : Ex (Fin (n + 1))), IsHecke (KGL w n) (fn1 n w e) ∧
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GLw n w) V) (x : V) (B : Multiset ℂˣ), IsSatVecGL w ρ x B →
    levOp ρ (KGL w n) (KGL w n) (fn1 n w e) LinearMap.id x = ev1 n w e B • x

def ExHecke2 : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (e : Ex (Fin (a + 1) × Fin (b + 1))), IsHecke (K2 a b w) (fn2 a b w e)

def CtEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), IsSplitAt w → ∀ μ : HChar E, μ.UnrAt w → ∀ (n a b : ℕ) (h : a + b = n),
  ∃ t : Fin (n + 1) → Ex (Fin (a + 1) × Fin (b + 1)),
    (∀ e, (ctMu h w (μ.loc w) fun x : UL n w => fn1 n w e x.1) = fn2 a b w (e.bind t)) ∧
    ∀ e B₁ B₂, B₁.card = a → B₂.card = b → ev2 a b w (e.bind t) B₁ B₂ = ev1 n w e (un μ a b w B₁ B₂)

def MuConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w : Pl E, IsSplitAt w → μ.UnrAt w →
  μ.val (cPl w) = (μ.val w)⁻¹

def Places : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], (∃ S : Set (Pl E), IsSection S) ∧ (∀ w : Pl E, cPl (cPl w) = w ∧ (IsSplitAt w ↔ cPl w ≠ w)) ∧
  {w : Pl E | IsSplitAt w}.Infinite ∧
  ∀ S : Set (Pl E), IsSection S → ∀ w, (w ∈ S ∨ cPl w ∈ S) ∧ (w ∈ S → cPl w ∈ S → cPl w = w)

def RegCt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), IsSplitAt w → ∀ (μ : HChar E) (n a b : ℕ) (h : a + b = n) (f : ∀ w : Pl E, GLw n w → ℂ),
  (∀ y, f w y ≠ 0 → y.val.charpoly.Separable) → RegAt2 a b w (ct0 μ h f w)

def LevelFn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w)), ∃ f, Lc (KGL w n) f ∧ trc τ.ρ (KGL w n) f ≠ 0

def RegFn : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ), HasSatGL w τ.ρ B →
  ∃ f, Lc (KGL w n) f ∧ trc τ.ρ (KGL w n) f ≠ 0 ∧ ∀ y, f y ≠ 0 → y.val.charpoly.Separable

def TrAvg : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → ∀ (μ : HChar E) (τ : SmIrr (GLw n w)) (f : ∀ w : Pl E, GLw n w → ℂ),
  Lc (KGL w n) (f w) → trc τ.ρ (KGL w n) (fun g => ct0 μ (Nat.add_zero n) f w (g, 1)) = trc τ.ρ (KGL w n) (f w)

def SplitLine : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (τ : SmIrr (GLw n w)), fixed τ.ρ (KGL w n) ≠ ⊥ →
  Module.finrank ℂ (fixed τ.ρ (KGL w n)) = 1 ∧ ∃ B, HasSatGL w τ.ρ B

def InertLine : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w → ∀ σ : SmIrr (UL n w),
  fixed σ.ρ (KL n w) ≠ ⊥ → FiniteDimensional ℂ (fixed σ.ρ (KL n w)) → Module.finrank ℂ (fixed σ.ρ (KL n w)) = 1

def UConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)) (w : Pl E), IsSplitAt w → ∀ (τ : SmIrr (GLw n w)) (B : Multiset ℂˣ),
  IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → HasSatGL w τ.ρ B →
  ∃ τ' : SmIrr (GLw n (cPl w)), IsCompAlong σ (locU n (cPl w)) ((cLoc (cPl w)).comp (locU n (cPl w)).subtype) τ'.ρ ∧
    HasSatGL (cPl w) τ'.ρ (inv B)

def Choice : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∃ (S : Set (Pl E)) (Z : Finset (Pl E)) (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)) (f : ∀ w : Pl E, GLw n w → ℂ),
    IsSection S ∧ SplitIn S Z ∧ (∀ w, Off Z w → (CG.mk π).HasSat w (B w) ∧ μ.UnrAt w) ∧
    (∀ w ∈ Z, π.IsLocComp w (τ w) ∧ Lc (KGL w n) (f w) ∧ trc (τ w).ρ (KGL w n) (f w) ≠ 0) ∧
    ∃ w ∈ Z, ∀ y, f w y ≠ 0 → y.val.charpoly.Separable

def RChoice : Prop := Places → LevelFn → RegFn → Choice

def UEval : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (Z : Finset (Pl E)), SplitIn S Z → ∀ f : ∀ w : Pl E, GLw n w → ℂ,
    (∀ w ∈ Z, Lc (KGL w n) (f w)) → (∃ w ∈ Z, ∀ y, f w y ≠ 0 → y.val.charpoly.Separable) →
    ∃ (K' : ∀ w : Pl E, Subgroup (UL n w)) (ι : Type) (_ : Fintype ι) (σ : ι → Submodule ℂ (UA E n → ℂ)) (A : ι → ℂ)
      (B : ι → Pl E → Multiset ℂˣ), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' ∧
      (∀ i, IsAutRepU (σ i) ∧ (∀ w : Pl E, ¬ IsSplitAt w → IsUnramU (σ i) w) ∧ ∀ w, Off Z w → IsSplitAt w →
        ∃ τ : SmIrr (GLw n w), IsCompAlong (σ i) (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ ∧ HasSatGL w τ.ρ (B i w)) ∧
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ e₁ e₂ k, GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) ∧
        geomU S lam (famU Z T f e₁ e₂ k) = ∑ i, A i * val1 T e₁ e₂ (B i) ^ k

def RUEval : Prop := USide → Places → ExAct → SplitLine → InertLine → UConj → UEval

def FamMatch : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (n : ℕ) (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e →
  ∀ S : Set (Pl E), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z → (∀ w, Off Z w → μ.UnrAt w) →
  ∀ f : ∀ w : Pl E, GLw n w → ℂ, (∀ w ∈ Z, Lc (KGL w n) (f w)) → ∀ (a b : ℕ) (h : a + b = n),
    (∀ w ∈ Z, Lc (K2 a b w) (ct0 μ h f w)) ∧
    ∃ t : Pl E → Fin (n + 1) → Ex (Fin (a + 1) × Fin (b + 1)), ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ e₁ e₂,
      (∀ B₁ B₂ : Pl E → Multiset ℂˣ, (∀ w, Off Z w → (B₁ w).card = a ∧ (B₂ w).card = b) →
        val T (fun w => (e₁ w).bind (t w)) (fun w => (e₂ w).bind (t w)) B₁ B₂ =
          val1 T e₁ e₂ fun w => un μ a b w (B₁ w) (B₂ w)) ∧
      ∀ k, IsTestP (fam Z T (ct0 μ h f) (fun w => (e₁ w).bind (t w)) (fun w => (e₂ w).bind (t w)) k) ∧ ∀ w ∈ S,
        Match n a b w (μ.loc w) (famU Z T f e₁ e₂ k w)
          (fam Z T (ct0 μ h f) (fun w => (e₁ w).bind (t w)) (fun w => (e₂ w).bind (t w)) k w) ∧
        fam Z T (ct0 μ h f) (fun w => (e₁ w).bind (t w)) (fun w => (e₂ w).bind (t w)) k w =
          if IsSplitAt w then ctMu h w (μ.loc w) (famU Z T f e₁ e₂ k w) else (K2 a b w : Set _).indicator 1

def RFamMatch : Prop := MatchUnit → MatchSplit → Places → ExAct → ExHecke2 → CtEx → MuConj → FamMatch

def Ends : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n), (a = 0 ∨ b = 0) → ∀ (μ : HChar E) (e : InfinitePlace E → ℤ) (S : Set (Pl E))
  (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (lam : InfinitePlace E → DomWeight n)
  (l₀ : InfinitePlace E → DomWeight 0) (f : ∀ w : Pl E, UL n w → ℂ) (Φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ)
  (Φ' : ∀ w : Pl E, GLw n w × GLw 0 w → ℂ),
  (∀ v, (infOfWeight (l₁ v)).map (· + (b : ℂ) * (e v : ℂ) / 2) + (infOfWeight (l₂ v)).map (· + (a : ℂ) * (e v : ℂ) / 2) =
    infOfWeight (lam v)) →
  (∀ w ∈ S, Φ w = if IsSplitAt w then ctMu h w (μ.loc w) (f w) else (K2 a b w : Set _).indicator 1) →
  (∀ w ∈ S, Φ' w = if IsSplitAt w then ctMu (Nat.add_zero n) w (μ.loc w) (f w) else (K2 n 0 w : Set _).indicator 1) →
  geomSt2 S l₁ l₂ Φ = geomSt2 S lam l₀ Φ'

def TwData : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ), a + b = n → 1 ≤ a → 1 ≤ b → ∀ (μ : HChar E) (D₁ : CD E a) (D₂ : CD E b),
  ∃ D : CD E n, (∀ π : CuspSub E n, ¬ D.Has π) ∧
    ∀ w B₁ B₂, μ.UnrAt w → D₁.Sat w B₁ → D₂.Sat w B₂ → D.Sat w (un μ a b w B₁ B₂)

def Sep : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ (Z : Finset (Pl E)) (I : Type) [Finite I]
  (B : Pl E → Multiset ℂˣ) (C : I → Pl E → Multiset ℂˣ),
  (∀ j, ∃ w, Off Z w ∧ IsSplitAt w ∧ (B w).card = n ∧ (C j w).card = n ∧ C j w ≠ B w) →
  ∃ (T : Finset (Pl E)) (e₁ e₂ : Pl E → Ex (Fin (n + 1))), SplitIn S T ∧ Disjoint T Z ∧ val1 T e₁ e₂ B = 1 ∧
    ∀ j, val1 T e₁ e₂ (C j) = 0

def RSep : Prop := Places → Sep

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
