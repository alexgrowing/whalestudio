import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.SphComm2
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

abbrev Pred : Type 1 := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), CD E N → ((E →+* ℂ) → Multiset ℂ) → Prop

def CuspReadP (P : Pred) : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (bad : Set (Pl E)) (m₀ : (E →+* ℂ) → Multiset ℂ) (X : Set (CuspSub E N)), IsOpen (K : Set (GL (Fin N) (Af E))) →
  FiniteDimensional ℂ W → bad.Finite → (∀ w ∉ bad, ∀ k ∈ KGL w N, locGL E N w k ∈ K) → X.Subsingleton →
  (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) →
  ∃ (J : Type) (_ : Fintype J) (D : J → CD E N) (C : J → Pl E → Multiset ℂˣ),
    (∀ j, (∀ π ∈ X, ¬ (D j).Has π) ∧ ∀ w ∉ bad, (D j).Sat w (C j w)) ∧ (∀ j, P E N (D j) m₀) ∧
    ∀ (φ : ℕ → Sm E N) (m : ℕ → (E →+* ℂ) → Multiset ℂ) (B : ℕ → Pl E → Multiset ℂˣ),
      (∀ k, φ k ≠ 0 ∧ IsAutForm (φ k) ∧ PositivityTheory.Rg.BcB.SpectralAccumulation.TypeB K W (φ k) ∧ UpperTheory.V.Cj.S.HasCap (φ k) (m k) ∧
        (∀ w ∉ bad, IsSatVecGL w (UpperTheory.V.Cj.S.fL N w) (φ k) (B k w)) ∧
        ∀ π ∈ X, ∀ ψ ∈ π.V, ∀ z : ℂ, ¬ ∀ g, (φ k).1 g = ψ.1 g * Complex.exp (z * PositivityTheory.Rg.BcB.logAbs g.val.det)) →
      (∀ τ (ε : ℝ), 0 < ε → ∀ᶠ k in atTop, Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (m k τ) (m₀ τ)) →
      ∃ (j : J) (s : ℕ → ℕ), StrictMono s ∧ ∀ w ∉ bad, ∀ i : ℕ,
        Tendsto (fun k => satEig (qV E w) N (B (s k) w) i) atTop (𝓝 (satEig (qV E w) N (C j w) i))

def Read (P : Pred) : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b),
  ∃ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W ∧
  ∀ (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
    ∀ X : Set (CuspSub E a), X.Subsingleton → (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E a t * g) = ψ.1 g) →
    ∃ (J : Type) (_ : Fintype J) (D₁ : J → CD E a) (D₂ : J → CD E b) (B₁ B₂ : J → Pl E → Multiset ℂˣ),
      (∀ j, (∀ π ∈ X, ¬ (D₁ j).Has π) ∧ ∀ w, Off Z w → (D₁ j).Sat w (B₁ j w) ∧ (D₂ j).Sat w (B₂ j w)) ∧
      (∀ j, P E a (D₁ j) (mW l₁) ∧ P E b (D₂ j) (mW l₂)) ∧
      ∀ T e₁ e₂ (g : ℕ → A.blk.Hb) (s : Gam a b S Z → ℂ), TIn S T e₂ → Disjoint T Z → Sees A.blk g X (Kg S L.L₁) W →
        (∀ γ, γ.arch → s γ = (A.gen S L T e₁ e₂ γ).val (chi l₁) (chi l₂)) → Realised (A.gen S L T e₁ e₂) (.inl ()) g s →
        ∃ j, s (.inr (.inr (.inr ()))) = val T e₁ e₂ (B₁ j) (B₂ j)

def Spec (P : Pred) : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
  (D : Dom E a b) (A : Ar l₁ l₂ D) (S : Set (Pl E)) (Z : Finset (Pl E)) (L : Lv a b Z), IsSection S → SplitIn S Z →
  ∀ X : Set (CuspSub E a), X.Subsingleton → (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E a t * g) = ψ.1 g) →
  ∀ (Q : Submodule ℂ A.blk.Hb) [CompleteSpace Q], Keeps A.blk Q →
  (∀ W : Submodule ℂ (Kinf E a → ℂ), FiniteDimensional ℂ W → ∃ g, Tests A.blk Q g ∧ Sees A.blk g X (Kg S L.L₁) W) →
  ∃ (J : Type) (_ : Fintype J) (D₁ : J → CD E a) (D₂ : J → CD E b) (B₁ B₂ : J → Pl E → Multiset ℂˣ),
    (∀ j, (∀ π ∈ X, ¬ (D₁ j).Has π) ∧ ∀ w, Off Z w → (D₁ j).Sat w (B₁ j w) ∧ (D₂ j).Sat w (B₂ j w)) ∧
    (∀ j, P E a (D₁ j) (mW l₁) ∧ P E b (D₂ j) (mW l₂)) ∧
    ∀ T e₁ e₂ (ρ : ℝ), TIn S T e₂ → Disjoint T Z → 0 < ρ → (∀ j, ‖val T e₁ e₂ (B₁ j) (B₂ j)‖ < ρ) →
      ∃ U R, 0 ≤ R ∧ Rep A.blk (chi l₁) (chi l₂) (A.hk S L T e₁ e₂) 1 R U ∧ ‖U ∘L Q.subtypeL‖ < ρ

def EndoP (P : Pred) : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ (a b : ℕ), 1 ≤ a + b → ∀ S : Set (Pl E), IsSection S →
  ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b) (Z : Finset (Pl E)), SplitIn S Z →
    ∀ φ : ∀ w : Pl E, GLw a w × GLw b w → ℂ, (∀ w ∈ Z, Lc (K2 a b w) (φ w)) → (∃ w ∈ Z, RegAt2 a b w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D₁ : J → CD E a) (D₂ : J → CD E b) (B₁ B₂ : J → Pl E → Multiset ℂˣ),
      (∀ j w, Off Z w → (D₁ j).Sat w (B₁ j w) ∧ (D₂ j).Sat w (B₂ j w)) ∧
      (∀ j, P E a (D₁ j) (mW l₁) ∧ P E b (D₂ j) (mW l₂)) ∧
      ∀ T : Finset (Pl E), (∀ w ∈ T, w ∈ S) → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (ρ : ℝ),
        (∀ w ∈ T, ¬ IsSplitAt w → e₂ w = .one) → 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) (B₂ j)‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k)

def StableP (P : Pred) : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∃ l₁ : InfinitePlace E → DomWeight n,
    ∀ (l₂ : InfinitePlace E → DomWeight 0) (S : Set (Pl E)), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
    ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, c ≠ 0 ∧
    ∀ φ : ∀ w : Pl E, GLw n w × GLw 0 w → ℂ, (∀ w ∈ Z, Lc (K2 n 0 w) (φ w)) → (∃ w ∈ Z, RegAt2 n 0 w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D : J → CD E n) (B₁ : J → Pl E → Multiset ℂˣ),
      (∀ j, ¬ (D j).Has π ∧ ∀ w, Off Z w → (D j).Sat w (B₁ j w)) ∧ (∀ j, P E n (D j) (mW l₁)) ∧
      ∀ T : Finset (Pl E), (∀ w ∈ T, w ∈ S) → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (ρ : ℝ),
        (∀ w ∈ T, ¬ IsSplitAt w → e₂ w = .one) → 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) 0‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) -
          c * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)) * val T e₁ e₂ B 0 ^ k

def RRead : Prop := ∀ P : Pred, CuspReadP P → Read P

def RSpec : Prop := ∀ P : Pred, Read P → Spec P

def REndo : Prop := ∀ P : Pred, Spec P → EndoP P

def RStable : Prop := PiFin → PiAdm → GrowthPiJ → CmbPi → ∀ P : Pred, Spec P → StableP P

theorem cuspReadP_inf (h : CuspReadI) : CuspReadP fun _ _ _ _ _ D m => D.Inf m := h

theorem endoG_of (h : EndoP fun _ _ _ _ _ D m => D.Inf m) : EndoBlockG := h

theorem stableG_of (h : StableP fun _ _ _ _ _ D m => D.Inf m) : StableBlockG := h

theorem cuspReadP_true (h : CuspRead) : CuspReadP fun _ _ _ _ _ _ _ => True := by
  intro E _ _ _ N K W bad m₀ X h1 h2 h3 h4 h5 h6
  obtain ⟨J, hJ, D, C, a1, a2⟩ := h E N K W bad m₀ X h1 h2 h3 h4 h5 h6
  exact ⟨J, hJ, D, C, a1, fun _ => trivial, a2⟩

theorem endo_of (P : Pred) (h : EndoP P) : EndoBlock := by
  intro E _ _ _ hE a b hab S hS l₁ l₂ Z hZ φ h1 h2
  obtain ⟨J, hJ, D₁, D₂, B₁, B₂, a1, -, a3⟩ := h E hE a b hab S hS l₁ l₂ Z hZ φ h1 h2
  exact ⟨J, hJ, D₁, D₂, B₁, B₂, a1, fun T hT hd e₁ e₂ ρ hρ hv =>
    a3 T (fun w hw => (hT w hw).1) hd e₁ e₂ ρ (fun w hw hn => absurd (hT w hw).2 hn) hρ hv⟩

theorem stable_of (P : Pred) (h : StableP P) : StableBlock := by
  intro E _ _ _ hE n hn π h1 h2
  obtain ⟨l₁, hl⟩ := h E hE n hn π h1 h2
  refine ⟨l₁, fun l₂ S hS Z hZ B τ hB hτ => ?_⟩
  obtain ⟨c, hc, hφ⟩ := hl l₂ S hS Z hZ B τ hB hτ
  refine ⟨c, hc, fun φ p1 p2 => ?_⟩
  obtain ⟨J, hJ, D, B₁, a1, -, a3⟩ := hφ φ p1 p2
  exact ⟨J, hJ, D, B₁, a1, fun T hT hd e₁ e₂ ρ hρ hv =>
    a3 T (fun w hw => (hT w hw).1) hd e₁ e₂ ρ (fun w hw hn => absurd (hT w hw).2 hn) hρ hv⟩

end UpperTheory.Zero.ConvolutionTheory.EB
