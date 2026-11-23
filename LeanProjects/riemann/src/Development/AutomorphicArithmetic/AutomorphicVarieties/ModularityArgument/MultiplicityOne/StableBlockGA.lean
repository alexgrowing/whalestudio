import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.TwTrSum

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Mult

open UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

def PiTermA : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (l : InfinitePlace E → DomWeight n) (u : GL (Fin n) E), IsTransl u →
  ∀ (μC : Measure (G n)) (μ : Measure (H E n 0)), μC.IsHaarMeasure → μ.IsHaarMeasure → ∃ c₀ : ℝ, 0 < c₀ ∧
  ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ v, π.HasInfChar v.embedding (infOfWeight (l v))) →
    ∀ S : Set (Pl E), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
    ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, ‖c‖ = c₀ ∧
    ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, Lc (K2 n 0 w) (φ₁ w) ∧ Lc (K2 n 0 w) (φ₂ w)) →
    ∀ T : Finset (Pl E), Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)))
      (k : ∀ v, Mat n → ((lefE n (l v).w).V →L[ℂ] (lefE n (l v).w).V)) (vl : InfinitePlace E → Inf n → ℂ) (R : ℝ),
      TEv S T e₂ → (∀ v, IsMult μC (lefE n (l v).w) (k v) (vl v) R) →
      IsTwTr μ π (phiProd (fun v => (l v).w) k (finU S u (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)))
        (c * (∏ v, vl v (infOf (l v).w)) * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0)

def StableBlockGA : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (l₁ : InfinitePlace E → DomWeight n) (l₂ : InfinitePlace E → DomWeight 0), ∃ c₀ : ℝ, 0 < c₀ ∧
  ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ v, π.HasInfChar v.embedding (infOfWeight (l₁ v))) →
    ∀ (S : Set (Pl E)), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
    ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, ‖c‖ = c₀ ∧
    ∀ φ : ∀ w : Pl E, GLw n w × GLw 0 w → ℂ, (∀ w ∈ Z, Lc (K2 n 0 w) (φ w)) → (∃ w ∈ Z, RegAt2 n 0 w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D : J → CD E n) (B₁ : J → Pl E → Multiset ℂˣ),
      (∀ j, ¬ (D j).Has π ∧ ∀ w, Off Z w → (D j).Sat w (B₁ j w)) ∧ (∀ j, (D j).Inf (mW l₁)) ∧
      ∀ T : Finset (Pl E), (∀ w ∈ T, w ∈ S) → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (ρ : ℝ),
        (∀ w ∈ T, ¬ IsSplitAt w → e₂ w = .one) → 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) 0‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) -
          c * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)) * val T e₁ e₂ B 0 ^ k

def StableBlockSA : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (l₁ : InfinitePlace E → DomWeight n) (l₂ : InfinitePlace E → DomWeight 0), ∃ c₀ : ℝ, 0 < c₀ ∧
  ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ v, π.HasInfChar v.embedding (infOfWeight (l₁ v))) →
    ∀ (S : Set (Pl E)), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
    ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∃ c : ℂ, ‖c‖ = c₀ ∧
    ∀ φ : ∀ w : Pl E, GLw n w × GLw 0 w → ℂ, (∀ w ∈ Z, Lc (K2 n 0 w) (φ w)) → (∃ w ∈ Z, RegAt2 n 0 w (φ w)) →
    ∃ (J : Type) (_ : Fintype J) (D : J → CD E n) (B₁ : J → Pl E → Multiset ℂˣ),
      (∀ j, ¬ (D j).Has π ∧ ∀ w, Off Z w → (D j).Sat w (B₁ j w)) ∧ (∀ j, (D j).Inf (mW l₁)) ∧
      (∀ j w, ¬ IsSplitAt w → inv (B w) = B w → inv (B₁ j w) = B₁ j w) ∧
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1))) (ρ : ℝ), 0 < ρ →
        (∀ j, ‖val T e₁ e₂ (B₁ j) 0‖ < ρ) → Small ρ fun k => geomSt2 S l₁ l₂ (fam Z T φ e₁ e₂ k) -
          c * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => φ w (g, 1)) * val T e₁ e₂ B 0 ^ k

end UpperTheory.V.Z.Mult
