import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.EvaluationAtUnitaryOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.DescWeakOfRun
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical
open GroundTheory.Automorphic.AutomorphicForm (constantTerm)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}

def ReadJ (bad : Set (Pl E)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)) (m₀ : (E →+* ℂ) → Multiset ℂ)
    (X : Set (CuspSub E N)) (P : Sm E N → Prop) : Prop :=
  ∃ (J : Type) (_ : Fintype J) (D : J → CD E N) (C : J → Pl E → Multiset ℂˣ),
    (∀ j, (∀ π ∈ X, ¬ (D j).Has π) ∧ ∀ w ∉ bad, (D j).Sat w (C j w)) ∧
    ∀ (φ : ℕ → Sm E N) (m : ℕ → (E →+* ℂ) → Multiset ℂ) (B : ℕ → Pl E → Multiset ℂˣ),
      (∀ k, EigT bad K W (φ k) (m k) (B k) ∧ P (φ k)) → MTo m m₀ →
      ∃ (j : J) (s : ℕ → ℕ), StrictMono s ∧ (D j).Inf m₀ ∧ ∀ w ∉ bad, STo (qV E w) N (fun k => B (s k) w) (C j w)

end

def CuspCaseJ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ), 1 ≤ N → ∀ (bad : Set (Pl E)) (K : Subgroup (GL (Fin N) (Af E)))
  (W : Submodule ℂ (Kinf E N → ℂ)) m₀ (X : Set (CuspSub E N)), bad.Finite → Lev bad K → FiniteDimensional ℂ W →
    (∀ π ∈ X, ∀ ψ ∈ π.V, ∀ t g, ψ.1 (splitCentre E N t * g) = ψ.1 g) → ReadJ bad K W m₀ X fun φ => IsCuspForm φ ∧ Excl X φ

def CtCaseJ : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ), 1 ≤ r → 1 ≤ s → ∀ bad : Set (Pl E),
  (∀ K (W : Submodule ℂ (Kinf E r → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W → ReadJ (N := r) bad K W m₀ ∅ fun _ => True) →
  (∀ K (W : Submodule ℂ (Kinf E s → ℂ)) m₀, Lev bad K → FiniteDimensional ℂ W → ReadJ (N := s) bad K W m₀ ∅ fun _ => True) →
  ∀ K (W : Submodule ℂ (Kinf E (r + s) → ℂ)) m₀ X, Lev bad K → FiniteDimensional ℂ W → ReadJ (N := r + s) bad K W m₀ X fun φ => ∃ g, constantTerm r φ.1 g ≠ 0

def CDAddG : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (D₁ : CD E r) (D₂ : CD E s) (ν ν' : HChar E),
  1 ≤ r → 1 ≤ s → ∃ D : CD E (r + s), (∀ π : CuspSub E (r + s), ¬ D.Has π) ∧ (∀ w B₁ B₂, ν.UnrAt w → ν'.UnrAt w → D₁.Sat w B₁ →
    D₂.Sat w B₂ → D.Sat w (B₁.map (· * ν.val w) + B₂.map (· * ν'.val w))) ∧
    ∀ τ, ∑ i, (D.P i).infChar τ = ∑ i, ((D₁.P i).twist ν).infChar τ + ∑ i, ((D₂.P i).twist ν').infChar τ

def AbsInf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (P : CG E N) (z : ℂ) (τ : E →+* ℂ),
  (P.twist (Model.absC E z)).infChar τ = (P.infChar τ).map (· + z) ∧
    (P.twist (GlobalTheory.Mem.Chr.CharModel.absChar E z)).infChar τ = (P.infChar τ).map (· + z)

def MToLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
  (∀ (m : ℕ → (E →+* ℂ) → Multiset ℂ) x y, MTo m x → MTo m y → x = y) ∧
  (∀ (m : ℕ → (E →+* ℂ) → Multiset ℂ) x (z : ℕ → ℂ) (z₀ : ℂ), MTo m x → Tendsto z atTop (𝓝 z₀) →
    MTo (fun k t => (m k t).map (· + z k)) fun t => (x t).map (· + z₀)) ∧
  ∀ (m m' : ℕ → (E →+* ℂ) → Multiset ℂ) x x', MTo m x → MTo m' x' → MTo (fun k t => m k t + m' k t) fun t => x t + x' t

def RegOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (l : InfinitePlace E → DomWeight n) (D : CD E n),
  D.Inf (mW l) → D.Reg

def TwDataT : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ), a + b = n → 1 ≤ a → 1 ≤ b →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ (l₁ : InfinitePlace E → DomWeight a) (l₂ : InfinitePlace E → DomWeight b)
    (lam : InfinitePlace E → DomWeight n),
    (∀ v, (infOfWeight (l₁ v)).map (· + (b : ℂ) * (e v : ℂ) / 2) + (infOfWeight (l₂ v)).map (· + (a : ℂ) * (e v : ℂ) / 2) =
      infOfWeight (lam v)) → ∀ (D₁ : CD E a) (D₂ : CD E b), D₁.Inf (mW l₁) → D₂.Inf (mW l₂) →
    ∃ D : CD E n, (∀ π : CuspSub E n, ¬ D.Has π) ∧ D.Reg ∧
      ∀ w B₁ B₂, μ.UnrAt w → D₁.Sat w B₁ → D₂.Sat w B₂ → D.Sat w (un μ a b w B₁ B₂)

def UnStable : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (a b : ℕ) (w : Pl E) (B₁ B₂ : Multiset ℂˣ),
  μ.val w = -1 → inv B₁ = B₁ → inv B₂ = B₂ → inv (un μ a b w B₁ B₂) = un μ a b w B₁ B₂

def CsdInert : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → ∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∀ B, (CG.mk π).HasSat w B → inv B = B

def PreOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n,
  GlobalTheory.ContraPair.DualIsConj π → ∀ D : CD E n, ¬ D.Has π → D.Reg →
    (∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∃ B, D.Sat w B ∧ inv B = B) →
    (∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B) →
    ∃ D' : PositivityTheory.Rg.BcB.F.Pre E n, D'.Reg ∧ D'.ThetaStable ∧ PositivityTheory.Rg.BcB.G.SplitLike D' π ∧ ¬ PositivityTheory.Rg.BcB.G.IsOne D' π

theorem descWeak_of_runTh (hN : GOne.NoOther) (hP : PreOf) (hRun : RunTh) : UpperTheory.V.Z.Desc.DescWeak := by
  intro E _ _ _ hunr p _ S _ hsp _ n hn _ π hreg hd hsat
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  rcases hRun E hunr n hn1 π hreg hd (fun w hw => hsat w fun h => hw (hsp w h)) with h | ⟨D, h1, h2, h3, h4⟩
  · exact h
  obtain ⟨D', a, b, c, d⟩ := hP E n hn1 π hd D h1 h2 h3 h4
  exact absurd (hN E n hn1 π hreg hd D' a b c) d

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula
