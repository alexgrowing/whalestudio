import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfBis
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableBlockGA
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.SplitLineAlt

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
open scoped Classical

namespace UpperTheory.V.Z.Mult

def NoData : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∀ D : CD E n, ¬ D.Has π → D.Reg →
    (∀ᶠ w : Pl E in cofinite, ¬ IsSplitAt w → ∃ B, D.Sat w B ∧ inv B = B) →
    ¬ ∀ᶠ w : Pl E in cofinite, IsSplitAt w → ∃ B, D.Sat w B ∧ (CG.mk π).HasSat w B

def GeomTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → dimW lam ≠ 0 ∧
    ∀ f, GlobalTheory.BCT.IsTest (KL n) K' f → (∃ w ∈ S, ∀ y, f w y ≠ 0 → y.1.val.charpoly.Separable) →
      trOn (forms S lam K') (hop S K' f) = dimW lam * geomU S lam f

def LevTr : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (K' K'' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K'' → (∀ w, K'' w ≤ K' w) →
    ∀ f, GlobalTheory.BCT.IsTest (KL n) K' f → trOn (forms S lam K'') (hop S K'' f) = trOn (forms S lam K') (hop S K' f)

def EvalD : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (Z : Finset (Pl E)), SplitIn S Z → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' →
    (∀ w ∉ Z, K' w = KL n w) → ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ →
    ∃ (t : ι → ∀ w : Pl E, SmIrr (GLw n w)) (B : ι → Pl E → Multiset ℂˣ),
      (∀ i, (∀ w : Pl E, ¬ IsSplitAt w → IsUnramU (σ i) w) ∧ (∀ w ∈ Z, Cp (σ i) w (t i w)) ∧
        ∀ w, Off Z w → IsSplitAt w → ∃ τ, Cp (σ i) w τ ∧ HasSatGL w τ.ρ (B i w)) ∧
      ∀ f : ∀ w : Pl E, GLw n w → ℂ, (∀ w ∈ Z, IsHecke (K' w) fun x : UL n w => f w x.1) →
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ e₁ e₂ k, GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) ∧
        trOn (forms S lam K') (hop S K' (famU Z T f e₁ e₂ k)) =
          dimW lam * ∑ i, (∏ w ∈ Z, trc (t i w).ρ (KGL w n) (f w)) * val1 T e₁ e₂ (B i) ^ k

def CpUniq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ σ : Submodule ℂ (UA E n → ℂ), IsAutRepU σ → ∀ w, IsSplitAt w →
  ∀ τ τ' : SmIrr (GLw n w), Cp σ w τ → Cp σ w τ' →
    (∀ B, HasSatGL w τ.ρ B → HasSatGL w τ'.ρ B) ∧ ∀ f, trc τ.ρ (KGL w n) f = trc τ'.ρ (KGL w n) f

def LevInd : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → ∀ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) → K ≤ KL n w →
  ∃ f : GLw n w → ℂ, Lc (KGL w n) f ∧ (∀ K₁ ≤ K, IsHecke K₁ fun x : UL n w => f x.1) ∧
    ∀ τ : SmIrr (GLw n w), fixed (τ.ρ.comp (UL n w).subtype) K ≠ ⊥ → trc τ.ρ (KGL w n) f ≠ 0

def LcLev : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → ∀ f : GLw n w → ℂ, Lc (KGL w n) f →
  ∃ K : Subgroup (UL n w), IsOpen (K : Set (UL n w)) ∧ K ≤ KL n w ∧ IsHecke K fun x : UL n w => f x.1

def ChoiceM : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ π : CuspSub E n, (∀ w, ¬ IsSplitAt w → ∃ B, (CG.mk π).HasSat w B) →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ S : Set (Pl E), IsSection S →
  ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w, ¬ IsSplitAt w → K' w = KL n w) →
  ∃ (Z : Finset (Pl E)) (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)) (w₀ : Pl E) (f₀ : GLw n w₀ → ℂ),
    SplitIn S Z ∧ (∀ w ∈ S, w ∉ Z → K' w = KL n w) ∧ (∀ w, Off Z w → (CG.mk π).HasSat w (B w) ∧ μ.UnrAt w) ∧
    (∀ w ∈ Z, π.IsLocComp w (τ w)) ∧ w₀ ∈ Z ∧ Lc (KGL w₀ n) f₀ ∧ trc (τ w₀).ρ (KGL w₀ n) f₀ ≠ 0 ∧
    ∀ y, f₀ y ≠ 0 → y.val.charpoly.Separable

def OffSec : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)) (K' K'' : ∀ w : Pl E, Subgroup (UL n w)), (∀ w ∈ S, K' w = K'' w) →
  globLev S K' = globLev S K''

def CountAt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∀ S : Set (Pl E), IsSection S →
  ∀ (lam : InfinitePlace E → DomWeight n) (Z : Finset (Pl E)), SplitIn S Z →
  ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w ∉ Z, K' w = KL n w) →
    ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ →
    ∃ (J : Type) (_ : Fintype J) (C : J → Pl E → Multiset ℂˣ),
      (∀ j, ∃ w, Off Z w ∧ IsSplitAt w ∧ (B w).card = n ∧ (C j w).card = n ∧ C j w ≠ B w) ∧
      ∀ f : ∀ w : Pl E, GLw n w → ℂ, (∀ w ∈ Z, IsHecke (K' w) fun x : UL n w => f w x.1) →
      ∀ T : Finset (Pl E), SplitIn S T → Disjoint T Z → ∀ e₁ e₂, val1 T e₁ e₂ B = 1 → (∀ j, val1 T e₁ e₂ (C j) = 0) →
        ∀ k, GlobalTheory.BCT.IsTest (KL n) K' (famU Z T f e₁ e₂ k) ∧ (1 ≤ k → trOn (forms S lam K') (hop S K' (famU Z T f e₁ e₂ k)) =
          dimW lam * ((Nat.card {i // At π (σ i)} : ℂ) * ∏ w ∈ Z, trc (τ w).ρ (KGL w n) (f w)))

def RCountAt : Prop := CompOf → EvalD → CpUniq → Places → CountAt

def Ident : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ lam : InfinitePlace E → DomWeight n, ∃ a : ℝ, 0 < a ∧
  ∀ π : CuspSub E n, (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → (∀ v, π.HasInfChar v.embedding (infOfWeight (lam v))) →
  ∀ (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ S : Set (Pl E), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
  ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)) (f : ∀ w : Pl E, GLw n w → ℂ),
    (∀ w, Off Z w → (CG.mk π).HasSat w (B w) ∧ μ.UnrAt w) →
    (∀ w ∈ Z, π.IsLocComp w (τ w) ∧ Lc (KGL w n) (f w) ∧ trc (τ w).ρ (KGL w n) (f w) ≠ 0) →
    (∃ w ∈ Z, ∀ y, f w y ≠ 0 → y.val.charpoly.Separable) →
    ∀ K' : ∀ w : Pl E, Subgroup (UL n w), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → (∀ w ∉ Z, K' w = KL n w) →
    (∀ w ∈ Z, IsHecke (K' w) fun x : UL n w => f w x.1) →
    ∀ (ι : Type) [Fintype ι] (σ : ι → Submodule ℂ (UA E n → ℂ)), IsDec S lam K' σ → (Nat.card {i // At π (σ i)} : ℝ) = a

def RIdent : Prop := NoData → CountAt → GeomTr → G2s → MatchUnit → MatchSplit → EndoBlockS → StableBlockSA → Ident

def RMult : Prop := Ident → CountAt → LevTr → GeomTr → LevInd → LcLev → ChoiceM → OffSec → MuEx → Mult

end UpperTheory.V.Z.Mult
