import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.StableBlockGA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.Zero.ConvolutionTheory.EB
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical
open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

namespace UpperTheory.V.Z.Mult.Pi

attribute [local instance] borelG borelF borelA borelH

def RankOne : Prop := ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] (f A : Module.End ℂ Y), f * f = f → A * A = 1 →
  A * f = f * A → (∀ x, ∃ c : ℂ, f * x * f = c • f) → LinearMap.trace ℂ Y (f * A) = 0 ∨ ‖LinearMap.trace ℂ Y (f * A)‖ = 1

def Corner : Prop := ∀ (I : Type) [Fintype I] (J : I → Type) (Y : Type) [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] [Nontrivial Y]
  (a b : ∀ i, J i → Module.End ℂ Y) (e e' : I → Module.End ℂ Y),
    (∀ i k, i ≠ k → ∀ f g, Commute (a i f) (a k g)) → (∀ i k f g, Commute (a i f) (b k g)) →
    (∀ i k, i ≠ k → ∀ f g, Commute (b i f) (b k g)) →
    (∀ W : Submodule ℂ Y, (∀ i f, ∀ x ∈ W, a i f x ∈ W ∧ b i f x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ i, e i ∈ Algebra.adjoin ℂ (Set.range (a i)) ∧ e i * e i = e i ∧
      ∀ x ∈ Algebra.adjoin ℂ (Set.range (a i)), ∃ c : ℂ, e i * x * e i = c • e i) →
    (∀ i, e' i ∈ Algebra.adjoin ℂ (Set.range (b i)) ∧ e' i * e' i = e' i ∧
      ∀ x ∈ Algebra.adjoin ℂ (Set.range (b i)), ∃ c : ℂ, e' i * x * e' i = c • e' i) →
    ∀ f, f = ((Finset.univ : Finset I).toList.map fun i => e i * e' i).prod → f * f = f ∧ ∀ x, ∃ c : ℂ, f * x * f = c • f

def MinIdem : Prop := ∀ (J M Y : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M] [AddCommGroup Y] [Module ℂ Y]
  (α : J → Module.End ℂ M) (a : J → Module.End ℂ Y), (∀ W : Submodule ℂ M, (∀ f, ∀ x ∈ W, α f x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ p, FreeAlgebra.lift ℂ α p = 0 → FreeAlgebra.lift ℂ a p = 0) → ∃ p : FreeAlgebra ℂ J,
      LinearMap.trace ℂ M (FreeAlgebra.lift ℂ α p * FreeAlgebra.lift ℂ α p) = 1 ∧
      FreeAlgebra.lift ℂ a p * FreeAlgebra.lift ℂ a p = FreeAlgebra.lift ℂ a p ∧
      ∀ q, ∃ c : ℂ, FreeAlgebra.lift ℂ a p * FreeAlgebra.lift ℂ a q * FreeAlgebra.lift ℂ a p = c • FreeAlgebra.lift ℂ a p

def AbsCoreA : Prop := ∀ (I : Type) [Fintype I] (J M : I → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
  [∀ i, FiniteDimensional ℂ (M i)] (Y : Type) [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y] [Nontrivial Y]
  (α : ∀ i, J i → Module.End ℂ (M i)) (a b : ∀ i, J i → Module.End ℂ Y) (A : Module.End ℂ Y),
    (∀ i, ∀ W : Submodule ℂ (M i), (∀ f, ∀ x ∈ W, α i f x ∈ W) → W = ⊥ ∨ W = ⊤) →
    (∀ i p, FreeAlgebra.lift ℂ (α i) p = 0 → FreeAlgebra.lift ℂ (a i) p = 0) →
    (∀ i k, i ≠ k → ∀ f g, Commute (a i f) (a k g)) → (∀ i k f g, Commute (a i f) (b k g)) →
    A * A = 1 → (∀ i f, A * a i f = b i f * A) →
    (∀ W : Submodule ℂ Y, (∀ i f, ∀ x ∈ W, a i f x ∈ W ∧ b i f x ∈ W) → W = ⊥ ∨ W = ⊤) →
    ∃ d : ℂ, ‖d‖ = 1 ∧ ∀ f g : ∀ i, J i,
      LinearMap.trace ℂ Y (((Finset.univ : Finset I).toList.map fun i => a i (f i) * b i (g i)).prod * A) =
        d * ∏ i, LinearMap.trace ℂ (M i) (α i (f i) * α i (g i))

def ZTrA : Prop := ForLev fun E _ _ _ n S Z N => ∀ π (y : Yd π (Lev S N)) (τ : ∀ w : Pl E, SmIrr (GLw n w)),
  (∀ w ∈ Z, π.IsLocComp w (τ w)) → (∀ w ∈ Z, fixed (τ w).ρ (N w) ≠ ⊥) ∧ ∃ d : ℂ, ‖d‖ = 1 ∧ ∀ F, Fam S N (Z ×ˢ Finset.univ) F →
    LinearMap.trace ℂ y.Y (y.r (pf S F) * y.A) =
      d * ∏ w ∈ Z, GlobalTheory.BCT.trOn (fixed (τ w).ρ (N w)) (Lv (τ w).ρ (N w) (F w false) * Lv (τ w).ρ (N w) (F w true))

def SeenTrA : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E), IsSplitAt w → ∀ (τ : SmIrr (GLw n w))
  (N : Subgroup (GLw n w)), IsOpen (N : Set (GLw n w)) → N ≤ KGL w n → ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w,
    (∀ b, IsHecke N (two φ₁ φ₂ w b)) →
      GlobalTheory.BCT.trOn (fixed τ.ρ N) (Lv τ.ρ N (two φ₁ φ₂ w false) * Lv τ.ρ N (two φ₁ φ₂ w true)) =
        ((N.relIndex (KGL w n) : ℕ) : ℂ) ^ 2 * trc τ.ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)

def ToYdA : Prop := ForLev fun E _ _ _ n S _ N => ∀ (π : CuspSub E n) (u : GL (Fin n) E), IsTransl u →
  (∀ k ∈ Lev S N, thetaF E n k ∈ Lev S N) ∧
  ∀ (μf : Measure (GF E n)), μf.IsHaarMeasure → ∀ (Y : Submodule ℂ (Sm E n)) (ρ : (GF E n → ℂ) → Module.End ℂ Y) (A : Module.End ℂ Y),
    Y ≤ π.V → FiniteDimensional ℂ Y → Y ≠ ⊥ → (∀ y ∈ Y, ∀ k ∈ Lev S N, finRep E n k y = y) → IsHeckeAct μf (Lev S N) Y ρ →
    (∀ W : Submodule ℂ Y, (∀ h, IsHeckeF (Lev S N) h → ∀ y ∈ W, ρ h y ∈ W) → W = ⊥ ∨ W = ⊤) → A * A = 1 →
    (∀ h, IsHeckeF (Lev S N) h → A * ρ h = ρ (fun g => h (thetaF E n g)) * A) →
    ∃ (y : Yd π (Lev S N)) (v : ℂ), v = (((μf (Lev S N : Set (GF E n))).toReal : ℝ) : ℂ) ∧ ∀ h, IsHecke (Lev S N) h → IsHeckeF (Lev S N) (fun g => h (g * (ratF E n u)⁻¹)) ∧
      LinearMap.trace ℂ Y (ρ (fun g => h (g * (ratF E n u)⁻¹)) * A) = v * LinearMap.trace ℂ y.Y (y.r h * y.A)

def LevelTrA : Prop := ForLev fun E _ _ _ n S Z N => ∀ π (y : Yd π (Lev S N)) (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)),
  (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) → (∀ w ∈ Z, π.IsLocComp w (τ w)) →
    (∃ φ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ N' ≤ N w, ∀ b, IsHecke N' (two φ φ w b)) ∧
      (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ φ w (g, 1)) ≠ 0) ∧
    ∃ d : ℂ, ‖d‖ = ∏ w ∈ Z, (((N w).relIndex (KGL w n) : ℕ) : ℝ) ^ 2 ∧ ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, ∀ b, IsHecke (N w) (two φ₁ φ₂ w b)) →
      ∀ T : Finset (Pl E), Disjoint T Z → ∀ e₁ e₂, TEv S T e₂ →
        IsHecke (Lev S N) (fun g => finFn S (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) (g, 1)) ∧
        LinearMap.trace ℂ y.Y (y.r (fun g => finFn S (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂) (g, 1)) * y.A) =
          d * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0

def LevIdx : Prop := ForLev fun E _ _ _ n S Z N => Lev S N ≤ Kf E n ∧
  (Lev S N).relIndex (Kf E n) = ∏ w ∈ Z, (N w).relIndex (KGL w n) ^ 2

def VolIdx : Prop := ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [MeasurableSpace Γ] [BorelSpace Γ]
  (μ : Measure Γ) [μ.IsHaarMeasure] (K K' : Subgroup Γ), IsOpen (K' : Set Γ) → IsCompact (K : Set Γ) → K' ≤ K →
    (μ K').toReal * (K'.relIndex K : ℕ) = (μ K).toReal

end UpperTheory.V.Z.Mult.Pi

end
