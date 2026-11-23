import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.StableBlock
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.FrameA
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RSplitCore2
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RGrowthPiJ
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalCharacter

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf TypeB TypeH)
open UpperTheory.V.Z.Tf.GlobalTraceComparison
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.Zero.ConvolutionTheory.EB

attribute [local instance] borelG borelF borelA borelH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

def intersection_update_fsHerm_neg_one (Z T : Finset (Pl E)) (φ : ∀ w : Pl E, LF a b w) (e : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) (w : Pl E) : LF a b w :=
  if w ∈ Z then φ w else if w ∈ T then fn2 a b w (e w) else (K2 a b w : Set _).indicator 1

def finU (S : Set (Pl E)) (u : GL (Fin n) E) (φ₁ φ₂ : ∀ w : Pl E, LF n 0 w) (g : GL (Fin n) (Af E)) : ℂ :=
  finFn S φ₁ φ₂ (g * (ratF E n u)⁻¹, 1)

def TIn (S : Set (Pl E)) (T : Finset (Pl E)) (e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) : Prop :=
  (∀ w ∈ T, w ∈ S) ∧ ∀ w ∈ T, ¬ IsSplitAt w → e₂ w = .one

def TEv (S : Set (Pl E)) (T : Finset (Pl E)) (e₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1))) : Prop :=
  (∀ w ∈ T, w ∈ S) ∧ ∀ w ∈ T, ¬ IsSplitAt w → ∀ x, (e₂ w).ev x = 1

def PiTerm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : CuspSub E n,
  (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.DualIsConj π → ∃ l : InfinitePlace E → DomWeight n,
    (∀ v, π.HasInfChar v.embedding (infOfWeight (l v))) ∧
    ∀ S : Set (Pl E), IsSection S → ∀ Z : Finset (Pl E), SplitIn S Z →
    ∀ (B : Pl E → Multiset ℂˣ) (τ : ∀ w : Pl E, SmIrr (GLw n w)), (∀ w, Off Z w → (CG.mk π).HasSat w (B w)) →
    (∀ w ∈ Z, π.IsLocComp w (τ w)) → ∀ u : GL (Fin n) E, IsTransl u →
    ∀ (μC : Measure (G n)) (μ : Measure (H E n 0)), μC.IsHaarMeasure → μ.IsHaarMeasure → ∃ c : ℂ, c ≠ 0 ∧
    ∀ φ₁ φ₂ : ∀ w : Pl E, LF n 0 w, (∀ w ∈ Z, Lc (K2 n 0 w) (φ₁ w) ∧ Lc (K2 n 0 w) (φ₂ w)) →
    ∀ T : Finset (Pl E), Disjoint T Z → ∀ (e₁ e₂ : Pl E → Ex (Fin (n + 1) × Fin (0 + 1)))
      (k : ∀ v, Mat n → ((lefE n (l v).w).V →L[ℂ] (lefE n (l v).w).V)) (vl : InfinitePlace E → Inf n → ℂ) (R : ℝ),
      TEv S T e₂ → (∀ v, IsMult μC (lefE n (l v).w) (k v) (vl v) R) →
      IsTwTr μ π (phiProd (fun v => (l v).w) k (finU S u (intersection_update_fsHerm_neg_one Z T φ₁ e₁) (intersection_update_fsHerm_neg_one Z T φ₂ e₂)))
        (c * (∏ v, vl v (infOf (l v).w)) * (∏ w ∈ Z, trc (τ w).ρ (KGL w n) fun g => seen φ₁ φ₂ w (g, 1)) * val T e₁ e₂ B 0)

def PiFin : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (D : Dom E n 0) (π : CuspSub E n),
  ThetaFix π → ∀ (μa : Measure (G n)) (μb : Measure (G 0)), μa.IsHaarMeasure → μb.IsHaarMeasure →
  ∀ (Ma : Mods E n) (Mb : Mods E 0) (κ : Type) (ka : Kers Ma) (kb : Kers Mb) va vb (R : ℝ) (ψ : Matrix κ κ (Hf E n 0 → ℂ))
    (U : Subgroup (Hf E n 0)), IsMults μa ka va R → IsMults μb kb vb R → IsFinM ψ → IsOpen (U : Set (Hf E n 0)) →
    (∀ x y, ∀ u ∈ U, ∀ h, ψ x y (u * h) = ψ x y h) → ∀ i j, FinOn D.μ π (tens ka kb ψ i j)

def PiAdm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (π : CuspSub E n), ThetaFix π →
  ∀ (K : Subgroup (GL (Fin n) (Af E))) (W : Submodule ℂ (Kinf E n → ℂ)), IsOpen (K : Set (GL (Fin n) (Af E))) →
    FiniteDimensional ℂ W → ∃ Y : Submodule ℂ (Sm E n), Y ≤ π.V ∧ FiniteDimensional ℂ Y ∧ ∀ ψ ∈ π.V, TypeB K W ψ → ψ ∈ Y

def TwTrSum : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (D : Dom E n 0) (π : CuspSub E n) (J : Type)
  (s : Finset J) (c : J → ℂ) (φ : J → H E n 0 → ℂ) (t : J → ℂ), (∀ j ∈ s, IsTestH (φ j) ∧ IsTwTr D.μ π (φ j) (t j)) →
    IsTwTr D.μ π (∑ j ∈ s, c j • φ j) (∑ j ∈ s, c j * t j)

end UpperTheory.Zero.ConvolutionTheory.EB
