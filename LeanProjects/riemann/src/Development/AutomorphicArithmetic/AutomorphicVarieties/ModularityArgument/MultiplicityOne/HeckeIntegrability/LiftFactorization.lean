import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GL4GeometricSide.InnerEq

noncomputable section

open NumberField Matrix MeasureTheory Finset
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.GKCoh GlobalTheory.WigAlg
open PositivityTheory.Rg.BcB (thetaA)
open PositivityTheory.Rg.BcB.E (H)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.Desc
open PositivityTheory.RgTw (Mat G)
open UpperTheory.V.Z.GSp4Splitting
open scoped InnerProductSpace ComplexConjugate Classical

namespace UpperTheory.V.Z.Mult.Pi

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

def AbsGlobA : Prop :=
  ∀ (n : ℕ) (ι : Type) [Fintype ι] (lam : ι → Fin n → ℤ), (∀ i, Antitone (lam i)) → ∀ (E : ι → KMod n)
    (T : ∀ i, (E i).V →L[ℂ] (E i).V), (∀ i, IsLefK (lam i) (E i) (T i)) →
    ∀ [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure], ν Set.univ = 1 →
    ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] (E1 E2 : ι → Fin n → Fin n → Module.End ℂ U)
      (σ : ι → Un n →* (U →ₗ[ℂ] U)) (Θ : Module.End ℂ U) (P : ι → Module.End ℂ U) (J : Type) (R : J → Module.End ℂ U),
      (∀ i, IsLoc (infOf (lam i)) (E1 i) (E2 i) (σ i) Θ) → (∀ i, IsAvg ν (σ i) (E i) (T i) (P i)) →
      (∀ i j, i ≠ j → ∀ a b, (∀ c d, Commute (E1 i a b) (E1 j c d) ∧ Commute (E1 i a b) (E2 j c d) ∧ Commute (E2 i a b) (E2 j c d)) ∧
        ∀ k, Commute (E1 i a b) (σ j k) ∧ Commute (E2 i a b) (σ j k)) →
      (∀ i j, i ≠ j → ∀ k k', σ i k * σ j k' = σ j k' * σ i k) →
      (∀ j i, (∀ a b, Commute (R j) (E1 i a b) ∧ Commute (R j) (E2 i a b)) ∧ ∀ k, Commute (R j) (σ i k)) →
      (∀ j, ∃ j', ∀ x y, ⟪R j x, y⟫_ℂ = ⟪x, R j' y⟫_ℂ) → (∀ j, ∃ j', Θ * R j = R j' * Θ) → Θ * Θ = 1 →
      (∀ W : Submodule ℂ U, (∀ i a b, ∀ x ∈ W, E1 i a b x ∈ W ∧ E2 i a b x ∈ W) → (∀ j, ∀ x ∈ W, R j x ∈ W) → W = ⊥ ∨ W = ⊤) →
      Nontrivial U → FiniteDimensional ℂ (⨅ i, isoSp (σ i) (E i) : Submodule ℂ U) → (∀ i, isoSp (σ i) (E i) ≠ ⊥) →
      ∃ (Y : Submodule ℂ U) (c : ℂ), ‖c‖ = (2 ^ n) ^ Fintype.card ι ∧ FiniteDimensional ℂ Y ∧ Y ≠ ⊥ ∧ (∀ j, ∀ y ∈ Y, R j y ∈ Y) ∧ (∀ y ∈ Y, Θ y ∈ Y) ∧
        (∀ W ≤ Y, (∀ j, ∀ y ∈ W, R j y ∈ W) → W = ⊥ ∨ W = Y) ∧
        (∀ x, ((univ : Finset ι).toList.map P).prod x ∈ (⨅ i, isoSp (σ i) (E i) : Submodule ℂ U)) ∧
        ∀ j, trOn (⨅ i, isoSp (σ i) (E i)) (((univ : Finset ι).toList.map P).prod * R j * Θ) = c * trOn Y (R j * Θ)

def OpFormA : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μC : Measure (G n))
    [μC.IsHaarMeasure] [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E)))
    [μf.IsHaarMeasure] (μ : Measure (PositivityTheory.Rg.BcB.E.H E n 0)) [μ.IsHaarMeasure], ∃ c : ℂ, c ≠ 0 ∧ (1 ≤ n →
  ∀ π : CuspSub E n, ThetaFix π → ∀ K : Subgroup (GL (Fin n) (Af E)), IsOpen (K : Set (GL (Fin n) (Af E))) →
    IsCompact (K : Set (GL (Fin n) (Af E))) → (∀ k ∈ K, thetaF E n k ∈ K) → ∀ (D : Rl π K μf) (lam : InfinitePlace E → Fin n → ℤ),
    (∀ w, ChAt π w (lam w)) → ∀ [MeasurableSpace (Un n)] [BorelSpace (Un n)] (ν : Measure (Un n)) [ν.IsHaarMeasure], ν Set.univ = 1 →
    ∀ P : InfinitePlace E → Module.End ℂ D.U, (∀ w, IsAvg ν (D.σ w) (lefE n (lam w)) (lefT n (lam w)) (P w)) →
      ∀ (k : ∀ w, Mat n → ((lefE n (lam w)).V →L[ℂ] (lefE n (lam w)).V)) (val : InfinitePlace E → Inf n → ℂ) (T : InfinitePlace E → ℝ),
        (∀ w, IsMult μC (lefE n (lam w)) (k w) (val w) (T w)) → ∀ h, IsHeckeF K h → ∀ (ψ : π.V) (u : D.U),
          (D.i u).1.1 = heckeOp μf h ψ.1.1 → ∀ x, ∫ y, phiProd lam k h y * ψ.1.1 (x * y.1) ∂μ =
            c * (∏ w, val w (infOf (lam w))) * (D.i (((univ : Finset (InfinitePlace E)).toList.map P).prod u)).1.1 x)

def GlobalTwistedTraceBound : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μC : Measure (G n))
    [μC.IsHaarMeasure] [MeasurableSpace (GL (Fin n) (Af E))] [BorelSpace (GL (Fin n) (Af E))] (μf : Measure (GL (Fin n) (Af E)))
    [μf.IsHaarMeasure] (μ : Measure (PositivityTheory.Rg.BcB.E.H E n 0)) [μ.IsHaarMeasure], ∃ c₀ : ℝ, 0 < c₀ ∧ (1 ≤ n →
  ∀ π : CuspSub E n, (CG.mk π).IsRegAlg →
    ThetaFix π → ∀ lam : InfinitePlace E → Fin n → ℤ, (∀ w, Antitone (lam w)) →
    (∀ w, HasInfCharGL π.V w.embedding (Multiset.map (PositivityTheory.RgBcC.infOf (lam w) true) Finset.univ.val) ∧
      HasInfCharGL π.V (ComplexEmbedding.conjugate w.embedding)
        (Multiset.map (PositivityTheory.RgBcC.infOf (lam w) false) Finset.univ.val)) →
    ∀ K : Subgroup (GL (Fin n) (Af E)), IsOpen (K : Set (GL (Fin n) (Af E))) → IsCompact (K : Set (GL (Fin n) (Af E))) →
    (∀ k ∈ K, thetaF E n k ∈ K) → (∃ ψ ∈ π.V, ψ ≠ 0 ∧ ∀ k ∈ K, finRep E n k ψ = ψ) →
    ∃ (Y : Submodule ℂ (Sm E n)) (ρ : (GL (Fin n) (Af E) → ℂ) → Module.End ℂ Y) (A : Module.End ℂ Y) (c : ℂ),
      Y ≤ π.V ∧ FiniteDimensional ℂ Y ∧ Y ≠ ⊥ ∧ (∀ y ∈ Y, ∀ k ∈ K, finRep E n k y = y) ∧
      (∀ h, IsHeckeF K h → ∀ y : Y, (((ρ h y : Y) : Sm E n) : GA E n → ℂ) = heckeOp μf h ((y : Sm E n) : GA E n → ℂ)) ∧
      (∀ W : Submodule ℂ Y, (∀ h, IsHeckeF K h → ∀ y ∈ W, ρ h y ∈ W) → W = ⊥ ∨ W = ⊤) ∧
      A * A = 1 ∧ (∀ h, IsHeckeF K h → A * ρ h = ρ (fun g => h (thetaF E n g)) * A) ∧ ‖c‖ = c₀ ∧
      ∀ (k : ∀ w, PositivityTheory.RgTw.Mat n → ((PositivityTheory.RgBcC.lefE n (lam w)).V →L[ℂ] (PositivityTheory.RgBcC.lefE n (lam w)).V))
        (val : InfinitePlace E → PositivityTheory.RgBcC.Inf n → ℂ) (T : InfinitePlace E → ℝ),
        (∀ w, PositivityTheory.RgBcC.IsMult μC (PositivityTheory.RgBcC.lefE n (lam w)) (k w) (val w) (T w)) →
        ∀ h, IsHeckeF K h →
          IsTwTr μ π (phiProd lam k h) (c * (∏ w, val w (PositivityTheory.RgBcC.infOf (lam w))) * LinearMap.trace ℂ Y (ρ h * A)))

end UpperTheory.V.Z.Mult.Pi

end
