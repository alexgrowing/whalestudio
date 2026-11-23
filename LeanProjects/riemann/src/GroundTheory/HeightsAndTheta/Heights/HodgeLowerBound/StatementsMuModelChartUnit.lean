import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelUnitSection
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuModelPointSteps
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

def IsMuLocalDatum {D : ComponentData II Ψ K ι Ω E} (H : HodgeData D) (c : (k : K) → ι k) (f : Ω)
    (b : ∀ τ, Fin D.N → E τ) (u : Ω) : Prop :=
  (∀ τ, IsAdaptedFrame D.y (D.W τ) (H.F τ) D.j_le_N c f (b τ)) ∧ IsUnitOn D.y c f u ∧
    H.Λ = (u * chartMono D.y c H.aMu) • PiTensorProduct.tprod Ω fun τ => quotWedge (H.F τ) D.j_le_N (b τ)

open Classical in

def MuModelChartUnit.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D)
    (H : HodgeData D.toComponentData), (∀ τ, H.F τ = D.F τ) →
    ∀ (c₀ : (k : K) → ι k) (f₀ : Ω) (b₀ : ∀ τ, Fin D.N → E τ) (u₀ : Ω), IsMuLocalDatum H c₀ f₀ b₀ u₀ →
    ∀ W : Ideal (MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ), W.IsPrime →
      (PXmu P).map (MvPolynomial.map (Int.castRingHom ℚ)) ≤ W →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant W →
      ∃ (dp dq : MuBlocks D → ℕ) (p q : MvPolynomial (Σ k : MuBlocks D, ιMu P k) ℚ),
        GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog p dp ∧
        GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog q dq ∧ p ∉ W ∧ q ∉ W ∧
        (∀ k, (dp k : ℤ) - dq k = muDeg D k - Sum.elim H.aMu (0 : Ψ ⊕ Ψ → ℤ) k) ∧
        aeval (muPointOf P b₀) p = (u₀⁻¹ * chartMono D.y c₀ (-H.aMu)) * aeval (muPointOf P b₀) q

def PlueckerFrameGen.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (P : PlueckerData D) (τ : Ψ) (i : Fin D.N)
    (c : (k : K) → ι k) (f : Ω) (b : Fin D.N → E τ), IsFrameOver D.y (D.W τ) c f b →
    (∀ m, ∃ n : ℕ, f ^ n * (P.gen τ i m (b ∘ Fin.castLE i.isLt) * twistFactor D.y c P.b) ∈
      chartRing ℤ (segreCoord D.y) c) ∧
    ∃ (M : ℕ) (a : Fin (P.M τ i) → Ω), (∀ m, a m ∈ chartRing ℤ (segreCoord D.y) c) ∧
      f ^ M = ∑ m, a m * (P.gen τ i m (b ∘ Fin.castLE i.isLt) * twistFactor D.y c P.b)

def WedgeTransition.Statement : Prop :=
  ∀ (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (F : ∀ τ, Submodule Ω (E τ)) (N j r s : ℕ) (hj : j ≤ N) (hr : r ≤ N) (hs : s ≤ N),
    r = j → s = N → ∀ b b' : ∀ τ, Fin N → E τ,
    (∀ τ, LinearIndependent Ω (b τ) ∧ Submodule.span Ω (Set.range (b τ)) = ⊤ ∧
      Submodule.span Ω (Set.range (b τ ∘ Fin.castLE hr)) = F τ) →
    (∀ τ, LinearIndependent Ω (b' τ) ∧ Submodule.span Ω (Set.range (b' τ)) = ⊤ ∧
      Submodule.span Ω (Set.range (b' τ ∘ Fin.castLE hr)) = F τ) →
    ∀ (φ : ∀ τ, E τ [⋀^Fin s]→ₗ[Ω] Ω) (ψ : ∀ τ, E τ [⋀^Fin r]→ₗ[Ω] Ω) (κ κ' : Ω),
      κ • PiTensorProduct.tprod Ω (fun τ => quotWedge (F τ) hj (b τ)) =
        κ' • PiTensorProduct.tprod Ω (fun τ => quotWedge (F τ) hj (b' τ)) →
      κ * ∏ τ, (φ τ (b τ ∘ Fin.castLE hs) * ψ τ (b' τ ∘ Fin.castLE hr)) =
        κ' * ∏ τ, (φ τ (b' τ ∘ Fin.castLE hs) * ψ τ (b τ ∘ Fin.castLE hr))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
