import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSpecialise
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

def HodgeFrameTransition.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (τ : Ψ) (c : (k : K) → ι k) (f : Ω)
    (bfr : Fin D.N → E τ) (z : (Σ k, ι k) → ℂ),
    z ∈ mcPts (mCoordIdeal D.y) → IsFrameOver D.y (D.W τ) c f bfr → InFrameDomain D.y c f z →
    ∃ (b' : Fin D.N → E τ) (R R' : Matrix (Fin D.N) (Fin D.N) Ω) (Rz R'z : Matrix (Fin D.N) (Fin D.N) ℂ),
      LinearIndependent Ω b' ∧ Submodule.span Ω (b' '' {i | (i : ℕ) < D.j}) = D.F τ ∧
      (∀ i, b' i = ∑ q, R q i • bfr q) ∧ (∀ q, bfr q = ∑ i, R' i q • b' i) ∧
      (∀ p q, IsValueAt D.y (R p q) z (Rz p q)) ∧ (∀ p q, IsValueAt D.y (R' p q) z (R'z p q)) ∧
      Rz * R'z = 1

def HodgeFibreSpan.Statement : Prop :=
  ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
    [∀ τ, Module Ω (E τ)] (D : ComponentDataHodge II Ψ K ι Ω E) (τ : Ψ) (bfr b' : Fin D.N → E τ)
    (R R' : Matrix (Fin D.N) (Fin D.N) Ω) (Rz R'z : Matrix (Fin D.N) (Fin D.N) ℂ) (z : (Σ k, ι k) → ℂ),
    z ∈ mcPts (mCoordIdeal D.y) → LinearIndependent Ω bfr → LinearIndependent Ω b' →
    Submodule.span Ω (b' '' {i | (i : ℕ) < D.j}) = D.F τ →
    (∀ i, b' i = ∑ q, R q i • bfr q) → (∀ q, bfr q = ∑ i, R' i q • b' i) →
    (∀ p q, IsValueAt D.y (R p q) z (Rz p q)) → (∀ p q, IsValueAt D.y (R' p q) z (R'z p q)) →
    fibreSub D τ bfr z = Submodule.span ℂ (Set.range fun a : Fin ((jIdx D : ℕ) + 1) => fun p =>
      firstCols Rz ((jIdx D : ℕ) + 1) (jIdx D).isLt p a)

def ColSpanFactor.Statement : Prop :=
  ∀ (N r : ℕ) (h : r ≤ N) (A g : Matrix (Fin N) (Fin N) ℂ), A.det ≠ 0 → g.det ≠ 0 →
    Submodule.span ℂ (Set.range fun a : Fin r => fun p => firstCols g r h p a) ≤
      Submodule.span ℂ (Set.range fun a : Fin r => fun p => firstCols A r h p a) →
    ∃ M : Matrix (Fin r) (Fin r) ℂ, firstCols g r h = firstCols A r h * M ∧ M.det ≠ 0

def FullColsFactor.Statement : Prop :=
  ∀ (N r : ℕ) (h : r ≤ N) (g : Matrix (Fin N) (Fin N) ℂ), N ≤ r → g.det ≠ 0 →
    ∃ M : Matrix (Fin r) (Fin r) ℂ, firstCols g r h = firstCols 1 r h * M ∧ M.det ≠ 0

def AltSumDet.Statement : Prop :=
  ∀ (N r : ℕ) (V : (Fin r → Fin N) → ℂ) (A : Matrix (Fin N) (Fin r) ℂ) (M : Matrix (Fin r) (Fin r) ℂ),
    (∀ q, ¬ Function.Injective q → V q = 0) →
    (∀ q (σ : Equiv.Perm (Fin r)), V (q ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * V q) →
    ∑ q, (∏ a, (A * M) (q a) a) * V q = M.det * ∑ q, (∏ a, A (q a) a) * V q

def PlueckerExpand.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (E : Type)
    [AddCommGroup E] [Module Ω E] (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (b : K → ℤ) (N r : ℕ)
    (φ : E [⋀^Fin r]→ₗ[Ω] Ω) (bfr : Fin N → E) (z : (Σ k, ι k) → ℂ) (V : (Fin r → Fin N) → ℂ)
    (A : Matrix (Fin N) (Fin r) Ω) (Az : Matrix (Fin N) (Fin r) ℂ),
    z ∈ mcPts (mCoordIdeal y) → (∀ q, IsTwValueAt y c b (φ (bfr ∘ q)) z (V q)) →
    (∀ p a, IsValueAt y (A p a) z (Az p a)) →
    (∀ q, ¬ Function.Injective q → V q = 0) ∧
    (∀ q (σ : Equiv.Perm (Fin r)), V (q ∘ σ) = ((Equiv.Perm.sign σ : ℤ) : ℂ) * V q) ∧
    ∃ w, IsValueAt y (φ (fun a => ∑ q, A q a • bfr q) * twistFactor y c b) z w ∧
      ∑ q, (∏ a, Az (q a) a) * V q = (∏ k, z ⟨k, c k⟩ ^ b k) * w

def SameSpanAltDet.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (r : ℕ) (u u' : Fin r → E),
    LinearIndependent Ω u → LinearIndependent Ω u' →
    Submodule.span Ω (Set.range u) = Submodule.span Ω (Set.range u') →
    ∃ δ : Ω, δ ≠ 0 ∧ ∀ φ : E [⋀^Fin r]→ₗ[Ω] Ω, φ u = δ * φ u'

def FrameSpanTop.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (E : Type)
    [AddCommGroup E] [Module Ω E] (N : ℕ) (y : (Σ k, ι k) → Ω) (W : ChartBundle ℤ (segreCoord y) N E)
    (c : (k : K) → ι k) (f : Ω) (b : Fin N → E),
    IsFrameOver y W c f b → Submodule.span Ω (Set.range b) = ⊤

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
