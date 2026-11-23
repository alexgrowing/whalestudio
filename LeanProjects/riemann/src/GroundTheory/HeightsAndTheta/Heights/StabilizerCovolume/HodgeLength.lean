import Mathlib
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.Objects
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements

open NumberField ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

section Herm

variable {Em : Type} [Field Em] [NumberField Em] [IsCMField Em] {Ψ : Type} [Fintype Ψ] {N j : ℕ}

def HermDatum.hodgeVec (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → Em) →+ EuclideanSpace ℂ (Ψ × Fin N) where
  toFun v := WithLp.toLp 2 fun p =>
    (Real.sqrt (2 * ‖A.emb p.1 A.ξ‖) : ℂ) * ((P p.1)⁻¹ *ᵥ fun a => A.emb p.1 (v a)) p.2
  map_zero' := by
    ext p
    have h0 : (fun a => A.emb p.1 ((0 : Fin N → Em) a)) = 0 := by
      ext
      simp
    simp only [h0]
    simp
  map_add' v w := by
    ext p
    have h0 : (fun a => A.emb p.1 ((v + w) a)) = (fun a => A.emb p.1 (v a)) + fun a => A.emb p.1 (w a) := by
      ext
      simp
    simp only [h0]
    simp [Matrix.mulVec_add, mul_add]

def HermDatum.hodgeLen (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) (v : Fin N → Em) : ℝ :=
  ‖A.hodgeVec P v‖

def HermDatum.firstMin (A : HermDatum Em Ψ N j) (P : Ψ → Matrix (Fin N) (Fin N) ℂ) : ℝ :=
  sInf {x | ∃ v ∈ A.L, v ≠ 0 ∧ A.hodgeLen P v = x}

end Herm

variable (Em : Type) [Field Em] [NumberField Em] in

def IsConjRadius (vr : ℝ) : Prop :=
  ∃ s : Finset (𝓞 Em), Submodule.span ℚ ((fun α : 𝓞 Em => (α : Em)) '' (s : Set (𝓞 Em))) = ⊤ ∧
    ∀ α ∈ s, ∀ σ : Em →+* ℂ, ‖σ (α : Em)‖ ≤ vr

namespace FullerData

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)] {Em : Type} [Field Em] [NumberField Em] [IsCMField Em]
  (D : FullerData II Ψ K ι Ω E Em)

def hodgeLen (z : (Σ k, ι k) → ℂ) (v : Fin D.N → Em) : ℝ :=
  D.herm.hodgeLen (D.per z) v

def firstMin (z : (Σ k, ι k) → ℂ) : ℝ :=
  D.herm.firstMin (D.per z)

end FullerData

namespace Gauss

end Gauss

namespace LineFuller

variable (II : IntersectionSystem)
  (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

theorem one_mem_interior :
    (fun _ => 1 : (Σ _ : Unit, Fin 2) → ℂ) ∈
      mcPts (mCoordIdeal (lineFuller II hII).y) \ (lineFuller II hII).Bd :=
  ⟨Line.mem_mcPts_line.2 ⟨0, one_ne_zero⟩, Set.notMem_empty _⟩

end LineFuller

end GroundTheory.Heights₂.Heights.NineStatements
