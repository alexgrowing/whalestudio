import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.VarMapInjective
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace FlagModelAlt

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def ValPoly (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) {σ : Type} (A : MvPolynomial σ Ω)
    (B : MvPolynomial σ ℂ) : Prop :=
  ∀ μ, IsValueAt y (A.coeff μ) z (B.coeff μ)

end Values

section GenPt

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

abbrev GV (D : ComponentData II Ψ K ι Ω E) : Type := (K ⊕ (Ψ × Fin (D.N - 1))) ⊕ (Ψ × Fin D.N × Fin D.N)

abbrev WedgeVals {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) (R : Type) : Type :=
  ∀ q : Ψ × Fin (D.N - 1), Fin (Pl.M q.1 q.2) → (Fin ((q.2 : ℕ) + 1) → Fin D.N) → R

def genPtR {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) {R : Type} [CommRing R]
    (x : (Σ k, ι k) → R) (V : WedgeVals Pl R) : (Σ k, Pl.ιY k) → MvPolynomial (GV D) R
  | ⟨Sum.inl k, t⟩ => X (Sum.inl (Sum.inl k)) * C (x ⟨k, t⟩)
  | ⟨Sum.inr q, m⟩ => X (Sum.inl (Sum.inr q)) *
      ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q m c)

def wedgeVals {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) (b : ∀ τ, Fin D.N → E τ) : WedgeVals Pl Ω :=
  fun q m c => Pl.gen q.1 q.2 m (exteriorPower.ιMulti Ω _ (b q.1 ∘ c))

def genPt {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) (b : ∀ τ, Fin D.N → E τ) :
    (Σ k, Pl.ιY k) → MvPolynomial (GV D) Ω :=
  genPtR Pl D.y (wedgeVals Pl b)

omit [DecidableEq Ψ] in
@[simp] theorem genPtR_inl {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) {R : Type} [CommRing R]
    (x : (Σ k, ι k) → R) (V : WedgeVals Pl R) (k : K) (t : ι k) :
    genPtR Pl x V ⟨Sum.inl k, t⟩ = X (Sum.inl (Sum.inl k)) * C (x ⟨k, t⟩) := rfl

omit [DecidableEq Ψ] in
@[simp] theorem genPtR_inr {D : ComponentData II Ψ K ι Ω E} (Pl : PlueckerData D) {R : Type} [CommRing R]
    (x : (Σ k, ι k) → R) (V : WedgeVals Pl R) (q : Ψ × Fin (D.N - 1)) (m : Fin (Pl.M q.1 q.2)) :
    genPtR Pl x V ⟨Sum.inr q, m⟩ = X (Sum.inl (Sum.inr q)) *
      ∑ c : Fin ((q.2 : ℕ) + 1) → Fin D.N,
        (∏ a, X (Sum.inr (q.1, headIdx (step_le q.2) a, c a))) * C (V q m c) := rfl

end GenPt

section Inhabitant

open Line

theorem genPt_line_inl :
    genPt linePlData linePlData.e ⟨Sum.inl (), (0 : Fin 2)⟩ =
      X (Sum.inl (Sum.inl ())) * C (lineDataHodgeZero.y ⟨(), 0⟩) := rfl

end Inhabitant

end FlagModelAlt

end GroundTheory.Heights₂.Heights.LowerBoundFree
