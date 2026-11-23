import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LogPair

def SameDiv {X : Scheme.{0}} {L M : LB X} (σ : L.Sec) (τ : M.Sec) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (i : L.ι) (j : M.ι) (hi : U ≤ L.U i) (hj : U ≤ M.U j) (u : Γ(X, U)ˣ),
    x ∈ U ∧ resG X hi (σ.f i) = (u : Γ(X, U)) * resG X hj (τ.f j)

theorem SameDiv.refl {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (σ : L.Sec) : SameDiv σ σ := fun x => by
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hL.cover.ge (Set.mem_univ x))
  exact ⟨L.U i, i, i, le_rfl, le_rfl, 1, hi, by simp⟩

theorem SameDiv.symm {X : Scheme.{0}} {L M : LB X} {σ : L.Sec} {τ : M.Sec} (h : SameDiv σ τ) : SameDiv τ σ :=
  fun x => by
    obtain ⟨U, i, j, hi, hj, u, hx, e⟩ := h x
    exact ⟨U, j, i, hj, hi, u⁻¹, hx, by rw [e, Units.inv_mul_cancel_left]⟩

end GlobalTheory.LogPair
