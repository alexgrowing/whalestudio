import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PnormInvStatement

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def x0F (X : Data E r) : Frame X.Ψ r := fun τ => (X.signature τ).choose

def OmF (X : Data E r) (x0 : Frame X.Ψ r) : Set (V (nd X)) := {z | cpt X x0 z ∈ X.dom}

def rhF (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : ℝ :=
  -∑ τ, Real.log ‖dmin X.Gm (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖

def eF (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : ℝ := rhF X x0 z + Real.log (1 + ‖z‖ ^ 2)

def densF (X : Data E r) (x0 : Frame X.Ψ r) (z : V (nd X)) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖dmin X.Gm (cpt X x0 z) τ i.castSucc‖ ^ (-2 : ℤ)

def muF (X : Data E r) (x0 : Frame X.Ψ r) : Measure (V (nd X)) :=
  (volume.restrict (OmF X x0)).withDensity fun z => ENNReal.ofReal (densF X x0 z)

def sat (X : Data E r) (x0 : Frame X.Ψ r) (C : Set (Frame X.Ψ r)) : Set (V (nd X)) :=
  {z | z ∈ OmF X x0 ∧ ∃ x ∈ C, ∃ b ∈ Bor X.Ψ r, cpt X x0 z = rmul x b}

def kaF (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) (z : V (nd X)) : ℝ := Real.exp (-bb * rhF X x0 z)

def IsOrth (X : Data E r) (x : Frame X.Ψ r) : Prop :=
  ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def poin (X : Data E r) (la : Wt X.Ψ r) (F : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  ∑' γ : X.Γ, (X.χ la γ.1)⁻¹ * F (lact γ.1 x)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up
