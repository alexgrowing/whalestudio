import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.GsFrCut

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section defs

variable (k r : ℕ)

def Xsp : Submodule ℂ (Fin (2 * r + k + 1) → ℂ) := Submodule.span ℂ (Set.range fun a : Fin r => bvec (eI k r a))

def Wsp (z : Fin (2 * r + k + 1) → ℂ) : Set (Fin (2 * r + k + 1) → ℂ) :=
  {v | inWb k r v ∧ herm (Hpk k r) v z = 0}

def wbPart (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0

def prW (z v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  wbPart k r v + (herm (Hpk k r) (wbPart k r v) z / (Tz k r z : ℂ)) • z

def xcof (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ b, (Zhat k r z z' g).adjugate b (Fin.last r) • (g *ᵥ fvec k r z' b)

def xcofL (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  ∑ a, star ((Zhat k r z z' g).adjugate (Fin.last r) a) • fvec k r z a

def omW (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ := prW k r z (xcof k r z z' g)

def omW' (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) : Fin (2 * r + k + 1) → ℂ :=
  prW k r z' (g⁻¹ *ᵥ xcofL k r z z' g)

end defs

structure GfBaseD (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) where
  nu : Fin (2 * r + k + 1) → ℂ
  nu' : Fin (2 * r + k + 1) → ℂ
  U0 : Set (Fin (2 * r + k + 1) → ℂ)
  nu_mem : nu ∈ Wsp k r z
  nu_unit : herm (Hpk k r) nu nu = 1
  nu'_mem : nu' ∈ Wsp k r z'
  nu'_unit : herm (Hpk k r) nu' nu' = 1
  isotropic_subspace_eq : ∀ u, u ∈ U0 ↔ u ∈ Wsp k r z ∧ herm (Hpk k r) u nu = 0
  isotropic_subspace_eq_primed : ∀ u, u ∈ U0 ↔ u ∈ Wsp k r z' ∧ herm (Hpk k r) u nu' = 0

def gfSig {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} (D0 : GfBaseD k r z z') : Set (B.Mat k r) :=
  {y | y ∈ B.GV k r ∧ 0 < Gf k r z z' y ∧
    (∃ t : ℝ, 0 < t ∧ omW k r z z' y = (t : ℂ) • D0.nu) ∧ (∃ t : ℝ, 0 < t ∧ omW' k r z z' y = (t : ℂ) • D0.nu') ∧
    ∀ u ∈ D0.U0, ∃ v ∈ Xsp k r, ∃ v' ∈ Xsp k r, y *ᵥ (u + v') = u + v}

def GfBase : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    Nonempty (GfBaseD k r z z')

def GfSat : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ y ∈ gfSig D0, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, n * y * n' ∈ gfSig D0

def GfStab : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ y ∈ gfSig D0, ∀ α ∈ UWset k r z, ∀ β ∈ UWset k r z',
      α * y * β ∈ gfSig D0 → Rel z z' y (α * y * β)

def GfLocal : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ D0 : GfBaseD k r z z', ∀ g₀ ∈ B.GV k r, 0 < Gf k r z z' g₀ →
      ∃ (O : Set (B.Mat k r)) (Fl : B.Mat k r → B.Mat k r × B.Mat k r),
        IsOpen O ∧ g₀ ∈ O ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Fl O ∧
        ∀ g ∈ O, g ∈ B.GV k r → 0 < Gf k r z z' g →
          (Fl g).1 ∈ UWset k r z ∧ (Fl g).2 ∈ UWset k r z' ∧ (Fl g).1 * g * (Fl g).2 ∈ gfSig D0

theorem gsSliceP_of_gf (hB : GfBase) (hS : GfSat) (hT : GfStab) (hL : GfLocal) : GsSliceP := by
  intro k r z z' hk hr hz hz'
  obtain ⟨D0⟩ := hB k r z z' hk hr hz hz'
  exact ⟨gfSig D0, hS k r z z' hk hr hz hz' D0, hT k r z z' hk hr hz hz' D0, hL k r z z' hk hr hz hz' D0⟩

theorem gramSlice_of_gf (hB : GfBase) (hS : GfSat) (hT : GfStab) (hL : GfLocal) : GramSlice :=
  gramSlice_of_slice (gsSliceP_of_gf hB hS hT hL)

theorem gsFrames_of_gf (hB : GfBase) (hS : GfSat) (hT : GfStab) (hL : GfLocal) : GsFrames :=
  gsFrames_of_slice (gsSliceP_of_gf hB hS hT hL)

end PI.UnitaryGroupMassFormula.GsFr
