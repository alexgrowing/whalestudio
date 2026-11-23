import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExphOnEmpty
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.ChernReg
open scoped TensorProduct ContDiff

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernReg.ExphOn

open Set GlobalTheory.ChartGlue

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

def glue (c : AlgChart p σ d) (ρ : CxPts p σ → ℝ) (E E' : ChartMap p σ d) : ChartMap p σ d :=
  fun c₀ y ξ => if ρ y = 0 then E c₀ y ξ else c.e.symm ((1 - ρ y) • c.e (E c₀ y ξ) + ρ y • c.e (E' c₀ y ξ))

theorem glue_trans (c : AlgChart p σ d) (ρ : CxPts p σ → ℝ) {E E' : ChartMap p σ d}
    (hE : ∀ (c c' : AlgChart p σ d), ∀ y ∈ c.e.source, y ∈ c'.e.source → ∀ ξ, E c y ξ = E c' y (c.dtrans c' y ξ))
    (hE' : ∀ (c c' : AlgChart p σ d), ∀ y ∈ c.e.source, y ∈ c'.e.source → ∀ ξ, E' c y ξ = E' c' y (c.dtrans c' y ξ)) :
    ∀ (c₀ c₁ : AlgChart p σ d), ∀ y ∈ c₀.e.source, y ∈ c₁.e.source → ∀ ξ,
      glue c ρ E E' c₀ y ξ = glue c ρ E E' c₁ y (c₀.dtrans c₁ y ξ) := by
  intro c₀ c₁ y h₀ h₁ ξ
  simp only [glue, hE c₀ c₁ y h₀ h₁ ξ, hE' c₀ c₁ y h₀ h₁ ξ]

theorem glue_zero (c : AlgChart p σ d) {ρ : CxPts p σ → ℝ} {E E' : ChartMap p σ d} {W W' W₀ O₁ : Set (CxPts p σ)}
    (hE : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, y ∈ W → E c y 0 = y)
    (hE' : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, y ∈ W' → E' c y 0 = y)
    (hW₀ : W₀ ⊆ W) (hO₁ : ∀ y ∈ O₁, ρ y = 1) (hρ : ∀ y, ρ y ≠ 0 → y ∈ W') (hW' : W' ⊆ c.e.source) :
    ∀ c₀ : AlgChart p σ d, ∀ y ∈ c₀.e.source, y ∈ W₀ ∪ O₁ → glue c ρ E E' c₀ y 0 = y := by
  intro c₀ y hy hW
  unfold glue
  split_ifs with h
  · rcases hW with hW | hW
    · exact hE c₀ y hy (hW₀ hW)
    · exact absurd (hO₁ y hW) (by rw [h]; exact zero_ne_one)
  · have h' := hρ y h
    rw [hE' c₀ y hy h']
    rcases hW with hW | hW
    · rw [hE c₀ y hy (hW₀ hW), ← add_smul, sub_add_cancel, one_smul]
      exact c.e.left_inv (hW' h')
    · rw [hO₁ y hW, sub_self, zero_smul, zero_add, one_smul]
      exact c.e.left_inv (hW' h')

theorem contDiffAt_trans (c c' : AlgChart p σ d) {v : ReciprocityTheory.L2DbarEstimates.V d} (hv : v ∈ c.e.target)
    (hv' : c.e.symm v ∈ c'.e.source) : ContDiffAt ℝ ∞ (c'.e ∘ c.e.symm) v := by
  have ho := isOpen_over c.e c'.e.open_source
  have h : ContDiffOn ℂ ∞ (c'.e ∘ c.e.symm) (c.e.target ∩ c.e.symm ⁻¹' c'.e.source) :=
    (contDiffOn_piLp 2).2 fun a => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn d _ _ ho
      (differentiableOn_euclidean.1 (c.holo_trans c') a)
  exact ((h.contDiffAt (ho.mem_nhds ⟨hv, hv'⟩)).restrict_scalars ℝ)

theorem exists_ball_subset (c : AlgChart p σ d) {L : Set (CxPts p σ)} (hL : IsCompact L) (hLs : L ⊆ c.e.source) :
    ∃ r > 0, ∀ y ∈ L, Metric.ball (c.e y) r ⊆ c.e.target := by
  obtain ⟨r, hr, h⟩ := (hL.image_of_continuousOn (c.e.continuousOn.mono hLs)).exists_thickening_subset_open
    c.e.open_target (image_subset_iff.2 fun y hy => c.e.map_source (hLs hy))
  exact ⟨r, hr, fun y hy => (Metric.ball_subset_thickening (mem_image_of_mem _ hy) r).trans h⟩

theorem exists_open_closure_subset {X : Type} [TopologicalSpace X] [T2Space X] [CompactSpace X] {K W : Set X}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) : ∃ W₀, IsOpen W₀ ∧ K ⊆ W₀ ∧ closure W₀ ⊆ W := by
  obtain ⟨W₀, h₁, h₂, h₃, -⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  exact ⟨W₀, h₁, h₂, h₃⟩

end GlobalTheory.ChernReg.ExphOn
