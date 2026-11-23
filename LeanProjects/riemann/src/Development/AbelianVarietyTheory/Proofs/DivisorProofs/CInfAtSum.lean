import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothBumpComplexPointsProjectiveStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points

namespace GlobalTheory.CInfGlue

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem cInfAt_inv {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) (h0 : f y ≠ 0) :
    CInfAt (fun z => (f z)⁻¹) y := by
  obtain ⟨W, ι, _, g, G, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, fun v => (G v)⁻¹, O ∩ G ⁻¹' {0}ᶜ, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ isOpen_compl_singleton, ⟨h₃, ?_⟩,
    (h₄.mono Set.inter_subset_left).inv fun v hv => hv.2, h₅.mono fun z hz => by simp only [hz]⟩
  have := h₅.self_of_nhds
  simp only at this
  rw [Set.mem_preimage, ← this]
  exact h0

theorem cInfAt_mul {f g : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) (h' : CInfAt g y) :
    CInfAt (fun z => f z * g z) y :=
  h.comp₂ h' (G := fun x => x.1 * x.2) (contDiff_fst.mul contDiff_snd)

theorem cInfAt_sum {κ : Type} (s : Finset κ) (f : κ → CxPts p σ → ℝ) {y : CxPts p σ}
    (h : ∀ j ∈ s, CInfAt (f j) y) : CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const 0 y
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem cInfAt_cut {χ v : CxPts p σ → ℝ} {O : Set (CxPts p σ)} (hχ : ∀ z, CInfAt χ z)
    (hs : tsupport χ ⊆ O) (hv : ∀ z ∈ O, CInfAt v z) (z : CxPts p σ) :
    CInfAt (fun w => χ w * v w) z := by
  by_cases hz : z ∈ O
  · exact cInfAt_mul (hχ z) (hv z hz)
  · have h0 : χ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hz (hs h)
    refine (cInfAt_const 0 z).congr ?_
    filter_upwards [h0] with w hw
    simp [hw]

theorem glue : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (σ : k →+* ℂ) (T : Type) (m : T → CxPts p σ) (u : T → ℝ), (∀ x : CxPts p σ, ∃ (O : Set (CxPts p σ)) (v : CxPts p σ → ℝ), IsOpen O ∧ x ∈ O ∧ (∀ z ∈ O, CInfAt v z) ∧ ∀ t, m t ∈ O → v (m t) = u t) → ∃ v : CxPts p σ → ℝ, (∀ z, CInfAt v z) ∧ ∀ t, v (m t) = u t := by
  intro k _ X p hp σ T m u h
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hp
  choose O v hO hx hv hu using h
  choose χ hχ hχ0 hχx hχs using fun x => GlobalTheory.T.exists_smooth_bump_complexPoints_projective k X p hp σ x (O x) (hO x) (hx x)
  have hc : ∀ x, Continuous (χ x) := fun x =>
    continuous_iff_continuousAt.2 fun z => (hχ x z).continuousAt
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => {z | 0 < χ x z})
    (fun x => isOpen_lt continuous_const (hc x))
    (fun z _ => Set.mem_iUnion.2 ⟨z, hχx z⟩)
  have hS : ∀ z, 0 < ∑ x ∈ s, χ x z := fun z => by
    obtain ⟨x, hxs, hz⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ z))
    exact Finset.sum_pos' (fun j _ => hχ0 j z) ⟨x, hxs, hz⟩
  refine ⟨fun z => (∑ x ∈ s, χ x z * v x z) * (∑ x ∈ s, χ x z)⁻¹, fun z => ?_, fun t => ?_⟩
  · exact cInfAt_mul
      (cInfAt_sum s (fun x w => χ x w * v x w) fun x _ => cInfAt_cut (hχ x) (hχs x) (hv x) z)
      (cInfAt_inv (cInfAt_sum s χ fun x _ => hχ x z) (hS z).ne')
  · have e : ∀ x ∈ s, χ x (m t) * v x (m t) = χ x (m t) * u t := fun x _ => by
      by_cases h0 : χ x (m t) = 0
      · simp [h0]
      · rw [hu x t (hχs x (subset_tsupport _ h0))]
    simp only
    rw [Finset.sum_congr rfl e, ← Finset.sum_mul, mul_right_comm, mul_inv_cancel₀ (hS _).ne', one_mul]

end GlobalTheory.CInfGlue
