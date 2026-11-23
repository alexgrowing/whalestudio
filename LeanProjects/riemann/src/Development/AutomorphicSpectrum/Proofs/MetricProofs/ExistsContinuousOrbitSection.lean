import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan

section Inverse

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem notMem_mcPts_top_inv (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := by
  intro h
  have h1 := h.2 1 trivial
  simp at h1

theorem minors_of_sameOrbit_inv {a z : (Σ k, ι k) → ℂ} (h : SameOrbit a z) (k : K) (i i' : ι k) :
    a ⟨k, i⟩ * z ⟨k, i'⟩ = a ⟨k, i'⟩ * z ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  show c k * z ⟨k, i⟩ * z ⟨k, i'⟩ = c k * z ⟨k, i'⟩ * z ⟨k, i⟩
  ring

theorem sameOrbit_of_minors_inv {a z : (Σ k, ι k) → ℂ} (ha : ∀ k, ∃ i, a ⟨k, i⟩ ≠ 0)
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (h : ∀ (k : K) (i i' : ι k), a ⟨k, i⟩ * z ⟨k, i'⟩ = a ⟨k, i'⟩ * z ⟨k, i⟩) : SameOrbit a z := by
  choose q hq using hz
  refine ⟨fun k => a ⟨k, q k⟩ / z ⟨k, q k⟩, fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := ha k
    refine div_ne_zero (fun h0 => hi ?_) (hq k)
    have h1 := h k i (q k)
    rw [h0, zero_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hq k)
  · funext ⟨k, i⟩
    show a ⟨k, i⟩ = a ⟨k, q k⟩ / z ⟨k, q k⟩ * z ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hq k)]
    exact h k i (q k)

end Inverse

theorem exists_continuousOn_inv_pts : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (e : ℕ) (R : AnLogRes P ⊤ e), Nonempty R.X →
    ∃ r : ((Σ k, ι k) → ℂ) → R.X, (∀ z ∈ mcPts P, SameOrbit (R.lift (r z) (r z)) z) ∧
      ContinuousOn r (mcPts P) := by
  intro K _ ι _ P e R hX
  have hs : ∀ z ∈ mcPts P, ∃ x, SameOrbit (R.lift x x) z :=
    fun z hz => R.surj z hz (notMem_mcPts_top_inv z)
  choose! r hr using hs
  refine ⟨r, hr, fun z₀ hz₀ => ?_⟩
  refine isCompact_univ.le_nhds_of_unique_clusterPt (by simp) fun x' _ hx' => ?_
  obtain ⟨G, hG, hGr⟩ := mapClusterPt_iff_ultrafilter.mp hx'
  have hUx : R.U x' ∈ 𝓝 x' := (R.isOpen_U x').mem_nhds (R.mem_U x')
  have hGS : ∀ᶠ z in (G : Filter _), z ∈ mcPts P := hG self_mem_nhdsWithin
  have hGU : ∀ᶠ z in (G : Filter _), r z ∈ R.U x' := hGr hUx
  have hGz : (G : Filter _) ≤ 𝓝 z₀ := hG.trans nhdsWithin_le_nhds
  have hmin : ∀ᶠ z in (G : Filter _), SameOrbit (R.lift x' (r z)) z := by
    filter_upwards [hGS, hGU] with z h1 h2
    exact orbit_trans (R.compat x' (r z) (r z) ⟨h2, R.mem_U _⟩) (hr z h1)
  have ha : ∀ p, Tendsto (fun z => R.lift x' (r z) p) (G : Filter _) (𝓝 (R.lift x' x' p)) :=
    fun p => (((continuousOn_lift R x' p).continuousAt hUx).tendsto).comp hGr
  have hzc : ∀ p, Tendsto (fun z : (Σ k, ι k) → ℂ => z p) (G : Filter _) (𝓝 (z₀ p)) :=
    fun p => ((continuous_apply p).tendsto z₀).comp hGz
  have hsame : SameOrbit (R.lift x' x') z₀ :=
    sameOrbit_of_minors_inv (R.mem x' x' (R.mem_U x')).1 hz₀.1 fun k i i' =>
      tendsto_nhds_unique_of_eventuallyEq ((ha _).mul (hzc _)) ((ha _).mul (hzc _))
        (hmin.mono fun z hz => minors_of_sameOrbit_inv hz k i i')
  exact R.inj x' (r z₀) (notMem_mcPts_top_inv _) (orbit_trans hsame (orbit_symm (hr z₀ hz₀)))

end GlobalTheory.CompanionTheory.Ar.PB.WMan
