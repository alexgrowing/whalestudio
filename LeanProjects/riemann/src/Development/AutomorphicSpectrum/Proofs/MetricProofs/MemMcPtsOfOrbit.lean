import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBaseChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionCompactEmbedded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.PB.Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev PtsOf (P : Ideal (MRing ι)) : Type := ↥(Pts (pC P))

theorem proj_eq_of_orbit {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) : proj z = proj w := by
  obtain ⟨c, hc, rfl⟩ := h
  exact Top.proj_smul c hc w

theorem orbit_of_proj {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (h : proj z = proj w) : SameOrbit z w := by
  refine orbit_of_cross hz hw fun k i i' => ?_
  obtain ⟨j, hj⟩ := hz k
  have hN : ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos (hz k)).ne'
  have hM : ((∑ l, ‖w ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos (hw k)).ne'
  have hj' : starRingEnd ℂ (z ⟨k, j⟩) ≠ 0 := by simpa using hj
  have h1 := congrFun h ⟨k, (i, j)⟩
  have h2 := congrFun h ⟨k, (i', j)⟩
  simp only [proj] at h1 h2
  rw [div_eq_div_iff hN hM] at h1 h2
  have : (z ⟨k, i⟩ * w ⟨k, i'⟩ - z ⟨k, i'⟩ * w ⟨k, i⟩) *
      (starRingEnd ℂ (z ⟨k, j⟩) * ((∑ l, ‖w ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ)) = 0 := by
    linear_combination (w ⟨k, i'⟩) * h1 - (w ⟨k, i⟩) * h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (mul_ne_zero hj' hM))

variable {P : Ideal (MRing ι)} {e : ℕ}

theorem rep_mem_mcPts (x : PtsOf P) : rep x ∈ mcPts P :=
  (mem_mcPts_iff_conePts_pC P _).2 (rep_mem x)

theorem pts_eq_of_orbit {x y : PtsOf P} (h : SameOrbit (rep x) (rep y)) : x = y := by
  apply Subtype.ext
  rw [← proj_rep x, ← proj_rep y]
  exact proj_eq_of_orbit h

def cls (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) : PtsOf P :=
  ⟨proj z, z, (mem_mcPts_iff_conePts_pC P z).1 hz, rfl⟩

theorem rep_cls_orbit (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) : SameOrbit (rep (cls z hz)) z :=
  orbit_of_proj (rep_mem_mcPts _).1 hz.1 (proj_rep (cls z hz))

theorem mem_mcPts_of_orbit (hP : IsMultiHomogIdeal P) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (h : SameOrbit z' z) : z' ∈ mcPts P := by
  have hz' := (mem_mcPts_iff_conePts_pC P z).1 hz
  refine (mem_mcPts_iff_conePts_pC P z').2 ⟨fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, fun h0 => hi (by
      obtain ⟨c, hc, rfl⟩ := h
      have : c k * z ⟨k, i⟩ = 0 := h0
      exact (mul_eq_zero.1 this).resolve_left (hc k))⟩
  · obtain ⟨c, hc, rfl⟩ := h
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul (isMultiHomogIdeal_pC hP) c z hz'.2

theorem orbit_aff (p : (k : K) → ι k) {x : PtsOf P} (hx : x ∈ src (pC P) p) :
    SameOrbit (affCoord p (rep x)) (rep x) := by
  refine ⟨fun k => (rep x ⟨k, p k⟩)⁻¹, fun k => inv_ne_zero (hx k), ?_⟩
  funext q
  simp [affCoord, div_eq_inv_mul]

theorem exists_alt_variant (x : PtsOf P) : ∃ p : (k : K) → ι k, x ∈ src (pC P) p := by
  choose p hp using (rep_mem_mcPts x).1
  exact ⟨p, hp⟩

theorem continuousOn_aff (p : (k : K) → ι k) :
    ContinuousOn (fun x : PtsOf P => affCoord p (rep x)) (src (pC P) p) :=
  continuousOn_iff_continuous_restrict.2 (Top.isEmbedding_affCoord p).continuous

def srcOf (C : OrbitChart P e) : Set (PtsOf P) := {x | rep x ∈ C.O}

theorem mem_O_of_orbit (C : OrbitChart P e) (hP : IsMultiHomogIdeal P) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ C.O)
    (h : SameOrbit z' z) (hzP : z ∈ mcPts P) : z' ∈ C.O :=
  C.O_orbit z hz z' (mem_mcPts_of_orbit hP hzP h) h

theorem isOpen_srcOf (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) : IsOpen (srcOf C) := by
  obtain ⟨O', hO', hO⟩ := C.O_open
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨p, hp⟩ := exists_alt_variant x
  have hS : src (pC P) p ∈ 𝓝 x := (Top.isOpen_alt_bis p).mem_nhds hp
  have hc : ContinuousAt (fun y : PtsOf P => affCoord p (rep y)) x := (continuousOn_aff p).continuousAt hS
  have hax : affCoord p (rep x) ∈ C.O :=
    mem_O_of_orbit C hP hx (orbit_aff p hp) (rep_mem_mcPts x)
  have hax' : affCoord p (rep x) ∈ O' := by rw [hO] at hax; exact hax.1
  filter_upwards [hS, hc (hO'.mem_nhds hax')] with y hy hy'
  have h1 : affCoord p (rep y) ∈ mcPts P := mem_mcPts_of_orbit hP (rep_mem_mcPts y) (orbit_aff p hy)
  have h2 : affCoord p (rep y) ∈ C.O := by rw [hO]; exact ⟨hy', h1⟩
  exact mem_O_of_orbit C hP h2 (Proj.orbit_symm (orbit_aff p hy)) h1

theorem continuousOn_rho (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) :
    ContinuousOn (fun x : PtsOf P => C.ρ (rep x)) (srcOf C) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨p, hp⟩ := exists_alt_variant x
  have hS : src (pC P) p ∈ 𝓝 x := (Top.isOpen_alt_bis p).mem_nhds hp
  have hO : srcOf C ∈ 𝓝 x := (isOpen_srcOf hP C).mem_nhds hx
  have hc : ContinuousAt (fun y : PtsOf P => affCoord p (rep y)) x := (continuousOn_aff p).continuousAt hS
  have hmem : ∀ y ∈ src (pC P) p, y ∈ srcOf C → affCoord p (rep y) ∈ C.O := fun y hy hy' =>
    mem_O_of_orbit C hP hy' (orbit_aff p hy) (rep_mem_mcPts y)
  have ht : Tendsto (fun y : PtsOf P => affCoord p (rep y)) (𝓝 x) (𝓝[C.O] (affCoord p (rep x))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hc, ?_⟩
    filter_upwards [hS, hO] with y hy hy' using hmem y hy hy'
  have h1 := (C.ρ_cont _ (hmem x hp hx)).tendsto.comp ht
  have e1 : C.ρ (affCoord p (rep x)) = C.ρ (rep x) :=
    C.ρ_orbit _ hx _ (hmem x hp hx) (orbit_aff p hp)
  rw [e1] at h1
  refine h1.congr' ?_
  filter_upwards [hS, hO] with y hy hy'
  exact C.ρ_orbit _ hy' _ (hmem y hy hy') (orbit_aff p hy)

def clsT (x₀ : PtsOf P) (z : (Σ k, ι k) → ℂ) : PtsOf P := if h : z ∈ mcPts P then cls z h else x₀

theorem clsT_of_mem (x₀ : PtsOf P) {z : (Σ k, ι k) → ℂ} (h : z ∈ mcPts P) : clsT x₀ z = cls z h := dif_pos h

theorem continuousOn_cls (C : OrbitChart P e) (x₀ : PtsOf P) :
    ContinuousOn (fun w => clsT x₀ (C.φ w)) C.D := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  have hφ : ContinuousOn C.φ C.D := continuousOn_pi.2 fun q => (C.holo q).continuousOn
  have h1 : ContinuousOn (fun w => proj (C.φ w)) C.D :=
    Top.continuousOn_proj.comp hφ fun w hw => (C.mem w hw).1
  refine h1.congr fun w hw => ?_
  simp only [Function.comp, clsT_of_mem x₀ (C.mem w hw), cls]

def orbChart (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) (x₀ : PtsOf P) :
    OpenPartialHomeomorph (PtsOf P) (Fin e → ℂ) where
  toFun x := C.ρ (rep x)
  invFun w := clsT x₀ (C.φ w)
  source := srcOf C
  target := C.D
  map_source' _ hx := C.ρ_mem _ hx
  map_target' w hw := by
    rw [clsT_of_mem x₀ (C.mem w hw)]
    exact mem_O_of_orbit C hP (C.φ_mem_O w hw) (rep_cls_orbit _ _) (C.mem w hw)
  left_inv' x hx := by
    have hm := C.mem _ (C.ρ_mem _ hx)
    show clsT x₀ (C.φ (C.ρ (rep x))) = x
    rw [clsT_of_mem x₀ hm]
    exact pts_eq_of_orbit (Proj.orbit_trans (rep_cls_orbit _ hm) (C.φ_ρ _ hx))
  right_inv' w hw := by
    show C.ρ (rep (clsT x₀ (C.φ w))) = w
    rw [clsT_of_mem x₀ (C.mem w hw)]
    have h1 := mem_O_of_orbit C hP (C.φ_mem_O w hw) (rep_cls_orbit _ (C.mem w hw)) (C.mem w hw)
    rw [C.ρ_orbit _ (C.φ_mem_O w hw) _ h1 (rep_cls_orbit _ (C.mem w hw)), C.ρ_φ w hw]
  open_source := isOpen_srcOf hP C
  open_target := C.isOpen_D
  continuousOn_toFun := continuousOn_rho hP C
  continuousOn_invFun := continuousOn_cls C x₀

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen
