import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R.FinalTheorems
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.DivSec

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {e : ℕ}

section Transport

variable {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (h : X ≃ₜ CxPts p σ)

def ChartsAlg : Prop := ∀ j, ∃ c : AlgChart p σ e, A.chart j = h.transOpenPartialHomeomorph c.finChart

variable {A h} (hA : ChartsAlg A h)

def algAtlas : FinHolAtlas e (CxPts p σ) where
  n := A.n
  chart j := (hA j).choose.finChart
  cover y := (A.cover (h.symm y)).imp fun j hj => by
    rw [(hA j).choose_spec, Homeomorph.transOpenPartialHomeomorph_source] at hj
    simpa using hj
  holo _ _ := AlgChart.analyticOnNhd_trans _ _

theorem isAlgAtlas_algAtlas : IsAlgAtlas (algAtlas hA) := fun _ => ⟨_, rfl⟩

theorem chart_eq (j : Fin A.n) :
    A.chart j = h.transOpenPartialHomeomorph ((algAtlas hA).chart j) := (hA j).choose_spec

theorem holoOn_comp_iff {S : Set (CxPts p σ)} {g : CxPts p σ → ℂ} :
    A.HoloOn (h ⁻¹' S) (g ∘ h) ↔ (algAtlas hA).HoloOn S g := by
  refine forall_congr' fun j => ?_
  rw [chart_eq hA j, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Homeomorph.transOpenPartialHomeomorph_target]
  have e1 : (g ∘ h) ∘ (h.symm ∘ ((algAtlas hA).chart j).symm) = g ∘ ((algAtlas hA).chart j).symm := by
    funext v; simp
  have e2 : (h.symm ∘ ((algAtlas hA).chart j).symm) ⁻¹' (h ⁻¹' S) = ((algAtlas hA).chart j).symm ⁻¹' S := by
    ext v; simp
  rw [e1, e2]

theorem smoothOn_comp_iff {S : Set (CxPts p σ)} {g : CxPts p σ → ℝ} :
    A.SmoothOn (h ⁻¹' S) (g ∘ h) ↔ (algAtlas hA).SmoothOn S g := by
  refine forall_congr' fun j => ?_
  rw [chart_eq hA j, Homeomorph.transOpenPartialHomeomorph_symm_apply,
    Homeomorph.transOpenPartialHomeomorph_target]
  have e1 : (g ∘ h) ∘ (h.symm ∘ ((algAtlas hA).chart j).symm) = g ∘ ((algAtlas hA).chart j).symm := by
    funext v; simp
  have e2 : (h.symm ∘ ((algAtlas hA).chart j).symm) ⁻¹' (h ⁻¹' S) = ((algAtlas hA).chart j).symm ⁻¹' S := by
    ext v; simp
  rw [e1, e2]

theorem isCompatChart_trans {ψ : OpenPartialHomeomorph (CxPts p σ) (Fin e → ℂ)}
    (hψ : IsCompatChart (algAtlas hA) ψ) : IsCompatChart A (h.transOpenPartialHomeomorph ψ) := fun j => by
  obtain ⟨h1, h2⟩ := hψ j
  rw [chart_eq hA j]
  simp only [Homeomorph.transOpenPartialHomeomorph_symm_apply, Homeomorph.transOpenPartialHomeomorph_apply,
    Homeomorph.transOpenPartialHomeomorph_target, Homeomorph.transOpenPartialHomeomorph_source]
  constructor
  · have e1 : (ψ ∘ h) ∘ (h.symm ∘ ((algAtlas hA).chart j).symm) = ψ ∘ ((algAtlas hA).chart j).symm := by
      funext v; simp
    have e2 : (h.symm ∘ ((algAtlas hA).chart j).symm) ⁻¹' (h ⁻¹' ψ.source) =
        ((algAtlas hA).chart j).symm ⁻¹' ψ.source := by
      ext v; simp
    rw [e1, e2]; exact h1
  · have e1 : (((algAtlas hA).chart j) ∘ h) ∘ (h.symm ∘ ψ.symm) = ((algAtlas hA).chart j) ∘ ψ.symm := by
      funext v; simp
    have e2 : (h.symm ∘ ψ.symm) ⁻¹' (h ⁻¹' ((algAtlas hA).chart j).source) =
        ψ.symm ⁻¹' ((algAtlas hA).chart j).source := by
      ext v; simp
    rw [e1, e2]; exact h2

theorem isPotential_pullback {L : LocPot (CxPts p σ)} (hL : IsPotential (algAtlas hA) L) :
    IsPotential A (L.pullback h h.continuous) := by
  refine ⟨fun x => (smoothOn_comp_iff hA).2 (hL.1 (h x)), fun x x' y hy => ?_⟩
  obtain ⟨W, hW, hyW, G, hG, e⟩ := hL.2 (h x) (h x') (h y) hy
  refine ⟨h ⁻¹' W, hW.preimage h.continuous, hyW, G ∘ h, (holoOn_comp_iff hA).2 hG, fun z hz => ?_⟩
  exact e (h z) ⟨⟨hz.1.1, hz.1.2⟩, hz.2⟩

theorem isSection_pullback {L : LocPot (CxPts p σ)} {s : CxPts p σ → CxPts p σ → ℂ}
    (hs : IsSection (algAtlas hA) L s) :
    IsSection A (L.pullback h h.continuous) (fun x z => s (h x) (h z)) :=
  ⟨fun x => (holoOn_comp_iff hA (g := s (h x))).2 (hs.1 (h x)),
    fun x x' y hy => hs.2 (h x) (h x') (h y) hy⟩

theorem isSNC_pullback {L : LocPot (CxPts p σ)} {s : CxPts p σ → CxPts p σ → ℂ} {r : ℕ} {m : Fin r → ℕ}
    {W : Fin r → Set (CxPts p σ)} (hs : IsSNC (algAtlas hA) L s m W) :
    IsSNC A (L.pullback h h.continuous) (fun x z => s (h x) (h z)) m (fun k => h ⁻¹' W k) := fun x => by
  obtain ⟨ψ, hc, hx, hsub, τ, hinj, hW, u, hu, hu0, he⟩ := hs (h x)
  refine ⟨h.transOpenPartialHomeomorph ψ, isCompatChart_trans hA hc, hx, fun z hz => hsub hz, τ, hinj,
    fun k => ?_, u ∘ h, ?_, fun z hz => hu0 (h z) hz, fun z hz => he (h z) hz⟩
  · ext z
    have := Set.ext_iff.1 (hW k) (h z)
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using this
  · have := (holoOn_comp_iff hA (S := ψ.source) (g := u)).2 hu
    simpa [Homeomorph.transOpenPartialHomeomorph_source] using this

end Transport

section Data

variable {d m : ℕ} {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

def eqV (i : Fin m) (y : CxPts p σ) : Y.affineOpens := ((hn i).2 y).choose

def eqT (i : Fin m) (y : CxPts p σ) : Γ(Y, (eqV hn i y).1) := ((hn i).2 y).choose_spec.choose

def eqF (i : Fin m) (y : CxPts p σ) : CxPts p σ → ℝ := ((hn i).2 y).choose_spec.choose_spec.choose

theorem eq_spec (i : Fin m) (y : CxPts p σ) :
    y ∈ ptsIn p σ (eqV hn i y).1 ∧
      (Scheme.IdealSheafData.vanishingIdeal (C i)).ideal (eqV hn i y) = Ideal.span {eqT hn i y} ∧
      R.SmoothOn (ptsIn p σ (eqV hn i y).1) (eqF hn i y) ∧
      ∀ z ∈ ptsIn p σ (eqV hn i y).1, n i z ^ 2 = ‖ev p σ (eqV hn i y).1 (eqT hn i y) z‖ ^ 2 * Real.exp (-eqF hn i y z) :=
  ((hn i).2 y).choose_spec.choose_spec.choose_spec

def divPot : LocPot (CxPts p σ) where
  U y := ⋂ i, ptsIn p σ (eqV hn i y).1
  isOpen_U y := isOpen_iInter_of_finite fun i => isOpen_ptsIn _
  mem_U y := Set.mem_iInter.2 fun i => (eq_spec hn i y).1
  φ y z := ∑ i, eqF hn i y z / 2

def divSec (y z : CxPts p σ) : ℂ := ∏ i, ev p σ (eqV hn i y).1 (eqT hn i y) z

theorem mem_eqV {y z : CxPts p σ} (hz : z ∈ (divPot hn).U y) (i : Fin m) : z ∈ ptsIn p σ (eqV hn i y).1 :=
  Set.mem_iInter.1 hz i

theorem norm_divSec_mul {y z : CxPts p σ} (hz : z ∈ (divPot hn).U y) :
    ‖divSec hn y z‖ * Real.exp (-(divPot hn).φ y z) = ∏ i, n i z := by
  have h1 : ∀ i, n i z = ‖ev p σ (eqV hn i y).1 (eqT hn i y) z‖ * Real.exp (-eqF hn i y z / 2) := fun i => by
    have e := (eq_spec hn i y).2.2.2 z (mem_eqV hn hz i)
    have h0 := ((hn i).1 z).1
    have hx : Real.exp (-eqF hn i y z) = Real.exp (-eqF hn i y z / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hx, ← mul_pow] at e
    exact (pow_left_inj₀ h0 (by positivity) two_ne_zero).1 e
  simp only [divSec, divPot, norm_prod, h1]
  rw [Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem divSec_eq_zero_iff (y : CxPts p σ) : divSec hn y y = 0 ↔ ∃ i, LiesIn y (C i) := by
  simp only [divSec, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
  exact exists_congr fun i => ev_eq_zero_iff (eq_spec hn i y).2.1 (eq_spec hn i y).1

end Data

section Sec

variable {d m : ℕ} {R : AnRead p σ d} {C : Fin m → Closeds Y} {n : Fin m → CxPts p σ → ℝ}
  (hn : ∀ i, IsDivNorm R (C i) (n i))

theorem holoOn_divSec (y : CxPts p σ) : R.HoloOn ((divPot hn).U y) (divSec hn y) := fun j => by
  have h : ∀ i, DifferentiableOn ℂ
      (fun v => ev p σ (eqV hn i y).1 (eqT hn i y) ((R.chart j).e.symm v))
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' (divPot hn).U y) := fun i =>
    (R.holoOn_ev _ (eqT hn i y) j).mono fun v hv => ⟨hv.1, mem_eqV hn hv.2 i⟩
  have key : ∀ s : Finset (Fin m), DifferentiableOn ℂ
      (fun v => ∏ i ∈ s, ev p σ (eqV hn i y).1 (eqT hn i y) ((R.chart j).e.symm v))
      ((R.chart j).e.target ∩ (R.chart j).e.symm ⁻¹' (divPot hn).U y) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using differentiableOn_const (1 : ℂ)
    | insert a s ha ih =>
      simp only [Finset.prod_insert ha]
      exact (h a).mul ih
  refine (key Finset.univ).congr fun v _ => ?_
  simp [divSec]

theorem isSection_divSec {B : FinHolAtlas d (CxPts p σ)} (hB : IsAlgAtlas B) :
    IsSection B (divPot hn) (divSec hn) :=
  ⟨fun y => (hB.holoOn_iff R ((divPot hn).isOpen_U y)).2 (holoOn_divSec hn y),
    fun _ _ _ hz => by rw [norm_divSec_mul hn hz.1, norm_divSec_mul hn hz.2]⟩

end Sec

end GlobalTheory.DivSec
