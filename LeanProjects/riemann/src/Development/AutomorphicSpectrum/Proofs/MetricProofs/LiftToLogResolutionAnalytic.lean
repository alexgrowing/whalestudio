import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BasePartFlagPt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionMapLocallyAnalytic

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.HoloLift

variable {e : ℕ} {V : Set (Fin e → ℂ)}

def inclChart (hV : IsOpen V) [Nonempty V] : OpenPartialHomeomorph V (Fin e → ℂ) :=
  hV.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val

theorem inclChart_source (hV : IsOpen V) [Nonempty V] : (inclChart hV).source = Set.univ := by
  simp [inclChart]

theorem inclChart_target (hV : IsOpen V) [Nonempty V] : (inclChart hV).target = V := by
  simp [inclChart]

theorem inclChart_apply (hV : IsOpen V) [Nonempty V] (y : V) : inclChart hV y = y := by
  simp [inclChart]

theorem val_inclChart_symm (hV : IsOpen V) [Nonempty V] {w : Fin e → ℂ} (hw : w ∈ V) :
    (((inclChart hV).symm w : V) : Fin e → ℂ) = w := by
  have h := (inclChart hV).right_inv (x := w) (by rw [inclChart_target]; exact hw)
  rwa [inclChart_apply] at h

theorem eventually_val_inclChart_symm (hV : IsOpen V) [Nonempty V] {w : Fin e → ℂ} (hw : w ∈ V) :
    ∀ᶠ w' in 𝓝 w, (((inclChart hV).symm w' : V) : Fin e → ℂ) = w' := by
  filter_upwards [hV.mem_nhds hw] with w' hw' using val_inclChart_symm hV hw'

def inclAtlas (hV : IsOpen V) [Nonempty V] : FinHolAtlas e V where
  n := 1
  chart _ := inclChart hV
  cover x := ⟨0, by rw [inclChart_source]; trivial⟩
  holo j k := by
    rintro w ⟨hw, -⟩
    rw [inclChart_target] at hw
    refine analyticAt_id.congr ?_
    filter_upwards [eventually_val_inclChart_symm hV hw] with w' hw'
    simp only [Function.comp, inclChart_apply, hw', id]

end GlobalTheory.CompanionTheory.Ar.PB.HoloLift

open GlobalTheory.CompanionTheory.Ar.PB.HoloLift in

theorem GlobalTheory.CompanionTheory.Ar.PB.HoloLift.holo_of_analytic_lift : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D e : ℕ) (R : AnLogRes P J D), J = ⊤ → ∀ (V : Set (Fin e → ℂ)) (μ : (Fin e → ℂ) → (Σ k, ι k) → ℂ) (g : (Fin e → ℂ) → R.X), IsOpen V → (∀ q, AnalyticOnNhd ℂ (fun u => μ u q) V) → (∀ u ∈ V, SameOrbit (R.lift (g u) (g u)) (μ u)) → ContinuousOn g V ∧ ∀ k, AnalyticOnNhd ℂ (R.A.chart k ∘ g) (V ∩ g ⁻¹' (R.A.chart k).source) := by
  intro K _ ι _ P J D e R hJ V μ g hV hμ hg
  subst hJ
  rcases V.eq_empty_or_nonempty with rfl | hne
  · refine ⟨continuousOn_empty _, fun k w hw => ?_⟩
    exact absurd hw.1 (Set.notMem_empty w)
  haveI : Nonempty V := hne.to_subtype
  let B : FinHolAtlas e V := inclAtlas hV
  let Vf : V → Set V := fun _ => Set.univ
  let μf : V → V → (Σ k, ι k) → ℂ := fun _ u => μ u
  let h : V → R.X := fun y => g y
  have hVo : ∀ y, IsOpen (Vf y) := fun _ => isOpen_univ
  have hVm : ∀ y, y ∈ Vf y := fun _ => Set.mem_univ _
  have hμf : ∀ y q, B.HoloOn (Vf y) fun u => μf y u q := by
    rintro y q j w ⟨hw, -⟩
    have hw' : w ∈ V := by simpa [B, inclAtlas, inclChart_target] using hw
    refine (hμ q w hw').congr ?_
    filter_upwards [eventually_val_inclChart_symm hV hw'] with w' h'
    simp only [Function.comp, μf, B, inclAtlas, h']
  have hc : ∀ y y', ∀ u ∈ Vf y ∩ Vf y', SameOrbit (μf y u) (μf y' u) := fun _ _ u _ =>
    Proj.orbit_trans (Proj.orbit_symm (hg u u.2)) (hg u u.2)
  have hh : ∀ y, SameOrbit (R.lift (h y) (h y)) (μf y y) := fun y => hg y y.2
  have hnz : ∀ y k, ∃ i, μf y y ⟨k, i⟩ ≠ 0 := fun y k => by
    obtain ⟨i, hi⟩ := (R.mem (h y) (h y) (R.mem_U _)).1 k
    exact ⟨i, Proj.orbit_ne (hh y) hi⟩
  have hcont : Continuous h := CovMap.continuous_of_orbit_of_ne R B hVo hVm hμf hnz hc hh
  refine ⟨continuousOn_iff_continuous_restrict.2 hcont, fun k w hw => ?_⟩
  have hA := Proj.analytic_of_orbit R B hVo hVm hμf hc hh hcont (0 : Fin 1) k
  have hmem : w ∈ (B.chart (0 : Fin 1)).target ∩
      (B.chart (0 : Fin 1)).symm ⁻¹' (h ⁻¹' (R.A.chart k).source) := by
    refine ⟨by simpa [B, inclAtlas, inclChart_target] using hw.1, ?_⟩
    have e1 := val_inclChart_symm hV hw.1
    show g (((inclChart hV).symm w : V) : Fin e → ℂ) ∈ (R.A.chart k).source
    rw [e1]
    exact hw.2
  refine (hA w hmem).congr ?_
  filter_upwards [eventually_val_inclChart_symm hV hw.1] with w' h'
  show R.A.chart k (g (((inclChart hV).symm w' : V) : Fin e → ℂ)) = R.A.chart k (g w')
  rw [h']
