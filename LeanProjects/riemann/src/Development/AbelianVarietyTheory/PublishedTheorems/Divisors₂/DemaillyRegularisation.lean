import Mathlib
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshBasic
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousAndSmul

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Set Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ChernReg

namespace GlobalTheory.Published

def IsPshExt {d : ℕ} (U : Set (Fin d → ℂ)) (v : (Fin d → ℂ) → EReal) : Prop :=
  (∀ z ∈ U, v z ≠ ⊤) ∧ UpperSemicontinuousOn v U ∧ U ⊆ closure {z ∈ U | v z ≠ ⊥} ∧
    ∀ κ : ℝ, ReciprocityTheory.AnForm.A.IsPsh U fun z => (max (v z) ((-κ : ℝ) : EReal)).toReal

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

def IsClosedForm (R : AnRead p σ d) (θ : ChartForm p σ d) : Prop := ∀ y, ∃ W φ, y ∈ W ∧ IsPotential R θ W φ

def IsFormPsh (R : AnRead p σ d) (θ : ChartForm p σ d) (v : CxPts p σ → EReal) : Prop :=
  ∀ W φ, IsPotential R θ W φ → ∀ c : AlgChart p σ d,
    IsPshExt (c.finChart.target ∩ c.finChart.symm ⁻¹' W) fun z => ((φ (c.finChart.symm z) : ℝ) : EReal) + v (c.finChart.symm z)

def DemaillyRegularisation : Prop :=
  ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (p : Y ⟶ Sp k) (σ : k →+* ℂ) (d : ℕ) [SmoothOfRelativeDimension d p],
    CompactSpace (CxPts p σ) → T2Space (CxPts p σ) →
    ∀ (a θ : ChartForm p σ d) (E : ChartMap p σ d) (v : CxPts p σ → EReal),
      IsKaehlerForm (AnRead.all p σ d) a → IsExph a E → IsClosedForm (AnRead.all p σ d) θ →
      IsFormPsh (AnRead.all p σ d) θ v →
      ∃ A K δ : ℝ, IsRegConst a θ (rho a E fun y => (v y).toReal) A K δ ∧
        (∀ y, ∀ t ∈ Ioo 0 δ, v y ≤ ((rho a E (fun y => (v y).toReal) y t + K * t ^ 2 : ℝ) : EReal)) ∧
        ∀ y, Tendsto (fun t => ((rho a E (fun y => (v y).toReal) y t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (v y))

section Checks

open ReciprocityTheory.AnForm.A (IsPsh isPsh_iff_isLeviPsh_thm isPsh_sup_thm)

example {R : AnRead p σ d} {a : ChartForm p σ d} (h : IsKaehlerForm R a) : IsClosedForm R a := h.1

theorem IsPshExt.of_isPsh {U : Set (Fin d → ℂ)} {u : (Fin d → ℂ) → ℝ} (hU : IsOpen U) (h : IsPsh U u) :
    IsPshExt U fun z => (u z : EReal) := by
  refine ⟨fun z _ => EReal.coe_ne_top _, ?_, fun z hz => subset_closure ⟨hz, EReal.coe_ne_bot _⟩, fun κ => ?_⟩
  · exact continuous_coe_real_ereal.comp_upperSemicontinuousOn h.1 EReal.coe_strictMono.monotone
  · have hc : IsPsh U fun _ => -κ := ⟨upperSemicontinuousOn_const, fun z w _ =>
      ⟨circleIntegrable_const _ _ _, by rw [Real.circleAverage_const]⟩⟩
    convert isPsh_sup_thm d Bool U (fun b => if b then u else fun _ => -κ) hU ?_ using 2 with z
    · rw [← EReal.coe_strictMono.monotone.map_max, EReal.toReal_coe]
      simp [Finset.sup'_insert]
    · rintro (_ | _)
      · simpa using hc
      · simpa using h

example : IsPshExt univ fun z : Fin d → ℂ => ((∑ j, ‖z j‖ ^ 2 : ℝ) : EReal) :=
  .of_isPsh isOpen_univ (ReciprocityTheory.AnForm.A.isPshInhabit_thm d).1

example : ¬ IsPshExt (univ : Set (Fin d → ℂ)) fun _ => ⊥ := fun h => by simpa using h.2.2.1

theorem IsFormPsh.of_smooth {R : AnRead p σ d} {θ : ChartForm p σ d} {u : CxPts p σ → ℝ} (hu : R.SmoothOn univ u)
    (h : ∀ c : AlgChart p σ d, ∀ y ∈ c.e.source, ∀ ξ, 0 ≤ θ c y ξ + ddcForm u c y ξ) :
    IsFormPsh R θ fun y => (u y : EReal) := by
  intro W φ hφ c
  have hs : R.SmoothOn W fun y => φ y + u y := fun i => (hφ.2.1 i).add ((hu.mono (subset_univ W)) i)
  have h₁ : ContDiffOn ℝ 2 ((fun y => φ y + u y) ∘ c.finChart.symm) (c.finChart.target ∩ c.finChart.symm ⁻¹' W) :=
    ((c.contDiffOn_finChart_iff _ W _).2 (hs.chart hφ.1 c)).of_le (WithTop.coe_le_coe.2 le_top)
  have ho := c.finChart.isOpen_inter_preimage_symm hφ.1
  refine .of_isPsh ho ((isPsh_iff_isLeviPsh_thm d _ _ ho h₁).2 ⟨h₁, fun z hz w => ?_⟩)
  have hy := c.finChart.map_target hz.1
  have e : θ c (c.finChart.symm z) w + ddcForm u c (c.finChart.symm z) w =
      ReciprocityTheory.AnForm.levi ((fun y => φ y + u y) ∘ c.finChart.symm) (c.finChart (c.finChart.symm z)) w / Real.pi := by
    rw [hφ.2.2 c _ hy hz.2, ← c.leviV_re_eq (hs.contDiffAt_two hφ.1 hy hz.2), ddcForm, ddcForm, ← add_div,
      ← AlgChart.levi_add (hφ.2.1.contDiffAt_two hφ.1 hy hz.2) (hu.contDiffAt_two isOpen_univ hy trivial)]
    rfl
  have := h c _ hy w
  rw [e, c.finChart.right_inv hz.1] at this
  exact (div_nonneg_iff.1 this).elim (·.1) fun h => absurd h.2 Real.pi_pos.not_ge

theorem IsFormPsh.const {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a) (r : ℝ) :
    IsFormPsh R a fun _ => (r : EReal) :=
  .of_smooth (u := fun _ => r) (fun _ => contDiffOn_const) fun c y hy ξ => by
    have e : ddcForm (fun _ => r) c y ξ = 0 := by
      rw [ddcForm, AlgChart.levi, c.leviV_re_eq (f := fun _ => r) contDiffAt_const]
      simp [ReciprocityTheory.AnForm.levi, Function.comp_def]
    rw [e, add_zero]
    rcases eq_or_ne ξ 0 with rfl | h
    · have := (continuous_and_smul ha hy).2 0 0
      simp only [smul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at this
      exact this.ge
    · exact (ha.2 c y hy ξ h).le

example [SmoothOfRelativeDimension d p] {R : AnRead p σ d} {a : ChartForm p σ d} (ha : IsKaehlerForm R a)
    (E : ChartMap p σ d) (r : ℝ) (y : CxPts p σ) :
    (∀ t : ℝ, (r : EReal) ≤ ((rho a E (fun _ => (r : EReal).toReal) y t + 0 * t ^ 2 : ℝ) : EReal)) ∧
      Tendsto (fun t => ((rho a E (fun _ => (r : EReal).toReal) y t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (r : EReal)) := by
  simp [rho_const ha]

end Checks

end GlobalTheory.Published

end
