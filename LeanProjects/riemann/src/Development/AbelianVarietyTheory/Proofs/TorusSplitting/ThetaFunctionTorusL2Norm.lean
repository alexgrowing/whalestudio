import Mathlib
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn.ThetaTorus

open MeasureTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
open MeasureTheory in

theorem _root_.GlobalTheory.EtaAn.ThetaTorus.setAverage_equiv {V W : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
    [BorelSpace W]
    (m₁ : Measure V) [m₁.IsAddHaarMeasure] (m₂ : Measure W) [m₂.IsAddHaarMeasure]
    (e : V ≃L[ℝ] W) (s : Set W) (f : W → ℝ) :
    ⨍ w in s, f w ∂m₂ = ⨍ v in e ⁻¹' s, f (e v) ∂m₁ := by
  set ν : Measure W := Measure.map e m₁
  have hc := Measure.isAddLeftInvariant_eq_smul m₂ ν
  set c := m₂.addHaarScalarFactor ν
  have hpos : (0 : ℝ) < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure m₂ ν
  let e' : V ≃ᵐ W := e.toHomeomorph.toMeasurableEquiv
  have hν : ν = Measure.map e' m₁ := rfl
  have hint : ∫ w in s, f w ∂ν = ∫ v in e ⁻¹' s, f (e v) ∂m₁ := by
    rw [hν]; exact setIntegral_map_equiv e' f s
  have hmeas : ν.real s = m₁.real (e ⁻¹' s) := by
    rw [hν, measureReal_def, measureReal_def, e'.map_apply]; rfl
  rw [setAverage_eq, setAverage_eq, hc, Measure.restrict_smul, integral_smul_nnreal_measure, hint,
    measureReal_nnreal_smul_apply, hmeas, NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_inv, _root_.mul_mul_mul_comm, inv_mul_cancel₀ hpos.ne', _root_.one_mul]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
open MeasureTheory in

theorem _root_.GlobalTheory.EtaAn.ThetaTorus.Hf_add_re {κ : Type} [Fintype κ] (v w : EuclideanSpace ℂ κ) :
    (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf (v + w) (v + w)).re = (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf v v).re + 2 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf v w).re + (_root_.ReciprocityTheory.ChartRestriction.G.I2.Hf w w).re := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.Hf
  simp only [PiLp.add_apply, map_add, mul_add, add_mul, Finset.sum_add_distrib, Complex.add_re,
    Complex.re_sum]
  have hsym : ∀ i, (w.ofLp i * (starRingEnd ℂ) (v.ofLp i)).re
      = (v.ofLp i * (starRingEnd ℂ) (w.ofLp i)).re := by
    intro i
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simp only [hsym]
  ring

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
open MeasureTheory in

theorem _root_.GlobalTheory.EtaAn.ThetaTorus.theta_section_l2_torus :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Pm : D.La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (T : _root_.ReciprocityTheory.ChartRestriction.G.I2.PT E) (ψ : (Fin g → ℂ) ≃ₗ[ℂ] _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) (θ : (Fin g → ℂ) → ℂ) (Fd : Set (Fin g → ℂ)), _root_.GlobalTheory.EtaAn.IsTorusOf D ty Pm Hm T ψ → Differentiable ℂ θ → (∀ a z, θ (z + Pm a) = (((Int.negOnePow (D.EF a (H.w0 • a)) : ℤˣ) : ℤ) : ℂ) * Complex.exp (Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (Pm a) + Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pm a) (Pm a)) * θ z) → MeasureTheory.IsAddFundamentalDomain Pm.range Fd MeasureTheory.volume → (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => θ (ψ.symm (v 0))) ∈ T.Sec 1 1 ∧ T.l2 1 (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => θ (ψ.symm (v 0))) = (∫ z in Fd, ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re)) / (MeasureTheory.volume Fd).toReal ∧ ∀ z, Real.sqrt (T.ptN2 1 (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ z)) = ‖θ z‖ * Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) := by
  intro E _ _ _ H D g ty Pm Hm T ψ θ Fd hT hθ hper hFd
  unfold _root_.GlobalTheory.EtaAn.IsTorusOf at hT
  obtain ⟨-, -, hψ, hL, -, heps⟩ := hT
  have hIJ : ∀ v w : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim,
      _root_.ReciprocityTheory.ChartRestriction.G.I2.HC v w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (ψ.symm (v 0)) (ψ.symm (w 0)) := by
    intro v w
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.HC
    rw [Fin.sum_univ_one, ← hψ, ψ.apply_symm_apply, ψ.apply_symm_apply]
  have hpt : ∀ z, T.ptN2 1 (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => θ (ψ.symm (v 0))) (fun _ => ψ z)
      = ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) := by
    intro z
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.ptN2
    rw [hIJ]
    simp only [ψ.symm_apply_apply, Nat.cast_one, _root_.one_mul]
  refine ⟨?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.Sec
    refine ⟨?_, ?_⟩
    · have hl : Differentiable ℂ (fun v : Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim => ψ.symm (v 0)) :=
        (LinearMap.toContinuousLinearMap
          (ψ.symm : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim →ₗ[ℂ] (Fin g → ℂ))).differentiable.comp (differentiable_apply 0)
      exact hθ.comp hl
    · intro p hp v
      obtain ⟨a, ha⟩ := (hL (p 0)).1 (hp 0)
      have h1 : ψ.symm ((v + p) 0) = ψ.symm (v 0) + Pm a := by
        rw [Pi.add_apply, map_add, ← ha, ψ.symm_apply_apply]
      simp only [h1, hper, hIJ, Fin.prod_univ_one, ← ha, heps, ψ.symm_apply_apply, Nat.cast_one,
        _root_.one_mul, pow_one]
      ring_nf
  · let ψR : (Fin g → ℂ) ≃L[ℝ] _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim :=
      (ψ.restrictScalars ℝ).toContinuousLinearEquiv
    let e : (Fin g → ℂ) ≃L[ℝ] (Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) :=
      ψR.trans (ContinuousLinearEquiv.funUnique (Fin 1) ℝ (_root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim)).symm
    have he : ∀ z, e z = fun _ => ψ z := fun z => rfl
    haveI : (volume : Measure (Fin 1 → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim)).IsAddHaarMeasure :=
      Measure.pi.isAddHaarMeasure _
    unfold _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.l2
    refine (_root_.GlobalTheory.EtaAn.ThetaTorus.setAverage_equiv volume volume e _ _).trans ?_
    simp only [he, hpt]
    have hS : e ⁻¹' T.fd 1 = ψ ⁻¹' ZSpan.fundamentalDomain T.b := by
      ext z
      simp [_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.fd, he]
    rw [hS]
    let emap : Submodule.span ℤ (Set.range T.b) → Pm.range := fun x =>
      ⟨ψ.symm x, by
        obtain ⟨a, ha⟩ := (hL x).1 x.2
        exact ⟨a, by rw [← ha, ψ.symm_apply_apply]⟩⟩
    have hbij : Function.Bijective emap := by
      refine ⟨fun x y h => ?_, fun y => ?_⟩
      · have h' := congrArg (fun u : Pm.range => ψ (u : Fin g → ℂ)) h
        simp only [emap, ψ.apply_symm_apply] at h'
        exact Subtype.ext h'
      · obtain ⟨y, a, rfl⟩ := y
        exact ⟨⟨ψ (Pm a), (hL _).2 ⟨a, rfl⟩⟩, Subtype.ext (by simp [emap])⟩
    haveI : Countable Pm.range := hbij.2.countable
    have hψm : Measurable (ψ : (Fin g → ℂ) → _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) := ψR.continuous.measurable
    have hFdS : IsAddFundamentalDomain Pm.range (ψ ⁻¹' ZSpan.fundamentalDomain T.b) volume :=
      (ZSpan.isAddFundamentalDomain T.b (Measure.map ψ volume)).preimage_of_equiv
        (MeasurePreserving.quasiMeasurePreserving ⟨hψm, rfl⟩) hbij
        (fun x z => by
          show ψ ((emap x : Fin g → ℂ) + z) = (x : _root_.ReciprocityTheory.ChartRestriction.G.I2.Vsp T.dim) + ψ z
          simp [emap])
    have hinv : ∀ (h : Pm.range) (z : Fin g → ℂ),
        ‖θ (h +ᵥ z)‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (h +ᵥ z) (h +ᵥ z)).re)
          = ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) := by
      rintro ⟨_, a, rfl⟩ z
      show ‖θ (Pm a + z)‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pm a + z) (Pm a + z)).re)
        = ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re)
      have hexp := _root_.GlobalTheory.EtaAn.ThetaTorus.Hf_add_re (ψ z) (ψ (Pm a))
      rw [← map_add] at hexp
      simp only [hψ] at hexp
      have hs : ‖((((Int.negOnePow (D.EF a (H.w0 • a)) : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
        rcases Int.units_eq_one_or (Int.negOnePow (D.EF a (H.w0 • a))) with h | h <;> simp [h]
      have hre : (↑Real.pi * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (Pm a) + ↑Real.pi / 2 * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pm a) (Pm a)).re
          = Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (Pm a)).re + Real.pi / 2 * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (Pm a) (Pm a)).re := by
        simp [Complex.add_re, Complex.mul_re]
      rw [add_comm, hper, norm_mul, norm_mul, hs, Complex.norm_exp, hre, hexp, _root_.one_mul,
        mul_pow, mul_comm (Real.exp _ ^ 2), _root_.mul_assoc, sq (Real.exp _), ← Real.exp_add,
        ← Real.exp_add]
      ring_nf
    rw [setAverage_eq, measureReal_def, hFdS.measure_eq hFd, hFdS.setIntegral_eq hFd (f := fun z =>
      ‖θ z‖ ^ 2 * Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re)) hinv,
      smul_eq_mul, div_eq_inv_mul]
  · intro z
    rw [hpt z]
    have hsq : Real.exp (-Real.pi * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re)
        = Real.exp (-(Real.pi / 2) * (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z z).re) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [hsq, ← mul_pow]
    exact Real.sqrt_sq (by positivity)

end GlobalTheory.EtaAn.ThetaTorus
