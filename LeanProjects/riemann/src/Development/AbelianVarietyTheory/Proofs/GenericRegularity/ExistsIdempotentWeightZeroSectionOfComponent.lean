import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSectionOfGenericValuesRegularOnChartsStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.SectionEqZeroOfGenericFramedPointValuesStatement

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Reg.exists_idem_section : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Reg.EvLaws Xo c → ∀ h : _root_.Formalism.L2.Pj.GenFrEx Xo c,
      _root_.GlobalTheory.Reg.Atlas h → ∀ Z : _root_.Formalism.L2.Pj.Comp Xo c, ∃ χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0,
        χ * χ = χ ∧ _root_.Formalism.L2.Pj.evC h Z χ = 1 ∧ ∀ Z', Z' ≠ Z → _root_.Formalism.L2.Pj.evC h Z' χ = 0 := by
  intro E _ _ _ H Dw l Xo c hev h hcov Z
  classical
  have hexp : _root_.Formalism.L2.Pj.ex Dw 0 0 = 0 := by
    unfold _root_.Formalism.L2.Pj.ex
    funext x
    cases x <;> rfl
  have hreg : ∀ C : _root_.GlobalTheory.Reg.FChart h,
      _root_.Formalism.L2.Pj.wchar (_root_.Formalism.L2.Pj.ex Dw 0 0) C.t *
        (fun Z' => if Z' = Z then (1 : _root_.Formalism.L2.Pj.Om Z') else 0) C.Z ∈ C.R := by
    intro C
    rw [hexp]
    unfold _root_.Formalism.L2.Pj.wchar
    simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, _root_.one_mul]
    split_ifs
    · exact C.R.one_mem
    · exact C.R.zero_mem
  obtain ⟨χ, hχ, hval⟩ := _root_.GlobalTheory.Reg.SecGlue.exists_sec_of_regular E H Dw l Xo c hev h
    hcov 0 0 (fun Z' => if Z' = Z then (1 : _root_.Formalism.L2.Pj.Om Z') else 0) hreg
  refine ⟨χ, hχ, ?_, by simp [hval], fun Z' hZ' => by simp [hval, hZ']⟩
  have hsq : χ * χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0 := by simpa using _root_.Formalism.L2.Pj.sec_mul Xo c 0 0 0 0 hχ hχ
  have hmem : χ * χ - χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0 := Submodule.sub_mem _ hsq hχ
  refine sub_eq_zero.mp (_root_.GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hev h hcov
    0 0 _ hmem fun Z' => ?_)
  have hmul : _root_.Formalism.L2.Pj.evC h Z' (χ * χ) = _root_.Formalism.L2.Pj.evC h Z' χ * _root_.Formalism.L2.Pj.evC h Z' χ := by
    unfold _root_.Formalism.L2.Pj.evC _root_.Formalism.L2.Pj.evR
    exact _root_.Formalism.L2.Pj.evalAt_mul _ _ _ _ _
  have hadd : _root_.Formalism.L2.Pj.evC h Z' (χ * χ - χ + χ) =
      _root_.Formalism.L2.Pj.evC h Z' (χ * χ - χ) + _root_.Formalism.L2.Pj.evC h Z' χ := by
    unfold _root_.Formalism.L2.Pj.evC _root_.Formalism.L2.Pj.evR
    exact _root_.Formalism.L2.Pj.evalAt_add _ _ _ _ _
  have hidem : _root_.Formalism.L2.Pj.evC h Z' χ * _root_.Formalism.L2.Pj.evC h Z' χ = _root_.Formalism.L2.Pj.evC h Z' χ := by
    rw [hval]
    split_ifs <;> simp
  rw [sub_add_cancel, hmul, hidem] at hadd
  exact add_eq_right.mp hadd.symm

end GlobalTheory.Reg
