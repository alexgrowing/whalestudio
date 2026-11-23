import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.TateFE

theorem quasiCharExponent_eq_zero_of_unit {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {χ : Fˣ →* ℂˣ} (hχ : IsUnit1 χ) : quasiCharExponent χ = 0 := by
  unfold quasiCharExponent
  rw [hχ.2]
  simp

theorem first_form {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    {ψ : AddChar F Circle} (hψ : IsStd ψ) {χ : Fˣ →* ℂˣ} (hχ : IsUnit1 χ)
    {f : F → ℂ} (hf : f ∈ schwartzBruhat F) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    localZeta (localFourier (selfDualMeasure ψ) ψ f) χ⁻¹ (1 - s) = gam ψ χ s * localZeta f χ s := by
  have he := quasiCharExponent_eq_zero_of_unit hχ
  have hs1 : -quasiCharExponent χ < s.re := by rw [he]; simpa using h0
  have hs2 : s.re < 1 - quasiCharExponent χ := by rw [he]; simpa using h1
  have hs' : -quasiCharExponent χ⁻¹ < (1 - s).re := by
    rw [quasiCharExponent_inv, Complex.sub_re, Complex.one_re]
    linarith
  have hL1 := localLFactor_ne_zero hχ.1 hs1
  have hL2 := localLFactor_ne_zero (continuous_quasiChar_inv hχ.1) hs'
  have hfe := localZeta_functionalEquation hψ.1 hψ.2.1 hχ.1 hf hs1 hs2
  unfold gam
  rw [div_eq_iff hL2] at hfe
  rw [hfe]
  field_simp

theorem second_form {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F]
    {ψ : AddChar F Circle} (hψ : IsStd ψ) {χ : Fˣ →* ℂˣ} (hχ : IsUnit1 χ)
    {f : F → ℂ} (hf : f ∈ schwartzBruhat F) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    localZeta f χ⁻¹ (1 - s) =
      ((χ (-1) : ℂˣ) : ℂ) * gam ψ χ s * localZeta (localFourier (selfDualMeasure ψ) ψ f) χ s := by
  have hc := hψ.1
  have hn := hψ.2.1
  set T := localFourier (selfDualMeasure ψ) ψ with hT
  have m1 : T f ∈ schwartzBruhat F := localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hc hn hf
  have m2 : T (T f) ∈ schwartzBruhat F := localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hc hn m1
  have m3 : T (T (T f)) ∈ schwartzBruhat F :=
    localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hc hn m2
  have e1 : T (T (T f)) = fun x => T f (-x) :=
    funext fun x => localFourier_localFourier_selfDual hc hn m1 x
  have e2 : T (T (T (T f))) = f := funext fun x => by
    have a1 : T (T (T (T f))) x = T (T f) (-x) := localFourier_localFourier_selfDual hc hn m2 x
    have a2 : T (T f) (-x) = f (- -x) := localFourier_localFourier_selfDual hc hn hf (-x)
    rw [a1, a2, neg_neg]
  have key := first_form hψ hχ m3 h0 h1
  rw [← hT, e2, e1, localZeta_comp_neg] at key
  rw [key]
  ring

theorem sTate : STate := by
  intro F _ _ _ _ _ _ ψ hψ χ hχ f hf s h0 h1
  exact ⟨first_form hψ hχ hf h0 h1, second_form hψ hχ hf h0 h1⟩

end GlobalTheory.CompanionTheory.TateFE
