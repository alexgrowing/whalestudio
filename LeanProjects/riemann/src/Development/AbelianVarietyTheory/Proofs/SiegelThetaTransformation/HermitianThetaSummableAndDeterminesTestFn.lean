import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EqOfSiegelThetaSeriesRationalEqStatement
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in

theorem _root_.GlobalTheory.SW.thH_summable_and_inj : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ)
    (φ : Matrix (Fin n) (Fin N) E → ℂ), _root_.GlobalTheory.SW.IsSB φ →
    ∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N,
      (∀ z z', Summable fun x => ‖φ x * cexp (2 * π * I * _root_.GlobalTheory.SW.expo Ψ x Z z z')‖) ∧
      ∀ ψ, _root_.GlobalTheory.SW.IsSB ψ →
        (∀ z z', _root_.GlobalTheory.SW.thH Ψ φ Z z z' = _root_.GlobalTheory.SW.thH Ψ ψ Z z z') → φ = ψ := by
  intro E _ _ _ Ψ hΨ n N φ hφ Z hZ
  obtain ⟨hbij, hup, hsurj, hdict, hSB⟩ := _root_.GlobalTheory.SW.thH_eq_thS_dictionary E Ψ hΨ n N
  classical
  have hexp : ∀ (z z' : _root_.GlobalTheory.SW.CM Ψ n N)
      (m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ),
      cexp (2 * π * I * _root_.GlobalTheory.SW.expo Ψ (_root_.GlobalTheory.SW.ofQ m) Z z z') =
        cexp (π * I * ∑ k, (_root_.GlobalTheory.SW.qv (m k) ⬝ᵥ
          (_root_.GlobalTheory.SW.tauOf Ψ Z) *ᵥ _root_.GlobalTheory.SW.qv (m k) +
          2 * _root_.GlobalTheory.SW.qv (m k) ⬝ᵥ (_root_.GlobalTheory.SW.zetaOf Ψ z z') k)) := by
    intro z z' m
    have h := hdict (fun x => if x = _root_.GlobalTheory.SW.ofQ m then 1 else 0) Z z z'
    unfold _root_.GlobalTheory.SW.thH _root_.GlobalTheory.SW.thS at h
    rw [tsum_eq_single (_root_.GlobalTheory.SW.ofQ m), tsum_eq_single m] at h
    · simpa using h
    all_goals (intro b hb; simp [hbij.1.eq_iff, hb])
  refine ⟨fun z z' => ?_, fun ψ hψ hθ => ?_⟩
  · rw [← (Equiv.ofBijective _ hbij).summable_iff]
    have hs := _root_.GlobalTheory.SW.SiegelSum.summable_norm_thetaTerm _ _ (fun m => φ (_root_.GlobalTheory.SW.ofQ m)) ((hSB φ).1 hφ) _ (hup Z hZ)
      (_root_.GlobalTheory.SW.zetaOf Ψ z z')
    refine hs.congr fun m => ?_
    simp only [Function.comp_apply, Equiv.ofBijective_apply, hexp]
  · have h := _root_.GlobalTheory.SW.eq_of_thS_eq _ _ (fun m => φ (_root_.GlobalTheory.SW.ofQ m))
      (fun m => ψ (_root_.GlobalTheory.SW.ofQ m)) ((hSB φ).1 hφ) ((hSB ψ).1 hψ) _ (hup Z hZ)
      (fun ζ => by
        obtain ⟨z, z', rfl⟩ := hsurj ζ
        rw [← hdict, ← hdict]
        exact hθ z z')
    funext x
    obtain ⟨m, rfl⟩ := hbij.2 x
    exact congrFun h m
