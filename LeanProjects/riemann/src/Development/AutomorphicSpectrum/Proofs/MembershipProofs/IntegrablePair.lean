import Mathlib
import Development.AutomorphicSpectrum.Definitions.MembershipCriteria.GoodChar
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.GoodCharIsLocallyConstant

noncomputable section

open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.SchrSys

section Pair

variable {R : Type} [TopologicalSpace R] {κ : Type}

theorem integrable_pair (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ)
    (φ φ' : SB (κ → R)) :
    @Integrable ℂ _ _ _ (borel _) (fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x) * (φ' : (κ → R) → ℂ) x) μ := by
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  have h1 : Continuous (φ : (κ → R) → ℂ) := φ.2.1.continuous
  have h2 : Continuous (φ' : (κ → R) → ℂ) := φ'.2.1.continuous
  have h3 : HasCompactSupport (φ' : (κ → R) → ℂ) := φ'.2.2
  exact Continuous.integrable_of_hasCompactSupport ((Complex.continuous_conj.comp h1).mul h2)
    (HasCompactSupport.mul_left (f := fun x => (starRingEnd ℂ) ((φ : (κ → R) → ℂ) x)) h3)

def pairForm (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ) :
    SB (κ → R) →ₗ⋆[ℂ] SB (κ → R) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun φ φ' => pair μ φ φ')
    (by
      intro f f' g
      simp only [pair, Submodule.coe_add, Pi.add_apply, map_add, add_mul]
      exact integral_add (integrable_pair μ hμ f g) (integrable_pair μ hμ f' g))
    (by
      intro a f g
      simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
      exact integral_const_mul _ _)
    (by
      intro f g g'
      simp only [pair, Submodule.coe_add, Pi.add_apply, mul_add]
      exact integral_add (integrable_pair μ hμ f g) (integrable_pair μ hμ f g'))
    (by
      intro a f g
      simp only [pair, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_left_comm _ a]
      exact integral_const_mul _ _)

theorem pair_conj (μ : @Measure (κ → R) (borel _)) (φ φ' : (κ → R) → ℂ) :
    (starRingEnd ℂ) (pair μ φ φ') = pair μ φ' φ := by
  letI : MeasurableSpace (κ → R) := borel _
  unfold pair
  rw [← integral_conj]
  congr 1
  funext x
  simp [mul_comm]

theorem pair_pos (μ : @Measure (κ → R) (borel _)) (hμ : @IsFiniteMeasureOnCompacts _ (borel _) _ μ)
    (hμ' : @Measure.IsOpenPosMeasure _ _ (borel _) μ) (φ : SB (κ → R)) (hφ : φ ≠ 0) : 0 < (pair μ φ φ).re := by
  letI : MeasurableSpace (κ → R) := borel _
  haveI : BorelSpace (κ → R) := ⟨rfl⟩
  have h1 : Continuous (φ : (κ → R) → ℂ) := φ.2.1.continuous
  have h3 : HasCompactSupport (φ : (κ → R) → ℂ) := φ.2.2
  have e : pair μ φ φ = ((∫ x, ‖(φ : (κ → R) → ℂ) x‖ * ‖(φ : (κ → R) → ℂ) x‖ ∂μ : ℝ) : ℂ) := by
    unfold pair
    rw [← integral_complex_ofReal]
    congr 1
    funext x
    rw [Complex.conj_mul']
    simp [sq]
  rw [e, Complex.ofReal_re]
  obtain ⟨x, hx⟩ : ∃ x, (φ : (κ → R) → ℂ) x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (Subtype.ext (funext h))
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x) (h1.norm.mul h1.norm)
    (HasCompactSupport.mul_left (f := fun x => ‖(φ : (κ → R) → ℂ) x‖) h3.norm)
    (fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _)) ?_
  have := norm_pos_iff.2 hx
  exact (mul_pos this this).ne'

end Pair

theorem exists_isModel : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) , GoodChar ψ O u → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∃ S : Sys W (SB (κ → R)), IsModel ψ d μ S := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ hψ hμ
  have law := fun w w' φ φ' => GlobalTheory.CompanionTheory.SchrLaw.schr_law ψ O u d μ w w' φ φ' hψ hμ
  have hc : @IsFiniteMeasureOnCompacts _ (borel _) _ μ := hμ.toIsFiniteMeasureOnCompacts
  have ho : @Measure.IsOpenPosMeasure _ _ (borel _) μ := hμ.toIsOpenPosMeasure
  let rho : W → SB (κ → R) →ₗ[ℂ] SB (κ → R) := fun w =>
    { toFun := fun φ => ⟨d.rho ψ w φ, (law w 0 φ 0).2.2.1 φ.2⟩
      map_add' := fun φ φ' => by
        apply Subtype.ext
        funext x
        simp [Darboux.rho, schr, mul_add]
      map_smul' := fun a φ => by
        apply Subtype.ext
        funext x
        simp [Darboux.rho, schr, mul_left_comm] }
  refine ⟨{ c := fun w w' => ψ (⅟(2 : R) * B w w')
            rho := rho
            B := pairForm μ hc
            c_add_left := ?_
            c_add_right := ?_
            c_self := ?_
            c_norm := fun _ _ => hψ.norm_one _
            rho_zero := fun φ => Subtype.ext (law 0 0 φ 0).2.1
            rho_rho := fun w w' φ => Subtype.ext (law w w' φ 0).1
            B_conj := fun φ φ' => pair_conj μ φ φ'
            B_pos := fun φ hφ => pair_pos μ hc ho φ hφ
            B_rho := fun w φ φ' => (law w 0 φ φ').2.2.2 },
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  · intro x x' y
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    ring
  · intro x y y'
    rw [← AddChar.map_add_eq_mul]
    congr 1
    simp only [d.form, map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
    ring
  · intro x
    simp [d.form]

end GlobalTheory.CompanionTheory.SchrSys
