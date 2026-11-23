import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InRealConeSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralSupportFunctionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RankIncreaseOfNonSpanStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformBoundSupportFunctionsStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.PolFan.FullCone

theorem exists_cone_span_balanced : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q g : ℕ) (φs : InvFun ℤ) (𝒩 : Finset ℕ) (φ : InvFun (𝓞 E)) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (k : ℕ) (γ : Fin k → LinearMap.BilinForm ℤ X), Module.finrank ℚ E * q ≤ g → IsPolFan id g φs → Refines H q φs 𝒩 φ → Module.finrank (𝓞 E) X ≤ q → ConeZ E φs X k γ → ∀ be ∈ balForms H.bar X, (∀ y, 0 ≤ be y y) → GlobalTheory.ChartMono.InRealCone γ be → ∃ (k₁ : ℕ) (δ : Fin k₁ → LinearMap.BilinForm ℤ X), IsCone H.bar φ δ ∧ GlobalTheory.ChartMono.InRealCone δ be ∧ ∀ β ∈ balForms H.bar X, GlobalTheory.ChartMono.InRealCone γ β → ∃ (M : ℕ) (a : Fin k₁ → ℤ), 0 < M ∧ (M : ℤ) • β = ∑ i, a i • δ i := by
  intro E _ _ _ H q g φs 𝒩 φ X _ _ _ _ k γ hg hφs hR hX hγ be hbe hbp hbc
  classical
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have hP : IsPolFanOn H.bar φ X := hR.1 X hX
  obtain ⟨Nmax, hN⟩ := GlobalTheory.T.exists_integral_support_function _ H.bar φ X hP
  let P : ℕ → Prop := fun m => ∃ δ : Fin m → LinearMap.BilinForm ℤ X, IsCone H.bar φ δ ∧ GlobalTheory.ChartMono.InRealCone δ be
  let B := Module.finrank ℤ (balForms H.bar X)
  have hB : ∀ m, P m → m ≤ B := by
    rintro m ⟨δ, hδ, -⟩
    obtain ⟨n, b, -⟩ := hδ.basis
    have := Module.finrank_eq_card_basis b
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega
  obtain ⟨m0, δ0, c0, hδ0, hc0, he0⟩ := hP.cover _ (toReal_mem_psdCone_of_nonneg E H X be hbe hbp)
  have hP0 : P m0 := ⟨δ0, hδ0, c0, hc0, he0⟩
  set ms := Nat.findGreatest P B with hms
  obtain ⟨δ, hδ, hbδ⟩ : P ms := Nat.findGreatest_spec (hB m0 hP0) hP0
  refine ⟨ms, δ, hδ, hbδ, fun β hβ hβc => ?_⟩
  by_contra hne
  have hβp : ∀ y, 0 ≤ β y y := fun y => by
    obtain ⟨c, hc, he⟩ := hβc
    have h1 := LinearMap.congr_fun₂ he y y
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
    have : (0 : ℝ) ≤ β y y := h1 ▸ Finset.sum_nonneg fun i _ => mul_nonneg (hc i) (by exact_mod_cast hγ.nonneg i y)
    exact_mod_cast this
  obtain ⟨m', ε, hε, hδε, hwε⟩ := GlobalTheory.T.uniform_bound_support_functions E H φ X hP Nmax hN ms δ hδ β hβ hβp
  have hlt := GlobalTheory.T.rank_increase_of_non_span X ms m' δ ε β hδ.linearIndependent hne (fun j => by
    obtain ⟨k, c, hk, hc⟩ := hδε j
    exact ⟨k, fun i => c i, hk, by rw [natCast_zsmul, hc]; simp only [natCast_zsmul]⟩) hwε
  have hPm' : P m' := by
    refine ⟨ε, hε, ?_⟩
    obtain ⟨c, hc, he⟩ := hbδ
    choose k d hk hd using hδε
    refine ⟨fun i => ∑ j, c j * (d j i : ℝ) / k j, fun i => Finset.sum_nonneg fun j _ => by
      have := hc j; positivity, LinearMap.ext₂ fun a b => ?_⟩
    have h1 := LinearMap.congr_fun₂ he a b
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1 ⊢
    have h2 : ∀ j, (δ j a b : ℝ) = ∑ i, (d j i : ℝ) * (ε i a b : ℝ) / k j := fun j => by
      have := LinearMap.congr_fun₂ (hd j) a b
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at this
      have hk0 : (k j : ℝ) ≠ 0 := by exact_mod_cast (hk j).ne'
      rw [← Finset.sum_div, eq_div_iff hk0]
      exact_mod_cast (by rw [mul_comm]; exact this)
    rw [h1]
    simp only [h2, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have := Nat.le_findGreatest (hB m' hPm') hPm'
  omega

end GlobalTheory.PolFan.FullCone
