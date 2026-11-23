import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianMetricGradingStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.CovTest.SwapFlProof

theorem comb_isometric_pullback {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {κ : Type} [Fintype κ]
    (L : κ → HermLB q) (M : κ → HermLB p) (ρ : Y ⟶ X) (wρ : ρ ≫ p = q) (n : κ → ℤ) (S : κ → Prop)
    (hn : ∀ z, S z → n z = 0) (hM : ∀ z, ¬ S z → ((M z).pull ρ wρ).Isometric (L z)) :
    (comb L n).Isometric ((comb M n).pull ρ wρ) := by
  refine HermLB.Isometric.trans ?_ (isometric_comb_pull M n ρ wρ)
  refine HermLB.icls_eq_iff.1 ?_
  rw [icls_comb, icls_comb]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : S z
  · rw [hn z hz, zero_smul, zero_smul]
  · rw [HermLB.icls_eq_iff.2 (hM z hz).symm]

theorem lin_update_two_coords {κ : Type} [Fintype κ] [DecidableEq κ] (x y : κ) (hxy : x ≠ y) (n n' : κ → ℤ)
    (hx0 : n' x = 0) (hy0 : n' y = 0) (hne : ∀ z, z ≠ x → z ≠ y → n' z = n z) (c₀ c₁ : ℤ) :
    (lin fun z => ∑ j : Fin 3, (![(c₀ : ℝ), c₁, 1] j) *
      ((![Pi.single x 1, Pi.single y 1, n'] : Fin 3 → κ → ℤ) j z : ℝ)) =
      lin fun z => ((Function.update (Function.update n x c₀) y c₁ z : ℤ) : ℝ) := by
  congr 1
  funext z
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Pi.single_apply, Function.update_apply]
  by_cases h1 : z = x
  · subst h1; simp [hx0, hxy]
  · by_cases h2 : z = y
    · subst h2; simp [hy0, h1]
    · simp [h1, h2, hne z h1 h2]

theorem swapFl_of_swap2 : ArCalc → ∀ G, Homog G → Swap2 G → SwapFl G := by
  intro _ G _ hS k _ B Y _ _ q p d D hq hp π w ι _ E r h H fl hfl Φ Ψ hΦ hΨ a i i' hi n
  obtain ⟨Y₁, q₁, d₁, ρ, wρ, E₁, h₁, H₁, fl₁, M, rfl, hY₁, hfl₁, hS0, hS1, hM⟩ :=
    GlobalTheory.T.flag_bundle_hermitian_metric_grading k B Y q p d D hq hp π w ι E r h H fl hfl a i i' hi
  haveI := hY₁.isIntegral
  set x : Σ a, Fin (r a) := ⟨a, i⟩ with hx
  set y : Σ a, Fin (r a) := ⟨a, i'⟩ with hy
  have hxy : x ≠ y := by
    intro e
    rw [hx, hy, Sigma.mk.inj_iff] at e
    have := congrArg Fin.val (eq_of_heq e.2)
    omega
  set L : (Σ a, Fin (r a)) → HermLB p := fun z => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w) with hL
  set n' : (Σ a, Fin (r a)) → ℤ := fun z => if z = x ∨ z = y then 0 else n z with hn'
  set Mf : Fin 3 → HermLB p := ![VMetric.grLB fl₁ 0 (H₁.pull ρ wρ), VMetric.grLB fl₁ 1 (H₁.pull ρ wρ),
    (comb M n').pull ρ wρ] with hMf
  set Am : Fin 3 → (Σ a, Fin (r a)) → ℤ := ![Pi.single x 1, Pi.single y 1, n'] with hAm
  have hiso : ∀ j, (comb L (Am j)).Isometric (Mf j) := by
    intro j
    fin_cases j
    · exact (isometric_comb_single L x).trans hS0.symm
    · exact (isometric_comb_single L y).trans hS1.symm
    · exact comb_isometric_pullback L M ρ wρ n' (fun z => z = x ∨ z = y) (fun z hz => if_pos hz)
        (fun z hz => hM z (fun e => hz (Or.inl e)) (fun e => hz (Or.inr e)))
  set f : Fin 3 → MvPolynomial (Σ a, Fin (r a)) ℝ := fun j => lin fun z => (Am j z : ℝ) with hf
  have hΦ' := ((Published.arIso_holds k Y p (d₁ + 1) hp).2 _ L Φ hΦ).2.2 (Fin 3) Mf Am hiso
  have hΨ' : IsGeoFun Mf (d₁ + 1) (Ψ ∘ₗ (aeval f : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] _).toLinearMap) := by
    refine ⟨fun m => ?_, fun P e he hP => ?_⟩
    · rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin]
      have h2 := hΨ.1 (fun z => ∑ j, m j * Am j z)
      simp only [Int.cast_sum, Int.cast_mul] at h2
      rw [h2]
      exact ((isometric_comb_comb L Am m).trans (isometric_comb_congr hiso m)).gdeg_eq _
    · rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
      exact hΨ.2 _ e he (by simpa using hP.aeval _ fun j => isHomogeneous_lin _)
  have key := hS k Y₁ Y q₁ p d₁ hY₁ hp ρ wρ E₁ h₁ H₁ fl₁ hfl₁ (comb M n') _ _ hΦ' hΨ' (n x) (n y)
  have hsw : aeval f (G (d₁ + 1) (n x) (n y)) = swapPol G (d₁ + 1) x y n := by
    unfold swapPol
    congr 2
    funext j
    fin_cases j
    · exact lin_single x
    · exact lin_single y
    · simp only [hf, hAm, hn', Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      congr 1
      funext z
      by_cases hz : z = x ∨ z = y <;> simp [hz]
  have hx0 : n' x = 0 := if_pos (Or.inl rfl)
  have hy0 : n' y = 0 := if_pos (Or.inr rfl)
  have hne : ∀ z, z ≠ x → z ≠ y → n' z = n z := fun z h1 h2 => if_neg (by tauto)
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin] at key
  rw [← hsw, ← key, hAm, lin_update_two_coords x y hxy n n' hx0 hy0 hne (n x) (n y), lin_update_two_coords x y hxy n n' hx0 hy0 hne (n y) (n x)]
  congr 4 <;> funext z
  · rw [Function.update_eq_self, Function.update_eq_self]
  · by_cases h1 : z = x
    · subst h1; simp [Function.update_apply, hxy, Equiv.swap_apply_left]
    · by_cases h2 : z = y
      · subst h2; simp [Function.update_apply, Equiv.swap_apply_right]
      · simp [Function.update_apply, h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]

end GlobalTheory.CovTest.SwapFlProof
