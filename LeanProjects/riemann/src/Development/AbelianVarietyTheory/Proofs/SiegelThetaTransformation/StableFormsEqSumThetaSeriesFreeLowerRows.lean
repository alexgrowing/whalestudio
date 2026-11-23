import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesLowerRowsZeroEqFreeLowerRowsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.VacuumMultiplierUnitaryCocycleStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsFormExtendToAllLatticesStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

private theorem thP_smul' {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ}
    (X : Data E r) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ)
    (idx : Fin g ≃ X.Ψ × Fin r) (φ : SW.TF n g) (c : ℂ) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n))
    (x : Frame X.Ψ r) : thP X hr bas idx φ (c • P) x = c * thP X hr bas idx φ P x := by
  unfold thP
  by_cases hc : c = 0
  · subst hc
    simp [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv]
  · simp only [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_smul_eq hc,
      MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => mul_assoc _ _ _

theorem GlobalTheory.Dict.stabForms_eq_sum_thP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → 4 * (Module.finrank ℚ E * r) + 4 ≤ n → ∀ (D : SW.Level X) (hn : r ≤ n) (M : ℕ) (𝔐 𝔍 : Ideal (𝓞 E)), 0 < M → (M : 𝓞 E) ∈ D.𝔪 → D.𝔪 = 𝔐 * 𝔍 → IsCoprime 𝔐 𝔍 → ∀ v₀ : Lt E r → TF n g, (∀ L ∈ D.lats, IsVac X bas D.w (tens (stdL E n) (D.sh L)) (v₀ L)) → ∀ mu : GL (Fin r) E → Lt E r → ℂ, (∀ ga ∈ D.grp, ∀ L ∈ D.lats, ∀ k : D.J, D.Red (fun i => (ga : Matrix (Fin r) (Fin r) E) *ᵥ D.β i) k → wG X bas idx ga (v₀ L) = (mu ga L * (D.lam k : ℂˣ)) • v₀ (mapL ga L)) → ∀ (k : X.Ψ → Fin q0 → ℕ) (k' : X.Ψ → Fin X.p0 → ℕ) (Jx : Type) [Finite Jx] (L : Jx → Lt E r) (Q : Jx → Frame X.Ψ r → ℂ), (∀ i, L i ∈ D.lats) → (∀ i i', ∀ ga ∈ D.grp, mapL ga (L i) = L i' → i = i') → (∀ i, ∀ ga ∈ D.grp, mapL ga (L i) = L i → mu ga (L i) = 1) → (∀ i, IsStabForm X D.grp (L i) (wtOf X hr k k' n) (Q i)) → ∃ (m : ℕ) (Λ : Fin m → Lt E n) (P : Fin m → Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)), (∀ j, Λ j ∈ Vset E n M ∧ P j ∈ Harm.rowHighest ℂ k k') ∧ ∀ i, ∀ x ∈ X.dom, Q i x = ∑ j, thP X hr bas idx (phiF bas D 𝔐 hn v₀ (L i) (Λ j)) (P j) x := by
  intro E _ _ _ r X g q0 hr bas idx n hS hE hn4 D hn M 𝔐 𝔍 hM hMm hmf hcop v₀ hv mu hmu k k' Jx _ L Q
    hL hinj hfix hQ

  obtain ⟨hnorm, -, hcoc⟩ := GlobalTheory.T.vacuum_multiplier_unitary_cocycle E r X g bas idx n hS hE D v₀ hv mu hmu

  have hsys := GlobalTheory.T.hermitianThetaLevelData_forms_system E r X g bas idx n hS hE hn4 D hn M hM hMm v₀ hv mu hmu

  obtain ⟨F, hF, hFL⟩ := GlobalTheory.T.exists_form_extend_to_all_lattices E r X D.grp D.lats mu (wtOf X hr k k' n) Jx L Q hsys.un
    (fun ga hga L' hL' => ⟨hsys.stab ga hga L' hL', hnorm ga hga L' hL'⟩) hcoc hL hinj hfix hQ

  obtain ⟨m, Λ, P, a, hΛP, hFsum⟩ :=
    GlobalTheory.SW.level_theta_span E r X g q0 hr bas idx n hS hE hn4 D hn M hM hMm v₀ hv mu hmu k k' F hF

  have h97 := fun j => GlobalTheory.T.thetaSeries_lowerRowsZero_eq_freeLowerRows E r X g q0 hr bas idx n hS hE D hn M 𝔐 𝔍 hM hMm hmf hcop v₀ hv
    k k' (Λ j) (hΛP j).1 (P j) (hΛP j).2
  choose Λ' hΛ' P' hP' heq using h97
  refine ⟨m, Λ', fun j => a j • P' j, fun j => ⟨hΛ' j, Submodule.smul_mem _ _ (hP' j)⟩, ?_⟩
  intro i x hx
  rw [← hFL i x hx, hFsum (L i) (hL i) x hx]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [heq j (L i) (hL i) x hx, thP_smul']
