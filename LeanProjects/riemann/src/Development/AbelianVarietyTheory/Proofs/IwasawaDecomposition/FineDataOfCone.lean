import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSymmetricFormAlongDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdOfValuationLeAllDvrStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.TorRef

theorem pow_eq_of_associated {W : Type} [CommRing W] [IsDomain W] {ϖ : W} (hϖ : Irreducible ϖ) {n m : ℕ}
    (h : Associated (ϖ ^ n) (ϖ ^ m)) : n = m :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd)
    ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)

theorem fineData_of_inCone : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m N : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsCN R → P.TorsionIso → InCone P.D.toPre γ → IsFine N γ →
    FineData P.D.toPre N := by
  intro E _ _ _ H R _ _ _ t P m N γ hR _ hC hF y
  obtain ⟨hN, hI, -, hZ⟩ := hR
  have hex : ∀ χ, ∃ r, Formalism.L2.Pj.PsiCoord P.D.toPre χ r ∧ r ≠ 0 := fun χ =>
    ((GlobalTheory.PsiCoordLocal.main R P.D hI χ).1).imp fun _ h => ⟨h.1, h.2.1⟩
  obtain ⟨μ₀, hμ₀⟩ := hF.exists_min y
  obtain ⟨r, hr, hr0⟩ := hex (y + N • μ₀)
  refine ⟨μ₀, r, hr, fun μ => ?_⟩
  obtain ⟨r', hr', -⟩ := hex (y + N • μ)
  obtain ⟨s, rfl⟩ : r ∣ r' := by
    refine GlobalTheory.T.dvd_of_valuation_le_all_dvr R hN hI r r' hr0 fun W _ _ _ hW ϖ hϖ f hf n n' hn hn' => ?_
    haveI : IsDiscreteValuationRing W := hW.1
    obtain ⟨be, hsym, hbe⟩ := GlobalTheory.T.exists_symmetric_form_along_dvr R hI P.D W f hf ϖ hϖ
    obtain ⟨c, hc, hce⟩ := hC W hW ϖ hϖ f be hsym hbe
    have key : ∀ (z : P.D.toPre.X) (r₀ : R) (k : ℕ), Formalism.L2.Pj.PsiCoord P.D.toPre z r₀ →
        Associated (f r₀) (ϖ ^ k) → (be z z : ℝ) = 2 * k := by
      intro z r₀ k hz hk
      obtain ⟨r₁, k₁, h1, h2, h3⟩ := hbe z
      obtain ⟨u, hu⟩ := GlobalTheory.PsiCoordLocal.exists_unit_of_coord hz h1
      have h4 : Associated (f r₀) (ϖ ^ k₁) := by
        refine Associated.trans ⟨Units.map f.toMonoidHom u, ?_⟩ h3
        rw [hu, map_mul, mul_comm]; rfl
      have h5 : k = k₁ := pow_eq_of_associated hϖ (hk.symm.trans h4)
      subst h5
      exact_mod_cast h2
    have e := fun z => congrArg (fun B : P.D.toPre.X →ₗ[ℤ] P.D.toPre.X →ₗ[ℤ] ℝ => B z z) hce
    simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul] at e
    have h1 := key _ _ _ hr hn
    have h2 := key _ _ _ hr' hn'
    have := hμ₀ c hc μ
    rw [← e, ← e, h1, h2] at this
    exact_mod_cast (by linarith : (n : ℝ) ≤ n')
  exact ⟨s, hr'⟩

end GlobalTheory.TorRef
