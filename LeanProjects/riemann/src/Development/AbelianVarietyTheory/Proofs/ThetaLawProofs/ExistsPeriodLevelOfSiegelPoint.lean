import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BijectiveTensorOmegaStd

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.SiegelObject

open GlobalTheory.TensorSiegel

theorem exists_lattice_form {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (hs : τ.IsSymm)
    (hp : (τ.map Complex.im).PosDef) :
    ∃ (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (Ef : LinearMap.BilinForm ℤ Λ),
      DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ Hm.IsHermitian ∧
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      (∀ a b : Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧
      (∀ z, z ∈ Λ ↔ ∃ a, z = per τ a) ∧
      ∀ a b, (hermForm Hm (per τ a) (per τ b)).im = omegaStd a b := by
  let σ : Fin 1 × Fin g ≃ Fin g := Equiv.uniqueProd _ _
  let G : Matrix (Fin 1) (Fin 1) ℤ := 1
  have hG : (G.map (Int.cast : ℤ → ℝ)).PosDef := by
    rw [show G.map (Int.cast : ℤ → ℝ) = 1 from Matrix.map_one _ Int.cast_zero Int.cast_one]
    exact Matrix.PosDef.one
  have hper : ∀ x : Fin 1 → (Fin g ⊕ Fin g → ℤ), period σ τ x = per τ (x 0) := fun x => by
    funext i
    exact period_apply σ τ x 0 i
  have hsum : ∀ x y : Fin 1 → (Fin g ⊕ Fin g → ℤ),
      ∑ u, ∑ v, G u v * omegaStd (x u) (y v) = omegaStd (x 0) (y 0) := fun x y => by simp [G]
  let EF : LinearMap.BilinForm ℤ (Fin 1 → (Fin g ⊕ Fin g → ℤ)) :=
    LinearMap.mk₂ ℤ (fun x y => omegaStd (x 0) (y 0))
      (fun x x' y => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun x y y' => by
        simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring)
      (fun c x y => by
        simp only [omegaStd, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring)
  have hEF : Function.Bijective EF :=
    bijective_tensor_omegaStd G (by simp [G]) EF fun x y => (hsum x y).symm
  obtain ⟨h1, h2, h3⟩ := period_isLattice σ hp
  have him := im_formMatrix_period σ G hs hp
  let Q := (period σ τ).toIntLinearMap
  let e := LinearEquiv.ofInjective Q h1
  refine ⟨LinearMap.range Q, formMatrix σ (G.map (Int.cast : ℤ → ℝ)) τ,
    e.symm.dualMap.toLinearMap ∘ₗ EF ∘ₗ e.symm.toLinearMap, h2, h3, formMatrix_isHermitian σ hG hp,
    fun z hz => formMatrix_pos σ hG hp hz, fun a b => ?_,
    e.symm.dualMap.bijective.comp (hEF.comp e.symm.bijective), fun z => ?_, fun a b => ?_⟩
  · obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    refine Eq.trans ?_ (him x y).symm
    rw [hsum]
    simp [EF]
  · exact ⟨fun ⟨x, hx⟩ => ⟨x 0, hx.symm.trans (hper x)⟩, fun ⟨a, ha⟩ => ⟨fun _ => a, (hper _).trans ha.symm⟩⟩
  · have := him (fun _ => a) (fun _ => b)
    rwa [hsum, hper, hper] at this

theorem exists_perLev_of_siegel : ThetaUnifAV → GlobalTheory.TorusAlgebraic → ∀ (g k : ℕ) (τ : Matrix (Fin g) (Fin g) ℂ), τ.IsSymm → (τ.map Complex.im).PosDef → ∃ (P : Out.PolAV (Sp ℂ)) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev := by
  intro hU _ g k τ hs hp
  obtain ⟨Λ, Hm, Ef, h1, h2, h3, h4, h5, h6, hΛ, hω⟩ := exists_lattice_form τ hs hp
  obtain ⟨P, u, χ, hg, rfl, hAH, -⟩ := GlobalTheory.principalTorus_algebraic g Λ Hm Ef h1 h2 h3 h4 h5 h6
  obtain ⟨E', hE', -, -, -, -, hW⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hU P g u Hm χ hAH
  refine ⟨P, fun a => u.ex ((k : ℂ)⁻¹ • per τ a), hg, hs, hp, u, hΛ, fun n a b c hn hc => ?_, fun _ => rfl⟩
  refine hW n ⟨per τ a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨per τ b, (hΛ _).2 ⟨b, rfl⟩⟩ c hn ?_
  have h : E' ⟨per τ a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨per τ b, (hΛ _).2 ⟨b, rfl⟩⟩ = omegaStd a b := by
    have h' := hE' ⟨per τ a, (hΛ _).2 ⟨a, rfl⟩⟩ ⟨per τ b, (hΛ _).2 ⟨b, rfl⟩⟩
    rw [Subtype.coe_mk, Subtype.coe_mk, hω] at h'
    exact Int.cast_injective h'
  rw [h, hc]

end GlobalTheory.SiegelObject
