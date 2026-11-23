import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnimodularSymplecticCoordinatesAndLatticeRank
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolUnifReparam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_perLev : ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (g k : ℕ), P.g = g → ∃ (τ : Matrix (Fin g) (Fin g) ℂ) (lev : (Fin g ⊕ Fin g → ℤ) → (𝟙_ (Over (Sp ℂ)) ⟶ P.A)), PerLev P τ k lev := by
  rintro hU P g k rfl
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨u, Hm, χ, Ef, hAH, -, -, -, -, -, hE, hb, hW⟩ := hU P rig hrig
  let Q : u.Λ →+ (Fin P.g → ℂ) := u.Λ.subtype.toAddMonoidHom
  have hrange : Set.range Q = (u.Λ : Set (Fin P.g → ℂ)) := Subtype.range_coe
  have hQ : Function.Injective Q ∧ DiscreteTopology Q.range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧
      Hm.IsHermitian ∧ (∀ z : Fin P.g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (Q x) (Q y)).im = Ef x y := by
    refine ⟨Subtype.val_injective, ?_, hrange ▸ u.full, hAH.1, hAH.2.1, fun x y => (hE x y).symm⟩
    have h := u.discrete
    change DiscreteTopology (Set.range Q)
    rw [hrange]
    exact h
  obtain ⟨h1, h2, h3, h4⟩ := unimodular_symplectic_coordinates_and_lattice_rank.2 _ Ef _ Q Hm hQ
  obtain ⟨bas, hbas⟩ := unimodular_symplectic_coordinates_and_lattice_rank.1 _ Ef _ hb h4 h3
  obtain ⟨h, τ, hh, -, -, hs, hp, -, hper⟩ := SiegelPeriod.exists_siegel_form _ Ef _ bas Q Hm hbas hQ
  let ψ : (Fin P.g → ℂ) ≃ₗ[ℂ] (Fin P.g → ℂ) := LinearEquiv.ofBijective h.mulVecLin
    ⟨Matrix.mulVec_injective_iff_isUnit.2 hh, Matrix.mulVec_surjective_iff_isUnit.2 hh⟩
  have hψ : ∀ a, ψ.symm (per τ a) = (bas a : Fin P.g → ℂ) := fun a => by
    rw [LinearEquiv.symm_apply_eq]
    exact (hper a).symm
  obtain ⟨u', hex, hΛ, -⟩ := exists_holUnif_reparam P.A P.L P.g u ψ.symm (fun _ => 1)
    (differentiable_const _) (fun _ => one_ne_zero) rfl
  refine ⟨τ, fun a => u'.ex ((k : ℂ)⁻¹ • per τ a), rfl, hs, hp, u', fun z => ?_, fun n a b c hn hc => ?_,
    fun _ => rfl⟩
  · rw [hΛ]
    constructor
    · intro hz
      refine ⟨bas.symm ⟨_, hz⟩, ψ.symm.injective ?_⟩
      rw [hψ, LinearEquiv.apply_symm_apply]
    · rintro ⟨a, rfl⟩
      rw [hψ]
      exact (bas a).2
  · rw [hex, hex, map_smul, map_smul, hψ, hψ]
    exact hW n (bas a) (bas b) c hn (by rw [hbas]; exact hc)

end GlobalTheory.KeyFam
