import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppellHumbertExistsLineBundlePosDefHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutingCoordinateDerivationsRegularFunctStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivePiLiftKaehlerCoordinateDerivationsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedOneFormEvaluationRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerAffineOpenFiniteProjectiveRankStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfSurjectiveProjectiveConstRankStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem kaehler_frame : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.affineOpens), ∃ (d : Fin g → Derivation ℂ (Sec (str A) U.1) (Sec (str A) U.1)) (ω : Fin g → Ω[Sec (str A) U.1⁄ℂ]), (∀ a b x, d a (d b x) = d b (d a x)) ∧ (∀ a x, ∀ z ∈ pre u.ex U.1, val u.ex U.1 (d a x) z = fderiv ℂ (val u.ex U.1 x) z (Pi.single a 1)) ∧ (∀ a b, (d a).liftKaehlerDifferential (ω b) = if a = b then 1 else 0) ∧ (∀ ξ, ξ = ∑ a, (d a).liftKaehlerDifferential ξ • ω a) ∧ ∀ a ξ, ∀ z ∈ pre u.ex U.1, evForm u.ex U.1 z ξ (Pi.single a 1) = val u.ex U.1 ((d a).liftKaehlerDifferential ξ) z := by
  intro A _ g L u hA U
  obtain ⟨d, hcomm, hval⟩ := GlobalTheory.T.exists_commuting_coordinate_derivations_regular_functions A g L u hA U.1
  have hsm := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨hfin, hproj, hrk⟩ := GlobalTheory.T.kaehler_affineOpen_finite_projective_rank A g hsm U
  have hsurj := GlobalTheory.T.surjective_pi_liftKaehler_coordinateDerivations A g L u hA U d hval
  set Φ : Ω[Sec (str A) U.1⁄ℂ] →ₗ[Sec (str A) U.1] (Fin g → Sec (str A) U.1) :=
    LinearMap.pi fun a => (d a).liftKaehlerDifferential with hΦ
  have hinj : Function.Injective Φ := GlobalTheory.T.injective_of_surjective_projective_constRank _ _ g Φ hfin hproj hrk hsurj
  let e := LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hΦa : ∀ ξ a, Φ ξ a = (d a).liftKaehlerDifferential ξ := fun ξ a => rfl
  refine ⟨d, fun b => e.symm (Pi.single b 1), hcomm, hval, ?_, ?_, ?_⟩
  · intro a b
    rw [← hΦa]
    have : Φ (e.symm (Pi.single b 1)) = Pi.single b 1 := e.apply_symm_apply _
    rw [this, Pi.single_apply]
  · intro ξ
    apply hinj
    funext c
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply]
    have h1 : ∀ b, Φ (e.symm (Pi.single b 1)) = Pi.single b 1 := fun b => e.apply_symm_apply _
    simp only [h1]
    rw [Finset.sum_eq_single c (fun b _ hb => by rw [Pi.single_eq_of_ne (Ne.symm hb), smul_zero])
      (fun h => absurd (Finset.mem_univ c) h), Pi.single_eq_same, hΦa]
    exact (_root_.mul_one _).symm
  · intro a ξ z hz
    obtain ⟨ev, hev⟩ := (GlobalTheory.T.uniformisation_preimage_value_rules A g L u).2.2.2.2.2.2.2.2.2.1 U.1 z hz
    obtain ⟨_, hsm', hD⟩ := GlobalTheory.T.uniformisedOneFormEvaluation_rules A g L u U.1 z hz
    have hmem : ξ ∈ Submodule.span (Sec (str A) U.1) (Set.range (KaehlerDifferential.D ℂ (Sec (str A) U.1))) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    have hev' : ∀ b : Sec (str A) U.1, val u.ex U.1 b z = ev b := hev
    suffices h : evForm u.ex U.1 z ξ (Pi.single a 1) = ev ((d a).liftKaehlerDifferential ξ) from
      h.trans (hev' _).symm
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      rw [hD, Derivation.liftKaehlerDifferential_comp_D]
      exact (hval a y z hz).symm.trans (hev' _)
    | zero => simp only [map_zero, ContinuousLinearMap.zero_apply]
    | add x y _ _ hx hy => simp only [map_add, ContinuousLinearMap.add_apply, hx, hy]
    | smul r x _ hx =>
      rw [hsm', ContinuousLinearMap.smul_apply, hx, map_smul, smul_eq_mul, smul_eq_mul, map_mul, hev' r]

end GlobalTheory.CechPer
