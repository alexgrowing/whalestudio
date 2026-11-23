import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsVeryAmpleH1Zero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleLiftSquareZeroThickeningStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVeryAmplePowerStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompatibleSectionsThickeningsLocalRingStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveAlgebraisationFormalCompleteLocaStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfSmoothThickeningsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLineBundleOfThickenings
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBaseStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalAlgebraise

theorem ker_factor_sq {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ^ 2 = ⊥ := by
  have hle : RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))) ≤
      (I ^ (e + 1)).map (Ideal.Quotient.mk _) := by
    intro x hx
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact Ideal.mem_map_of_mem _ hx
  refine le_bot_iff.1 ((Ideal.pow_right_mono hle _).trans ?_)
  rw [← Ideal.map_pow, ← pow_mul, le_bot_iff, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
  exact Ideal.pow_le_pow_right (by omega)

open GlobalTheory.AbLaw in

theorem algebraisation : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≠ ⊤ → IsAdicComplete I R → IsAdicComplete (IsLocalRing.maximalIdeal R) R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, Smooth (Y e).hom) → (∀ e, (N e).IsLB ∧ (v e).IsGen) → RelAmple (Y 0) (N 0) → ∃ (B : Over (Spec (CommRingCat.of R))) (M : LB B.left) (b : ∀ e, (Y e).left ⟶ B.left), GlobalTheory.AbLaw.IsProjBy B.hom ∧ Smooth B.hom ∧ M.IsLB ∧ RelAmple B M ∧ (∀ e, IsPullback (b e) (Y e).hom B.hom (thick R I e)) ∧ (∀ e, β e ≫ b (e + 1) = b e) ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro _ _ R _ _ _ _ I hI hc _ Y β N v hβ hY hN hA
  have hfl : ∀ e, Flat (Y e).hom := fun e => by have := hY e; infer_instance
  have hamp : ∀ e, RelAmple (Y e) (N e) := by
    intro e
    induction e with
    | zero => exact hA
    | succ e ih =>
      have := hY (e + 1)
      exact GlobalTheory.T.relAmple_lift_squareZero_thickening _ _ _ (Ideal.Quotient.factor_surjective _) (ker_factor_sq I e) (Y (e + 1)) (Y e) (β e)
        (hβ e) inferInstance _ _ (hN _).1 (hN _).1 ⟨v e, (hN e).2⟩ ih
  have hproj : ∀ e, IsProjBy (Y e).hom := fun e => by
    obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ (Y e) (N e) (hN e).1).1 (hamp e)
    exact ⟨_, isLB_pw (hN e).1 _, n, s, hs⟩
  have hle : I ^ (0 + 1) ≤ IsLocalRing.maximalIdeal R := by
    rw [zero_add, pow_one]
    exact IsLocalRing.le_maximalIdeal hI
  let g₀ : R ⧸ I ^ (0 + 1) →+* IsLocalRing.ResidueField R := Ideal.Quotient.factor hle
  have hg₀ : Function.Surjective g₀ := Ideal.Quotient.factor_surjective hle
  have hpb := IsPullback.of_hasPullback (Y 0).hom (Spec.map (CommRingCat.ofHom g₀))
  obtain ⟨d, hd, h0, n, s₀, hs₀⟩ := GlobalTheory.T.exists_very_ample_power _ (Y 0) (N 0) (hN 0).1 hA _ g₀ _ _ _ hpb
  have hv : ∀ e, LBIso (AbLaw.pw (N e) d) ((AbLaw.pw (N (e + 1)) d).pull (β e)) := fun e => by
    rw [GlobalTheory.Algebraise.pw_pull]
    exact GlobalTheory.Algebraise.lbIso_pw ⟨v e, (hN e).2⟩ d
  choose v' hv' using hv
  have hN' : ∀ e, (AbLaw.pw (N e) d).IsLB ∧ (v' e).IsGen := fun e => ⟨isLB_pw (hN e).1 d, hv' e⟩
  have hL := LB.isLB_pull (hN' 0).1 (pullback.fst (Y 0).hom (Spec.map (CommRingCat.ofHom g₀)))
  choose s hs0 hs using fun j => GlobalTheory.T.exists_compatible_sections_thickenings_localRing R I hI Y β hβ hfl hproj
    (fun e => AbLaw.pw (N e) d) v' hN' _ g₀ hg₀ _ _ _ hpb _ _ hL (CubePf.idIsoL_isGen hL) h0 (s₀ j)
  have hva : VeryAmpleBy (Y 0).hom (AbLaw.pw (N 0) d) (fun j => s j 0) := by
    have : (fun j => s j 0) = s₀ := funext hs0
    rw [this]
    exact hs₀
  obtain ⟨B, H, s', b, w, hH, hB, hb, hbβ, -, -⟩ := GlobalTheory.T.exists_projective_algebraisation_formal_complete_local R I hI hc Y β hβ hfl
    (fun e => AbLaw.pw (N e) d) v' hN' n (fun e j => s j e) (fun e j => hs j e) hva
  have hP : IsProjBy B.hom := ⟨H, hH, n, s', hB⟩
  have hS : Smooth B.hom := GlobalTheory.T.smooth_of_smooth_thickenings' R I hI B (isProper_of_isProjBy R B.left B.hom hP) Y b hb hY
  have hF : Flat B.hom := inferInstance
  obtain ⟨M, hM, hNM⟩ := GlobalTheory.LBAlgLocal.exists_lineBundle_of_thickenings R I hI hc Y β hβ B b hP hF hb hbβ N v hN
  haveI : Nontrivial (R ⧸ I ^ (0 + 1)) := g₀.domain_nontrivial
  exact ⟨B, M, b, hP, hS, hM, GlobalTheory.T.relAmple_of_ample_on_closed_subscheme_localBase R B M hF hP hM _ _ Ideal.Quotient.mk_surjective (Y 0) (b 0) (hb 0)
    (N 0) (hN 0).1 (hNM 0) hA, hb, hbβ, hNM⟩

end GlobalTheory.FormalAlgebraise
