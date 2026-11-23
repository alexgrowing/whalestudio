import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieSpanLoc

open GlobalTheory.Serre GlobalTheory.FlatRow.EigLocal

theorem exists_smul_mem_span : ∀ {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G],
    Smooth G.hom → ∀ (a : OAct O G) (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → GlobalTheory.Serre.Lie a),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i).hom (v i)) → IsLieBasis v) →
    ∀ l : GlobalTheory.Serre.Lie a, ∃ s ∉ p, s • l ∈ Submodule.span R (Set.range w) := by
  intro R O _ _ G _ _ hsm a p _ n w hw l
  haveI := hsm
  let Gp := (Over.pullback (spMap (algebraMap R (Localization.AtPrime p)))).obj G
  letI : GrpObj Gp := Functor.grpObjObj
  haveI : IsCommMonObj Gp := Functor.isCommMonObj_obj
  have hp := isGrpPullback_pullback G (spMap (algebraMap R (Localization.AtPrime p)))
  obtain ⟨ap, hap⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback a hp
  obtain ⟨ρ, hρ, -⟩ := exists_res hp a ap hap
  have hb := hw Gp _ hp (fun i => (ρ (w i)).hom) (fun i => hρ (w i))
  have hbij := (Lie.isLieBasis_iff (a := ap) fun i => ρ (w i)).1 hb
  obtain ⟨c, hc⟩ := hbij.2 (ρ l)
  rw [Fintype.linearCombination_apply] at hc
  obtain ⟨⟨q, hq⟩, hqi⟩ := IsLocalization.exist_integer_multiples p.primeCompl (Finset.univ : Finset (Fin n)) c
  choose b hb' using fun i => hqi i (Finset.mem_univ _)
  have hz : ρ (q • l - ∑ i, b i • w i) = 0 := by
    rw [map_sub, map_smulₛₗ, ← hc, map_sum, Finset.smul_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smulₛₗ, hb', smul_smul, Algebra.smul_def]
  obtain ⟨r, hr, e⟩ := exists_smul_eq_zero a p (q • l - ∑ i, b i • w i) (by
    have e := hρ (q • l - ∑ i, b i • w i)
    have e₀ := hρ 0
    rw [map_zero, Lie.hom_zero, Lie.hom_zero] at e₀
    rw [hz, Lie.hom_zero] at e
    exact e.symm.trans e₀)
  refine ⟨r * q, p.primeCompl.mul_mem hr hq, ?_⟩
  rw [mul_smul, sub_eq_zero.1 ((smul_sub _ _ _).symm.trans e)]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

end GlobalTheory.LieSpanLoc
