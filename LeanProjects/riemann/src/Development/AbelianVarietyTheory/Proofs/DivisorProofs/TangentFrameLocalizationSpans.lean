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

open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem isLieBasis_of_local_restrict : ∀ {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G], Smooth G.hom →
    ∀ (p : Ideal R) [p.IsPrime] {n : ℕ} (w : Fin n → (epsR R ⟶ G)),
    (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) →
    ∀ (T : Type) [CommRing T] [IsLocalRing T] (g : R →+* T), (IsLocalRing.maximalIdeal T).comap g = p →
    ∀ (G' : Over (Sp T)) [GrpObj G'] (ψ : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) ψ →
    ∀ v : Fin n → (epsR T ⟶ G'), (∀ i, GlobalTheory.IsVecOver g ψ (w i) (v i)) → IsLieBasis v := by
  intro R _ G _ hsm p _ n w hw T _ _ g hg G' _ ψ h v hv
  haveI : Smooth G.hom := hsm
  let φp : Localization.AtPrime p →+* T := IsLocalization.lift (M := p.primeCompl) (g := g)
    (fun x => not_not.1 fun h0 => x.2 (hg ▸ (show x.1 ∈ (IsLocalRing.maximalIdeal T).comap g from h0)))
  have hφ : φp.comp (algebraMap R (Localization.AtPrime p)) = g := IsLocalization.lift_comp _
  have hsp : spMap g = spMap φp ≫ Chart.fB R (Localization.AtPrime p) := by
    show Spec.map (CommRingCat.ofHom g) = Spec.map (CommRingCat.ofHom φp) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have h' : IsGrpPullback G' G (spMap φp ≫ Chart.fB R (Localization.AtPrime p)) ψ := hsp ▸ h
  have hG := Chart.isGrpPullback_factor (Chart.fB R (Localization.AtPrime p)) (spMap φp) h'
  have : Smooth (Chart.Gp (G := G) p).hom := show Smooth (pullback.snd G.hom _) from inferInstance
  have hb : IsLieBasis (G := Chart.Gp (G := G) p) (fun i => Chart.resP p (w i)) := by
    refine hw (Chart.Gp (G := G) p) (pullback.fst G.hom (Chart.fB R (Localization.AtPrime p)))
      (isGrpPullback_pullback G (Chart.fB R (Localization.AtPrime p))) _ fun i => ?_
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w i))
    simp only [Chart.pushR_left, Over.comp_left] at e
    exact e
  refine Chart.isLieBasis_baseChange φp hG hb fun j => ?_
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hv j, Category.assoc]
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w j))
    simp only [Chart.pushR_left, Over.comp_left] at e
    rw [e, ← Category.assoc]
    congr 1
    show Spec.map (CommRingCat.ofHom (Chart.dualMapR g)) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Chart.dualMapR_comp, hφ]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (v j), Category.assoc]
    rw [show (Chart.resP p (w j)).left ≫ pullback.snd G.hom (Chart.fB R (Localization.AtPrime p)) =
      (Chart.sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p))).hom from Over.w (Chart.resP p (w j))]
    show Spec.map (CommRingCat.ofHom (algebraMap T (DualNumber T))) ≫ Spec.map (CommRingCat.ofHom φp) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_ <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl']

end GlobalTheory
