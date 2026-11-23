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

noncomputable section

namespace GlobalTheory.LieFrameLoc

theorem scaleD_scaleD {R : Type} [CommRing R] {G : Over (Sp R)} (a b : R)
    (y : Chart.sp (R₀ := R) (DualNumber R) ⟶ G) :
    Chart.spMap (Chart.scaleD a) ≫ Chart.spMap (Chart.scaleD b) ≫ y = Chart.spMap (Chart.scaleD (a * b)) ≫ y := by
  rw [← Category.assoc, Chart.spMap_comp]
  congr 2
  refine AlgHom.ext fun x => TrivSqZeroExt.ext ?_ ?_
  · simp [Chart.scaleD]
  · simp only [Chart.scaleD, AlgHom.comp_apply, TrivSqZeroExt.snd_map, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul]
    ring

theorem isLieBasis_scale {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {n : ℕ} {u : Fin n → (epsR R ⟶ G)}
    (hu : IsLieBasis u) (a : Fin n → Rˣ)
    (ht : ∀ i, IsTangent (Chart.spMap (Chart.scaleD (a i : R)) ≫ u i : epsR R ⟶ G)) :
    IsLieBasis (fun i => (Chart.spMap (Chart.scaleD (a i : R)) ≫ u i : epsR R ⟶ G)) := by
  have key : ∀ c : Fin n → R, Chart.prodPts c (fun i => Chart.spMap (Chart.scaleD (a i : R)) ≫ u i) =
      Chart.prodPts (fun i => c i * a i) u := fun c => by
    unfold Chart.prodPts
    exact congrArg List.prod (congrArg List.ofFn (funext fun i => scaleD_scaleD _ _ _))
  refine ⟨ht, fun w hw => ?_⟩
  obtain ⟨c, hc, huniq⟩ := hu.2 w hw
  refine ⟨fun i => c i * ↑(a i)⁻¹, ?_, fun c' hc' => ?_⟩
  · rw [Chart.isLieComb_iff] at hc ⊢
    rw [key, hc]
    congr 1
    funext i
    simp [mul_assoc]
  · replace hc' := (Chart.isLieComb_iff _ _ _).mp hc'
    rw [key] at hc'
    have := huniq _ ((Chart.isLieComb_iff _ _ _).mpr hc')
    funext i
    have hi := congrFun this i
    rw [← hi]
    simp [mul_assoc]

end GlobalTheory.LieFrameLoc

open GlobalTheory.LieFrameLoc in
open scoped CategoryTheory.Obj in

theorem GlobalTheory.exists_tangent_isLieBasis_atPrime : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G], Smooth G.hom → ∀ (p : Ideal R) [p.IsPrime],
    ∃ (n : ℕ) (w : Fin n → (epsR R ⟶ G)), (∀ i, IsTangent (w i)) ∧
      (∀ (G' : Over (Sp (Localization.AtPrime p))) [GrpObj G'] (ψ : G'.left ⟶ G.left),
        IsGrpPullback G' G (spMap (algebraMap R (Localization.AtPrime p))) ψ →
        ∀ v : Fin n → (epsR (Localization.AtPrime p) ⟶ G'),
          (∀ i, GlobalTheory.IsVecOver (algebraMap R (Localization.AtPrime p)) ψ (w i) (v i)) → IsLieBasis v) := by
  intro R _ G _ hsm p _
  haveI := hsm
  have : ∀ s : R, Smooth (Chart.Gs G s).hom := fun s => show Smooth (pullback.snd G.hom _) from inferInstance
  have hGp : Smooth (Chart.Gp (G := G) p).hom := show Smooth (pullback.snd G.hom _) from inferInstance
  obtain ⟨n, u, hu⟩ := Chart.exists_isLieBasis (Chart.Gp (G := G) p) hGp
  have lift : ∀ i, ∃ q ∈ p.primeCompl, ∃ w : epsR R ⟶ G, IsTangent w ∧
      Chart.resP p w = Chart.spMap (Chart.scaleD (algebraMap R (Localization.AtPrime p) q)) ≫ u i := by
    intro i
    have hT : Chart.TanS (Chart.pushR G (u i)) := (Chart.isTan_iff_tanS p (u i)).mp ((Chart.isTan_iff _).mpr (hu.1 i))
    obtain ⟨q, hq, w, hw, he⟩ := Chart.tan_prime_lift p hT
    refine ⟨q, hq, w, (Chart.isTan_iff _).mp hw, Chart.pushR_inj G ?_⟩
    rw [Chart.pushR_resP, he, Chart.pushR_spMap]
    congr 2
  choose q hq w hw hres using lift
  refine ⟨n, w, hw, fun G' _ ψ hψ v hv => ?_⟩
  let a : Fin n → (Localization.AtPrime p)ˣ := fun i => (IsLocalization.map_units _ ⟨q i, hq i⟩).unit
  have hres' : ∀ i, Chart.resP p (w i) = Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i := hres
  have htan : ∀ i, IsTangent (Chart.resP p (w i)) := fun i =>
    (Chart.isTan_iff _).mp ((Chart.isTan_iff_tanS p _).mpr (by
      rw [Chart.pushR_resP]; exact Chart.tanS_restrict _ ((Chart.isTan_iff _).mpr (hw i))))
  have hbasis : IsLieBasis (G := Chart.Gp (G := G) p) (fun i => Chart.resP p (w i)) := by
    have e : (fun i => Chart.resP p (w i)) = fun i => Chart.spMap (Chart.scaleD (a i : Localization.AtPrime p)) ≫ u i :=
      funext hres'
    rw [e]
    exact isLieBasis_scale hu a fun i => hres' i ▸ htan i
  let φp : Localization.AtPrime p →+* Localization.AtPrime p := RingHom.id _
  have hφ : φp.comp (algebraMap R (Localization.AtPrime p)) = algebraMap R (Localization.AtPrime p) := RingHom.id_comp _
  have hsp : spMap (algebraMap R (Localization.AtPrime p)) = spMap φp ≫ Chart.fB R (Localization.AtPrime p) := by
    show Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p))) = Spec.map (CommRingCat.ofHom φp) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.AtPrime p)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]
  have h' : IsGrpPullback G' G (spMap φp ≫ Chart.fB R (Localization.AtPrime p)) ψ := hsp ▸ hψ
  have hG := Chart.isGrpPullback_factor (Chart.fB R (Localization.AtPrime p)) (spMap φp) h'
  have hv' : ∀ j, (v j).left ≫ ψ = spMap (Chart.dualMapR (algebraMap R (Localization.AtPrime p))) ≫ (w j).left := hv
  refine Chart.isLieBasis_baseChange φp hG hbasis fun j => ?_
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, hv' j, Category.assoc]
    have e := congrArg (fun q => Over.Hom.left q) (Chart.pushR_resP (G := G) p (w j))
    simp only [Chart.pushR_left, Over.comp_left] at e
    rw [e, ← Category.assoc]
    congr 1
    show Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p)))) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (Chart.dualMapR (algebraMap R (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Chart.dualMapR_comp, hφ]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (v j), Category.assoc]
    rw [show (Chart.resP p (w j)).left ≫ pullback.snd G.hom (Chart.fB R (Localization.AtPrime p)) =
      (Chart.sp (R₀ := Localization.AtPrime p) (DualNumber (Localization.AtPrime p))).hom from Over.w (Chart.resP p (w j))]
    show Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p)))) ≫
        Spec.map (CommRingCat.ofHom φp) =
      Spec.map (CommRingCat.ofHom (Chart.dualMapR φp)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime p) (DualNumber (Localization.AtPrime p))))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_ <;> simp [φp, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl']
