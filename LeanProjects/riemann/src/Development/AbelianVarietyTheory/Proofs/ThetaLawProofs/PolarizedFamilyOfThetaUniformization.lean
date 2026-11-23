import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAlgHomOfFiniteTypeOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenLeOfIsQProjOver
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.StalkOfAppLEEq
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SqOfCalculus
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPointOfPerLev
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPerLev
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsTwoTorsionTranslateSameLambdaBundleStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundleStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LiftIdempotentEqOfSameComplexComponentStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.GeomIntegralOfEtaleFaithfullyFlatCoverStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SiegelFamilyStandardLevelPointsSameComponentStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSiegelFamilyOverNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNumberFieldPointSiegelFamilyKnownValueStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTwStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.PolFamPf
open GlobalTheory.ZM.SiegPull GlobalTheory.CoordToExt

theorem exists_polPB (hB : Out.PolBaseChangeSt) {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), PolPB P' P f φ := by
  obtain ⟨P', φ, hφ, hg, hm, t, ht⟩ := hB S S' f P
  refine ⟨P', φ, ⟨hφ, fun T x y x₀ y₀ hx hy => ?_⟩, hg, LBIso.symm ⟨t, ht⟩⟩
  rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hφ.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hφ.w y), ← hm]
  rfl

theorem polPB_cancel {S S' S'' : Scheme.{0}} {P : Out.PolAV S} {P' : Out.PolAV S'} {P'' : Out.PolAV S''}
    {f : S' ⟶ S} {g : S'' ⟶ S'} {φ : P'.A.left ⟶ P.A.left} {χ : P''.A.left ⟶ P.A.left}
    (h : PolPB P' P f φ) (n : PolPB P'' P (g ≫ f) χ) : ∃ ψ, PolPB P'' P' g ψ := by
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ g) ≫ f := n.1.1.w.trans (Category.assoc _ _ _).symm
  have e : h.1.1.lift χ _ w ≫ φ = χ := h.1.1.lift_fst _ _ _
  refine ⟨h.1.1.lift χ _ w, h.1.cancel (n.1.congr rfl e.symm) (h.1.1.lift_snd _ _ _), n.2.1.trans h.2.1.symm, ?_⟩
  have k := GlobalTheory.ZM.SiegPull.lbIso_pull_comp h.2.2 (h.1.1.lift χ _ w)
  rw [e] at k
  exact LBIso.trans P''.isLB (pull_isLB P.isLB _) (pull_isLB P'.isLB _) n.2.2 k.symm

theorem lbIso_drop {k : Type} [Field k] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ Sp k) (a : Sp k ⟶ X)
    (u : Y ⟶ X) (φ : Fin 2 → (Y ⟶ X)) (h₀ : φ 0 = u) (h₁ : φ 1 = p ≫ a) :
    LBIso (LB.LinComb L φ ![1, -1]) (L.pull u) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := k) L hL (K := PUnit) (fun _ => a) (fun _ => 1)
  refine ((refines_self _ _).div (refines_self φ _)).exists_gen hL (fun U _ f => ?_) _
    (DVR.pullGen_isGen _ _ _ e he p)
  refine Eq.symm ((Fintype.prod_sum_type _).trans ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Fintype.prod_unique, h₀, h₁]
  simp

theorem exists_translate (hL : Out.Laws) {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S : Scheme.{0}} {s : S ⟶ Sp o}
    (c : SiegPre h k ζ s) {R : Type} [CommRing R] (f : Sp R ⟶ S) (Q : Out.PolAV (Sp R)) (φ : Q.A.left ⟶ c.A.left)
    (hQ : SqOf Q c f φ) (hT : TorsConst Q.A 2) (x : Sp ℂ ⟶ Sp R) (P : Out.PolAV (Sp ℂ)) (χ : P.A.left ⟶ c.A.left)
    (hP : SqOf P c (x ≫ f) χ) :
    ∃ (Q' : Out.PolAV (Sp R)) (φ' : Q'.A.left ⟶ c.A.left) (ψ : P.A.left ⟶ Q'.A.left),
      SqOf Q' c f φ' ∧ PolPB P Q' x ψ := by
  obtain ⟨P₁, π, hπ⟩ := exists_polPB hL.polBaseChange x Q
  have h₁ := (sqOf_calculus h k o ζ S (Sp R) (Sp ℂ) s c f).1 x Q P₁ φ π hQ hπ
  obtain ⟨e, he, -, hl⟩ := (sqOf_calculus h k o ζ S (Sp ℂ) (Sp ℂ) s c (x ≫ f)).2.1 P₁ P _ _ h₁ hP
  obtain ⟨t₁, ht₁, hi⟩ := GlobalTheory.T.exists_twoTorsion_translate_same_lambdaBundle hL ℂ P₁ P e he hl
  obtain ⟨t, ht, hy⟩ := hT ℂ _ (pushHom hπ.1 _ t₁) (by rw [← map_pow, ht₁, map_one])
  obtain ⟨Q', e', he', hg', hl', hi'⟩ := GlobalTheory.T.exists_rigidTranslate_principalPolarisation_order_two hL R Q t ht
  have hy' : t₁.left ≫ π = x ≫ t.left := by
    refine (congrArg (fun q => q.left) hy).trans ?_
    refine congrArg (· ≫ t.left) ?_
    exact (Category.comp_id _).symm.trans ((Over.w (toUnit (Over.mk ((𝟙_ (Over (Sp ℂ))).hom ≫ x)))).trans
      (Category.id_comp _))
  have : IsMonHom e'.symm.hom := inferInstanceAs (IsMonHom e'.inv)
  have gp₀ : IsGrpPullback P.A Q.A x (e.hom.left ≫ π) :=
    ((isGrpPullback_of_iso e).comp hπ.1).congr (Category.id_comp _) rfl
  have gp : IsGrpPullback P.A Q'.A x ((e.hom.left ≫ π) ≫ e'.inv.left) :=
    (gp₀.comp (isGrpPullback_of_iso e'.symm)).congr (Category.comp_id _) rfl
  have ee : ((e.hom.left ≫ π) ≫ e'.inv.left) ≫ e'.hom.left = e.hom.left ≫ π := by
    rw [Category.assoc, ← Over.comp_left, e'.inv_hom_id, Over.id_left, Category.comp_id]
  refine ⟨Q', _, (e.hom.left ≫ π) ≫ e'.inv.left,
    (sqOf_calculus h k o ζ S (Sp R) (Sp R) s c f).2.2 Q Q' φ e' he' hg' hl' hQ, gp,
    hP.2.1.trans (hg'.trans hQ.2.1).symm, ?_⟩
  have k₁ := LBIso.trans P.isLB (pull_isLB P₁.isLB _) (pull_isLB Q.isLB _) hi
    (GlobalTheory.ZM.SiegPull.lbIso_pull_comp hπ.2.2 (e.hom ≫ ((toUnit P₁.A ≫ t₁) * 𝟙 P₁.A)).left)
  have k₂ := LBIso.chartPull (Geo.Tor.chartPullPull Q'.L _ ((e.hom.left ≫ π) ≫ e'.inv.left) rfl)
    (chartPullSame Q.L _ _ _ ((e.hom.left ≫ π) ≫ e'.inv.left) fun _ => rfl) hi'
  have k₃ := lbIso_drop Q.isLB P.A.hom (x ≫ t.left) ((e.hom ≫ ((toUnit P₁.A ≫ t₁) * 𝟙 P₁.A)).left ≫ π)
    (fun i => ((e.hom.left ≫ π) ≫ e'.inv.left) ≫
      (![(e'.hom ≫ ((toUnit Q.A ≫ t) * 𝟙 Q.A)).left, (toUnit Q'.A ≫ t).left] : Fin 2 → _) i) ?_ ?_
  · exact LBIso.trans P.isLB (pull_isLB Q.isLB _) (pull_isLB Q'.isLB _) k₁
      (LBIso.trans (pull_isLB Q'.isLB _) (DVR.linComb_isLB _ Q.isLB _ _) (pull_isLB Q.isLB _) k₂ k₃).symm
  · show _ ≫ (e'.hom.left ≫ ((toUnit Q.A ≫ t) * 𝟙 Q.A).left) = (e.hom.left ≫ _) ≫ π
    rw [← Category.assoc, ee, Category.assoc, Category.assoc]
    refine congrArg (e.hom.left ≫ ·) ?_
    let ρ : Over.mk (P₁.A.hom ≫ x) ⟶ Q.A := Over.homMk π hπ.1.1.w
    refine Eq.trans ?_ (hπ.1.2 P₁.A (toUnit P₁.A ≫ t₁) (𝟙 _) (ρ ≫ toUnit _ ≫ t) (ρ ≫ 𝟙 _) ?_
      ((Category.comp_id _).trans (Category.id_comp _).symm))
    · exact congrArg (fun f => f.left) (MonObj.comp_mul ρ (toUnit _ ≫ t) (𝟙 _))
    · show π ≫ Q.A.hom ≫ t.left = (P₁.A.hom ≫ t₁.left) ≫ π
      rw [Category.assoc, hy', ← Category.assoc, hπ.1.1.w, Category.assoc]
  · show _ ≫ Q'.A.hom ≫ t.left = P.A.hom ≫ x ≫ t.left
    rw [← Category.assoc, gp.1.w, Category.assoc]

theorem exists_lift_point {R R₁ : Type} [CommRing R] [CommRing R₁] [Algebra R R₁] [Module.Finite R R₁]
    [Module.FaithfullyFlat R R₁] (p : R →+* ℂ) : ∃ p₁ : R₁ →+* ℂ, p₁.comp (algebraMap R R₁) = p := by
  letI := p.toAlgebra
  haveI : Nontrivial (ℂ ⊗[R] R₁) := Module.FaithfullyFlat.rTensor_nontrivial R R₁ ℂ
  obtain ⟨a⟩ := exists_algHom_of_finiteType_of_isAlgClosed ℂ (ℂ ⊗[R] R₁) ℂ
  refine ⟨a.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom, RingHom.ext fun r => ?_⟩
  show a (Algebra.TensorProduct.includeRight (algebraMap R R₁ r)) = p r
  rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R ℂ (ℂ ⊗[R] R₁), AlgHom.commutes]
  rfl

theorem exists_affine {K : Type} [CommRing K] {X : Scheme.{0}} (s : X ⟶ Sp K) (hs : IsQProjOver s)
    {K₁ K₂ : Type} [Field K₁] [Field K₂] (p : Sp K₁ ⟶ X) (q : Sp K₂ ⟶ X) :
    ∃ (R : Type) (_ : CommRing R) (i : Sp R ⟶ X) (a : K →+* R) (p' : R →+* K₁) (q' : R →+* K₂),
      IsOpenImmersion i ∧ i ≫ s = spMap a ∧ spMap p' ≫ i = p ∧ spMap q' ≫ i = q := by
  obtain ⟨V, hV, hF, -⟩ := exists_isAffineOpen_le_of_isQProjOver K X s hs (Set.range p ∪ Set.range q) ⊤
    ((Set.finite_range _).union (Set.finite_range _)) (fun _ _ => trivial)
  have hr : Set.range hV.fromSpec = V := hV.range_fromSpec
  refine ⟨Γ(X, V), inferInstance, hV.fromSpec, (Spec.preimage (hV.fromSpec ≫ s)).hom,
    (Spec.preimage (IsOpenImmersion.lift hV.fromSpec p (hr ▸ Set.subset_union_left.trans hF))).hom,
    (Spec.preimage (IsOpenImmersion.lift hV.fromSpec q (hr ▸ Set.subset_union_right.trans hF))).hom,
    inferInstance, (Spec.map_preimage _).symm, ?_, ?_⟩
  · exact (congrArg (· ≫ hV.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)
  · exact (congrArg (· ≫ hV.fromSpec) (Spec.map_preimage _)).trans (IsOpenImmersion.lift_fac _ _ _)

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end GlobalTheory.KeyFam.PolFamPf

open GlobalTheory.KeyFam.PolFamPf in

theorem GlobalTheory.KeyFam.polFam : Out.Laws → Out.Laws2 → ThetaUnifAV → GlobalTheory.TorusAlgebraic → PolFam := by
  intro hL hL2 hU hA P hg
  obtain ⟨k, K, _, _, ζ, σ, hk, ho, hζ, ⟨F⟩⟩ := GlobalTheory.T.exists_siegelFamily_over_numberField hL hL2 hU P.g hg
  obtain ⟨τ, lev, hper⟩ := exists_perLev hU P P.g k rfl
  obtain ⟨p, χ, hp, hP, hlev⟩ := exists_point_of_perLev hL P.g k K ζ σ F hg hk ho hζ P τ lev hper
  obtain ⟨K₁, _, _, j₁, σ₁, y, q, χy, τ', hσ, hq, hy, hyq, hpt⟩ :=
    GlobalTheory.T.exists_numberField_point_siegelFamily_knownValue hL hU P.g k K ζ σ F hg hk ho hζ inferInstance
  have hq' : (spMap σ₁ ≫ q) ≫ F.s = spMap σ := by rw [Category.assoc, hq, ← spMap_comp, hσ]
  have hc := GlobalTheory.T.siegelFamily_standard_level_points_same_component hL hL2 hU hA P.g k K ζ σ F hg hk ho hζ τ τ' p _ hp hq' ⟨P, lev, χ, hper, hP, hlev⟩ hpt
  obtain ⟨R, _, i, a, p', q', hi, ha, rfl, rfl⟩ := exists_affine F.s F.qproj p q
  letI := σ.toAlgebra
  letI := j₁.toAlgebra
  letI := a.toAlgebra
  have hp' : p'.comp a = σ := spMap_inj (by rw [spMap_comp, ← ha, ← hp, Category.assoc])
  have hq'' : q'.comp a = j₁ := spMap_inj (by rw [spMap_comp, ← ha, ← hq, Category.assoc])
  let pA : R →ₐ[K] ℂ := { p' with commutes' := fun r => DFunLike.congr_fun hp' r }
  let qA : R →ₐ[K] K₁ := { q' with commutes' := fun r => DFunLike.congr_fun hq'' r }
  let σA : K₁ →ₐ[K] ℂ := { σ₁ with commutes' := fun r => DFunLike.congr_fun hσ r }
  have hsm : Smooth F.s := by
    have := F.smooth
    exact SmoothOfRelativeDimension.smooth (P.g * (P.g + 1) / 2) F.s
  have hid := GlobalTheory.T.lift_idempotent_eq_of_sameComplexComponent K F.X F.s R i pA (σA.comp qA) hsm hi ha (by
    have e : spMap (σA.comp qA).toRingHom ≫ i = spMap σ₁ ≫ spMap q' ≫ i := by
      rw [← Category.assoc, ← spMap_comp]; rfl
    rw [e]; exact hc)
  haveI : Algebra.Smooth K R := by
    have : Smooth (spMap a) := ha ▸ inferInstance
    exact RingHom.smooth_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Smooth)).1 this)
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  letI : Algebra ℚ R := (a.comp (algebraMap ℚ K)).toAlgebra
  have hu : IsUnit ζ := by
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, map_zero] at hζ
    exact Complex.exp_ne_zero _ hζ.symm
  obtain ⟨R₁, _, _, Q, φ, ⟨c₁, c₂, c₃⟩, hQ, hT⟩ := GlobalTheory.T.exists_symmetric_sqrt_principal_siegel_finite_etale hL P.g k K ζ R F.X F.s F.univ i (by omega) hu F.princ
  obtain ⟨p₁, hp₁⟩ := exists_lift_point (R₁ := R₁) p'
  obtain ⟨Q', φ', ψ, hQ', hψ⟩ := exists_translate hL F.univ _ Q φ hQ hT (spMap p₁) P χ (by
    rw [← Category.assoc, ← spMap_comp, hp₁]; exact hP)
  letI : Algebra K R₁ := ((algebraMap R R₁).comp a).toAlgebra
  haveI : IsScalarTower K R R₁ := IsScalarTower.of_algebraMap_eq' rfl
  let p₁A : R₁ →ₐ[K] ℂ :=
    { p₁ with commutes' := fun r => (DFunLike.congr_fun hp₁ (a r)).trans (DFunLike.congr_fun hp' r) }
  have hpp : p₁A.comp (IsScalarTower.toAlgHom K R R₁) = pA := AlgHom.ext fun r => DFunLike.congr_fun hp₁ r
  obtain ⟨k', _, _, S, _, _, j, s, s₀, ii, hS, hs, hs₀⟩ :=
    GlobalTheory.T.geom_integral_of_etale_faithfully_flat_cover K R R₁ K₁ σA p₁A qA ⟨c₁, c₂, c₃⟩ (by rw [hpp]; exact hid)
  obtain ⟨Q'', π, hπ⟩ := exists_polPB hL.polBaseChange (spMap j) Q'
  obtain ⟨ψ', hψ'⟩ := polPB_cancel (g := spMap s) hπ (by
    rw [← spMap_comp, hs]; exact hψ)
  refine ⟨k', inferInstance, inferInstance, S, inferInstance, inferInstance, Q'', s, s₀, ψ', hS, hψ',
    fun P₀ φ₀ h₀ => ?_⟩
  have a₁ := (sqOf_calculus _ k K ζ F.X _ _ F.s F.univ _).1 _ _ _ _ _
    ((sqOf_calculus _ k K ζ F.X _ _ F.s F.univ _).1 _ _ _ _ _ hQ' hπ) h₀
  obtain ⟨y', hy'⟩ := keyIn_baseChange hL.polBaseChange K₁ k' y ii
  have hk' : Known k' y' := by
    obtain ⟨t₀, ht₀⟩ := hy
    exact ⟨ii t₀, fun e x hx => ht₀ (e.comp ii) x (keyPB_trans _ _ _ y y' x ii e hy' hx)⟩
  obtain ⟨β, -, w, hβg, -, hβ, hw, -⟩ := hy'
  have a₂ := (sqOf_calculus _ k K ζ F.X _ _ F.s F.univ _).1 _ _ _ _ _ hyq (⟨hβ, hβg, w, hw⟩ : PolPB y'.P y.P _ β)
  have e : spMap s₀.toRingHom ≫ spMap j ≫ spMap (algebraMap R R₁) ≫ i = spMap ii ≫ spMap q' ≫ i := by
    rw [← Category.assoc, ← Category.assoc, ← Category.assoc, ← spMap_comp, ← spMap_comp, ← spMap_comp, hs₀,
      spMap_comp, Category.assoc]
  rw [e] at a₁
  obtain ⟨ε, hε, -, hl⟩ := (sqOf_calculus _ k K ζ F.X _ (Sp k') F.s F.univ _).2.1 _ _ _ _ a₂ a₁
  exact GlobalTheory.T.potentiallyKnown_of_same_lambdaBundle hL hU k' y' P₀ ε hε hl hk'
