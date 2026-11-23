import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmConnModelDescends
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayDescentRangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationAwayPolynomialSubringLiftInjectiveStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SpreadCurve

open Polynomial

theorem group_sections_curve_descend : ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, 1 ≤ m → (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → ∀ (P : Polynomial k), P ≠ 0 → ∀ (u : Sp (Localization.Away P) ⟶ G.left) (a b : Localization.Away P →ₐ[k] k), u ≫ G.hom = spMap (algebraMap k (Localization.Away P)) → spMap a.toRingHom ≫ u ≠ spMap b.toRingHom ≫ u → ∃ (R : Subring k) (G₁ : Over (Sp R)) (_ : GrpObj G₁), Algebra.FiniteType ℤ R ∧ IsUnit (m : R) ∧ IsCommMonObj G₁ ∧ Smooth G₁.hom ∧ IsSeparated G₁.hom ∧ QuasiCompact G₁.hom ∧ GeometricallyConnected (pullback.snd G₁.hom (spMap R.subtype)) ∧ SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R.subtype)) ∧ (∃ s₁ : Finset (𝟙_ (Over (Sp R)) ⟶ G₁), s₁.card = s.card ∧ (∀ x ∈ s₁, x ^ m = 1) ∧ ∀ x ∈ s₁, ∀ y ∈ s₁, x ≠ y → spMap R.subtype ≫ x.left ≠ spMap R.subtype ≫ y.left) ∧ ∃ (P₁ : Polynomial R) (_ : P₁ ≠ 0) (u₁ : Sp (Localization.Away P₁) ⟶ G₁.left) (α β : R) (hα : IsUnit (Polynomial.evalRingHom α P₁)) (hβ : IsUnit (Polynomial.evalRingHom β P₁)), u₁ ≫ G₁.hom = spMap (algebraMap R (Localization.Away P₁)) ∧ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠ spMap R.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
  intro k _ G _ hG g hg m hm hmk s hs P hP u a b hu hab
  classical
  obtain ⟨hc, h1, h2, h3, h5⟩ := hG
  obtain ⟨R₀, G₀, i₀, ic₀, φ, -, hR₀, s₁, s₂, s₃, hφ⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring k G ∅ h1 h2 h3

  haveI := s₁; haveI := s₂; haveI := s₃
  set L := Localization.Away P with hL

  have hu₀ : (u ≫ φ) ≫ G₀.hom = spMap (algebraMap R₀ L) := by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, hu]
    exact ModelDescent.spMap_comp_eq (RingHom.ext fun r => (IsScalarTower.algebraMap_apply R₀ k L r).symm)
  obtain ⟨S, yS, hSfg, -, hyS⟩ := Spread.exists_fg_points G₀.hom (fun _ : Unit => u ≫ φ) (fun _ => hu₀) ⊥
    Subalgebra.fg_bot
  obtain ⟨T, hT⟩ := hSfg
  obtain ⟨Fc, hFc⟩ := GlobalTheory.T.exists_finset_away_lift_descent k P T

  set X' : L := algebraMap (Polynomial k) L X with hX'
  have haev : ∀ (c : L →ₐ[k] k) (q : Polynomial k), c (algebraMap (Polynomial k) L q) = q.eval (c X') := by
    intro c q
    have : (c : L →+* k).comp (algebraMap (Polynomial k) L) = Polynomial.evalRingHom (c X') := by
      refine Polynomial.ringHom_ext (fun r => ?_) ?_
      · simp only [RingHom.coe_comp, Function.comp_apply, coe_evalRingHom, eval_C]
        have e : algebraMap (Polynomial k) L (C r) = algebraMap k L r := by
          rw [IsScalarTower.algebraMap_apply k (Polynomial k) L, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
        rw [e]
        exact c.commutes r
      · simp [hX']
    exact congrArg (fun f : Polynomial k →+* k => f q) this
  have hne : ∀ c : L →ₐ[k] k, P.eval (c X') ≠ 0 := by
    intro c
    rw [← haev]
    exact ((IsLocalization.Away.algebraMap_isUnit P).map c).ne_zero

  let F : Finset k := Fc ∪ P.coeffs ∪ {(m : k)⁻¹, a X', b X', (P.eval (a X'))⁻¹, (P.eval (b X'))⁻¹}

  have hx₀ : ∀ i : s, (i.1.left ≫ φ) ≫ G₀.hom = spMap (algebraMap R₀ k) := by
    intro i
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w i.1]
    exact Category.id_comp _
  obtain ⟨R, y, hRfg, hR₁R, hy⟩ := Spread.exists_fg_points G₀.hom (fun i : s => i.1.left ≫ φ) hx₀
    (Algebra.adjoin R₀ (F : Set k)) (Subalgebra.fg_adjoin_finset F)
  let R' : Subring k := R.toSubring
  have hFR : (F : Set k) ⊆ R' := fun x hx => hR₁R (Algebra.subset_adjoin hx)
  have hR₀R : R₀ ≤ R' := fun r hr => R.algebraMap_mem ⟨r, hr⟩
  let jn : R₀ →+* R' := Subring.inclusion hR₀R
  have hjn : R'.subtype.comp jn = R₀.subtype := rfl
  have hjnsp : spMap R'.subtype ≫ spMap jn = spMap R₀.subtype := ModelDescent.spMap_comp_eq hjn
  let G₁ : Over (Sp R') := (Over.pullback (spMap jn)).obj G₀
  letI : GrpObj G₁ := Functor.grpObjObj
  have hG₁c : IsCommMonObj G₁ := Functor.isCommMonObj_obj
  have hψ := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor (spMap jn) (spMap R'.subtype)
    (hφ.congr hjnsp.symm rfl)
  set ψ := pullback.lift φ (G.hom ≫ spMap R'.subtype) (by rw [hφ.1.w, Category.assoc, hjnsp]) with hψdef
  have hψ₁ : ψ ≫ pullback.fst G₀.hom (spMap jn) = φ := pullback.lift_fst _ _ _
  have hψ₂ : ψ ≫ pullback.snd G₀.hom (spMap jn) = G.hom ≫ spMap R'.subtype := pullback.lift_snd _ _ _
  have hyR : ∀ i : s, (y i : Sp R' ⟶ G₀.left) ≫ G₀.hom = spMap jn := fun i => (hy i).1
  have hyk : ∀ i : s, spMap R'.subtype ≫ (y i : Sp R' ⟶ G₀.left) = i.1.left ≫ φ := fun i => (hy i).2

  have hsq : IsPullback hψ.1.isoPullback.inv (pullback.snd G₁.hom (spMap R'.subtype)) G.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, IsPullback.isoPullback_inv_snd]⟩
  have hgc : GeometricallyConnected (pullback.snd G₁.hom (spMap R'.subtype)) :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hsq h5
  have hgd : SmoothOfRelativeDimension g (pullback.snd G₁.hom (spMap R'.subtype)) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hsq hg
  have hunit : IsUnit (m : R') := by
    refine IsUnit.of_mul_eq_one (a := (m : R')) ⟨(m : k)⁻¹, hFR (by simp [F])⟩ (Subtype.ext ?_)
    simp [mul_inv_cancel₀ hmk]

  let sec : s → (𝟙_ (Over (Sp R')) ⟶ G₁) := fun i =>
    Over.homMk (pullback.lift (y i : Sp R' ⟶ G₀.left) (𝟙 _) (by rw [hyR i, Category.id_comp]))
      (pullback.lift_snd _ _ _)
  have hsec₁ : ∀ i : s, (sec i).left ≫ pullback.fst G₀.hom (spMap jn) = y i := fun i => pullback.lift_fst _ _ _
  have hkey : ∀ i : s, i.1.left ≫ ψ = spMap R'.subtype ≫ (sec i).left := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, hψ₁, Category.assoc, hsec₁, hyk]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w i.1, Category.assoc]
      erw [pullback.lift_snd]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  have hdist : ∀ i j : s, spMap R'.subtype ≫ (sec i).left = spMap R'.subtype ≫ (sec j).left → i = j := by
    intro i j e
    have e' : i.1.left ≫ φ = j.1.left ≫ φ := by
      rw [← hψ₁, ← Category.assoc, ← Category.assoc, hkey, hkey, e]
    refine Subtype.ext (Over.OverMorphism.ext (hφ.1.hom_ext e' ?_))
    rw [Over.w i.1, Over.w j.1]
  have hsec_inj : Function.Injective sec := fun i j e => hdist i j (by rw [e])
  haveI hsep₁ : IsSeparated G₁.hom := show IsSeparated (pullback.snd _ _) from inferInstance
  have hpow : ∀ i : s, sec i ^ m = 1 := by
    intro i
    have A := GlobalTheory.FrameMove.pow_comm hψ (hkey i) m
    have B := GlobalTheory.FrameMove.pow_comm hψ (hkey i) 0
    rw [hs i.1 i.2] at A
    rw [pow_zero, pow_zero] at B
    refine Over.OverMorphism.ext (Spread.point_ext R'.subtype Subtype.val_injective G₁.hom ?_ (A.symm.trans B))
    rw [Over.w, Over.w]

  have hPl : P ∈ Polynomial.lifts R'.subtype := by
    refine (Polynomial.lifts_iff_coeff_lifts P).2 fun n => ?_
    by_cases hn : P.coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    · exact ⟨⟨P.coeff n, hFR (by simp [F, Polynomial.coeff_mem_coeffs hn])⟩, rfl⟩
  obtain ⟨P₁, hP₁⟩ := Polynomial.mem_lifts P |>.1 hPl
  have hP₁0 : P₁ ≠ 0 := by
    rintro rfl
    exact hP (by rw [← hP₁, Polynomial.map_zero])
  have hPu : IsUnit (((algebraMap (Polynomial k) L).comp (Polynomial.mapRingHom R'.subtype)) P₁) := by
    rw [RingHom.comp_apply, Polynomial.coe_mapRingHom, hP₁]
    exact IsLocalization.Away.algebraMap_isUnit P
  set Lm := IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hPu with hLm
  have hinj : Function.Injective Lm := GlobalTheory.T.localizationAway_polynomial_subring_lift_injective k P hP R' P₁ hPu hP₁
  have hrange : ∀ t ∈ T, t ∈ Lm.range := hFc R' (fun x hx => hFR (by simp [F, hx])) P₁ hPu hP₁
  have hLmC : ∀ r : R', Lm (algebraMap R' (Localization.Away P₁) r) = algebraMap k L r := by
    intro r
    rw [IsScalarTower.algebraMap_apply R' (Polynomial R') (Localization.Away P₁), hLm,
      IsLocalization.Away.lift_eq]
    simp [Polynomial.algebraMap_apply, IsScalarTower.algebraMap_apply k (Polynomial k) L]

  have hcl : Subring.closure (Set.range (algebraMap R₀ L) ∪ (T : Set L)) ≤ Lm.range := by
    rw [Subring.closure_le]
    rintro z (⟨r, rfl⟩ | hz)
    · refine ⟨algebraMap R' (Localization.Away P₁) (jn r), ?_⟩
      rw [hLmC]
      exact (IsScalarTower.algebraMap_apply R₀ k L r).symm
    · exact hrange z hz
  have hSr : ∀ z : S, S.val.toRingHom z ∈ Lm.range := by
    intro z
    apply hcl
    rw [← Algebra.adjoin_eq_ring_closure, hT]
    exact z.2
  obtain ⟨gS, hgS⟩ := ModelDescent.exists_factor S.val.toRingHom Lm hinj hSr
  have hcomp : gS.comp (algebraMap R₀ S) = (algebraMap R' (Localization.Away P₁)).comp jn := by
    refine RingHom.ext fun r => hinj ?_
    change Lm (gS (algebraMap R₀ S r)) = Lm (algebraMap R' _ (jn r))
    rw [← RingHom.comp_apply Lm gS, hgS, hLmC]
    change (algebraMap R₀ L r) = _
    exact IsScalarTower.algebraMap_apply R₀ k L r
  let u₁' : Sp (Localization.Away P₁) ⟶ G₀.left := spMap gS ≫ yS ()
  have hu₁' : u₁' ≫ G₀.hom = spMap (algebraMap R' (Localization.Away P₁)) ≫ spMap jn := by
    rw [Category.assoc, (hyS ()).1, ModelDescent.spMap_comp_eq hcomp]
    exact (ModelDescent.spMap_comp_eq rfl).symm
  let u₁ : Sp (Localization.Away P₁) ⟶ G₁.left :=
    pullback.lift u₁' (spMap (algebraMap R' (Localization.Away P₁))) hu₁'
  have hu₁f : u₁ ≫ pullback.fst G₀.hom (spMap jn) = u₁' := pullback.lift_fst _ _ _
  have hu₁s : u₁ ≫ G₁.hom = spMap (algebraMap R' (Localization.Away P₁)) := pullback.lift_snd _ _ _

  have hpt : ∀ c : L →ₐ[k] k, c X' ∈ R' → (P.eval (c X'))⁻¹ ∈ R' → ∃ (w0 : R')
      (hw0 : IsUnit (Polynomial.evalRingHom w0 P₁)),
      R'.subtype.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) = c.toRingHom.comp Lm := by
    intro c hc hci
    have hev : ((Polynomial.eval (⟨c X', hc⟩ : R') P₁ : R') : k) = P.eval (c X') := by
      refine Eq.trans ?_ (congrArg (Polynomial.eval (c X')) hP₁)
      rw [Polynomial.eval_map]
      exact (Polynomial.eval₂_at_apply R'.subtype _).symm
    have hw0 : IsUnit (Polynomial.evalRingHom (⟨c X', hc⟩ : R') P₁) := by
      refine IsUnit.of_mul_eq_one (b := ⟨(P.eval (c X'))⁻¹, hci⟩) (Subtype.ext ?_)
      rw [Subring.coe_mul, Polynomial.coe_evalRingHom, hev]
      exact mul_inv_cancel₀ (hne c)
    refine ⟨⟨c X', hc⟩, hw0, IsLocalization.ringHom_ext (Submonoid.powers P₁) ?_⟩
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, hLm, Polynomial.coe_evalRingHom,
        Polynomial.eval_C, Polynomial.coe_mapRingHom, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        haev]
    · simp only [RingHom.comp_apply, IsLocalization.Away.lift_eq, hLm, Polynomial.coe_evalRingHom,
        Polynomial.eval_X, Polynomial.coe_mapRingHom, Polynomial.map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rfl

  obtain ⟨α, hα, hαe⟩ := hpt a (hFR (by simp [F])) (hFR (by simp [F]))
  obtain ⟨β, hβ, hβe⟩ := hpt b (hFR (by simp [F])) (hFR (by simp [F]))
  have key : ∀ (c : L →ₐ[k] k) (w0 : R') (hw0 : IsUnit (Polynomial.evalRingHom w0 P₁)),
      R'.subtype.comp (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) = c.toRingHom.comp Lm →
      (spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hw0) ≫ u₁) ≫
        pullback.fst G₀.hom (spMap jn) = spMap c.toRingHom ≫ u ≫ φ := by
    intro c w0 hw0 hce
    rw [Category.assoc, Category.assoc, hu₁f, ← Category.assoc, ModelDescent.spMap_comp_eq hce,
      ← ModelDescent.spMap_comp_eq (f := Lm) (g := c.toRingHom) rfl, Category.assoc, ← Category.assoc (spMap Lm),
      ModelDescent.spMap_comp_eq hgS, (hyS ()).2]
  have hcG : ∀ c : L →ₐ[k] k, spMap c.toRingHom ≫ u ≫ G.hom = 𝟙 _ := by
    intro c
    rw [hu, ModelDescent.spMap_comp_eq (h := RingHom.id k) (RingHom.ext c.commutes)]
    simp [spMap]
  have hdistc : spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hα) ≫ u₁ ≠
      spMap R'.subtype ≫ spMap (IsLocalization.Away.lift (S := Localization.Away P₁) P₁ hβ) ≫ u₁ := by
    intro e
    apply hab
    have ea := key a α hα hαe
    have eb := key b β hβ hβe
    rw [e] at ea
    have e2 : spMap a.toRingHom ≫ u ≫ φ = spMap b.toRingHom ≫ u ≫ φ := ea.symm.trans eb
    refine hφ.1.hom_ext (by simpa only [Category.assoc] using e2) ?_
    rw [Category.assoc, hcG, Category.assoc, hcG]
  refine ⟨R', G₁, inferInstance, SpreadGroup.finiteType_of_fg hR₀ hRfg, hunit, hG₁c,
    show Smooth (pullback.snd _ _) from inferInstance, hsep₁, show QuasiCompact (pullback.snd _ _) from inferInstance,
    hgc, hgd, ⟨s.attach.image sec, ?_, ?_, ?_⟩, P₁, hP₁0, u₁, α, β, hα, hβ, hu₁s, hdistc⟩
  · rw [Finset.card_image_of_injective _ hsec_inj, Finset.card_attach]
  · intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hpow i
  · intro x hx z hz hxz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hz
    exact fun e => hxz (by rw [hdist i j e])

end GlobalTheory.SpreadCurve
