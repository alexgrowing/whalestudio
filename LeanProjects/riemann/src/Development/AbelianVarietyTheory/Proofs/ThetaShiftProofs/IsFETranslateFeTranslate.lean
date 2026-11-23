import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdNeg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LinearIndependentOfIsExtension

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TopologicalSpace NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ConstFam

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.FieldBaseChange

section General

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F]

abbrev toF : R →+* F := (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))

abbrev strF : (DegPre.BF D F).left ⟶ Spec (CommRingCat.of F) := (fst (TF (R := R) F) D.P.A).left

abbrev SecBMod (j : ℕ) (α : D.X) : Type :=
  SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB α) (DegPre.famε j))

abbrev SecFMod (j : ℕ) (α : D.X) : Type :=
  SecOver (strF D F) (LB.LinComb D.P.L (DegPre.famφ D F α) (DegPre.famε j))

theorem TF_hom : (TF (R := R) F).hom = Spec.map (CommRingCat.ofHom (toF (R := R) F)) := by
  show Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem isPullback_prB : IsPullback (DegPre.prB D F).left (strF D F) D.P.A.hom
    (Spec.map (CommRingCat.ofHom (toF (R := R) F))) := by
  rw [← TF_hom]
  exact (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip

def resF (j : ℕ) (α : D.X) : SecBMod D j α →ₛₗ[toF (R := R) F] SecFMod D F j α :=
  pullOver D.P.L (DegPre.famε j) (isPullback_prB D F).w (GC.famφ_eq D F α)

theorem sval_resF {j : ℕ} {α : D.X} (s : SecBMod D j α) {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) {z : Z} {J}
    (hJ : Good D.P.L z J) : sval (resF D F j α s) r z J = sval s (r ≫ (DegPre.prB D F).left) z J :=
  sval_pullOver _ _ s r hJ

theorem resF_injective (j : ℕ) (α : D.X) : Function.Injective (resF D F j α) := by
  have := D.P.isAb.smooth
  have hinj : Function.Injective (toF (R := R) F) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R _)
  have : IsDominant (Spec.map (CommRingCat.ofHom (toF (R := R) F))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      rw [CommRingCat.hom_ofHom, (RingHom.injective_iff_ker_eq_bot _).1 hinj]; exact bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (Spec.map (CommRingCat.ofHom (toF (R := R) F)))
  have : IsSchemeTheoreticallyDominant (DegPre.prB D F).left := .of_isPullback (isPullback_prB D F).flip
  have : QuasiCompact (DegPre.prB D F).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_prB D F).flip inferInstance
  intro s t h
  refine SecOver.ext _ _ fun i => (DegPre.prB D F).left.app_injective _ (fn_ext fun y hy => ?_)
  have e := congrArg (fun q : SecFMod D F j α => gs (𝟙 _) y _ (LB.Sec.f q i)) h
  have hy' : (𝟙 (DegPre.BF D F).left : _ ⟶ _) y ∈ LB.wchart D.P.L (DegPre.famφ D F α) i :=
    (wchart_eq (GC.famφ_eq D F α) i).ge hy
  exact (gs_pull _ _ y _ hy _).trans ((gs_pullFn _ _ _ _ y hy').symm.trans (e.trans
    ((gs_pullFn _ _ _ _ y hy').trans (gs_pull _ _ y _ hy _).symm)))

theorem secScal_iff_resF {j : ℕ} {α : D.X} (s₁ : SecFMod D F j α) (s : SecBMod D j α) (r : R) :
    GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε j) s₁ (D.famφB α) (DegPre.famε j) s (DegPre.prB D F).left
      (scal (DegPre.BF D F).hom r) ↔ resF D F j α s = toF (R := R) F r • s₁ :=
  secScal_iff (isPullback_prB D F).w (GC.famφ_eq D F α) D.P.isLB s₁ s _ _
    ((Over.w (fst (TF (R := R) F) D.P.A)).symm.trans (congrArg _ (TF_hom F))) r

def famComp (j : ℕ) (α : D.X) : Fam D F j →ₗ[F] SecFMod D F j α where
  toFun s := s.s α
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def IsFETranslate (j : ℕ) (mu α : D.X) (s : SecBMod D j α) (t : SecBMod D j (α + j • mu)) : Prop :=
  ∀ u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) j α mu) (DegPre.deltaε j)), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
      (DegPre.famMult D (FractionRing R) j mu α) →
    GeneratorPullback.SecRel D.P.L (DegPre.famφ D (FractionRing R) (α + j • mu)) (DegPre.famε j)
      (resF D (FractionRing R) j (α + j • mu) t) (DegPre.famφ D (FractionRing R) α) (DegPre.famε j)
      (resF D (FractionRing R) j α s) (DegPre.trF D (FractionRing R) mu).left
      (DegPre.deltaφ D (FractionRing R) j α mu) (DegPre.deltaε j) u

theorem IsFETranslate.unique (hG : GlobalFnsSt) {j : ℕ} {mu α : D.X} {s : SecBMod D j α}
    {t t' : SecBMod D j (α + j • mu)} (h : IsFETranslate D j mu α s t) (h' : IsFETranslate D j mu α s t') : t = t' := by
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := FractionRing R) hG j mu α
  refine resF_injective D (FractionRing R) j _ (sec_ext' D.P.isLB fun y J hJ => ?_)
  exact ((secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h u hu hc) _ _ y J hJ).trans
    ((secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).1 (h' u hu hc) _ _ y J hJ).symm

abbrev trB (mu : D.X) : D.P.A ⟶ D.P.A := 𝟙 D.P.A * cP D D.P.A mu

theorem trF_prB (mu : D.X) : DegPre.trF D F mu ≫ DegPre.prB D F = DegPre.prB D F ≫ trB D mu := by
  rw [trF_eq, tr_pr, MonObj.comp_mul, comp_cP, comp_cP, Category.comp_id]

end General

section OverField

variable {k : Type} [Field k] (D : DegPre k)

theorem exists_feGen (j : ℕ) (mu α : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB (α + j • mu)) (fun i => (trB D mu).left ≫ D.famφB α i))
      (DegPre.deltaε j)), u.IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of k))) (ρ : T ⟶ D.P.A) (κ : T ⟶ TK k)
      (z : T.left) (J), Good D.P.L z J →
      val u ρ.left z J = cubN (th D z J) j (cP D T α) (cP D T mu) ρ * (th D z J (cP D T α) ρ (cP D T mu))⁻¹ *
        (val (D.tau mu α) κ.left z J * (val (D.psi mu) κ.left z J ^ j * val D.rigK κ.left z J ^ j)) := by
  let _ : Algebra (FractionRing k) k := (FractionRing.algEquiv k k).toRingEquiv.toRingHom.toAlgebra
  have h₁ : jFK (R := k) k ≫ jK k = 𝟙 _ := by
    refine (TF_hom (R := k) k).trans ?_
    rw [show toF (R := k) k = RingHom.id k from RingHom.ext fun x => (FractionRing.algEquiv k k).commutes x,
      CommRingCat.ofHom_id, Spec.map_id]
  have h₂ : jK k ≫ jFK (R := k) k = 𝟙 _ := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, show (algebraMap k (FractionRing k)).comp
      (algebraMap (FractionRing k) k) = RingHom.id _ from RingHom.ext fun x =>
        ((FractionRing.algEquiv k k).symm.commutes _).symm.trans ((FractionRing.algEquiv k k).symm_apply_apply x),
      CommRingCat.ofHom_id, Spec.map_id]
  obtain ⟨u, hu, hv⟩ := SectionScalarValuation.exists_eB D j α mu (DegPre.famMult D k j mu α)
    (pullGen_isGen _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _
      (powGen_isGen _ _ _ _ (D.psi_gen mu) j) (tau_isGen D mu α))
      (powGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.rig_gen _) j)) _) (fun U _ h => by
    have a₁ : ∀ χ, D.P.A.hom ≫ jFK (R := k) k ≫ D.xK χ = (SectionScalarValuation.cQ D D.P.A χ).left := fun χ => by
      show D.P.A.hom ≫ jFK (R := k) k ≫ jK k ≫ (D.c χ).left = D.P.A.hom ≫ (D.c χ).left
      rw [← Category.assoc (jFK (R := k) k), h₁, Category.id_comp]
    have a₂ : D.P.A.hom ≫ jFK (R := k) k ≫ (toUnit (TK k)).left ≫ eSec D.P.A = (1 : D.P.A ⟶ D.P.A).left := by
      show D.P.A.hom ≫ jFK (R := k) k ≫ jK k ≫ eSec D.P.A = D.P.A.hom ≫ eSec D.P.A
      rw [← Category.assoc (jFK (R := k) k), h₁, Category.id_comp]
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, a₁, a₂]
    rw [add_comm mu α, SectionScalarValuation.cQ_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module)
  refine ⟨u, hu, fun T ρ κ z J hJ => (hv T ρ z J hJ).trans (congrArg₂ (· * ·) rfl ?_)⟩
  let σ : T ⟶ TF (R := k) k := Over.homMk T.hom (by
    show T.hom ≫ jFK (R := k) k ≫ jK k = _
    rw [h₁, Category.comp_id])
  have e : σ.left ≫ jFK (R := k) k = κ.left := by
    show T.hom ≫ _ = _
    rw [← Over.w κ]
    show (κ.left ≫ jK k) ≫ _ = _
    rw [Category.assoc, h₂]; exact Category.comp_id _
  rw [Over.w ρ]
  refine (val_famMult σ hJ j mu α).trans ?_
  rw [UUA.val_powGen', UUA.val_powGen', e]

def feGen (j : ℕ) (mu α : D.X) := (exists_feGen D j mu α).choose

theorem feGen_isGen (j : ℕ) (mu α : D.X) : (feGen D j mu α).IsGen := (exists_feGen D j mu α).choose_spec.1

theorem val_feGen (j : ℕ) (mu α : D.X) {T : Over (Spec (CommRingCat.of k))} (ρ : T ⟶ D.P.A) (κ : T ⟶ TK k)
    {z : T.left} {J} (hJ : Good D.P.L z J) :
    val (feGen D j mu α) ρ.left z J =
      cubN (th D z J) j (cP D T α) (cP D T mu) ρ * (th D z J (cP D T α) ρ (cP D T mu))⁻¹ *
        (val (D.tau mu α) κ.left z J * (val (D.psi mu) κ.left z J ^ j * val D.rigK κ.left z J ^ j)) :=
  (exists_feGen D j mu α).choose_spec.2 T ρ κ z J hJ

theorem exists_feTranslate (j : ℕ) (mu α : D.X) (s : SecBMod D j α) : ∃ t : SecBMod D j (α + j • mu),
    ∀ (Z : Scheme.{0}) (ρ : Z ⟶ D.P.A.left) (z : Z) (J), Good D.P.L z J →
      sval t ρ z J = sval s (ρ ≫ (trB D mu).left) z J * (val (feGen D j mu α) ρ z J).val := by
  obtain ⟨t, ht⟩ := exists_sec D.P.isLB (φ' := D.famφB (α + j • mu)) (ε' := DegPre.famε j) (fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [DegPre.deltaε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg,
        Finset.prod_inv_distrib]
      exact (mul_comm _ _).trans (inv_mul_cancel_right _ _))
    (pullMulSec s (trB D mu).left (feGen D j mu α) (feGen_isGen D j mu α))
  exact ⟨t, fun Z ρ z J hJ => (ht Z ρ z J hJ).trans (sval_pullMulSec _ _ _ _ ρ z hJ)⟩

def feTranslate (j : ℕ) (mu α : D.X) (s : SecBMod D j α) : SecBMod D j (α + j • mu) :=
  (exists_feTranslate D j mu α s).choose

theorem sval_feTranslate (j : ℕ) (mu α : D.X) (s : SecBMod D j α) {Z : Scheme.{0}} (ρ : Z ⟶ D.P.A.left) {z : Z} {J}
    (hJ : Good D.P.L z J) : sval (feTranslate D j mu α s) ρ z J =
      sval s (ρ ≫ (trB D mu).left) z J * (val (feGen D j mu α) ρ z J).val :=
  (exists_feTranslate D j mu α s).choose_spec Z ρ z J hJ

theorem noetherianSpace_B : NoetherianSpace D.P.A.left := by
  have := D.P.isAb.smooth
  have := D.P.isAb.proper
  have : IsLocallyNoetherian D.P.A.left := LocallyOfFiniteType.isLocallyNoetherian D.P.A.hom
  have : CompactSpace D.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.P.A.hom
  have : IsNoetherian D.P.A.left := {}
  infer_instance

end OverField

section ThetaShiftProofs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {k : Type} [Field k] {b : O →+* k} {a : ArcIn D l β k b}
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {oP : letI := H.starRing; P.toPre.OAct (𝓞 E)} {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left}
  {he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A}
  {w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X} (hW : WitData a P oP φ he w e)

include hW

theorem push_cP (T : Over (Spec (CommRingCat.of (PowerSeries k)))) (χ : a.D₀.X) :
    pushHom hW.1 T (cP P.toPre T (e χ)) = cP a.D₀ _ χ := Over.OverMorphism.ext (by
  show (T.hom ≫ (P.toPre.c (e χ)).left) ≫ φ = (T.hom ≫ spMap (PowerSeries.C (R := k))) ≫ (a.D₀.c χ).left
  rw [Category.assoc, hW.2.2.2.2.1, Category.assoc])

theorem famφB_comp (α : a.D₀.X) (i : Fin 4) : P.toPre.famφB (e α) i ≫ φ = φ ≫ a.D₀.famφB α i := by
  let ρ := pushHom hW.1 P.toPre.P.A (𝟙 _)
  have hρ : ρ.left = φ := Category.id_comp _
  fin_cases i
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e₁ : pushHom hW.1 _ (𝟙 _ * cP P.toPre _ (e α)) = ρ ≫ (𝟙 _ * cP a.D₀ _ α) := by
      rw [map_mul, push_cP hW, MonObj.comp_mul, comp_cP, Category.comp_id]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom hW.1 _ (cP P.toPre _ (e α)) = ρ ≫ cP a.D₀ _ α := by rw [push_cP hW, comp_cP]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom hW.1 P.toPre.P.A 1 = ρ ≫ (1 : a.D₀.P.A ⟶ a.D₀.P.A) := by rw [map_one, MonObj.comp_one]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)

def pullB (j : ℕ) (α : a.D₀.X) :
    SecBMod a.D₀ j α →ₛₗ[PowerSeries.C (R := k)] SecBMod P.toPre j (e α) :=
  pullThrough hW.2.1 a.D₀.P.isLB P.toPre.P.isLB (famφB_comp hW α) (DegPre.famε j) hW.1.1.w

theorem secThrough_pullB (j : ℕ) (α : a.D₀.X) (s : SecBMod a.D₀ j α) :
    SecThrough w (P.toPre.famφB (e α)) (a.D₀.famφB α) (DegPre.famε j) (pullB hW j α s) s φ :=
  secThrough_pullThrough _ _ _ _ _ s

variable (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F]

omit hW in

abbrev constF (k : Type) [Field k] (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F] : k →+* F :=
  (toF (R := PowerSeries k) F).comp (PowerSeries.C (R := k))

theorem famφ_comp (α : a.D₀.X) (i : Fin 4) :
    DegPre.famφ P.toPre F (e α) i ≫ φ = ((DegPre.prB P.toPre F).left ≫ φ) ≫ a.D₀.famφB α i := by
  rw [GC.famφ_eq, Category.assoc, famφB_comp hW, Category.assoc]

theorem isPullback_prB_comp : IsPullback ((DegPre.prB P.toPre F).left ≫ φ) (strF P.toPre F) a.D₀.P.A.hom
    (Spec.map (CommRingCat.ofHom (constF k F))) := by
  have := (isPullback_prB P.toPre F).paste_horiz hW.1.1
  rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp] at this

def pullF (j : ℕ) (α : a.D₀.X) : SecBMod a.D₀ j α →ₛₗ[constF k F] SecFMod P.toPre F j (e α) :=
  pullThrough hW.2.1 a.D₀.P.isLB P.toPre.P.isLB (famφ_comp hW F α) (DegPre.famε j) (isPullback_prB_comp hW F).w

theorem secThrough_pullF (j : ℕ) (α : a.D₀.X) (s : SecBMod a.D₀ j α) :
    SecThrough w (DegPre.famφ P.toPre F (e α)) (a.D₀.famφB α) (DegPre.famε j) (pullF hW F j α s) s
      ((DegPre.prB P.toPre F).left ≫ φ) :=
  secThrough_pullThrough _ _ _ _ _ s

theorem resF_pullB (j : ℕ) (α : a.D₀.X) (s : SecBMod a.D₀ j α) :
    resF P.toPre F j (e α) (pullB hW j α s) = pullF hW F j α s := sec_ext' P.toPre.P.isLB fun y J' hJ' => by
  obtain ⟨J, hJ⟩ := exists_good' a.D₀.P.isLB y
  have e₁ := (secThrough_pullB hW j α s).sval (famφB_comp hW α) (𝟙 _ ≫ (DegPre.prB P.toPre F).left) hJ hJ'
  have e₂ := (secThrough_pullF hW F j α s).sval (famφ_comp hW F α) (𝟙 _) hJ hJ'
  simp only [GC.famφ_eq, ← Category.assoc] at e₂
  rw [sval_resF _ _ _ _ hJ']
  exact (Units.mul_right_inj _).1 (e₁.symm.trans e₂)

theorem isExtension_pullF (j : ℕ) (α : a.D₀.X) :
    letI : Algebra k F := (constF k F).toAlgebra
    IsExtension (K := k) (F := F) (pullF hW F j α) := by
  let _ : Algebra k F := (constF k F).toAlgebra
  have := noetherianSpace_B a.D₀
  exact isExtension_pullThrough (isPullback_prB_comp hW F) hW.2.1 a.D₀.P.isLB P.toPre.P.isLB (famφ_comp hW F α)

variable (hG : GlobalFnsSt) {j : ℕ} (hj : 1 ≤ j)

def constFam (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) : Fam P.toPre F j :=
  (FamFree.exists_fam_single hG P.tau_bimult hj (e α) (pullF hW F j α s₀)).choose

theorem constFam_self (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) :
    famComp P.toPre F j (e α) (constFam hW F hG hj α s₀) = pullF hW F j α s₀ :=
  (FamFree.exists_fam_single hG P.tau_bimult hj (e α) (pullF hW F j α s₀)).choose_spec.1

theorem constFam_off (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) (χ : P.toPre.X) (hχ : ∀ mu, e α + j • mu ≠ χ) :
    famComp P.toPre F j χ (constFam hW F hG hj α s₀) = 0 :=
  SecOps.sec_ext ((FamFree.exists_fam_single hG P.tau_bimult hj (e α) (pullF hW F j α s₀)).choose_spec.2 χ hχ)

theorem eq_constFam {α : a.D₀.X} {s₀ : SecBMod a.D₀ j α} {s : Fam P.toPre F j}
    (h₁ : famComp P.toPre F j (e α) s = pullF hW F j α s₀)
    (h₂ : ∀ χ, (∀ mu, e α + j • mu ≠ χ) → famComp P.toPre F j χ s = 0) : s = constFam hW F hG hj α s₀ := by
  refine fam_ext fun χ i => congrArg (fun q => LB.Sec.f q i) (?_ : s.s χ = (constFam hW F hG hj α s₀).s χ)
  by_cases hχ : ∃ mu, e α + j • mu = χ
  · exact FamFree.eq_of_eq_add_nsmul hG _ _ hχ (h₁.trans (constFam_self hW F hG hj α s₀).symm)
  · exact (h₂ χ fun mu h => hχ ⟨mu, h⟩).trans (constFam_off hW F hG hj α s₀ χ fun mu h => hχ ⟨mu, h⟩).symm

omit hW in

def expo (a : ArcIn D l β k b) (j : ℕ) (α mu : a.D₀.X) : ℤ := j * (a.be mu mu / 2) + a.be mu α

omit hW in
theorem two_mul_expo (a : ArcIn D l β k b) (j : ℕ) (α mu : a.D₀.X) :
    2 * expo a j α mu = j * a.be mu mu + 2 * a.be mu α := by
  obtain ⟨n, hn⟩ : (2 : ℤ) ∣ a.be mu mu := (Dvd.intro _ rfl).trans (a.be_dvd mu mu)
  rw [expo, hn, Int.mul_ediv_cancel_left _ two_ne_zero]; ring

def IsIntegralForm (j : ℕ) (α : a.D₀.X) (s₀ : SecBMod a.D₀ j α) (m : ℕ) (f : ∀ χ, SecBMod P.toPre j χ) : Prop :=
  (∀ mu, 0 ≤ (m : ℤ) + expo a j α mu ∧ f (e (α + j • mu)) =
    (PowerSeries.X : PowerSeries k) ^ ((m : ℤ) + expo a j α mu).toNat •
      pullB hW j (α + j • mu) (feTranslate a.D₀ j mu α s₀)) ∧
  ∀ χ, (∀ mu, e α + j • mu ≠ χ) → f χ = 0

end ThetaShiftProofs

end GlobalTheory.ConstFam
