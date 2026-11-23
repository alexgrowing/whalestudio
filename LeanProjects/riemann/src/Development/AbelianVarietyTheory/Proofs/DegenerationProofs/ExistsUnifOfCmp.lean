import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsUniquePartner
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEqIffExpansionEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfOnto
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfExpBij
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFamFieldPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThickIsoOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfLaws
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueExpansionSectionAdmissibleBaseStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.FamFieldPull

theorem exists_restrict {X Y Z : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (h : Z ⟶ Y) (φ' : K → (Z ⟶ X)) (hφ : ∀ k, φ' k = h ≫ φ k) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ t : LB.Sec (LB.LinComb L φ' ε), GeneratorPullback.SecScal L φ' ε t φ ε s h 1 := by
  obtain rfl : φ' = fun k => h ≫ φ k := funext hφ
  refine ⟨DVR.pullSec L φ ε s h, fun j₁ j₂ hco => ?_⟩
  obtain rfl : j₁ = j₂ := funext fun k => hco (Sum.inl k) (Sum.inr k) rfl
  rw [resTop, map_one, _root_.one_mul]
  exact (DVR.rs_rs _ _ _).symm

theorem scal_one {R : Type} [CommRing R] {Y : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) :
    scal p (1 : R) = 1 := by
  unfold scal
  rw [map_one, map_one]

section Field

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}

def Restricts (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ} (s : Raw D F k) (f : ∀ α, D.SecB k α) : Prop :=
  ∀ α, GeneratorPullback.SecScal D.P.L (DegPre.famφ D F α) (DegPre.famε k) (s α) (D.famφB α) (DegPre.famε k) (f α)
    (DegPre.prB D F).left 1

theorem exists_restricts (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ} (f : ∀ α, D.SecB k α) :
    ∃ s : Raw D F k, Restricts F s f := by
  choose s hs using fun α => exists_restrict D.P.L _ _ _ _ (ExpGTrans.famφ_eq D F α) (f α)
  exact ⟨s, hs⟩

theorem fe_of_field (hG : GlobalFnsSt) (F : Type) [Field F] [Algebra (FractionRing R) F] {k : ℕ}
    {f : ∀ α, D.SecB k α} {t : Raw D F k} {s : Raw D (FractionRing R) k} (ht : Restricts F t f)
    (hs : Restricts (FractionRing R) s f) (H : DegPre.FamFE D F k t) : DegPre.FamFE D (FractionRing R) k s := by
  intro mu α u hu hc
  have hj : jFK (R := R) (FractionRing R) = 𝟙 _ := Spec.map_id _
  let a : TF (R := R) F ⟶ TF (R := R) (FractionRing R) := Over.homMk (jFK (R := R) F) (by
    show _ ≫ jFK (R := R) (FractionRing R) ≫ jK R = _
    rw [hj, Category.id_comp]; rfl)
  let π : DegPre.BF D F ⟶ DegPre.BF D (FractionRing R) := a ▷ D.P.A
  have p₁ : π ≫ fst _ _ = fst _ _ ≫ a := whiskerRight_fst _ _
  have p₂ : π ≫ DegPre.prB D (FractionRing R) = DegPre.prB D F := whiskerRight_snd _ _
  have hinj : ∀ U, Function.Injective (π.left.app U).hom := by
    have sq : IsPullback π.left (fst (TF (R := R) F) D.P.A).left (fst (TF (R := R) (FractionRing R)) D.P.A).left
        a.left := by
      refine IsPullback.of_right (h₁₂ := (DegPre.prB D (FractionRing R)).left) (v₁₃ := D.P.A.hom)
        (h₂₂ := (TF (R := R) (FractionRing R)).hom) ?_ (congrArg (fun q => q.left) p₁)
        (IsPullback.of_hasPullback (TF (R := R) (FractionRing R)).hom D.P.A.hom).flip
      rw [← Over.comp_left, p₂, Over.w a]
      exact (IsPullback.of_hasPullback (TF (R := R) F).hom D.P.A.hom).flip
    have := D.P.isAb.smooth
    have : Flat (fst (TF (R := R) (FractionRing R)) D.P.A).left := by
      show Flat (pullback.fst _ _)
      infer_instance
    have hq : QuasiCompact a.left := inferInstanceAs (QuasiCompact (Spec.map _))
    have : IsDominant a.left := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (algebraMap (FractionRing R) F).injective).le.trans bot_le)⟩
    have : IsReduced (TF (R := R) (FractionRing R)).left := inferInstanceAs (IsReduced (Spec _))
    have := IsSchemeTheoreticallyDominant.of_isDominant a.left
    have : IsSchemeTheoreticallyDominant π.left := IsSchemeTheoreticallyDominant.of_isPullback sq.flip
    have : QuasiCompact π.left := MorphismProperty.of_isPullback (P := @QuasiCompact) sq.flip hq
    exact fun U => π.left.app_injective U
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  refine Eq.trans (FamPull.sval_eq_of_app_injective D.P.isLB (u := s (α + k • mu))
    (u' := pullMulSec (s α) (DegPre.trF D _ mu).left u hu) (fun U _ h => ?_) π.left hinj (fun y J hJ => ?_) _ _ y J hJ)
    (sval_pullMulSec _ _ _ _ _ y hJ)
  · simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, DegPre.deltaφ, DegPre.deltaε, zpow_neg,
      Finset.prod_inv_distrib]
    rw [mul_comm, inv_mul_cancel_right]
  · have b : (π ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) =
        (fst (TF (R := R) F) D.P.A).left ≫ jFK (R := R) F := by
      rw [p₁, hj]; exact Category.comp_id _
    have e := (FamPull.famFE_iff hG t f ht).1 H mu α _ (𝟙 _) y J hJ
    rw [sval_pullMulSec _ _ _ _ _ y hJ, (gen_fe (D := D) (F := FractionRing R) hG k mu α).2 u hu hc _ π y J hJ,
      FamPull.val_feUnit k mu α π hJ, ← SectionScalarValuation.secScal_sval (hs _) _ y hJ, ← SectionScalarValuation.secScal_sval (hs _) _ y hJ,
      FamPull.comp_trF, ← Over.comp_left, p₂, b]
    simp only [Category.id_comp] at e
    exact e

end Field

section Pull

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D')

theorem fe_of_pull (hG : GlobalFnsSt) (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]
    (hT : (TF (R := R') F).hom ≫ specOf φ = (TF (R := R) F).hom) {k : ℕ} {f : ∀ α, D.SecB k α}
    {f' : ∀ α, D'.SecB k α} {s : Raw D F k} {s' : Raw D' F k} (hs : Restricts F s f) (hs' : Restricts F s' f')
    (hf : ∀ x, IsSecPull hD.w (D'.famφB x) (D.famφB (hD.xe x)) (DegPre.famε k) (prA hD) (f' x) (f (hD.xe x)))
    (H : DegPre.FamFE D' F k s') : DegPre.FamFE D F k s := by
  obtain ⟨Θ, h₁, h₂⟩ := ThetaBaseChange.exists_cmp hT (pull_grp hD).1.w
  obtain ⟨Λ, l₁, l₂⟩ := ThetaBaseChange.exists_cmp_inv hT (pull_grp hD).1
  have hΛ : Λ ≫ Θ = 𝟙 _ := ThetaDescent.inv_cmp l₁ l₂ h₁ h₂
  have hv : ∀ (x : D'.X) (r : (DegPre.BF D F).left ⟶ (DegPre.BF D' F).left) (z) {J J'}, Good D.P.L z J →
      Good D'.P.L z J' → sval (s (hD.xe x)) (r ≫ Θ) z J =
        (∏ κ, wGerm hD.w z J J' (r ≫ DegPre.famφ D' F x κ) ^ DegPre.famε k κ).val * sval (s' x) r z J' :=
    fun x r z J J' hJ hJ' => by
      have e := (hf x).val (ExpGTrans.famφB_pull hD x) (r ≫ (DegPre.prB D' F).left) z hJ hJ'
      have c : (r ≫ (DegPre.prB D' F).left) ≫ prA hD = (r ≫ Θ) ≫ (DegPre.prB D F).left := by
        rw [Category.assoc, Category.assoc]
        exact congrArg (r ≫ ·) h₂.symm
      rw [c, SectionScalarValuation.secScal_sval (hs _) _ z hJ, SectionScalarValuation.secScal_sval (hs' _) _ z hJ'] at e
      simp only [Category.assoc, ← ExpGTrans.famφ_eq] at e
      exact e
  intro mu₀ α₀
  obtain ⟨mu, rfl⟩ := hD.xe.surjective mu₀
  obtain ⟨α, rfl⟩ := hD.xe.surjective α₀
  intro u hu hc
  obtain ⟨u', hu', hc'⟩ := (gen_fe (D := D') (F := F) hG k mu α).1
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := BoxFamily.exists_good_at (Z := (DegPre.BF D F).left) D'.P.isLB y
  have e₁ := hv (α + k • mu) Λ y hJ hJ'
  have e₂ := hv α (Λ ≫ (DegPre.trF D' F mu).left) y hJ hJ'
  have e₃ := gen_pr hD F hT h₁ h₂ hG k α mu u' hu' hc' u hu hc Λ y hJ hJ'
  have e₄ := (secRel_iff D'.P.isLB _ _ _ _ _ _ _ _ _ u').1 (H _ _ u' hu' hc') _ Λ y J' hJ'
  have e₅ : (∏ a, wGerm hD.w y J J' (Λ ≫ DegPre.deltaφ D' F k α mu a) ^ DegPre.deltaε k a) =
      (∏ a, wGerm hD.w y J J' (Λ ≫ DegPre.famφ D' F (α + k • mu) a) ^ DegPre.famε k a) *
      (∏ a, wGerm hD.w y J J' ((Λ ≫ (DegPre.trF D' F mu).left) ≫ DegPre.famφ D' F α a) ^
        DegPre.famε k a)⁻¹ := by
    simp only [Category.assoc]
    exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
  have c : (Λ ≫ (DegPre.trF D' F mu).left) ≫ Θ = 𝟙 _ ≫ (DegPre.trF D F (hD.xe mu)).left :=
    (Category.assoc _ _ _).trans ((congrArg (Λ ≫ ·) (trF_pr hD F hT h₁ h₂ mu)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hΛ)))
  rw [c] at e₂
  have e₁' := (congrArg (fun q => sval (s (hD.xe (α + k • mu))) q y J) hΛ).symm.trans e₁
  have e₃' := (congrArg (fun q => val u q y J) hΛ).symm.trans e₃
  rw [← map_nsmul, ← map_add]
  refine e₁'.trans (Eq.trans ?_ (congrArg₂ (· * ·) e₂ (congrArg Units.val e₃')).symm)
  rw [e₄, e₅]
  exact (BoxFamily.unit_shuffle _ _ _ _).symm

end Pull

section Exp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem fe_of_expandsAt (hR : AdmBase R I) (U : UnifPre I D A G) {k : ℕ} (hU : ∀ s, ∃ E, U.Expands k s E)
    {σ : H0 U.LG.L k} {f : ∀ α, D.toPre.SecB k α} (hE : ∀ e, U.ExpandsAt e k σ f)
    {t : Raw D.toPre (FractionRing R) k} (ht : Restricts (FractionRing R) t f) :
    DegPre.FamFE D.toPre (FractionRing R) k t := by
  obtain ⟨s, hσ⟩ := exists_restrict U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
    (pullback.fst G.hom (jK R)) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (Category.comp_id _).symm) σ
  obtain ⟨E, r', hr', σ', f', hσ', hf', hE'⟩ := hU s
  have := U.smooth
  have : Flat G.hom := inferInstance
  have e : (TF (R := R) (FractionRing R)).hom = jK R := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]; rfl
  rw [← scal_one (pullback.snd G.hom (jK R) ≫ jK R)] at hσ
  have hs := ExpansionFunction.eq_iff_comb_eq_zero U.LG.isLB G.hom (pullback.snd G.hom (jK R))
    pullback.condition (fun _ => (Category.comp_id _).symm) (ExpInt.generic_app_injective G) _ rfl
    one_ne_zero hr' hσ hσ'
  have hw : (DegPre.BF D.toPre (FractionRing R)).hom =
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R := by
    rw [← e]; exact (Over.w _).symm
  have hd : IsDominant (TF (R := R) (FractionRing R)).hom := DVR.GC.isDominant_jFR (V := R) (FractionRing R)
  have h₁ : IsSchemeTheoreticallyDominant (TF (R := R) (FractionRing R)).hom := .of_isDominant _
  have h₅ : QuasiCompact (jK R) :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  have h₃ : QuasiCompact (TF (R := R) (FractionRing R)).hom := e ▸ h₅
  have := D.toPre.P.isAb.smooth
  have : Flat D.toPre.P.A.hom := inferInstance
  have hF := fun α => ExpansionFunction.eq_iff_comb_eq_zero D.toPre.P.isLB D.toPre.P.A.hom
    (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left
    ((Over.w (DegPre.prB D.toPre (FractionRing R))).trans hw) (DVR.GC.famφ_eq D.toPre (FractionRing R) α)
    (pullback.snd (TF (R := R) (FractionRing R)).hom D.toPre.P.A.hom).app_injective _ hw one_ne_zero hr'
    (by rw [scal_one]; exact ht α) (hf' α)
  have H := comb_eq_zero_iff_expansion_comb_eq_zero R I hR D A G U k 2 ![r', -1] ![σ, σ'] ![f, f']
    (fun i => by fin_cases i; exacts [hE, hE'])
  have hc : ∀ α (i : Fin 2), (![f, f'] i) α = ![f α, f' α] i := fun α i => by fin_cases i <;> rfl
  simp only [hc] at H
  obtain rfl : t = E.s := funext fun α => (hF α).2 (H.1 (hs.1 rfl) α)
  exact E.fe

theorem exists_extends (hG : IsSemiAbelian G) (U : UnifPre I D A G) (k : ℕ) (s : U.SecK k) :
    ∃ r : R, r ≠ 0 ∧ ∃ σ : H0 U.LG.L k,
      GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
        (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK R))
        (scal (pullback.snd G.hom (jK R) ≫ jK R) r) := by
  have := hG.quasiCompact
  have := U.separated
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : QuasiSeparatedSpace G.left := (quasiSeparated_iff_quasiSeparatedSpace G.hom).mp inferInstance
  obtain ⟨s₁, hs₁⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left)
    (ε' := fun _ => (k : ℤ)) (fun V _ h => by simp only [Category.comp_id]) s
  obtain ⟨t, ht, σ, hσ⟩ := TwistLoc.exists_clear_denominator (nonZeroDivisors R)
    (IsPullback.of_hasPullback G.hom (jK R)) U.LG.isLB (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) s₁
  refine ⟨t, nonZeroDivisors.ne_zero ht, σ, (FieldBaseChange.secScal_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => ?_⟩
  rw [← hs₁ _ _ y J hJ, ExpInt.gs_scal, ← pullback.condition,
    sval_of σ _ y J (fun a => J (𝟙 _ ≫ pullback.fst G.hom (jK R) ≫ 𝟙 G.left)) (fun a => by rw [Category.assoc])]
  exact hσ _ (𝟙 _) y _ (hJ.mem (fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left) (𝟙 _))

theorem expBij_of_total (hS : SecBaseChangeSt) (hR : AdmBase R I) [GeometricallyConnected G.hom] (U : UnifPre I D A G)
    {k : ℕ} (hk : 1 ≤ k) (hfin : Module.Finite (FractionRing R) (Fam D.toPre (FractionRing R) k))
    (hdim : Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) = k ^ A.g)
    (htot : ∀ s, ∃ E, U.Expands k s E) : U.ExpBij k := by
  refine ExpansionCriterion.expBij_of_onto hS R I hR D A G U k hk hfin hdim fun E => ?_
  obtain ⟨b, hex, huniq⟩ := GenericSectionBasis.exists_secK_basis hS R I D A G U k hk
  choose F hF using fun i => htot (b i)
  let ψ : (Fin (k ^ A.g) → FractionRing R) →ₗ[FractionRing R] Fam D.toPre (FractionRing R) k :=
    Fintype.linearCombination (FractionRing R) F
  have hlin : ∀ c s, _ → U.Expands k s (ψ c) := fun c s hs => expands_linear R I hR D A G U k _ b F c s hF hs
  have hinj : Function.Injective ψ := fun c c' h => by
    obtain ⟨s, hs⟩ := hex c
    obtain ⟨s', hs'⟩ := hex c'
    obtain rfl : s = s' := (eq_iff_expansion_eq R I hR D A G U k s s' _ _ (hlin c s hs) (hlin c' s' hs')).2 h
    exact (huniq s).unique hs hs'
  obtain ⟨c, rfl⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hdim]; simp)).1 hinj E
  obtain ⟨s, hs⟩ := hex c
  exact ⟨s, hlin c s hs⟩

end Exp

section Cmp

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
  {φ : R →+* R'} {D : DegData R I} {D' : DegData R' I'}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']

def Level (hD : IsPullDeg φ D.toPre D'.toPre) (U : UnifPre I D A G) (U' : UnifPre I' D' A' G') (Ψ : G'.left ⟶ G.left)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull Ψ)) (e : ℕ) : Prop :=
  ∃ h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left, h ≫ (fstG I e G).left = (fstG I' e G').left ≫ Ψ ∧
    ((U'.gt e).pG.left ≫ prA hD = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X,
      (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ prA hD = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧
      PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x)
        ((U.gt e).t (hD.xe x)) h) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι)
      (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), prA hD ((U'.gt e).pG.left (r z)) ∈ D.toPre.P.L.U jM →
      (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → Ψ ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL →
      (fstG I' e G').left (r z) ∈ U'.LG.L.U jL' →
      Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') =
        Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL'

theorem expBij_descends (hL : Laws) (hL₂ : Laws2) (hR : AdmBase R I) (hR' : AdmBase R' I')
    (hφ : Function.Injective φ) (hD : IsPullDeg φ D.toPre D'.toPre) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (U : UnifPre I D A G) (U' : Unif I' D' A' G') {Ψ : G'.left ⟶ G.left} (gΨ : IsGrpPullback G' G (specOf φ) Ψ)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull Ψ)) (hwL : wL.IsGen) (hlev : ∀ e, Level hD U U'.toUnifPre Ψ wL e)
    {k : ℕ} (hk : 1 ≤ k) (hint : ∀ σ : H0 U.LG.L k, ∃ f, ∀ e, U.ExpandsAt e k σ f) : U.ExpBij k := by
  have := hG.geomConnected
  have := hG'.geomConnected
  have inj : Function.Injective ((algebraMap R' (FractionRing R')).comp φ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hφ
  letI : Algebra (FractionRing R) (FractionRing R') := (IsFractionRing.lift (K := FractionRing R) inj).toAlgebra
  have hF : ∀ r : R, algebraMap (FractionRing R) (FractionRing R') (algebraMap R (FractionRing R) r) =
      algebraMap (FractionRing R') (FractionRing R') (algebraMap R' (FractionRing R') (φ r)) := fun r =>
    IsFractionRing.lift_algebraMap (K := FractionRing R) inj r
  obtain ⟨g, hg₁, hg₂⟩ := ThetaBaseChange.exists_fraction_map φ (FractionRing R') hF
  have hT : (jFK (R := R') (FractionRing R') ≫ jK R') ≫ specOf φ = jFK (R := R) (FractionRing R') ≫ jK R := by
    rw [Category.assoc, ← hg₁, ← Category.assoc, hg₂]
  have gA := ThetaBaseChange.grp_generic U
  have gA' := (ThetaBaseChange.grp_generic U'.toUnifPre).comp gΨ
  have hA : A'.g = A.g := by
    have sq : IsPullback (gA.1.lift _ (A'.A.hom ≫ g) (by rw [gA'.1.w, Category.assoc, hg₁])) A'.A.hom A.A.hom g :=
      IsPullback.of_right (by rw [gA.1.lift_fst, hg₁]; exact gA'.1) (gA.1.lift_snd _ _ _) gA.1
    exact H1.dim_unique _ A'.smoothDim
      ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback sq A.smoothDim)
      (eSec A'.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R')))
  have hB : D'.toPre.P.g = D.toPre.P.g := H1.dim_unique _ D'.toPre.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp hD).1 D.toPre.P.smoothDim)
    (eSec D'.toPre.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R'))
  have hrk : D'.toPre.rank = D.toPre.rank := hD.xe.toIntLinearEquiv.finrank_eq
  obtain ⟨hfin, hd⟩ := finrank_fam_of_laws hL hL₂ R D.toPre D.tau_bimult (FractionRing R) k hk
  obtain ⟨-, hd'⟩ := finrank_fam_of_laws hL hL₂ R' D'.toPre D'.tau_bimult (FractionRing R') k hk
  have hdA := finrank_fam_of_expBij hL.secBaseChange R' I' hR' D' A' G' U'.toUnifPre k hk (U'.expand k hk)
  refine expBij_of_total hL.secBaseChange hR U hk hfin (by rw [hd, ← hrk, ← hB, ← hd', hdA, hA]) fun s => ?_
  obtain ⟨r, hr, σ, hσ⟩ := exists_extends hG U k s
  obtain ⟨f, hf⟩ := hint σ
  obtain ⟨σ', hσ', -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.LG.L U'.LG.L _ U.LG.isLB U'.LG.isLB wL hwL
    (Fin 1) (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)) Ψ
    (fun _ => by rw [Category.id_comp, Category.comp_id]) σ
  choose f' hf' using fun x => (SecPull.existsUnique_secPull _ _ _ _ _ _ _ D.toPre.P.isLB D'.toPre.P.isLB hD.w
    hD.w_gen (Fin 4) (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k) _ (ExpGTrans.famφB_pull hD x)
    (f (hD.xe x))).exists
  have hE' : ∀ e, U'.ExpandsAt e k σ' f' := fun e => by
    obtain ⟨h, hh⟩ := hlev e
    exact expandsAt_transport R R' I I' D D' A A' G G' U U'.toUnifPre _ hD.w hD.xe _ wL hD.w_gen hwL
      (ExpGTrans.famφB_pull hD) e e k h hh σ σ' f f' hσ' hf' (hf e)
  obtain ⟨t', ht'⟩ := exists_restricts (FractionRing R') f'
  obtain ⟨t₁, ht₁⟩ := exists_restricts (FractionRing R') f
  obtain ⟨t, ht⟩ := exists_restricts (FractionRing R) f
  have fe := fe_of_field hL.globalFns _ ht₁ ht (fe_of_pull hD hL.globalFns _ hT ht₁ ht' hf'
    (fe_of_expandsAt hR' U'.toUnifPre (fun s => ((U'.expand k hk).1 s).exists) hE' ht'))
  let E₀ : Fam D.toPre (FractionRing R) k := ⟨t, fe⟩
  refine ⟨(algebraMap R (FractionRing R) r)⁻¹ • E₀, r, hr, σ, f, hσ, fun α => ?_, hf⟩
  refine (FieldBaseChange.secScal_iff_val D.toPre.P.isLB _ _ _ _).2 fun y J hJ => ?_
  have hm := hJ.mem (DegPre.famφ D.toPre (FractionRing R) α) (𝟙 _)
  have hw : (DegPre.BF D.toPre (FractionRing R)).hom =
      (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jK R :=
    (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).symm.trans (congrArg (_ ≫ ·)
      ((congrArg (· ≫ jK R) (Spec.map_id _ : jFK (R := R) (FractionRing R) = 𝟙 _)).trans (Category.id_comp _)))
  have e₁ : gs (𝟙 _) y ⊤ (scal (DegPre.BF D.toPre (FractionRing R)).hom r) =
      cst (V := FractionRing R) (𝟙 _ ≫ (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left) y
        (algebraMap R (FractionRing R) r) := by
    rw [ExpInt.gs_scal, hw, ← Category.assoc]
    exact cst_comp _ _ _ _
  have e₂ : sval (((algebraMap R (FractionRing R) r)⁻¹ • E₀).s α) (𝟙 _) y J =
      cst (V := FractionRing R) (𝟙 _ ≫ (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left) y
        (algebraMap R (FractionRing R) r)⁻¹ * sval (t α) (𝟙 _) y J :=
    (gs_mul _ y _ hm _ _).trans (congrArg₂ (· * ·) ((gs_res _ y le_top hm _).trans
      (gs_pull _ (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left y ⊤ trivial _)) rfl)
  rw [SectionScalarValuation.secScal_sval (ht α) _ y hJ, e₁, e₂, ← _root_.mul_assoc, ← H1.cst_mul,
    mul_inv_cancel₀ ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 hr), H1.cst_one, _root_.one_mul]

theorem level_of_cmp (hI : I.map φ ≤ I') (U : PreU I D.toPre A G) (U' : PreU I' D'.toPre A' G')
    (U₀ : UnifPre I D A G) (U₀' : UnifPre I' D' A' G') (hU : Under U U₀) (hU' : Under U' U₀') {F : G'.left ⟶ G.left}
    (C : Cmp φ U U' F) (hD : IsPullDeg φ D.toPre D'.toPre) (hβ : prA hD = C.β) (hv : HEq hD.w C.v)
    (hx : hD.xe = C.xe) :
    ∃ wL : LB.Iso U₀'.LG.L (U₀.LG.L.pull F), wL.IsGen ∧ (∃ he : eSec G' ≫ F = specOf φ ≫ eSec G,
      LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) U₀'.LG.rig
        (rigPullOf F (specOf φ) he U₀.LG.L U₀.LG.rig)) ∧ ∀ e, Level hD U₀ U₀' F wL e := by
  obtain ⟨pb, wL, wL_map, β, pbB, v, v_gen, xe, c_pr, lev⟩ := C
  obtain ⟨_, _, _, _, LG, _, _, _, _, _, gt, _, _, w, _, _, _, _, _⟩ := U₀
  obtain ⟨_, _, _, _, LG', _, _, _, _, _, gt', _, _, w', _, _, _, _, _⟩ := U₀'
  obtain ⟨-, h₂, -, -, h₅, h₆⟩ := hU
  obtain ⟨-, h₂', -, -, h₅', h₆'⟩ := hU'
  dsimp only at h₂ h₅ h₆ h₂' h₅' h₆' hβ hv hx
  subst h₂ h₅ h₂' h₅' hβ hx
  obtain rfl := eq_of_heq h₆
  obtain rfl := eq_of_heq h₆'
  obtain rfl := eq_of_heq hv
  have he : eSec G' ≫ F = specOf φ ≫ eSec G := (cubeMapOf pb).e_comm
  refine ⟨wL, wL_map.gen, ⟨he, ?_⟩, fun e => ?_⟩
  · refine (maps_iff wL _ (fun _ => eSec G) _ U'.P.L.rig U.P.L.rig (specOf φ) _
      (rigPull_le F (specOf φ) he U.P.L.L) (fun _ => rfl)).2 ?_
    refine ThickIso.pmaps_of_good ((isGen_iff wL).1 wL_map.gen) U.P.L.isLB U'.P.L.isLB (fun _ => he)
      U'.P.L.rigGen U.P.L.rigGen fun y J J' hJ hJ' => ?_
    have e := (wL_map.vals (𝟙_ _) y J' J hJ' hJ _ (fun _ => rfl)).1
    rw [Fintype.prod_unique, zpow_one]
    exact e
  · obtain ⟨q, hq⟩ : ∃ q : Spec (CommRingCat.of (R' ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))),
        q ≫ thick R I e = thick R' I' e ≫ specOf φ := by
      refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I' ^ (e + 1)) φ ?_)), ?_⟩
      · exact Ideal.map_le_iff_le_comap.1 ((Ideal.map_pow φ I _).le.trans (Ideal.pow_right_mono hI _))
      · simp only [thick, specOf, ← Spec.map_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]
    obtain ⟨h, hh⟩ : ∃ h : (thickObj R' I' e G').left ⟶ (thickObj R I e G).left,
        h ≫ (fstG I e G).left = (fstG I' e G').left ≫ F :=
      ⟨pullback.lift ((fstG I' e G').left ≫ F) (pullback.snd G'.hom (thick R' I' e) ≫ q) (by
        rw [Category.assoc, pb.1.w, Category.assoc, hq, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ _) pullback.condition), pullback.lift_fst _ _ _⟩
    have ho : h ≫ ((Over.map (thick R I e)).obj (thickObj R I e G)).hom =
        ((Over.map (thick R' I' e)).obj (thickObj R' I' e G')).hom ≫ specOf φ := by
      rw [← Over.w (fstG I e G), ← Over.w (fstG I' e G'), ← Category.assoc, hh, Category.assoc, Category.assoc, pb.1.w]
    have lv := fun Z (r : Z ⟶ _) => lev e Z r (r ≫ h) (by rw [Category.assoc, hh])
    have hp : (U'.gt e).pG.left ≫ prA hD = h ≫ (U.gt e).pG.left := by
      simpa only [Category.id_comp] using (lv _ (𝟙 _)).1
    have hO : ∀ x κ, D'.toPre.Oφ (U'.gt e).pG x κ ≫ prA hD = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ := fun x κ => by
      have c := cPoint_left_pr hD (T' := (Over.map (thick R' I' e)).obj (thickObj R' I' e G'))
        (T := (Over.map (thick R I e)).obj (thickObj R I e G)) h ho x
      fin_cases κ
      · exact mul_left_pr hD (T' := (Over.map (thick R' I' e)).obj (thickObj R' I' e G'))
          (T := (Over.map (thick R I e)).obj (thickObj R I e G)) h ho hp c
      · exact c
      · exact hp
      · exact one_left_pr hD (T' := (Over.map (thick R' I' e)).obj (thickObj R' I' e G'))
          (T := (Over.map (thick R I e)).obj (thickObj R I e G)) h ho
    refine ⟨h, hh, ⟨hp, fun x => ⟨hO x, ?_⟩⟩, fun Z r z jM jM' jL jL' hM hM' hL hL' => ?_⟩
    · refine ThickIso.pmaps_of_good ((isGen_iff hD.w).1 hD.w_gen) D.toPre.P.isLB D'.toPre.P.isLB (hO x)
        ((U'.gt e).t_gen x) ((U.gt e).t_gen _) fun y J J' hJ hJ' => ?_
      exact (((lv _ (𝟙 _)).2 y J J' hJ hJ').1 x).trans (mul_comm _ _)
    · obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB z (fun _ : Unit => (r ≫ h) ≫ (U.gt e).pG.left)
        (fun _ => jM) (fun _ _ _ => rfl) (fun _ => by rw [Category.assoc, ← hp]; exact hM)
      obtain ⟨J', hJ', eJ'⟩ := exists_good D'.toPre.P.L D'.toPre.P.isLB z (fun _ : Unit => r ≫ (U'.gt e).pG.left)
        (fun _ => jM') (fun _ _ _ => rfl) (fun _ => hM')
      obtain rfl := eJ ()
      obtain rfl := eJ' ()
      refine ((lv Z r).2 z J J' hJ hJ').2 jL jL' ?_ hL'
      show (h ≫ (fstG I e G).left) (r z) ∈ _
      rw [hh]; exact hL

end Cmp

theorem exists_expandsAt (hL : Laws) (hL₂ : Laws2) (hE : Ega) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {I : Ideal R} (hR : AdmBase R I) (hI : I ≠ ⊤) {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G) (hU : Under U U₀) (k : ℕ) (σ₀ : H0 U₀.LG.L k) :
    ∃ f₀, ∀ e, U₀.ExpandsAt e k σ₀ f₀ := by
  obtain ⟨σ₁, h₁⟩ : ∃ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ :=
    (by rintro _ _ rfl σ; exact ⟨σ, HEq.rfl⟩ :
      ∀ L L' : RigLB G, L = L' → ∀ σ : H0 L'.L k, ∃ σ₁ : H0 L.L k, HEq σ₁ σ) _ _ hU.2.1 σ₀
  obtain ⟨σ, hσ⟩ := exists_restrict U.P.L.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) (snd (𝟙_ _) G).left
    (fun _ => (snd (𝟙_ _) G).left) (fun _ => (Category.comp_id _).symm) σ₁
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.existsUnique_expansion_section_admissible_base hL hL₂ hE R I hR hI D.toPre A G U k σ
  let n : D.toPre.P.A ⟶ 𝟙_ _ ⊗ D.toPre.P.A := lift (toUnit _) (𝟙 _)
  have n₁ : n.left ≫ (snd (𝟙_ _) D.toPre.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = 𝟙 _)
  have n₂ : (snd (𝟙_ _) D.toPre.P.A).left ≫ n.left = 𝟙 _ :=
    congrArg (fun q => q.left) (show snd _ _ ≫ n = 𝟙 _ from
      CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by simp [n]))
  have hφ : ∀ α κ, famφT D.toPre (𝟙_ _) α κ = (snd (𝟙_ _) D.toPre.P.A).left ≫ D.toPre.famφB α κ := fun α κ => by
    rw [FamPull.comp_famφB]
    fin_cases κ
    exacts [rfl, congrArg (fun q : 𝟙_ _ ⊗ D.toPre.P.A ⟶ D.toPre.P.A => q.left)
      (mul_comm (snd (𝟙_ _) D.toPre.P.A) (cP D.toPre _ α)), rfl, rfl]
  choose f₀ hf₀ using fun α => exists_restrict D.toPre.P.L _ _ n.left (D.toPre.famφB α)
    (fun κ => by rw [hφ, ← Category.assoc, n₁, Category.id_comp]) (f α)
  refine ⟨f₀, ((GlobalTheory.T.uniformisation_chart_value_forms_correspond hL hL₂ R I D A G U.semi).2.2 U U₀ hU k σ f σ₀ f₀ (fun σ₂ h₂ z J hJ => ?_)
    (fun α z J hJ => ?_)).1 hf⟩
  · obtain rfl : σ₂ = σ₁ := eq_of_heq (h₂.trans h₁.symm)
    rw [← SectionScalarValuation.secScal_sval hσ _ z hJ, Category.id_comp]
  · rw [← SectionScalarValuation.secScal_sval (hf₀ α) _ z hJ, n₂]

theorem exists_unif_of_cmp : Laws → Laws2 → Ega → ∀ (R V : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V), AdmBase R I → AdmBase V I' → I ≠ ⊤ → ∀ φ : R →+* V, Function.Injective φ → I.map φ ≤ I' → ∀ (D : DegData R I) (D' : DegData V I') (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D.toPre A G) (U' : PreU I' D'.toPre A' G') (U₀' : Unif I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F) (hD : IsPullDeg φ D.toPre D'.toPre), Under U' U₀'.toUnifPre → hD.e.hom.left ≫ pullback.fst _ _ = C.β → HEq hD.w C.v → hD.xe = C.xe → ∃ (U₀ : Unif I D A G) (bc : G' ≅ (Over.pullback (specOf φ)).obj G), Under U U₀.toUnifPre ∧ IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst _ _ = F ∧ IsPullUnif φ hD bc U₀ U₀' := by
  intro hL hL₂ hE R V _ _ _ _ _ I I' hR hV hI φ hφ hII D D' A A' G _ _ G' _ _ U U' U₀' F C hD hU' hβ hv hx
  obtain ⟨U₀, hU⟩ := (GlobalTheory.T.uniformisation_chart_value_forms_correspond hL hL₂ R I D A G U.semi).2.1 U
  obtain ⟨wL, hwL, ⟨he, hrig⟩, hlev⟩ := level_of_cmp hII U U' U₀ U₀'.toUnifPre hU hU' C hD hβ hv hx
  have hexp : ∀ k : ℕ, 1 ≤ k → U₀.ExpBij k := fun k hk =>
    expBij_descends hL hL₂ hR hV hφ hD U.semi U'.semi U₀ U₀' C.pb wL hwL hlev hk
      (exists_expandsAt hL hL₂ hE hR hI U U₀ hU k)
  obtain ⟨bc, hbc, hF⟩ := grpPullback_iso C.pb (isGrpPullback_pullback G (specOf φ))
  clear hβ hv hx C
  subst hF
  exact ⟨⟨U₀, hexp⟩, bc, hU, hbc, rfl,
    (isPullUnif_iff_stalks R V I I' φ D D' hD A A' G G' bc ⟨U₀, hexp⟩ U₀').2 ⟨wL, hwL, he, hrig, hlev⟩⟩

end GlobalTheory.UnifDescent
