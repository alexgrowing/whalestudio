import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RatTors
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteIsAlgClosedCExt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionCoordinatesEqDegenerationSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPointsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LiftValuationIntegralNormStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValuesStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespondStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTripleStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRigidifiedIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamilyFibreEqUniformisedPullbackGenericFibreStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLinearUniformisationBaseChangeAdmissibleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRExtensionTorsionRationalStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarisedAVIsoDescendsOfRationalThreeTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsomorphismValuesCocycleEqBundleIsoValueStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuesIsoCommActionAbelianPartTorsionStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolarizedAbelianPullbackLineBundleStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelIsoOfValuedAgreementOverFieldStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsMatchOfLevelGeFourStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TwistedLabelsAllLevelsOfFourLeStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionValuedFieldTwistedUniformisationStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LevelConditionOfOneAlgClosedFieldStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Trait

noncomputable section
namespace GlobalTheory.Ex.Trait

theorem exists_odd_prime (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ n : ℕ, n.Prime ∧ Odd n ∧ 3 ≤ n ∧ ‖(n : C)‖ = 1 := by
  by_cases h : ‖((3 : ℕ) : C)‖ = 1
  · exact ⟨3, Nat.prime_three, by decide, le_rfl, h⟩
  refine ⟨5, Nat.prime_five, by decide, by decide, ?_⟩
  by_contra h'
  have h3 := lt_of_le_of_ne (IsUltrametricDist.norm_natCast_le_one C 3) h
  have h5 := lt_of_le_of_ne (IsUltrametricDist.norm_natCast_le_one C 5) h'
  have e : (1 : C) = ((3 : ℕ) : C) + ((3 : ℕ) : C) + -((5 : ℕ) : C) := by push_cast; ring
  have := IsUltrametricDist.norm_add_le_max (((3 : ℕ) : C) + ((3 : ℕ) : C)) (-((5 : ℕ) : C))
  rw [← e, norm_one, norm_neg] at this
  have h6 := (IsUltrametricDist.norm_add_le_max ((3 : ℕ) : C) ((3 : ℕ) : C)).trans_lt (by rwa [max_self])
  exact absurd this (not_le.2 (max_lt h6 h5))

theorem admissible_base_of_complete_dvr {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.LN.CDvr V) :
    AdmBase V (IsLocalRing.maximalIdeal V) :=
  haveI := hV.1
  ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem mono_j {V : ValuationSubring c.F} (Y : Model Xo c V.subtype) : Mono Y.j := by
  have : IsPreimmersion (spMap V.subtype) :=
    IsPreimmersion.of_isLocalization (R := V) (S := c.F) (nonZeroDivisors V)
  have := Y.jQ_open
  unfold Model.j
  infer_instance

set_option maxHeartbeats 1000000 in

theorem hasArcData_of_model (hV : HV) (h6 : Laws6) (hU : GlobalTheory.LN.UDvrSt) (hH : GlobalTheory.LN.HomExtSt) (hT : ThetaPtDeterminesSt)
    (hE : EndDeterminedOnTorsionSt) (hTU : ThetaUnifAV) {W₀ : ValuationSubring ℂ} (Y : Model Xo c (c.V W₀).subtype)
    {O' : Type} [CommRing O'] [IsDomain O'] [CharZero O'] {b : c.V W₀ →+* O'} {ϖ : O'}
    (a : ArcIn D l (c.V W₀).subtype O' b) (hB : GlobalTheory.LN.ArcBase O' ϖ) {C : Type} [NontriviallyNormedField C]
    [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing O') C] (A : Lift a C)
    {u : Cˣ} {r : ℕ → Cˣ} {o : Full D C} (M : Mdl o) (f : O' →+* M.W) (u₀ : M.W) (hI : A.ν.IntN)
    (hR : Realises o A.arc A.be u r) (hu₁ : ‖(u : C)‖ < 1)
    (hu : (u : C) = algebraMap (FractionRing M.W) C (algebraMap _ _ u₀)) (hf : Along f C) {χ : Sp M.W ⟶ Y.X}
    (m : SABMap M.t Y.t χ) {y : Sp (FractionRing M.W) ⟶ Xo.XF c} (hy : y ≫ Y.j = jK M.W ≫ χ)
    {φ₀ : o.P.A.left ⟶ Y.oF.t.G.left}
    (hφ : M.φ ≫ M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W) ≫ m.φ = φ₀ ≫ Y.m.φ)
    (hA : ∀ v, (o.I.ev l.A v).left ≫ φ₀ = (jFK (R := M.W) C ≫ y) ≫ (Y.oF.etaA v).left)
    (hM : ∀ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      (o.I.ev l.M v).left ≫ φ₀ = (jFK (R := M.W) C ≫ y) ≫ (Y.oF.eta v).left)
    (t₁ : RatTors M.P.D.toPre.P C 3)
    (t₂ : ∀ (B : PolAV (Sp M.W)) ψ, IsGrpPullback B.A a.D₀.P.A (spMap f) ψ → RatTors B C 3) :
    Y.HasArcData a (IsLocalRing.maximalIdeal M.W) f u₀ χ := by
  letI := H.starRing
  have hLL := hV.1
  obtain ⟨hL, hL2, hL3, hL4, hL5⟩ := hV.1
  have hGt : BrGtSt := GlobalTheory.T.torus_torsion_points_correspond_values
  have : IsNoetherianRing O' := by
    rcases hB with h | h
    · letI := h.1.toField; infer_instance
    · have := h.1; infer_instance
  have := M.cdv.1
  have := M.cdv.2.2
  have tors := GlobalTheory.T.torsionIso_of_linear_uniformisation_triple hV.1 hV.2.1 hV.2.2.1 hV.2.2.2.1 hV.2.2.2.2 E H M.W _ (admissible_base_of_complete_dvr M.cdv) M.t M.P
  obtain ⟨n, hn, hno, hn3, hn1⟩ := exists_odd_prime C
  obtain ⟨N', ν', J, hlin, hlab, DW, _, oW, φ, he, w₀, e₀, νW, hm, -, hpt, Φ, wΦ, -, hΦ, hwΦ, hΦpt, -⟩ :=
    GlobalTheory.T.lift_valuation_integral_norm hV h6 hU hH hT hE hTU E H D l Xo c W₀ Y O' b ϖ a hB C A u r o M f u₀ hI hR.1 hu₁ hu hf n hn hno hn1
      fun j => ⟨hR.2.2.1 _ (pow_pos hn.pos j), fun p hp => (hR.2.2.2 _ hno.pow p hp).2.1⟩
  obtain ⟨Ψ, hΨ, lΨ, pΨ⟩ := GlobalTheory.T.polarisedAVIso_descends_of_rational_threeTorsion hL hL2 hH M.W M.cdv C DW.P M.P.D.toPre.P (t₂ _ _ hm.1) t₁ Φ
    (νW.eA.symm.trans (J.φ.trans ν'.eA))  hΦ
    (fun x => by obtain ⟨x, rfl⟩ := νW.eA.surjective x; simpa using hΦpt x) ⟨wΦ, hwΦ⟩
  set ψ := Ψ.hom.left ≫ φ with hψ
  have gψ : IsGrpPullback M.P.D.toPre.P.A a.D₀.P.A (spMap f) ψ :=
    ((isGrpPullback_of_iso Ψ).comp hm.1).congr (Category.id_comp _) rfl
  have lψ : LBIso M.P.D.toPre.P.L (a.D₀.P.L.pull ψ) :=
    LBIso.trans M.P.D.toPre.P.isLB (pull_isLB DW.P.isLB _) (pull_isLB a.D₀.P.isLB _) lΨ
      (LBIso.chartPull (Geo.Tor.chartPullPull DW.P.L _ _ rfl)
        (chartPullSame a.D₀.P.L _ (fun _ : PUnit => φ) _ Ψ.hom.left fun _ => rfl) ⟨w₀, hm.2.1⟩)
  have pψ : ∀ x : A.N.A, (ν'.eA (J.φ x)).left ≫ ψ = (A.ν.eA x).left := fun x => by
    have e : ν'.eA (J.φ x) ≫ Ψ.hom = νW.eA x :=
      (congrArg (fun z => ν'.eA (J.φ z) ≫ Ψ.hom) (νW.eA.symm_apply_apply x)).symm.trans (pΨ (νW.eA x))
    rw [hψ, ← Category.assoc, ← Over.comp_left]
    exact (congrArg (fun z => CommaMorphism.left z ≫ φ) e).trans (hpt x)
  have heψ := GlobalTheory.PolBaseChange.eSec_comm gψ
  obtain ⟨w, hw, hrig⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap f) a.D₀.P.A M.P.D.toPre.P.A ψ heψ
    ⟨a.D₀.P.L, a.D₀.rig, a.D₀.P.isLB, a.D₀.rig_gen⟩
    ⟨M.P.D.toPre.P.L, M.P.D.toPre.rig, M.P.D.toPre.P.isLB, M.P.D.toPre.rig_gen⟩ lψ
  let e : a.D₀.X ≃ₗ[𝓞 E] M.P.D.toPre.X :=
    { A.ν.eX.symm.trans (J.e.trans ν'.eX) with
      map_smul' := fun x y => by
        obtain ⟨y, rfl⟩ := A.ν.eX.surjective y
        exact (hlin x y).trans (congrArg (fun z => x • ν'.eX (J.e z)) (A.ν.eX.symm_apply_apply y).symm) }
  have fit : Fit A u M f ν' J ψ w e :=
    ⟨gψ, hw, pψ, fun y => congrArg (fun z => ν'.eX (J.e z)) (A.ν.eX.symm_apply_apply y),
      GlobalTheory.T.isomorphismValues_cocycle_eq_bundleIso_value hL hL2 M.W O' f _ _ C hf N' A.N ν' A.ν ψ w J.toIso gψ hw pψ⟩
  have act : ∀ x, (M.P.oD.onB.act x).left ≫ ψ = ψ ≫ (a.oa.onB.act x).left := fun x => by
    refine GlobalTheory.T.polarized_abelian_pullback_line_bundle hL hE E H M.W _ _ _ _ M.P.oD.onB a.oa.onB ψ gψ lψ C n hn.two_le x fun j z hz => ?_
    obtain ⟨z, rfl⟩ := (J.φ.trans ν'.eA).surjective z
    have hz' : (z : A.N.A) ^ n ^ j = 1 := (J.φ.trans ν'.eA).injective (by rw [map_pow, map_one]; exact hz)
    have e₁ := GlobalTheory.T.valuesIso_comm_action_abelianPart_torsion hLL hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors _ (pow_pos hn.pos j) (hlab j) hlin x z
      (A.ν.eA.symm (A.ν.eA z ≫ a.oa.onB.act x)) hz' (A.ν.eA.apply_symm_apply _)
    refine (congrArg (fun z => CommaMorphism.left z ≫ ψ) e₁.symm).trans ((pψ _).trans ?_)
    rw [MulEquiv.apply_symm_apply, Over.comp_left]
    exact (congrArg (· ≫ _) (pψ z).symm).trans (Category.assoc _ _ _)
  obtain ⟨s₁, s₂, s₃, s₄, s₅, s₆⟩ := GlobalTheory.T.modelIso_of_valued_agreement_over_field hLL E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf u₀ hu ψ heψ w e fit hrig act
  have lab := GlobalTheory.T.twistedLabels_all_levels_of_four_le hLL hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors
    (GlobalTheory.T.twistedLabels_match_of_level_ge_four hLL (GlobalTheory.T.torsionCoordinates_eq_degenerationSeries hV hGt (GlobalTheory.T.families_values_correspond hL hL2)) hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors
      hR n hno hn3 (hlab 2))
  refine ⟨M.t, m, M.P, ψ, heψ, w, e, s₁, s₂, s₃, s₄, s₅, fun F _ _ _ _ uF hF huF => ⟨s₆ F uF hF huF, ?_⟩⟩
  intro yF hyF k p₀ σ hσ q₀ q x h₀ hq hg hx
  have := mono_j Y
  obtain rfl : yF = jFK (R := M.W) F ≫ y := by rw [← cancel_mono Y.j, hyF, Category.assoc, hy]
  obtain ⟨hk, hkM, v, hv, hev⟩ : 0 < k ∧ k ∣ l.M' ∧ ∃ v, (∀ p, QkExt (algebraMap _ C) p₀ p → QkPt.Equiv a.D₀ C p (A.I.ev k v)) ∧
      (o.I.ev k v).left ≫ φ₀ = (jFK (R := M.W) C ≫ y) ≫ σ.left := by
    rcases hσ with ⟨rfl, v, h, rfl⟩ | ⟨rfl, v, hv, h, rfl⟩
    · obtain rfl := eq_of_heq h
      exact ⟨l.A_pos, Nat.dvd_lcm_right _ _, v, A.levA v, hA v⟩
    · obtain rfl := eq_of_heq h
      exact ⟨l.odd.pos, Nat.dvd_lcm_left _ _, v, A.levM v hv, hM v hv⟩
  have := M.P.U.gen_hom
  have gp : IsPullback (M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W) ≫ m.φ) M.P.A.A.hom Y.t.G.hom (jK M.W ≫ χ) := by
    have : IsMonHom M.P.U.gen.symm.hom := by show IsMonHom M.P.U.gen.inv; infer_instance
    exact (((isGrpPullback_of_iso M.P.U.gen.symm).comp ((isGrpPullback_pullback M.t.G (jK M.W)).comp m.cart)).congr
      (Category.id_comp _) rfl).1
  have hσw : (y ≫ σ.left ≫ Y.m.φ) ≫ Y.t.G.hom = 𝟙 _ ≫ jK M.W ≫ χ := by
    have e₁ : σ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w σ
    rw [Category.assoc, Category.assoc, Y.m.cart.1.w, reassoc_of% e₁, Category.id_comp, ← hy]; rfl
  let x₀ := gp.lift _ _ hσw
  have hx₀ : ∀ (K : Type) [Field K] [Algebra (FractionRing M.W) K] (z : Sp K ⟶ M.P.A.A.left),
      z ≫ M.P.A.A.hom = jFK (R := M.W) K → z ≫ M.P.U.gen.inv.left ≫ pullback.fst M.t.G.hom (jK M.W) ≫ m.φ =
        (jFK (R := M.W) K ≫ y) ≫ σ.left ≫ Y.m.φ → z = jFK (R := M.W) K ≫ x₀ := fun K _ _ z h₁ h₂ => by
    apply gp.hom_ext
    · rw [h₂, Category.assoc, Category.assoc (jFK (R := M.W) K), gp.lift_fst]
    · rw [h₁, Category.assoc, gp.lift_snd]; exact (Category.comp_id _).symm
  have hzw : ((o.I.ev k v).left ≫ M.φ) ≫ M.P.A.A.hom = jFK (R := M.W) C := by
    have e₁ : (o.I.ev k v).left ≫ o.P.A.hom = 𝟙 _ := Over.w _
    rw [Category.assoc, M.cart.1.w, reassoc_of% e₁]
  obtain ⟨q₁, q₂, a₁, a₂, a₃, a₄⟩ := GlobalTheory.T.levelCondition_valuedField_twistedUniformisation hLL hGt E H D l c _ _ O' b a C A u r o M f N' ν' J hR.1 hf tors ψ w e fit k hk hkM
    (lab k hk) p₀ v hv (Over.homMk ((o.I.ev k v).left ≫ M.φ) hzw) rfl
  refine GlobalTheory.T.levelCondition_of_one_algClosed_field hLL E H M.W O' _ (admissible_base_of_complete_dvr M.cdv) M.t M.P a.D₀ a.bimult f ψ w e.toAddEquiv s₁ s₂ k hk p₀
    (fun z => algebraMap M.W _ u₀ ^ (a.be p₀.y z / k)) x₀ C hf q₁ q₂ _ a₁ a₂ (fun z => ?_) ?_ a₄ F (fun x => (hF x).symm) q₀ q x
    h₀ hq (fun z => ?_) (hx₀ F _ (Over.w x) hx)
  · rw [map_zpow₀, ← hu, ← a₁.1]; exact a₃ z
  · refine hx₀ C _ hzw ?_
    change ((o.I.ev k v).left ≫ M.φ) ≫ _ = _
    rw [Category.assoc, hφ, ← Category.assoc, hev, Category.assoc]
  · rw [map_zpow₀, ← huF, ← h₀.1]; exact hg z

theorem eq_of_generic {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {R : Type} [CommRing R] [IsDomain R]
    (C : Type) [Field C] [Algebra (FractionRing R) C] {x x' : Sp R ⟶ Y.X}
    (h : jFK (R := R) C ≫ jK R ≫ x = jFK (R := R) C ≫ jK R ≫ x') : x = x' := by
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by rw [← terminal.comp_from Y.s]; infer_instance⟩
  have : IsDominant (spMap ((algebraMap (FractionRing R) C).comp (algebraMap R _))) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (((RingHom.injective_iff_ker_eq_bot ((algebraMap (FractionRing R) C).comp (algebraMap R _))).1
      ((algebraMap (FractionRing R) C).injective.comp (IsFractionRing.injective R (FractionRing R)))).trans_le bot_le)⟩
  refine ext_of_isDominant (spMap ((algebraMap (FractionRing R) C).comp (algebraMap R _))) ?_
  rw [spMap_comp, Category.assoc, Category.assoc]
  exact h

theorem hasArcData_at_trait : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllA fun {E} _ _ _ {H} {D} {l} {Xo} {c} {W₀} Y {O'} _ _ {b} a => ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (g : PowerSeries O' →+* R₁) (y₁ : Sp (FractionRing R₁) ⟶ Xo.XF c), Function.Injective g → g.Finite → IsIntegrallyClosed R₁ → RealAt Y a g y₁ → y₁ ≫ Y.j ≫ Y.s = jK R₁ ≫ spMap g ≫ spMap (PowerSeries.C (R := O')) ≫ spMap b → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (φ : R₁ →+* W) (gam : FractionRing R₁ →+* FractionRing W), (∀ r, gam (algebraMap R₁ _ r) = algebraMap W _ (φ r)) → ∀ χ : Sp W ⟶ Y.X, spMap gam ≫ y₁ ≫ Y.j = jK W ≫ χ → ¬ IsUnit (φ (g PowerSeries.X)) → ∃ (W' : Type) (_ : CommRing W') (_ : IsDomain W') (_ : IsLocalRing W') (io : W →+* W'), GlobalTheory.LN.CDvr W' ∧ Function.Injective io ∧ io.Finite ∧ Y.HasArcData a (IsLocalRing.maximalIdeal W') (io.comp (φ.comp (g.comp (PowerSeries.C (R := O'))))) (io (φ (g PowerSeries.X))) (spMap io ≫ χ) := by
  intro hV h6 hU hH hT hE hTU E _ _ _ H D l Xo c W₀ Y O' _ _ _ b ϖ a hB R₁ _ _ g y₁ hg _ _ hR hs W _ _ _ hW φ gam hgam χ hχ hu
  obtain ⟨hL, hL2, hL3, hL4, hL5⟩ := hV.1
  have := hW.1
  have := hW.2.2
  have hφ : Function.Injective φ := fun x y h => IsFractionRing.injective R₁ (FractionRing R₁) (gam.injective (by
    rw [hgam, hgam, h]))
  obtain ⟨C, _, _, _, _, _, -, -, hext⟩ := exists_complete_isAlgClosed_cExt W (FractionRing W)
  have : CharZero C := charZero_of_injective_ringHom (algebraMap (FractionRing W) C).injective
  set f₀ := φ.comp (g.comp (PowerSeries.C (R := O'))) with hf₀
  have inj₀ : Function.Injective f₀ := hφ.comp (hg.comp PowerSeries.C_injective)
  have injW : Function.Injective ((algebraMap (FractionRing W) C).comp (algebraMap W _)) :=
    (algebraMap (FractionRing W) C).injective.comp (IsFractionRing.injective W _)
  have injC : Function.Injective (((algebraMap (FractionRing W) C).comp (algebraMap W _)).comp f₀) := injW.comp inj₀
  letI : Algebra (FractionRing O') C := (IsFractionRing.lift (K := FractionRing O') injC).toAlgebra
  have al₀ : Along f₀ C := fun x => (IsFractionRing.lift_algebraMap injC x).symm
  have hu0 : algebraMap (FractionRing W) C (algebraMap W _ (φ (g PowerSeries.X))) ≠ 0 := fun h =>
    PowerSeries.X_ne_zero (hg (hφ (injW (h.trans (by simp)))))
  have hu1 := hext.2 _ ((IsLocalRing.mem_maximalIdeal _).2 hu)
  obtain ⟨A, r, o, hI, -, hF, hRe⟩ := hR.2 C ((algebraMap (FractionRing W) C).comp gam) (Units.mk0 _ hu0)
    (fun x => (al₀ x).symm.trans (congrArg _ (hgam _).symm)) (fun x => by
      rw [RingHom.comp_apply, hgam]; exact hext.1 _) (congrArg _ (hgam _).symm) hu1
  rw [spMap_comp, Category.assoc] at hF
  have sq : spMap gam ≫ jK R₁ = jK W ≫ spMap φ :=
    (spMap_comp _ gam).symm.trans ((congrArg spMap (RingHom.ext hgam)).trans (spMap_comp φ _))
  obtain ⟨M, f₁, χ₁, m₁, fin₁, al₁, hχ₁, -⟩ := GlobalTheory.T.moduli_model_ultrametric_points hV h6 hU hH hT hE hTU E H D l Xo c W₀ Y C W hW hext
    (FractionRing W) (algebraMap _ C) (fun _ => rfl) (spMap gam ≫ y₁) (f₀.comp b) (by
      have e : spMap (algebraMap (FractionRing W) (FractionRing W)) = 𝟙 _ := Spec.map_id _
      rw [e, Category.id_comp, Category.assoc, hs, reassoc_of% sq, hf₀, spMap_comp, spMap_comp, spMap_comp]
      simp only [Category.assoc]) o hF
  have inj₁ : Function.Injective f₁ := fun x y h => injW ((al₁ x).symm.trans (h ▸ al₁ y))
  obtain ⟨W₂, _, _, _, _, io, hW₂, inj₂, fin₂, loc₂, al₂, ext₂, t₁, t₂⟩ := GlobalTheory.T.exists_completeDVR_extension_torsion_rational hL M.W M.cdv C M.ext 3 (by decide)
    _ _ (𝟙 _) (spMap (f₁.comp f₀)) M.P.D.toPre.P a.D₀.P
  have := hW₂.1
  have := hW₂.2.2
  obtain ⟨t, m₀, P, ψ, gψ⟩ := GlobalTheory.T.exists_linearUniformisation_baseChange_admissible hL hL3 hL4 hL5 E H M.W W₂ _ _ (admissible_base_of_complete_dvr M.cdv) (admissible_base_of_complete_dvr hW₂) io inj₂
    (Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit io x hx) M.t M.P
  obtain ⟨m, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m₀
  have al : Along (io.comp f₁) C := fun x => (al₂ _).trans (al₁ x)
  have inj : Function.Injective ((algebraMap W₂ (FractionRing W₂)).comp (io.comp f₁)) :=
    (IsFractionRing.injective W₂ _).comp (inj₂.comp inj₁)
  let δ : FractionRing W →+* FractionRing W₂ := IsFractionRing.lift inj
  have hδ : ∀ x, δ (algebraMap W _ x) = algebraMap W₂ _ (io (f₁ x)) := IsFractionRing.lift_algebraMap inj
  have sq₂ : spMap δ ≫ jK W = jK W₂ ≫ spMap (io.comp f₁) :=
    (spMap_comp _ δ).symm.trans ((congrArg spMap (RingHom.ext hδ)).trans (spMap_comp _ _))
  have jδ : jFK (R := W₂) C ≫ spMap δ = spMap (algebraMap (FractionRing W) C) :=
    (spMap_comp δ _).symm.trans (congrArg spMap (IsLocalization.ringHom_ext (nonZeroDivisors W) (RingHom.ext fun x =>
      (congrArg (algebraMap (FractionRing W₂) C) (hδ x)).trans (al x))))
  have jio : jFK (R := W₂) C ≫ jK W₂ ≫ spMap io = jFK (R := M.W) C ≫ jK M.W :=
    ((congrArg (_ ≫ ·) (spMap_comp _ _).symm).trans (spMap_comp _ _).symm).trans
      ((congrArg spMap (RingHom.ext fun x => al₂ x)).trans (spMap_comp _ _))
  have hy : (spMap δ ≫ spMap gam ≫ y₁) ≫ Y.j = jK W₂ ≫ spMap (io.comp f₁) ≫ χ := by
    rw [Category.assoc, Category.assoc, hχ, reassoc_of% sq₂]
  have eχ : spMap io ≫ χ₁ = spMap (io.comp f₁) ≫ χ := by
    refine eq_of_generic Y C ?_
    rw [← hy, reassoc_of% jio, hχ₁, Category.assoc (spMap δ), reassoc_of% jδ]
  obtain ⟨φ₀, g₀, l₀, a₀, hA, hM, -⟩ := hF
  have ey : spMap (algebraMap (FractionRing W) C) ≫ spMap gam ≫ y₁ = jFK (R := W₂) C ≫ spMap δ ≫ spMap gam ≫ y₁ := by
    rw [reassoc_of% jδ]
  rw [ey] at g₀ hA hM
  rw [← eχ] at hy
  obtain ⟨φ₂, g₂, l₂, a₂, e₂⟩ := GlobalTheory.T.family_fibre_eq_uniformised_pullback_generic_fibre E H D l Xo c _ _ Y W₂ _ t _ m P C _ (by rw [Category.assoc, hy]) o φ₀ g₀ l₀ a₀
  let M₂ : Mdl o := ⟨W₂, hW₂, ext₂, t, P, φ₂, g₂, l₂, a₂⟩
  refine ⟨W₂, _, _, _, io.comp f₁, hW₂, inj₂.comp inj₁, fin₂.comp fin₁, ?_⟩
  rw [← eχ]
  exact hasArcData_of_model hV h6 hU hH hT hE hTU Y a hB A M₂ ((io.comp f₁).comp f₀) _ hI hRe hu1 (al _).symm
    (fun x => (al _).trans (al₀ x)) m hy e₂ hA hM (t₁ _ ψ (gψ.congr (Category.comp_id _).symm rfl))
    fun B ψ' h => t₂ B ψ' (h.congr (spMap_comp (f₁.comp f₀) io) rfl)

end GlobalTheory.Ex.Trait
end
