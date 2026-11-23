import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LocalComponentAtPlaceDetermined
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EvLgGFieldOfSmallField
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RationalSeriesCoeffAtState
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalTupleAtState
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelCharAllStStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalFixedPointAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalTupleAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalConjExpansionAtPlace
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.HeightCounting.Up (PrN)
namespace GlobalTheory.PlaceRead
variable {D : D7} {c : NChoice D} {w : D.what₂.places.Pl}
variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}
end GlobalTheory.PlaceRead
namespace GlobalTheory.PlaceRead
variable {D : D7} {X : RealSide D} {X0 : BaseLevelRowSide D} {Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0} {S : NX.RatDat D.ntw}
  {YS : NX.NExpRealS X.R X.cG S} {Z : ExportTie YS X.geo.v₀} {c : NChoice D} {w : D.what₂.places.Pl} {j : Fin D.R.m}
theorem exists_local_component_at_place_alt (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (H : AtPlace Y Z c w j) {ε : KE c w →+* ℂ} (hε : Extends Z.ρ ε) :
    ∃ (Ψ : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[ε.comp (c.embW w)] Amb D j) (N : ℕ) (z₁ : ℂ),
      (∀ (I : Type) (b : I → D.what₂.MtL (D.what₂.muTw w) (j.1 + 1)),
        LinearIndependent ℂ (fun k => D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) (b k)) → LinearIndependent ℂ fun k => Ψ (b k)) ∧
      ((baseOf Z c w j).mtLat (embLL0 D) (labLL0 D) (ringOf ε) (twVia Z.ρ ε) : Set (Amb D j)) =
        Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)) ∧
      IsUnit (N : c.Oe w) ∧ UnitOff N z₁ ∧
      ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
        (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
          Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
        (baseOf Z c w j).classSum (Z.ρ.om (c.twI w) j (c.sd w) (twVia Z.ρ ε).chi) (twVia Z.ρ ε)
          (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) (Ψ x) =
          z₁ • (Z.ν (c.twI w) j (c.sd w))⁻¹ • ∑ k, ε (c.embW w (a k)) • evW YS X.geo.v₀ j (f k).val := by
  obtain ⟨τ, hτ0⟩ := GlobalTheory.BigOn.Exp.TwConj.exists_aut_on D.what₂.embLL (ε.comp (c.embW w))
    (GlobalTheory.BigOn.Exp.TwConj.countable_alg D.what₂.embLL)
  have hτ : ∀ x, τ (D.what₂.embLL x) = ε (c.embW w x) := fun x =>
    hτ0 x ((Algebra.IsAlgebraic.isAlgebraic x).algHom D.what₂.embLL.toRatAlgHom)
  have hfix : ∀ a, τ (embLL0 D a) = embLL0 D a := fun a => (hτ a).trans (H.emb ε hε a)
  obtain ⟨ι, hιε⟩ : ∃ ι : KE c w →+* ℂ, (τ : ℂ →+* ℂ).comp ι = ε :=
    ⟨(τ.symm : ℂ →+* ℂ).comp ε, RingHom.ext fun y => τ.apply_symm_apply _⟩
  have hι : ∀ x, ι (c.embW w x) = D.what₂.embLL x := fun x => τ.injective ((RingHom.congr_fun hιε _).trans (hτ x).symm)
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo : BaseOf X.R.toRealDat j (baseOf Z c w j) :=
    GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  obtain ⟨hg, ha, hcc⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ι
  obtain ⟨hg', ha', -⟩ := GlobalTheory.T.chosen_twist_via_embedding_good_conjugate D c w Z.ρ Z.good H.ok j ε
  have hcj : ConjChar τ (twVia Z.ρ ι) (twVia Z.ρ ε) := hιε ▸ hcc τ
  obtain ⟨u, cc, κ, hu, hc, hκ, hval, hfn, hs, hν⟩ := GlobalTheory.T.exists_scale_twisted_place_coefficient_map D X X0 Y S YS Z c w j H
  obtain ⟨hfb, hfd⟩ := _root_.GlobalTheory.T.local_fixed_point_of_third_layer hP D X X0 Y S YS Z c w j H τ hfix
  obtain ⟨C, hC1, hC2⟩ := GlobalTheory.T.conjugation_scaled_coords_integral_forms_twist D j _ hB hBo.lam (X.R.ioP j (PiTensorProduct.tprod ℂ u) ∘ₗ cc) κ hκ hval hfn τ hfix _ _ hg hg' hcj hfd
  have hω := Z.good.weil (c.twI w) j (c.sd w) _ hg
  have hω' := Z.good.weil (c.twI w) j (c.sd w) _ hg'
  have hcl' := Z.good.classes (c.twI w) j (c.sd w) _ hg' ha'
  have hcl : IsClassSystem (Vc D j) ((baseOf Z c w j).levJ (twVia Z.ρ ι)) (Z.ρ.rep (c.twI w) j (c.sd w) (twVia Z.ρ ε)) := by
    rw [← levJ_congr (baseOf Z c w j) hcj.1]
    exact hcl'
  refine (GlobalTheory.T.thetaLift_twistLevelForm_eq_unit_mul_classSum D X j _ hB hBo _ _ hg ha (H.tup ι hι) _ hω _ _ hcl u).elim fun z hz => hz.elim fun a₀ hz => ?_
  obtain ⟨hz, ha₀, hth⟩ := hz
  refine (GlobalTheory.T.classSums_conjugate_twists_conjugate_expansions D X j _ hB _ _ hg hg' ha (_root_.GlobalTheory.T.exists_local_tuple_of_discrete_series_read hCo hCW hHM hP D X X0 Y S YS Z c w j H ι hι τ hfix _ hg' hcj) u cc κ hu hc hκ τ hfb hfd
    hcj _ _ hω hω').elim fun ζ hζ => ?_
  obtain ⟨hζ, hcs⟩ := hζ
  obtain ⟨hinj, hrange⟩ := GlobalTheory.T.definiteComplexForms_eq_twistComplexForms_fockModel D X X0 Y S YS Z c w j H ι hι u hu
  have hmem : ∀ y, fockOf Y (used_of_tw H.tw) j u y ∈ (baseOf Z c w j).formsC (twVia Z.ρ ι) := fun y =>
    hrange.le (LinearMap.mem_range_self _ y)
  have hΦv : ∀ y h, trOf H u κ z y h ∈ (baseOf Z c w j).valSpace := fun y h =>
    Submodule.smul_mem _ κ⁻¹ (((baseOf Z c w j).mem_formsC.1 (hmem y)).1 _)
  have hN := (GlobalTheory.T.isUnit_primeProduct_of_twistedPlaceTuple D X X0 Y S YS Z c w j H ι hι).2.2
  refine ⟨semiComp τ (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1)) (trOf H u κ z) C (ε.comp (c.embW w)) hτ, _, _, fun I b hb => ?_, ?_, hN, unitOff_conj τ ha₀ hζ hν, fun x hx n a f hf => ?_⟩
  · exact indep_conj τ (trOf H u κ z) C (fun y hy => trOf_eq_zero H hκ hinj y ((hC1 _ (hΦv y)).2 hy)) hb
  · have e1 : (ringOf ι).map (τ : ℂ →+* ℂ) = ringOf ε := by
      rw [← hιε, ringOf, ringOf, RingHom.map_range, RingHom.comp_assoc]
    have e2 := hC2 _ (coefficient_ring_of_integral_le (intLL_le hι))
    rw [e1] at e2
    exact span_conj H hι hιε hu hκ hs hz C _ e2
  · have h1 := expansion_eq H hu hκ ha₀.1 _ hx (hth _ (hmem (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))) hf
    have h2 := _root_.GlobalTheory.T.local_conj_expansion_of_third_layer hP D X X0 Y S YS Z c w j H τ hfix ζ _ _
      (hcs _ _ hcl'.fin _ _ (hC1 _ (hΦv (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x))).1) n _ f h1
    exact rescale_conj τ hκ (Z.scalar (c.twI w) j (c.sd w)).ne (fun k => hτ (a k)) h2
theorem exists_basisAt_latAt_thetaAt_of_atPlace (hCo : GlobalTheory.Published.DiscreteSeriesCover) (hCW : GlobalTheory.Published.CasselmanWallach) (hHM : GlobalTheory.Published.HarishChandraModules) (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (H : AtPlace Y Z c w j) :
    ∃ (e : D.what₂.MtL (D.what₂.muTw w) (j.1 + 1) →ₛₗ[c.embW w] Tgt c w (j.1 + 1)) (u : (FractionRing (c.Oe w))ˣ),
      BasisAt c w (j.1 + 1) e ∧ LatAt c w (j.1 + 1) e (u : FractionRing (c.Oe w)) ∧ ThetaAt Y YS c w j e (u : FractionRing (c.Oe w)) := by
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField D c w Z.ρ Z.good).1
  refine (_root_.GlobalTheory.PlaceRead.exists_local_component_at_place_alt hCo hCW hHM hP H hε).elim fun Ψ h => h.elim fun N h => h.elim fun z₁ h => ?_
  obtain ⟨hind, hlat, hN, hz, hth⟩ := h
  obtain ⟨hinj, hmt⟩ := GlobalTheory.T.definiteFormReading_injective_lattice_integralForms D c w Z.ρ Z.good j _ (Z.tie (c.twI w) j (c.sd w)) ε hε H.ok H.field.roots
  have hsub : ∀ F ∈ Submodule.span (ringOf ε) (Ψ '' latS w (j.1 + 1)), ∃ y ∈ latT c w (j.1 + 1),
      rdE (Z.tie (c.twI w) j (c.sd w)) hε y = F := fun F hF => (hmt F).1 (hlat.ge hF)
  obtain ⟨e, he⟩ := exists_lift (c.embW w) ε _ hinj Ψ (GlobalTheory.T.rationalLatticeTwistedTuple_span_top D w (j.1 + 1)) fun x hx =>
    (hsub _ (Submodule.subset_span ⟨x, hx, rfl⟩)).imp fun _ h => h.2
  have hL : Submodule.span (c.Oe w) (e '' latS w (j.1 + 1)) = latT c w (j.1 + 1) := by
    have h1 := image_span (ε.comp (algebraMap (c.Oe w) (KE c w))) (ringOf ε) rfl
      (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom
      (fun r v => (congrArg _ (algebraMap_smul (KE c w) r v).symm).trans ((rdE (Z.tie (c.twI w) j (c.sd w)) hε).map_smulₛₗ _ v)) (e '' latS w (j.1 + 1))
    have h2 : (rdE (Z.tie (c.twI w) j (c.sd w)) hε).toAddMonoidHom '' (e '' latS w (j.1 + 1)) = Ψ '' latS w (j.1 + 1) := by
      rw [Set.image_image]
      exact Set.image_congr fun x _ => he x
    rw [h2] at h1
    refine le_antisymm (fun y hy => ?_) fun y hy => ?_
    · obtain ⟨y', hy', e1⟩ := hsub _ (h1.le ⟨y, hy, rfl⟩)
      exact hinj e1 ▸ hy'
    · obtain ⟨y', hy', e1⟩ := h1.ge (hlat.le ((hmt _).2 ⟨y, hy, rfl⟩))
      exact hinj e1 ▸ hy'
  have hb : BasisAt c w (j.1 + 1) e := fun b => by
    refine ⟨indep_of_read ε (rdE (Z.tie (c.twI w) j (c.sd w)) hε) ?_, top_unique ?_⟩
    · simp only [he]
      exact hind _ b (D.what₂.jMt_basis _ _ b).1
    · rw [← span_latT, ← hL]
      refine Submodule.span_le.2 fun y hy => ?_
      refine (Submodule.span_le (p := (Submodule.span (KE c w) (Set.range fun i => e (b i))).restrictScalars (c.Oe w))).2 ?_ hy
      rintro _ ⟨x, -, rfl⟩
      exact mem_span_basis e b x
  have hfa : Faithful (Z.rd (c.twI w) j (c.sd w)) :=
    GlobalTheory.SeriesTie.realRd_faithful _ _ _ _ _ _ _ X.R X.cG S YS X.geo.v₀ Z.ρ Z.good _ j _ _ (Z.scalar _ j _).ne X.unif
      X.char.models.HW (Z.vec j) H.ks
  have hrat := GlobalTheory.T.class_sums_twisted_definite_forms_rational D Z.ρ Z.good _ j _ _ (Z.tie (c.twI w) j (c.sd w)) (Z.rat H.rat).2.1 H.field.roots _ _ _ H.ok H.cls
  have key : ∀ x ∈ Idx.TjV D (D.what₂.muTw w) (j.1 + 1), ∀ (n : ℕ) (a : Fin n → D.what₂.LL) (f : Fin n → NX.FmK S (j.1 + 1)),
      (X.R.FW j).j (sg0 D X.A3.A) ((YS.fi j).e (∑ k, a k • (f k).val)) =
        Y.mj.eW j (D.what₂.thetaP (D.what₂.muTw w) (j.1 + 1) (D.what₂.jMt (D.what₂.muTw w) (j.1 + 1) x)) →
      rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (NChoice.thPe D c w (j.1 + 1) (e x)) =
        z₁ • rdF (Z.rd (c.twI w) j (c.sd w)) Z.good hε (∑ k, c.embW w (a k) ⊗ₜ[D.ntw.O (c.twI w)]
          (YS.eF (c.twI w) (j.1 + 1) (c.sd w) (Nat.le_add_left _ _) j.2).symm ((1 : NX.KB S (c.twI w) (c.sd w)) ⊗ₜ[S.Ks] f k)) := by
    intro x hx n a f hf
    have h1 := hth x hx n a f hf
    rw [hε.twVia_eq] at h1
    refine (rdF_thPe _ hε H.ok hrat _).trans ((congrArg _ (he x)).trans (h1.trans (congrArg (z₁ • ·) ?_)))
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [rdF_tmul, smul_comm]
    refine congrArg (ε (c.embW w (a k)) • ·) ?_
    refine Eq.trans ?_ (realRd_tmul YS X.geo.v₀ Z.good (c.twI w) j (c.sd w) _ 1 (f k)).symm
    rw [show Z.ρ.e (c.twI w) (c.sd w) (1 : NX.KB S (c.twI w) (c.sd w)) = 1 from map_one _, mul_one]
  have hco := fun x hx n a f hf => GlobalTheory.T.chosenField_forms_proportional_of_readings D c w Z.ρ Z.good j _ hfa ε hε _ _ z₁ (key x hx n a f hf)
  obtain ⟨o, ho⟩ : ∃ o : (c.Oe w)ˣ, ThetaAt Y YS c w j e (algebraMap (c.Oe w) (KE c w) o) := by
    by_cases hex : ∃ t : KE c w, ε t = z₁
    · obtain ⟨t, ht⟩ := hex
      obtain ⟨o, rfl⟩ := GlobalTheory.T.exists_integral_unit_of_isUnitAwayFromLevel_embedding (c.Oe w) ε N t hN (ht ▸ hz)
      refine ⟨o, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', e1⟩ := h1 hB
      exact e1.trans (congrArg (· • _) (ε.injective (ht'.trans ht.symm)))
    · refine ⟨1, fun x hx n a f hf => ?_⟩
      obtain ⟨h0, h1⟩ := hco x hx n a f hf
      refine (Classical.em _).elim (fun hB => (h0 hB).trans ((smul_zero _).symm.trans (congrArg _ hB.symm))) fun hB => ?_
      obtain ⟨t', ht', -⟩ := h1 hB
      exact absurd ⟨t', ht'⟩ hex
  exact ⟨e, Units.map (algebraMap (c.Oe w) (KE c w)).toMonoidHom o, hb, hL.trans (span_smul_latT _ o).symm, ho⟩
end GlobalTheory.PlaceRead
namespace GlobalTheory.PlaceRead
open Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
theorem exists_local_map_at_place_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∀ v, TwistedAt (Dof x) v → ∀ i : Fin (Dof x).R.m, ∃ (e : (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1)) (u : (FractionRing (ch.Oe v))ˣ), GlobalTheory.ChoiceRead.BasisAt ch v (i.1 + 1) e ∧ GlobalTheory.ChoiceRead.LatAt ch v (i.1 + 1) e (u : FractionRing (ch.Oe v)) ∧ GlobalTheory.ChoiceRead.ThetaAt x.r.Y l.b.YS ch v i e (u : FractionRing (ch.Oe v)) := by
  intro hCo hCW hHM hP hS hL
  have ev : ∀ {Q : Ctx → Prop}, Ev Q → StepW Start fun K _ _ _ _ => Q K := fun h =>
    Step.of_evG ((evG_of_ev h).imp fun _ _ _ _ _ H _ _ _ _ _ _ _ _ _ => H)
  have hF : StepW Start fun _ _ _ _ w => ∀ (Z : w.Lt) (X : RealSide (w.st Z).toD7), X.R.C = TC.cf w.I w.l Z → FieldOk X :=
    EvG.imp (_root_.GlobalTheory.TwInputs.SmallField.fieldOk_and_exists_lamDat_ok_teich_valuesIn hP) fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp _ _ w _ Z => (H kp T w Z).1
  refine (((((_root_.GlobalTheory.T.ratRow_of_levelB2_nonzero_index hP hS hL).and (_root_.GlobalTheory.T.clsQ_of_choiceSide_twOK_at_state hP hL)).and (_root_.GlobalTheory.T.series_character_eq_inv_emb_psi0 hL)).and hF).and
    ((ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev).and (ev GlobalTheory.Mem.StdSize.vstd_size_ev))).trans
    (StepW.of_all fun K B f T w hO _ H P x => ?_)
  intro l ch tp hxi hpsi hQ hk hside hok v hv i
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6⟩ := H
  obtain ⟨hHo, -⟩ := h5 (w.st x.o.Z) hO
  obtain ⟨hStd, hSize⟩ := h6 (w.st x.o.Z) hO
  let X := RealSide.ofPins x.m.z.geo x.m.z.pins x.m.intersectionNumber_baseChange x.m.inGeo (Finite.of_injective _ (ixOf_injective w.I _)) hHo hStd hSize
  have hf : FieldOk X := h4 x.o.Z X x.m.z.lev.C
  obtain ⟨k1, k2⟩ := h2 P x l ch tp hxi hpsi hQ hk hside v hv (hok v hv)
  obtain ⟨k3, k4⟩ := h3 P x l
  obtain ⟨ψ0, -, k5, -⟩ := hside.nct.psi_eq
  exact _root_.GlobalTheory.PlaceRead.exists_basisAt_latAt_thetaAt_of_atPlace (X := X) (Y := x.r.Y) (YS := l.b.YS) (Z := l.b.ser.ex) hCo hCW hHM hP
    { pins := x.m.z.pins, intersectionNumber_baseChange := x.m.intersectionNumber_baseChange, field := hf, tw := hv, ok := hok v hv, cls := k1
      emb := (GlobalTheory.T.exists_extension_complexDataEmbedding_restrict_coeffField _ ch v _ l.b.ser.ex.good).2 hside.nct
      val := fun σ => ⟨_, (k5 v σ).trans (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
      U_eq := k3, psi_eq := k4, ks := l.rat.In.ks _ (Nat.le_add_left _ _) i.2
      rat := h1 P x l _ (GlobalTheory.Mem.Top.twistedPlaceIndex_mem_firstPair_of_compatibleChoice _ ch hside.nct hf.galois v hv) i _
      tup := k2 i }
end GlobalTheory.PlaceRead
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_at_place_determined_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ T w P x => ∀ (l : _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevel hL x) (ch : NChoice (Dof x)) (tp : TupTied (Dof x) (cfOf x) ch), tp.xi = w.I.xi → tp.psi = T.psi → ch.Q = QOf P → (∀ v, TwistedAt (Dof x) v → ch.k' v = T.k v) → ChoiceSide (Dof x) (cfOf x) l.mt.M l.b.Bs.exp ch tp → (∀ v, TwistedAt (Dof x) v → IntegralHeckeForms.TwOK (ch.twI v) (ch.k' v) (ch.Q v) ((ch.psi' v).comp ((Dof x).ntw.art (ch.twI v) (ch.Q v)))) → ∀ v, TwistedAt (Dof x) v → ∀ i : Fin (Dof x).R.m, ∃ (e : (Dof x).what₂.MtL ((Dof x).what₂.muTw v) (i.1 + 1) →ₛₗ[ch.embW v] GlobalTheory.ChoiceRead.Tgt ch v (i.1 + 1)) (u : (FractionRing (ch.Oe v))ˣ), GlobalTheory.ChoiceRead.BasisAt ch v (i.1 + 1) e ∧ GlobalTheory.ChoiceRead.LatAt ch v (i.1 + 1) e (u : FractionRing (ch.Oe v)) ∧ GlobalTheory.ChoiceRead.ThetaAt x.r.Y l.b.YS ch v i e (u : FractionRing (ch.Oe v)) := by
  first | exact @_root_.GlobalTheory.PlaceRead.exists_local_map_at_place_alt | exact _root_.GlobalTheory.PlaceRead.exists_local_map_at_place_alt | (intros; apply _root_.GlobalTheory.PlaceRead.exists_local_map_at_place_alt <;> assumption)
end
end
