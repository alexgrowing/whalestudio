import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefAEqOfHeq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Formalism.LocalToGlobal.IndefiniteReal.LiftCoordinatesInGoodPartFamily
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.RangeAdjointRat
import Formalism.LocalToGlobal.IndefiniteReal.RationalAdjoints.CoordRat
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.CxLemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftMatBase

section Gen

open Formalism.IndefR.CxPass LevelOperators

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

theorem dnLevL_of_ratZL {s : ℕ} (hok : A3.fam3.Ok3 s) {gW : ∀ j, Representation ℂ G (X.W j)}
    (Hs : ∀ j t, Hyp A3.fam3.base3.v0.embedding (X.jL j t) (A3.fam3.F.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j)
      (X.θ' j t))
    (hRZ : ∀ j t, Submodule.span ℂ ((X.jL j t) '' (X.Zl j t : Set (A3.fam3.amb3.FL j t))) =
      LinearMap.range (LinearMap.adjoint (X.θ' j t)))
    {cv : CrdV A3.fam3.amb3} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ j t, cv.v0L X.zs b j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ))
    (hE : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW b P ψ) :
    X.DnLevL cv b := by
  intro j t
  rintro _ ⟨u, hu, rfl⟩
  have hu0 : u ∈ Submodule.span ℂ (X.jL j t '' (BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ) : Set _)) := by
    have := hu
    unfold CxData.goodPartComplexPoints at this
    rwa [hv j t] at this
  rw [lift_good_part_complex_eq_range_family (Hs j t) (hv j t)] at hu
  rw [hE j]
  refine ⟨?_, ?_⟩
  · have hle : LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A3.fam3.F.lvlA P ψ).X (A3.fam3.F.lvlA P ψ).P (A3.fam3.F.lvlA P ψ).ψ)) ≤
        LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opLC j t (Sum.inr g))
          (goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ)) := by
      have e1 : goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ = idemOf A3.fam3.F.X :=
        goodAt_bot A3.fam3.F.X _
      rw [e1]
      exact (Hs j t).range_le A3.fam3.F.X P ψ⁻¹
    obtain ⟨u', hu', hΘ⟩ := (Hs j t).dn _ (opF_goodAt_idem _ (A3.fam3.F.lvlA ⊥ 1).X hok.ok2.irr _ _) (hle hu)
    rw [← (Hs j t).ratLev (hRZ j t) _ (opF_goodAt_idem _ (A3.fam3.F.lvlA ⊥ 1).X hok.ok2.irr _ _)] at hu'
    have hZeq : ((LinearMap.range (LinearMap.adjoint (X.θ' j t))).comap (X.jL j t) ⊓
          LinearMap.range (opF (A3.fam3.F.L j t).r (goodAt (A3.fam3.F.lvlA ⊥ 1).X (A3.fam3.F.lvlA ⊥ 1).P (A3.fam3.F.lvlA ⊥ 1).ψ))) =
        LinearMap.range ((A3.fam3.F.L j t).toF (A3.fam3.F.lvlA ⊥ 1) (X.Zl j t)) := by
      rw [range_toF, goodR_eq]
      rfl
    rw [hZeq] at hu'
    have h2 : Submodule.span ℂ (X.jL j t '' (LinearMap.range ((A3.fam3.F.L j t).toF (A3.fam3.F.lvlA ⊥ 1) (X.Zl j t)) :
          Set _)) ≤ LinearMap.range (lin (X.uL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)) := by
      rw [Submodule.span_le]
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨cpt A3.fam3.base3.v0.embedding x, (X.jL_toL (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t x).symm⟩
    obtain ⟨c, hc⟩ := h2 hu'
    show X.θ' j t u ∈ principalFormsSubspace A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) j
    refine Submodule.mem_iSup_of_mem t ?_
    rw [← hΘ, ← hc, ← X.tC_eq]
    exact ⟨c, rfl⟩
  · show X.θ' j t u ∈ typeSubspace A3 X j (gW j) P ψ⁻¹
    unfold typeSubspace
    rw [Submodule.mem_iInf]
    intro h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    refine (Hs j t).type (h : G) (((ψ⁻¹) h : Kˣ) : K) _ (fun x hx => ?_) hu0
    rw [goodR_eq] at hx
    exact opF_goodAt_type _ _ hok.ok2.irr P ψ⁻¹ h x hx

end Gen

section Conc

open Formalism.IndefR.CxPass

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tC_single_mem (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F)
    (j : Fin D.R.m) (k : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0)) :
    (R.toCx3 F).tC F.cr false j A3.A.μ0 (Pi.single k 1) ∈ LinearMap.range ((R.toCx3 F).w0C false j) := by
  have kL := RealDat3.kFormL_of (F := F) hC.base.models
  have jL := RealDat3.jIsoL_of (F := F) hC.base.models
  have rz : ∀ j t, Submodule.span ℂ (((R.toCx3 F).jL j t) '' ((R.toCx3 F).Zl j t : Set (A3.fam3.amb3.FL j t))) =
      LinearMap.range (LinearMap.adjoint ((R.toCx3 F).θ' j t)) := fun j t => by
    obtain ⟨N, ψ, hψ, hr⟩ := hL.liftTest j
    exact Formalism.IndefR.Rat.range_adjoint_rat A3.fam3.base3.v0.embedding ((R.toCx3 F).jL j t)
      ((cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1).hL j t) _ (kL j t).1 (kL j t).2 (jL j t) _ ψ hψ (fun i x => hr t i x)
  have hdn : (R.toCx3 F).DnLevL (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) false :=
    dnLevL_of_ratZL (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) hL.ok
      (fun j t => lift_hypotheses_of_unitary hL.ok kL (cvOf3 A3 F.P0 F.ψ0 F.P1 F.ψ1) (fun _ _ _ _ => rfl) jL hL.gUnit.2 hL.gEquiv.2 j t)
      rz F.P0 F.ψ0 (fun _ _ => rfl) hL.levW
  rw [Formalism.IndefR.Cx.CxData.tC, Formalism.IndefR.Cx.lin_single]
  exact hdn j _ ⟨_, Submodule.subset_span ⟨_, lift_coordinates_in_good_part_family (P0 := F.P0) (ψ0 := F.ψ0) (P1 := F.P1) (ψ1 := F.ψ1)
    (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.toCx3 F) false j _ (Pi.single k 1), rfl⟩, rfl⟩

theorem liftMatC_isRat (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F) (j : Fin D.R.m) :
    Formalism.IndefR.Cx.IsRat A3.fam3.base3.v0.embedding ((R.toCx3 F).liftMatC F.cr false j A3.A.μ0) := by
  intro i k
  obtain ⟨N, ψ, hψ, hr, hbase⟩ := hL.liftTestB j
  have hinj := (R.toCx3 F).principal_form_injective false (RealDat3.kForm_of (F := F) hL.unif false) (RealDat3.ewNorm false)
    (RealDat.nP_pos false) j
  have hmem := tC_single_mem R F hC hL j k
  obtain ⟨a, ha⟩ := Formalism.IndefR.Rat.coord_rat _ ψ hψ ((R.toCx3 F).w0C false j) hinj (fun i l => hbase i l)
    (Formalism.IndefR.Cx.solve ((R.toCx3 F).w0C false j) ((R.toCx3 F).tC F.cr false j A3.A.μ0 (Pi.single k 1)))
    (fun i' => by
      rw [Formalism.IndefR.Cx.solve_spec _ hmem, Formalism.IndefR.Cx.CxData.tC, Formalism.IndefR.Cx.lin_single]
      exact hr _ _ _) i
  exact ⟨a, by simpa [Formalism.IndefR.Cx.CxData.liftMatC, Formalism.IndefR.Cx.relMat] using ha⟩

theorem liftMatrix_computes_lift_rational (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hL : Rw.HoldsL R F) (j : Fin D.R.m)
    (x : Fin ((lv (F.fc (R.toCx3 F).zs) false).dZ j A3.A.μ0) → D.what₂.LL) :
    (R.toCx3 F).w0C false j (Formalism.IndefR.Cx.cpt A3.fam3.base3.v0.embedding
        (((R.toCx3 F).liftMat F.cr false j A3.A.μ0).mulVec x)) =
      (R.toCx3 F).tC F.cr false j A3.A.μ0 (Formalism.IndefR.Cx.cpt A3.fam3.base3.v0.embedding x) := by
  rw [Formalism.IndefR.Cx.cpt_mulVec, Formalism.IndefR.Cx.CxData.liftMat, Formalism.IndefR.Cx.kMat_map _ (liftMatC_isRat R F hC hL j)]
  exact Formalism.IndefR.Cx.relMat_spec _ _ (tC_single_mem R F hC hL j) _

end Conc

theorem baseLevelLiftMatrix_solves_relation_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, (z.R.toCx3 z.F).w0C false j (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 *ᵥ x)) = (z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ => ?_
  intro B f T w _ _ _ _ Z hX Wt z _ _ _ hHL _ _ _ _ _ _ _ _ _ _ _ _ _ x
  exact liftMatrix_computes_lift_rational z.R z.F z.pins.char hHL _ x

end GlobalTheory.Mem.R3.LiftMatBase
