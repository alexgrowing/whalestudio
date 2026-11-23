import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepVector
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedDatumEqProdStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.STiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesFixedValues
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LinkedFamiliesKernelFrame
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LayerTwoFamilyClass
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ColJoinSOfSTiesR
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FormsAtZero

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
namespace GlobalTheory.MidDat
end GlobalTheory.MidDat
open GlobalTheory.MidDat in
theorem GlobalTheory.MidDat.moved_datum_prod_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg), GPin G → _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j, j + 1 < D.R.m → ∀ d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d₀ → ∀ (M : GlobalTheory.FinPl.Lat (Yc D j)) (M' : GlobalTheory.FinPl.Lat (Yc D (j + 1))), IsSelfDualC (Yc D j) M → IsSelfDualC (Yc D (j + 1)) M' → GlobalTheory.FinPl.Moves (Yc D j) (f.g.b j) ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M (fun _ => True) → GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (fun _ => True) → GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (fun _ => True) ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) → ∃ κ : ℂ, κ ≠ 0 ∧ ∃ Lp : Fin n → GlobalTheory.SeeSaw.LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M', (∀ i, (Lp i).q.v = (G i).q.v) ∧ (∀ i, (Lp i).e = (G i).eg j) ∧ (∀ i, IntIn (Lp i).q (Yc D j) (Lp i).FS (v.N j) ∧ IntIn (Lp i).q (Yc D (j + 1)) (Lp i).FT (v.N (j + 1))) ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W j ((_root_.GlobalTheory.Fam.pk_z W).MY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j) d → ∃ F, IsThetaFunO f.c.ψ (Yc D j) (Yc D (j + 1)) F ∧ IsThetaAt f.c.ψ (symplO (Yc D j) (Yc D (j + 1))) (heisO f.c.ψ (Yc D j) (Yc D (j + 1))) (∑ i, (Lp i).q.e) (latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) fun _ => True) 1 ((_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).vac j)) (GlobalTheory.SeeSaw.prodDat Lp) F ∧ (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)) = κ • F := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj d₀ hd₀ M M' hM hM' hmv hmv' hvac
  have hstd : IsStdChar D f.c.ψ (-1) := hd₀.2.1.1
  have ha : ∀ i, j + ((G i).s - j) = (G i).s := fun i => by have := (G i).hs; omega
  have hA := _root_.GlobalTheory.T.descent_data_step_exponents_alt D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hPin hRead j hj (fun i => (G i).s - j) ha
  obtain ⟨κ, hκ, hdat⟩ := hA
  have ho : ∀ i, ∃ o : WO (Yc D j) (Yc D (j + 1)) →₀ ℂ, (∀ x ∈ o.support, IsHalf ((G i).q.e + cA D (G i).q.e) x) ∧
      ∀ Tm, (ofSplit (G i).q).IsModel f.c.ψ ((G i).FY j ((G i).s - j + 1) (by have := ha i; omega)) ((G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega)) Tm → ∀ Φ₀ Φ₁, IsOne Φ₁ →
        Φ₀.1 = Set.indicator {x | (ofSplit (G i).q).up ((G i).FY j ((G i).s - j + 1) (by have := ha i; omega)) ((G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega)) x ∈ latO (Yc D j) (Yc D (j + 1)) (M : Set _) (M' : Set _) (· = (G i).q.v)} (fun _ => 1) →
        Tm Φ₁ = comb f.c.ψ (Yc D j) (Yc D (j + 1)) o (Tm Φ₀) := fun i => exists_o hstd (G i).q _ _ hM hM'
  choose o ho1 ho2 using ho
  let Lp : Fin n → LocPl f.c.ψ (Yc D j) (Yc D (j + 1)) M M' := fun i =>
    { k := (G i).k, q := (G i).q, unit := (G i).unit, Y := _, Y' := _,
      FS := (G i).FY j ((G i).s - j + 1) (by have := ha i; omega), FT := (G i).FY (j + 1) ((G i).s - j) (by have := ha i; omega),
      Φ := ⟨((G i).S.T (Fin D.R.t)).Phi j ((G i).s - j) (ha i), (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 j _ (ha i)⟩,
      e := (G i).eg j, e_is := (G i).eg_is j _ (ha i), o := o i, o_at := ho1 i, o_is := ho2 i }
  refine ⟨κ, hκ, Lp, fun i => rfl, fun i => rfl, fun i => ⟨(G i).latY _ _ _, (G i).latY _ _ _⟩, fun d hd => ?_⟩
  obtain ⟨-, e, he, hθ⟩ := hd.2
  have hLev := hPk.bot.hyp.2.2.2.1.lev
  have sdY : ∀ i, i < D.R.m → IsSelfDualC (Yc D i) ((_root_.GlobalTheory.Fam.pk_z W).ΛY i) := fun i hi =>
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hLev.βY i hi)
  have hWe := W.Q.charW.base.chain.ωY W.P.A3.A.μ0 j hj
  have hb : f.g.b j ∈ GfC _ := hVT.b j ▸ hv.b j
  have hb' : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
  have hvth : IsThetaFunO (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ ((_root_.GlobalTheory.Fam.pk_z W).vac j) := hd₀.2.1.2.theta
  have hcth := GlobalTheory.VecTheta.isThetaFunO_stepVec hd.2
  have he' : IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg) := by simpa only [datY, Finset.union_empty] using he
  have hee : e = ∑ i, (G i).q.e := idem_eq he' _ pl fun i => (hRead.idem i).1
  have hmove := GlobalTheory.VacMove.isThetaAt_moveLat D f.c.ψ _ _ _ _ _ hWe ((_root_.GlobalTheory.Fam.pk_z W).ΛY j) M ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M' (sdY j (by omega)) hM (sdY (j + 1) hj) hM'
    _ hb _ hb' hmv hmv' e _ _ _ (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he) hvth hcth hθ
  subst hee
  have hfun : (fun x => (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x) ∧
          IsIntM (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)) then
        omegaG (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1))
            (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x))) *
          omegaQ ∅ (datY _ D.R.r D.R.t j (r_le_Y j) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1
            (fun PP => redM PP (frMapO (Yc D j) (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).βY j) ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (actO _ _ (f.g.b j)⁻¹ (f.g.b (j + 1))⁻¹ x)))
        else 0)) = κ • prodDat Lp := funext fun x => hdat x
  rw [hfun] at hmove
  refine ⟨κ⁻¹ • (_root_.GlobalTheory.Fam.pk_z W).ωY W.P.A3.A.μ0 j (f.g.b j, f.g.b (j + 1)) (comb f.c.ψ _ _ d ((_root_.GlobalTheory.Fam.pk_z W).vac j)),
    GlobalTheory.OrientedHeis.theta_smul _ (hWe.om_pres _ _ hcth), isThetaAt_smul hκ hmove, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ hκ, one_smul]
end
