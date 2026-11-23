import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentTopStandardCharacter
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalLatticeAtPlace
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InverseLevelCardinality
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ComIs
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
noncomputable section
namespace GlobalTheory.TopDatumTheta
open GlobalTheory.LocMod.StepVec
open GlobalTheory.FunObj.Comparison₂ (IsRed)
section Gen
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
end Gen
section Fam
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : D.what₂.Word} {f : _root_.GlobalTheory.Fam.FamilyCharacter W u}
  {v : VCom f.c}
theorem k_add_s_succ_eq_r (G : GLoc v) : D.R.k + (G.s + 1) = D.R.r := by
  have := G.hs
  unfold Ranks.r
  omega
def ReducesModIdeal (G : GLoc v) (w : Pl D.host.E) (x : G.S.P.J) (g : GL (Fin D.R.r) (kP w)) : Prop :=
  ∀ (a b : Fin D.R.k ⊕ Fin (G.s + 1)) (a' b' : Fin D.R.r),
    a'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ a → b'.val = GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.framePos _ _ b → ∀ z : 𝓞 D.host.E,
      Ideal.Quotient.mk w.asIdeal z = g.val a' b' →
      valuation G.k ((x : GL (Fin D.R.k ⊕ Fin (G.s + 1)) G.k).val a b - (ofSplit G.q).pr (z : D.host.E)) < 1
theorem reducesModIdeal_iff_maxM_sub {w : Pl D.host.E} (G : GLoc v) {π' : Datum.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) (x : G.S.P.J)
    (g : GL (Fin D.R.r) (kP w)) (M : Matrix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.k ⊕ Fin (G.s + 1)) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hM : g.val.submatrix (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G)) (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G)) = M.map (resS D.host.F w)) :
    _root_.GlobalTheory.TopDatumTheta.ReducesModIdeal G w x g ↔ MaxM ((x : GL _ G.k).val - M.map (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) := by
  have key : ∀ a b (z : 𝓞 D.host.E), Ideal.Quotient.mk w.asIdeal z = g.val (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) a) (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) b) →
      valuation G.k ((π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (M a b) - (ofSplit G.q).pr (z : D.host.E)) < 1 :=
    fun a b z hz => by
      have h1 : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E z) =
          (ofSplit G.q).pr (z : D.host.E) := hπ (incA D (z : D.host.E))
      rw [← h1, ← RingHom.map_sub, ← hred.ker, RingHom.map_sub, Formalism.L2.DIV.resS_oToS, sub_eq_zero]
      exact (hz.trans (congrFun (congrFun hM a) b)).symm
  constructor
  · intro h a b
    obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (g.val (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) a) (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) b))
    have := Valuation.map_sub_lt _ (h a b _ _ (firstOrd_val _ a) (firstOrd_val _ b) z hz) (key a b z hz)
    rwa [sub_sub_sub_cancel_right] at this
  · intro h a b a' b' ha hb z hz
    obtain rfl : a' = firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) a := Fin.ext (ha.trans (firstOrd_val _ a).symm)
    obtain rfl : b' = firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G) b := Fin.ext (hb.trans (firstOrd_val _ b).symm)
    have := Valuation.map_add_lt _ (h a b) (key a b z hz)
    rwa [Matrix.sub_apply, Matrix.map_apply, sub_add_sub_cancel] at this
theorem chS_eq_chrStep_fst (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) (j : ℕ) : (_root_.GlobalTheory.BaseChain.com_z W).chS j = (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta j).1 := by
  have hL : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.Is W.P.A3.A.μ0 := hPk.bot.hyp.2.2.2.1.lev
  have hb : (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = 1 :=
    MonoidHom.ext (GlobalTheory.TwistFactorCompare.eq_one_of_chrEq_one (hL.xi_base ▸ hL.xi W.P.A3.A.μ0))
  have e : (_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0 = (_root_.GlobalTheory.Fam.pk_z W).mu0 := funext fun i => by
    change (_root_.GlobalTheory.Fam.pk_z W).mu0 i * (_root_.GlobalTheory.Fam.pk_z W).xi W.P.A3.A.μ0 = _
    rw [hb, mul_one]
  change (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta j).1 = _
  rw [e]
theorem locF_iter_alt {w : Pl D.host.E} (G : GLoc v) {π' : Datum.EAf D →+* G.k} (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) {j a b : ℕ}
    (ha : a = D.R.r + j * D.R.t) (hb : b = D.R.r + (j + 1) * D.R.t) (hr : D.R.r ≤ a)
    {ea : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) j ≃ Fin a} {eb : Ix (Fin D.R.k ⊕ Fin (G.s + 1)) (Fin D.R.t) (j + 1) ≃ Fin b}
    (oa : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos ea) (ob : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eb) (χ : ℕ → (kP w)ˣ →* ℂˣ)
    (hχ : ∀ c, c ≤ j → GlobalTheory.FunObj.Comparison₂.Compat (resS D.host.F w) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)
      (χ (c + 1)) (G.S.μ (c + 1))) {N : Matrix (Fin b) (Fin a) (Datum.EAf D)} (hN : IsIntM N) :
    locF D.R.t j hr (_root_.GlobalTheory.TopDatumTheta.ReducesModIdeal G w) (fun y => G.S.P.lam y) χ (redM w N) =
      G.S.P.iterPhi (Fin D.R.t) G.S.μ G.S.tame j ((N.map π').submatrix eb ea) := by
  rw [redM_eq_map _ hN]
  exact locF_eq (GlobalTheory.FunObj.TieLev.iterPhi_read _ _ _ _ _ hred _ _ _ _ _ _ (firstOrd (_root_.GlobalTheory.TopDatumTheta.k_add_s_succ_eq_r G)) ea eb
    (isIx_of_isOrd _ ha oa) (isIx_of_isOrd _ hb ob) hr G.S.P G.S.μ G.S.tame χ hχ (_root_.GlobalTheory.TopDatumTheta.ReducesModIdeal G w) (_root_.GlobalTheory.TopDatumTheta.reducesModIdeal_iff_maxM_sub G hπ hred)
    (Matrix.of fun i j => (⟨N i j, hN i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E)))
theorem chi_compat_of_mu_eq (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) (G : GLoc v) (w : (_root_.GlobalTheory.Fam.pk_z W).Pg) (hq : Formalism.L2.NTheta.IsIdemAt G.q.e w.1) {π' : Datum.EAf D →+* G.k}
    (hπ : ∀ a, π' (toEAf D a) = G.q.pr a)
    (hred : IsRed (resS D.host.F w.1) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype)) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ D.R.m)
    (hμ : (ofSplit G.q).IsComp (Lift.chrStep (_root_.GlobalTheory.Fam.pk_z W).mu0 (_root_.GlobalTheory.Fam.pk_z W).eta c).1⁻¹ (G.S.μ c)) :
    GlobalTheory.FunObj.Comparison₂.Compat (resS D.host.F w.1) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) ((_root_.GlobalTheory.Fam.pk_z W).chi c w.1) (G.S.μ c) :=
  GlobalTheory.ChainOnto.chi_compat_of_isComp D _ G.q w.1 hq π' hπ hred (_root_.GlobalTheory.BaseChain.com_z W) (_root_.GlobalTheory.BaseChain.com_is_alt W hPk) w.2 c h1 h2 _
    (G.S.tame _) (by rw [_root_.GlobalTheory.TopDatumTheta.chS_eq_chrStep_fst hPk]; exact hμ)
set_option maxHeartbeats 1000000 in
theorem place_alt (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg} (hGR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl) (i : Fin n) {j : ℕ}
    (h : j + 2 * 0 + 2 = D.R.m) (x : WO (Yc D (j + 1)) D.sp.X') {N : Matrix (Fin D.sp.X'.rank) (Fin (Yc D (j + 1)).rank) (Datum.EAf D)}
    (hN : N = frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x)) :
    (((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x) ≠ 0 →
      ∀ a b, toEAf D (G i).q.e * N a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
    (IsIntM N → locF D.R.t (j + 1) (r_le_Y (j + 1)) (_root_.GlobalTheory.TopDatumTheta.ReducesModIdeal (G i) (pl i).1) (fun y => (G i).S.P.lam y) (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1)
      (redM (pl i).1 N) = ((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x)) := by
  obtain rfl : (G i).s = j := _root_.GlobalTheory.TopLocData.s_eq_alt (G i) h
  have hq := (hGR.idem i).1
  obtain ⟨π', hπ, hred, hint, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D _ (G i).q (pl i).1 hq
  obtain ⟨ea, ha, mS⟩ := hGR.frame i ((G i).s + 1) 0 rfl
  obtain ⟨eb, hb, mT⟩ := hGR.frameTop i
  have hco := coords_moved (ofSplit (G i).q) ((G i).FY ((G i).s + 1) 0 rfl) (G i).FT hπ
    (typeFrame (G i).S.ϖ (stdOrd _ _ ((G i).s + 1) 0 rfl)) (LatFrame.refl _ _) ea eb mS
    (by rw [show (LatFrame.refl (G i).k _).bas.val = 1 from rfl, Matrix.mul_one]; exact mT) x
  have hP : ((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x) =
      (G i).S.P.iterPhi (Fin D.R.t) (G i).S.μ (G i).S.tame ((G i).s + 1) ((N.map π').submatrix eb ea) := by
    rw [hN]
    exact congrArg ((G i).S.P.iterPhi (Fin D.R.t) (G i).S.μ (G i).S.tame ((G i).s + 1)) hco
  rw [hP]
  refine ⟨fun hz a b => part_int (G i).q hπ hint ?_, fun hI => ?_⟩
  · simpa using TypeDatum.intM_of_Phi_ne_zero _ _ hz ((ixSucc _ _ ((G i).s + 1)).symm (eb.symm a)) (ea.symm b)
  · have r1 : (Yc D ((G i).s + 1)).rank = D.R.r + ((G i).s + 1) * D.R.t := by
      rw [D.sp.Y_rank _ (min_le_right _ _), min_eq_left (by omega)]; rfl
    have r2 : D.sp.X'.rank = D.R.r + ((G i).s + 1 + 1) * D.R.t := by
      rw [D.sp.X'_rank, (G i).hs]; rfl
    have hs := (G i).hs
    exact _root_.GlobalTheory.TopDatumTheta.locF_iter_alt (G i) hπ hred r1 r2 _ ha hb (fun c => (_root_.GlobalTheory.Fam.pk_z W).chi c (pl i).1)
      (fun c hc => _root_.GlobalTheory.TopDatumTheta.chi_compat_of_mu_eq hPk (G i) (pl i) hq hπ hred (by omega) (by omega) (hGR.mu i (c + 1) (by omega) (by omega))) hI
set_option maxHeartbeats 1000000 in
theorem datum_eq_alt (hPk : _root_.GlobalTheory.Fam.PackageHypotheses W) {n : ℕ} {G : Fin n → GLoc v} {pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg} (hGR : _root_.GlobalTheory.Fam.LocalGroupReading f G pl) {j : ℕ}
    (h : j + 2 * 0 + 2 = D.R.m) (x : WO (Yc D (j + 1)) D.sp.X') :
    (if IsHalf (∑ i, (G i).q.e) (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x) ∧
        IsIntM (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x)) then
      omegaG (datY _ D.R.r D.R.t (j + 1) (r_le_Y (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B) ((_root_.GlobalTheory.Fam.pk_z W).chi (j + 1 + 1))
          (fun PP => redM PP (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x))) *
        omegaQ ∅ (datY _ D.R.r D.R.t (j + 1) (r_le_Y (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).Pg ∅ (_root_.GlobalTheory.Fam.complexLevelStructure W) (_root_.GlobalTheory.Fam.pk_z W).chi (fun _ => 1) Frm.B).r (fun _ => 1) 1
          (fun PP => redM PP (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x)))
      else 0) =
    if IsHalf (∑ i, (G i).q.e) x then
      ∏ i, ((G i).S.T (Fin D.R.t)).PhiTop ((ofSplit (G i).q).down (_root_.GlobalTheory.TopLocData.frameOfSuccessor (G i) h) (G i).FT x) else 0 := by
  obtain ⟨G', rfl⟩ : ∃ G' : (_root_.GlobalTheory.Fam.pk_z W).Pg → GLoc v, G = fun i => G' (pl i) :=
    ⟨fun w => G (pl.symm w), funext fun i => congrArg G (pl.symm_apply_apply i).symm⟩
  have hpl := fun i => _root_.GlobalTheory.TopDatumTheta.place_alt hPk hGR i h x rfl
  by_cases hx : IsHalf (∑ i, (G' (pl i)).q.e) x
  swap
  · rw [if_neg hx, if_neg fun H => hx ((isHalf_actO_iff _ _ _).1 H.1)]
  have hy := (isHalf_actO_iff (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x).2 hx
  rw [if_pos hx]
  by_cases hI : IsIntM (frMapO (Yc D (j + 1)) D.sp.X' ((_root_.GlobalTheory.Fam.pk_z W).βY (j + 1)) (_root_.GlobalTheory.Fam.pk_z W).βX (actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x))
  · rw [if_pos ⟨hy, hI⟩, GlobalTheory.FunObj.Comparison₂.omegaQ_eq_prod, Finset.prod_empty, mul_one,
      omegaG_eq_prod (r_le_Y (j + 1)) _ _ _ _ _ (fun w => _root_.GlobalTheory.TopDatumTheta.ReducesModIdeal (G' w) w.1) (fun w y => (G' w).S.P.lam y)
        (fun g => (hGR.lev g).1.trans (pl.forall_congr_right (q := fun w => ∃ y, _root_.GlobalTheory.TopDatumTheta.ReducesModIdeal (G' w) w.1 y (g w))))
        (fun g y hy => ((hGR.lev g.1).2 g.2 (fun i => y (pl i)) fun i => hy (pl i)).trans
          (Equiv.prod_comp pl fun w => (G' w).S.P.lam (y w))), ← Equiv.prod_comp pl]
    exact Finset.prod_congr rfl fun i _ => (hpl i).2 hI
  · rw [if_neg fun H => hI H.2]
    refine (Finset.prod_eq_zero_iff.2 (by_contra fun hne => hI fun a b => ?_)).symm
    have h1 : (∑ i, (G' (pl i)).q.e) • actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x = actO _ _ (f.g.b (j + 1))⁻¹ f.g.bT⁻¹ x :=
      Matrix.ext fun r s => hy r s
    rw [← h1, frMapO_smul]
    exact sum_part_mem _ _ _ _ fun i => (hpl i).1 (fun h0 => hne ⟨i, Finset.mem_univ _, h0⟩) a b
theorem exists_isWeilDatumO_omT_at_last (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (j : ℕ) (h : j + 2 * 0 + 2 = D.R.m) : ∃ χS χT, IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D (j + 1)) D.sp.X' χS χT
    (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h) := by
  have key : ∀ n (e : D.R.m - 1 = n), IsWeilDatumO (_root_.GlobalTheory.Fam.pk_z W).ψ (Yc D n) D.sp.X'
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).1
      (Lift.chrStep ((_root_.GlobalTheory.Fam.pk_z W).toLevCh.mu W.P.A3.A.μ0) (_root_.GlobalTheory.Fam.pk_z W).eta D.R.m).2
      (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') ((_root_.GlobalTheory.Fam.pk_z W).ωX W.P.A3.A.μ0) e) := by
    rintro n rfl
    exact W.Q.charW.base.chain.ωX W.P.A3.A.μ0
  exact ⟨_, _, key _ (GlobalTheory.Fam.idx_top h)⟩
end Fam
set_option maxHeartbeats 1000000 in
theorem moved_top_datum_alt : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (u : D.what₂.Word) (f : _root_.GlobalTheory.Fam.FamilyCharacter W u), _root_.GlobalTheory.Fam.PackageHypotheses W → f.RowOK → ∀ v : VCom f.c, v.Is → _root_.GlobalTheory.Fam.CommutingVectorTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (_root_.GlobalTheory.Fam.pk_z W).Pg) (hGP : GPin G), _root_.GlobalTheory.Fam.LocalGroupReading f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (hψ : IsStdChar D f.c.ψ (-1)) d₀, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d₀ → IsSelfDualC (Yc D (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) → IsSelfDualC D.sp.X' (_root_.GlobalTheory.Fam.pk_z W).ΛX → ∀ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (hM : IsSelfDualC (Yc D (j + 1)) M) (hLT : IsSelfDualC D.sp.X' f.g.LT), (∀ P, GlobalTheory.FinPl.Moves (Yc D (j + 1)) (f.g.b (j + 1)) ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M P) → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, _root_.GlobalTheory.Fam.IsDivisorGlobal W (j + 1) (_root_.GlobalTheory.Fam.pk_z W).MX (_root_.GlobalTheory.Fam.pk_z W).ΛX (_root_.GlobalTheory.Fam.pk_z W).βX (vacT (_root_.GlobalTheory.Fam.pk_z W) j h) d → ∃ F, IsThetaAt f.c.ψ (symplO (Yc D (j + 1)) D.sp.X') (heisO f.c.ψ (Yc D (j + 1)) D.sp.X') (∑ i, (_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT i).q.e) (latO (Yc D (j + 1)) D.sp.X' (M : Set _) (f.g.LT : Set _) fun _ => True) 1 (omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) (prodDat (_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT)) F ∧ IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' F ∧ omT (_root_.GlobalTheory.Fam.pk_z W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (_root_.GlobalTheory.Fam.pk_z W) j h)) = κ • F := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk _ v hv hVT n G pl hGP hGR j h hψ _ _ hΛ hΛX M hM hLT hMv
  refine ⟨1, one_ne_zero, fun d hd => ?_⟩
  obtain ⟨hvac, e, he, hθ⟩ := hd.2
  obtain ⟨χS, χT, hWe⟩ := _root_.GlobalTheory.TopDatumTheta.exists_isWeilDatumO_omT_at_last W j h
  have hb : f.g.b (j + 1) ∈ GfC _ := hVT.b (j + 1) ▸ hv.b (j + 1)
  have hb' : f.g.bT ∈ GfC _ := hVT.bT.1 ▸ hv.bT
  have hcth := GlobalTheory.VecTheta.isThetaFunO_stepVec hd.2
  have he' : IsIdemSum e ((_root_.GlobalTheory.Fam.pk_z W).Pg) := by simpa only [datY, Finset.union_empty] using he
  have hee : e = ∑ i, (G i).q.e := idem_eq he' _ pl fun i => (hGR.idem i).1
  have hmove := GlobalTheory.VacMove.isThetaAt_moveLat D f.c.ψ _ _ _ _ _ hWe ((_root_.GlobalTheory.Fam.pk_z W).ΛY (j + 1)) M (_root_.GlobalTheory.Fam.pk_z W).ΛX f.g.LT hΛ hM hΛX hLT
    _ hb _ hb' (hMv _) (hVT.movesT _) e _ _ _ (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    hvac.2.theta hcth hθ
  subst hee
  refine ⟨_, ?_, hWe.om_pres _ _ hcth, (one_smul _ _).symm⟩
  have hfun : prodDat (_root_.GlobalTheory.TopLocData.localLatticeAtPlace hψ hGP h hM hLT) = _ := funext fun x => (_root_.GlobalTheory.TopDatumTheta.datum_eq_alt hPk hGR h x).symm
  rw [hfun]
  exact hmove
end GlobalTheory.TopDatumTheta
end
end
