import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryRowPairProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChrQuotChartFreeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMore
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlacesInjective
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MovedAtStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseFrTopEqStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IdemEqAddTwistStatement

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel
set_option maxHeartbeats 1000000
noncomputable section
namespace GlobalTheory.TwPlaces
section Steps
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T} (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (i : Fin J.r)
def sgnAt_alt (j : ℕ) (hj : j < B.R.m) (β : J.Ch₀ j) (n : ℕ) : ℂ :=
  GlobalTheory.TwBridge.sgn I.sel (I.tup (W.P.I.tup t)) (J.P i) ((J.E i).tw (J.hψ i) (J.sg i))
    ((I.idx (W.P.I.tup t)).h j ((J.A.b0 j β).get hj) (J.P i)) n
def FactorisationCondition (j : ℕ) (hj : j + 1 ≤ B.R.m) (α : J.Ch j) (γ : J.Ch (j + 1)) (c : ℂ) : Prop :=
  GlobalTheory.LocMod.IsLocFac (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) (J.pl i) ((J.E i).dL j (α i) (γ i))
               (fun z => c * B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z))) ∧
    GlobalTheory.FinPl.CombAt (S := (I.rec7 l Z).sp.X j) (T := (I.rec7 l Z).sp.X (j + 1)) (· = (J.G i).q.v) ((J.E i).dL j (α i) (γ i))
variable {J i}
theorem facAt_sgnAt_mul_sgnAt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (haT : a.True) (hJ : J.Reads)
    (hm : MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i)) (j d : ℕ) (H : j + 1 + d = (J.G i).s) (hj : j + 1 ≤ B.R.m)
    (hj' : j + 1 < B.R.m) (α : J.Ch j) (γ : J.Ch (j + 1)) :
    _root_.GlobalTheory.TwPlaces.FactorisationCondition J i j hj α γ (_root_.GlobalTheory.TwPlaces.sgnAt_alt J i j hj (J.ι j α) (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) *
      _root_.GlobalTheory.TwPlaces.sgnAt_alt J i (j + 1) hj' (J.ι (j + 1) γ) (B.R.N j + Formalism.L2.Col.cOf B.R j)) := by
  have H' : j + 1 + d = (a.Q (J.pl i) ⟨t, J.mem i⟩).s := H
  refine isLocFac_of (J.G i).q (J.G i).unit (J.G i).idem (J.G i).compl.dense _ ((J.G i).FX j (by omega)) ((J.G i).FX (j + 1) (by omega))
    (a.g.x j).L (a.g.x (j + 1)).L (ha.x j (Nat.le_of_succ_le hj)).sd (ha.x (j + 1) hj).sd (haT.pinX.xs j (Nat.le_of_succ_le hj)).2.2
    (haT.pinX.xs (j + 1) hj).2.2 ((J.G i).latX j _) ((J.G i).latX (j + 1) _) _ _
    (GlobalTheory.StepData.xi_mem_SB _ _ _ _ _ (J.hψ i) _ (J.G i).unitVol.1 _ ⟨_, (J.E i).reg.1 j (d + 1) (by omega)⟩ _ _ _ _)
    ((J.E i).dL_mid j d H (α i) (γ i)) _ fun z => ?_
  obtain ⟨e', he'⟩ := exists_xOrd B.R j
  obtain ⟨e, he⟩ := exists_xOrd B.R (j + 1)
  have h1 := (GlobalTheory.T.finiteDatum_factors_over_twistPrimes_local I hW.tr.ok hW.tr.tw l Z u _ J.Ch₀ J.A hJ.is).2 _ rfl _ _ _ (J.G i) _ (J.E i) (J.hψ i) (J.sg i) (J.π i) (J.P i)
    hm.toReadsAt j d H hj hj' (J.ι j α) (J.ι (j + 1) γ) e' e he' he (homOf I l Z j hj z)
  rw [hJ.sec j (Nat.le_of_succ_le hj), hJ.sec (j + 1) hj] at h1
  have h2 := toLoc_frames ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj))
    (rankN (I.rec7 l Z) (j + 1) hj) e e' _ _ z _ _ (hm.low (j + 1) (by omega) hj (J.ι (j + 1) γ) e he)
    (hm.low j (by omega) (Nat.le_of_succ_le hj) (J.ι j α) e' he')
  exact h1.symm.trans (congrArg _ (frame_cancel ((J.G i).FX (j + 1) (by omega)) h2))
theorem lastAgree_of_reads (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (hJ : J.Reads) :
    GlobalTheory.TwBridge.LastAgree I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) B.embLL (J.P i)
      ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).s ((J.E i).tw (J.hψ i) (J.sg i)) (J.G i).ν (I.idx (W.P.I.tup t)) := by
  have hI := hW.tr.ok
  have hs : (J.G i).s = B.R.m - 2 := by have := (hJ.tw i).steps; omega
  have hL : (I.idx (W.P.I.tup t)).Ok I.Ch I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) I.glob (J.G i).s := by
    rw [hs]; exact hI.idx_ok _
  exact GlobalTheory.T.twistParahoricChain_lastSteps_agree_columns B.fields (B.primes X) B.R I.Ch I.sel _ _ _ B.embLL (J.P i) (J.G i).k _ (J.G i).s _ (J.G i).ν (J.G i).unitVol
    (hI.idx_ok _).cst_ok (hJ.tw i) _ I.glob hL
variable (J i) in
def TranslationCondition (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))) (hm : (J.G i).s + 1 ≤ B.R.m)
    (β : J.Ch₀ ((J.G i).s + 1)) (c : ℂ) : Prop :=
  ∃ κ : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) ((J.G i).s + 1) ⊕ Fin 0) (J.G i).k,
    (∀ r b, (ofSplit (J.G i).q).pr (baseFr J.A (J.P i) ((J.G i).s + 1) hm β r (e b)) =
      (((J.G i).FX ((J.G i).s + 1) le_rfl).β * κ.val.toBlocks₁₁) r b) ∧
    (J.E i).cos (J.π i ((J.G i).s + 1) β) = Submodule.Quotient.mk (κ.val.toBlocks₁₁ *ᵥ ownVec J.A (J.G i) (J.P i) e β) ∧
    (∀ h x₀ y, ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).Psi h (κ.val.toBlocks₁₁ * x₀) (κ.val.toBlocks₁₁ *ᵥ y) =
      c * ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).Psi h x₀ y) ∧
    ∀ (ψ : AddChar (J.G i).k Circle) (ε : (J.G i).k) (w : (J.G i).kˣ) y x,
      ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).xiTop (box _ w) ψ (J.G i).ν ε (Submodule.Quotient.mk y) (x * κ.val.toBlocks₁₁) =
        c * ((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).xiTop (box _ w) ψ (J.G i).ν ε (Submodule.Quotient.mk (κ.val.toBlocks₁₁ *ᵥ y)) x
theorem exists_root_of_unity_moveAt (hm : MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i)) (e) (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e)
    (h : (J.G i).s + 1 ≤ B.R.m) (β) : ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ _root_.GlobalTheory.TwPlaces.TranslationCondition J i e h β c := by
  obtain ⟨κ, hκ, h1, h2⟩ := hm.pen h β e he
  obtain ⟨c, hc, h3, h4⟩ := GlobalTheory.T.parahoricChain_last_two_steps_root_of_unity (J.G i).k (J.G i).ν (J.G i).unitVol (J.G i).s (Fin B.R.k) (Fin B.R.t) (J.E i).δ (J.E i).tame
    (J.E i).η (J.E i).unr κ hκ
  exact ⟨c, hc, κ, h1, h2, h3, h4⟩
theorem facAt_s_sgnAt_mul_of_moveAt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (haT : a.True) (hJ : J.Reads)
    (hm : MovedAt J.A (J.P i) (J.E i) (J.hψ i) (J.sg i) (J.π i)) (hj : (J.G i).s + 1 ≤ B.R.m) (e)
    (he : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e) (α : J.Ch (J.G i).s) (γ : J.Ch ((J.G i).s + 1)) (c : ℂ)
    (hc : _root_.GlobalTheory.TwPlaces.TranslationCondition J i e hj (J.ι _ γ) c) :
    _root_.GlobalTheory.TwPlaces.FactorisationCondition J i (J.G i).s hj α γ (_root_.GlobalTheory.TwPlaces.sgnAt_alt J i _ hj (J.ι _ α) (B.R.N ((J.G i).s + 1) + Formalism.L2.Col.cOf B.R ((J.G i).s + 1)) * c) := by
  refine isLocFac_of (J.G i).q (J.G i).unit (J.G i).idem (J.G i).compl.dense _ ((J.G i).FX _ (Nat.le_succ _)) ((J.G i).FX _ le_rfl)
    (a.g.x _).L (a.g.x _).L (ha.x _ (Nat.le_of_succ_le hj)).sd (ha.x _ hj).sd (haT.pinX.xs _ (Nat.le_of_succ_le hj)).2.2
    (haT.pinX.xs _ hj).2.2 ((J.G i).latX _ _) ((J.G i).latX _ _) _ _
    (GlobalTheory.QPl.LastTwo.entries_mem_SB _ _ _ _ (J.E i).toAt (α i) ((J.E i).cos (γ i))).1
    ((J.E i).dL_pen (α i) (γ i)) _ fun z => ?_
  obtain ⟨e', he'⟩ := exists_xOrd B.R (J.G i).s
  obtain ⟨κ, h1, h2, h3, -⟩ := hc
  have hs : (J.G i).s + 2 = B.R.m := (J.G i).hs
  have hA := ((_root_.GlobalTheory.TwPlaces.lastAgree_of_reads (i := i) hW hJ).1 ((J.A.b0 _ (J.ι _ α)).get hj) _ (hJ.rep i _ 0 rfl hj (J.ι _ α))).2 e' e he' he
    (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ α)).1.1 (J.P i))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ γ)).1.1 (J.P i)) (homOf I l Z _ hj z))
    ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ γ)).1.1 (J.P i)).symm (Formalism.L2.Col.repY (J.A.p0 _ (J.ι _ γ)).1.2))
  rw [hJ.sec _ (Nat.le_of_succ_le hj)] at hA
  rw [hJ.sec _ hj] at h2
  have h4 := toLoc_frames ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (rankN (I.rec7 l Z) _ (Nat.le_of_succ_le hj))
    (rankN (I.rec7 l Z) _ hj) e e' _ _ z _ _ h1 (hm.low _ le_rfl (Nat.le_of_succ_le hj) (J.ι _ α) e' he')
  have h5 := frame_cancel ((J.G i).FX ((J.G i).s + 1) le_rfl) ((Matrix.mul_assoc _ _ _).symm.trans h4)
  have h6 := Chain.xiPen_mk (J.E i).adapt (((J.E i).rep_bij _ 0 rfl).mapsTo (Set.mem_univ (α i)))
    (κ.val.toBlocks₁₁ *ᵥ ownVec J.A (J.G i) (J.P i) e (J.ι _ γ))
  refine Eq.symm ?_
  refine (congrArg₂ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).xiPen _ _) h2 h5.symm).trans ((h6 _).trans ((h3 _ _ _).trans ?_))
  refine (congrArg (c * ·) hA).trans ?_
  simp only [locXi, dif_neg (show ¬ (J.G i).s + 2 < B.R.m by omega), dif_pos hs, _root_.GlobalTheory.TwPlaces.sgnAt_alt]
  ring
theorem facAt_s_succ_inv_of_moveAt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (haT : a.True)
    (hiA : ∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) (hJ : J.Reads) (hj : (J.G i).s + 1 + 1 ≤ B.R.m) (e')
    (he' : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos e') (α : J.Ch ((J.G i).s + 1)) (γ : J.Ch ((J.G i).s + 1 + 1)) (c : ℂ) (hc0 : c ≠ 0)
    (hc : _root_.GlobalTheory.TwPlaces.TranslationCondition J i e' (Nat.le_of_succ_le hj) (J.ι _ α) c) : _root_.GlobalTheory.TwPlaces.FactorisationCondition J i ((J.G i).s + 1) hj α γ c⁻¹ := by
  refine isLocFac_of (J.G i).q (J.G i).unit (J.G i).idem (J.G i).compl.dense _ ((J.G i).FX _ le_rfl) (J.G i).FM
    (a.g.x _).L (a.g.x _).L (ha.x _ (Nat.le_of_succ_le hj)).sd (ha.x _ hj).sd (haT.pinX.xs _ (Nat.le_of_succ_le hj)).2.2
    (haT.pinX.xs _ hj).2.2 ((J.G i).latX _ _) (J.G i).latM _ _
    (xiTop_mem_SB _ (J.E i).reg (J.G i).cond (J.G i).unitVol _ ((J.E i).cos (α i)))
    ((J.E i).dL_top (α i) (γ i)) _ fun z => ?_
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  obtain ⟨e, he⟩ := exists_topOrd B.R (J.G i).s hs
  obtain ⟨κ, h1, h2, -, h3⟩ := hc
  rw [hJ.sec _ (Nat.le_of_succ_le hj)] at h2
  have h4 := toLoc_frames ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (rankN (I.rec7 l Z) _ (Nat.le_of_succ_le hj))
    (rankN (I.rec7 l Z) _ hj) e e' _ _ z _ _ (_root_.GlobalTheory.T.true_geometry_row_pair_value_alt W hW u a ha haT hiA t J hJ i hj (J.ι _ γ) e he) h1
  have h5 := (frame_cancel (J.G i).FM h4).trans (Matrix.mul_assoc _ _ _).symm
  have hmem := ownVec_mem J.A (G := J.G i) (J.P i) (hJ.tw i).nmem (hJ.tw i).compl e' (J.ι _ α)
  have hA := (_root_.GlobalTheory.TwPlaces.lastAgree_of_reads (i := i) hW hJ).2 e' (e.trans (finCongr (congrArg B.R.N hs))) he' (fun r => he r)
    (castSp B.fields.E (congrArg B.R.N hs) ∘ₗ Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ α)).1.1 (J.P i))
      (Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ γ)).1.1 (J.P i)) (homOf I l Z _ hj z))
    ((Formalism.L2.Col.frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 _ (J.ι _ α)).1.1 (J.P i)).symm (Formalism.L2.Col.repY (J.A.p0 _ (J.ι _ α)).1.2))
    (fun n => ?_)
  · refine Eq.symm ((eq_inv_mul_iff_mul_eq₀ hc0).2 ?_)
    rw [h2]
    refine (h3 _ _ _ _ _).symm.trans ?_
    rw [← hJ.M i] at hA
    refine Eq.trans ?_ (hA.trans ?_)
    · exact congrArg _ (h5.symm.trans rfl)
    · simp only [locXi, dif_neg (show ¬ (J.G i).s + 1 + 2 < B.R.m by omega), dif_neg (show ¬ (J.G i).s + 1 + 2 = B.R.m by omega),
        dif_pos hs]
      rfl
  · obtain ⟨r, rfl⟩ := e'.surjective n
    have h6 := hmem r
    have hcp := (hJ.tw i).compl
    refine (hcp.int _).1 ?_
    have h7 : 0 < valuation (J.G i).k (((J.G i).ϖ : (J.G i).k) ^ (I.cst (W.P.I.tup t)).M) := by
      rw [map_pow]
      exact pow_pos ((Valuation.pos_iff _).2 (J.G i).ϖ.ne_zero) _
    rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, ← mul_one (_⁻¹), le_inv_mul_iff₀ h7] at h6
    rw [map_mul, map_pow, ← hcp.unif, Valuation.mem_integer_iff, map_mul]
    exact h6
theorem sgnAt_mul_eq_one_of_even_add (hJ : J.Reads) (j : ℕ) (hj : j < B.R.m) (β : J.Ch₀ j) {n n' : ℕ} (h : Even (n + n')) :
    _root_.GlobalTheory.TwPlaces.sgnAt_alt J i j hj β n * _root_.GlobalTheory.TwPlaces.sgnAt_alt J i j hj β n' = 1 := by
  unfold _root_.GlobalTheory.TwPlaces.sgnAt_alt GlobalTheory.TwBridge.sgn
  show J.sg i ^ _ * J.sg i ^ _ = 1
  rcases hJ.sg i with h1 | h1 <;> rw [h1]
  · simp
  · rw [← zpow_add₀ (by norm_num), ← mul_add]
    refine Even.neg_one_zpow (Even.mul_left ?_ _)
    exact_mod_cast h
theorem exists_pow_sgnAt_eq_one (hJ : J.Reads) (j : ℕ) (hj : j < B.R.m) (β : J.Ch₀ j) (n : ℕ) :
    ∃ N : ℕ, 0 < N ∧ _root_.GlobalTheory.TwPlaces.sgnAt_alt J i j hj β n ^ N = 1 :=
  ⟨2, two_pos, by rw [sq, _root_.GlobalTheory.TwPlaces.sgnAt_mul_eq_one_of_even_add hJ j hj β ⟨n, rfl⟩]⟩
theorem ch_zero_subsingleton (α α' : J.Ch 0) : α = α' := funext fun n => by
  have hb := (J.E n).rep_bij 0 (J.G n).s (Nat.zero_add _)
  have h1 := hb.mapsTo (Set.mem_univ (α n))
  have h2 := hb.mapsTo (Set.mem_univ (α' n))
  rw [(J.E n).reps.zero] at h1 h2
  exact hb.injOn (Set.mem_univ _) (Set.mem_univ _) (h1.trans h2.symm)
variable (i) in
theorem exists_roots_of_unity_signs_facAt (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (haT : a.True)
    (hiA : ∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) (hJ : J.Reads) :
    ∃ (σ : ∀ j, J.Ch₀ j → ℂ) (τ : ∀ j, J.Ch₀ (j + 1) → ℂ), (∀ j β, ∃ n : ℕ, 0 < n ∧ σ j β ^ n = 1) ∧
      (∀ j β, ∃ n : ℕ, 0 < n ∧ τ j β ^ n = 1) ∧ (∀ j, j + 1 < B.R.m → ∀ β, τ j β * σ (j + 1) β = 1) ∧
      ∀ j (hj : j + 1 ≤ B.R.m) (α : J.Ch j) (γ : J.Ch (j + 1)), _root_.GlobalTheory.TwPlaces.FactorisationCondition J i j hj α γ (σ j (J.ι j α) * τ j (J.ι (j + 1) γ)) := by
  have hm := _root_.GlobalTheory.T.moved_at_of_reads W hW u a ha haT t J hJ i
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  obtain ⟨e, he⟩ := exists_xOrd B.R ((J.G i).s + 1)
  choose c hc hc' using _root_.GlobalTheory.TwPlaces.exists_root_of_unity_moveAt hm e he (by omega)
  have hc0 : ∀ β, c β ≠ 0 := fun β h => by
    obtain ⟨n, hn, h1⟩ := hc β
    rw [h, zero_pow hn.ne'] at h1
    exact zero_ne_one h1
  let C : ∀ j, J.Ch₀ j → ℂ := fun j β => if h : j = (J.G i).s + 1 then c (h ▸ β) else 1
  have hC : ∀ β, C ((J.G i).s + 1) β = c β := fun β => dif_pos rfl
  have hCr : ∀ j β, ∃ n : ℕ, 0 < n ∧ C j β ^ n = 1 := fun j β => by
    by_cases h : j = (J.G i).s + 1
    · subst h
      rw [hC]
      exact hc β
    · exact ⟨1, one_pos, by simp only [C, dif_neg h, one_pow]⟩
  refine ⟨fun j β => if h : j + 1 < B.R.m then _root_.GlobalTheory.TwPlaces.sgnAt_alt J i j (by omega) β (B.R.N (j + 1) + Formalism.L2.Col.cOf B.R (j + 1)) else (C j β)⁻¹,
    fun j β => if h : j + 2 < B.R.m then _root_.GlobalTheory.TwPlaces.sgnAt_alt J i (j + 1) (by omega) β (B.R.N j + Formalism.L2.Col.cOf B.R j) else C (j + 1) β,
    fun j β => ?_, fun j β => ?_, fun j hj β => ?_, fun j hj α γ => ?_⟩
  · beta_reduce
    split_ifs
    · exact _root_.GlobalTheory.TwPlaces.exists_pow_sgnAt_eq_one hJ _ _ _ _
    · exact rou_inv (hCr j β)
  · beta_reduce
    split_ifs
    · exact _root_.GlobalTheory.TwPlaces.exists_pow_sgnAt_eq_one hJ _ _ _ _
    · exact hCr _ β
  · beta_reduce
    by_cases h : j + 2 < B.R.m
    · rw [dif_pos h, dif_pos (show j + 1 + 1 < B.R.m from h)]
      exact _root_.GlobalTheory.TwPlaces.sgnAt_mul_eq_one_of_even_add hJ _ _ _ (even_ranks B.R j h)
    · rw [dif_neg h, dif_neg (show ¬ j + 1 + 1 < B.R.m from h)]
      obtain rfl : j = (J.G i).s := by omega
      rw [hC]
      exact mul_inv_cancel₀ (hc0 β)
  · beta_reduce
    rcases lt_trichotomy (j + 2) B.R.m with h | h | h
    · rw [dif_pos h, dif_pos (show j + 1 < B.R.m by omega)]
      exact _root_.GlobalTheory.TwPlaces.facAt_sgnAt_mul_sgnAt hW ha haT hJ hm j ((J.G i).s - (j + 1)) (by omega) hj _ α γ
    · obtain rfl : j = (J.G i).s := by omega
      rw [dif_neg (show ¬ (J.G i).s + 2 < B.R.m by omega), dif_pos (show (J.G i).s + 1 < B.R.m by omega), hC]
      exact _root_.GlobalTheory.TwPlaces.facAt_s_sgnAt_mul_of_moveAt hW ha haT hJ hm hj e he α γ _ (hc' _)
    · obtain rfl : j = (J.G i).s + 1 := by omega
      rw [dif_neg (show ¬ (J.G i).s + 1 + 2 < B.R.m by omega), dif_neg (show ¬ (J.G i).s + 1 + 1 < B.R.m by omega), hC]
      have h1 : C ((J.G i).s + 1 + 1) (J.ι _ γ) = 1 := dif_neg (by omega)
      rw [h1, mul_one]
      exact _root_.GlobalTheory.TwPlaces.facAt_s_succ_inv_of_moveAt hW ha haT hiA hJ hj e he α γ _ (hc0 _) (hc' _)
theorem exists_disjoint_places_isIdemSum (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (haT : a.True) (hJ : J.Reads) {e₀ : AE (I.rec7 l Z)}
    (he₀ : IsIdemSum e₀ ((B.primes X).vT u ∪ (B.primes X).vGs)) :
    ∃ Q : Finset (Formalism.L2.DIV.Pl (I.rec7 l Z).host.E), (∀ PP, PP ∈ Q ↔ ∃ n, J.pl n = PP) ∧
      Disjoint ((B.primes X).vT u ∪ (B.primes X).vGs) Q ∧
      IsIdemSum (e₀ + ∑ n, (J.G n).q.e) (((B.primes X).vT u ∪ (B.primes X).vGs) ∪ Q) := by
  have hI : I.Ok := hW.tr.ok
  have hPr := l.pr
  have hd : Disjoint ((B.primes X).vT u) (Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup (W.P.I.tup t))) :=
    Finset.disjoint_left.2 fun P h1 h2 =>
      GlobalTheory.Proof.NarrowJetMoments.notMem_rowSG hPr hI.sel_ok (hPr.T_prime u) (hI.T_mem u) (hPr.T_ne_g u) h2
        (GlobalTheory.Mem.Col2.T_mem_vT hPr u ⟨P, h1⟩)
  have hgq : Disjoint (B.primes X).vGs
      (Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K)) :=
    GlobalTheory.NormOneUnit.disjoint_vGs_QE (I.tup (W.P.I.tup t)) hPr hI.sel_ok hI.g_mem
  have hid := hJ.is.idem
  have hS : Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup (W.P.I.tup t)) u =
      ((B.primes X).vT u ∪ (B.primes X).vGs) ∪
        Formalism.L2.Col.QE I.sel (I.tup (W.P.I.tup t) : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) := by
    simp only [Formalism.L2.Col.Sall, Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG, Finset.union_assoc]
  rw [hS] at hid
  obtain ⟨e₁, h1, h2⟩ := _root_.GlobalTheory.T.true_geometry_twist_quadratic_level_alt W hW u a ha haT t J hJ
  obtain rfl : e₀ = e₁ := (GlobalTheory.ExportSeries.idem_eq he₀).symm.trans (GlobalTheory.ExportSeries.idem_eq h1)
  refine ⟨_, fun PP => ⟨fun h => hJ.surj PP ((hW.tq.Q t PP).2 h), ?_⟩,
    Finset.disjoint_union_left.2 ⟨hd.mono_right Finset.subset_union_right, hgq⟩, h2 ▸ hid⟩
  rintro ⟨n, rfl⟩
  exact (hW.tq.Q t _).1 (J.mem n)
end Steps
theorem ratDatum_add_twist_places_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.Reads → ∃ (p : ∀ j, J.Ch j → ℂ) (q : ∀ j, J.Ch (j + 1) → ℂ), (∀ j, j < B.R.m → ∀ α, ∃ n : ℕ, 0 < n ∧ (p j α * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ)) ^ n = 1) ∧ (∀ j, j < B.R.m → ∀ γ, ∃ n : ℕ, 0 < n ∧ (q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹) ^ n = 1) ∧ (∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ ∀ α, p 0 α * (J.A.chr 1 (J.A.xr 0 (J.ι 0 α)) : ℂ) = c) ∧ (∀ j, j + 1 < B.R.m → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ ∀ γ, q j γ * ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹ * (p (j + 1) γ * (J.A.chr (j + 1 + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ)) = c) ∧ ∀ e₀ : AE (I.rec7 l Z), IsIdemSum e₀ ((B.primes X).vT u ∪ (B.primes X).vGs) → ∀ j (hj : j + 1 ≤ B.R.m) α γ (Ξ : Matrix (Fin ((I.rec7 l Z).sp.X (j + 1)).rank) (Fin ((I.rec7 l Z).sp.X j).rank) (I.rec7 l Z).host.E → ℂ) (f : WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ), IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ e₀ Ξ (a.g.vac j) f → IsRatDatum (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (e₀ + ∑ i, (J.G i).q.e) (fun z => Ξ z * (p j α * q j γ * ∏ i, B.embLL (locXi J.A j (J.ι j α) (J.ι (j + 1) γ) (J.P i) (homOf I l Z j hj z)))) (a.g.vac j) (comb (_root_.GlobalTheory.Fam.pk_z W).ψ _ _ (aconv (List.ofFn fun i => (J.E i).dL j (α i) (γ i))) f) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha haT hiA t J hJ
  choose σ τ hσ hτ hστ hloc using fun i => _root_.GlobalTheory.TwPlaces.exists_roots_of_unity_signs_facAt (J := J) i hW ha haT hiA hJ
  have hcob := _root_.GlobalTheory.T.true_geometry_twist_local_identity_alt W hW u a ha haT t J hJ
  have hm := B.R.two_le_m
  obtain ⟨hP⟩ := hW.tr.pins
  have hc : ∀ j, j < B.R.m → ∀ i, i ≤ B.R.m → ∀ β, ∃ n : ℕ, 0 < n ∧ ((J.A.chr (j + 1) (J.A.xr i β) : ℂ)) ^ n = 1 :=
    fun j hj i hi β => rou_circle (GlobalTheory.T.tupleCharacter_at_basePointDetRoot_rootOfUnity I hW.tr.ok hP l Z u _ J.Ch₀ J.A hJ.is j hj i hi β)
  have c1 : ∀ j, j < B.R.m → ∀ α : J.Ch j, ∃ n : ℕ, 0 < n ∧
      ((∏ i, σ i j (J.ι j α)) * (J.A.chr (j + 1) (J.A.xr j (J.ι j α)) : ℂ)) ^ n = 1 :=
    fun j hj α => rou_mul (rou_prod _ _ fun i _ => hσ i j _) (hc j hj j hj.le _)
  refine ⟨fun j α => ∏ i, σ i j (J.ι j α), fun j γ => ∏ i, τ i j (J.ι (j + 1) γ), c1, ?_, ?_, ?_, ?_⟩
  · intro j hj γ
    exact rou_mul (rou_prod _ _ fun i _ => hτ i j _) (rou_inv (hc j hj (j + 1) (by omega) _))
  · by_cases hne : Nonempty (J.Ch 0)
    · obtain ⟨α₀⟩ := hne
      exact ⟨_, c1 0 (by omega) α₀, fun α => by rw [_root_.GlobalTheory.TwPlaces.ch_zero_subsingleton α α₀]⟩
    · exact ⟨1, ⟨1, one_pos, one_pow 1⟩, fun α => (hne ⟨α⟩).elim⟩
  · intro j hj
    have hqp : ∀ γ : J.Ch (j + 1), (∏ i, τ i j (J.ι (j + 1) γ)) * ∏ i, σ i (j + 1) (J.ι (j + 1) γ) = 1 := by
      intro γ
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => hστ i j hj _
    by_cases hne : Nonempty (J.Ch (j + 1))
    · obtain ⟨γ₀⟩ := hne
      refine ⟨_, rou_mul (hc (j + 1) hj (j + 1) hj.le (J.ι _ γ₀)) (rou_inv (hc j (by omega) (j + 1) (by omega) (J.ι _ γ₀))),
        fun γ => ?_⟩
      have h1 := congrArg (fun x : Circle => (x : ℂ)) (hcob j hj (J.ι _ γ) (J.ι _ γ₀))
      simp only [Circle.coe_mul, Circle.coe_inv] at h1
      calc _ = ((∏ i, τ i j (J.ι (j + 1) γ)) * ∏ i, σ i (j + 1) (J.ι (j + 1) γ)) *
            ((J.A.chr (j + 1 + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ) *
              ((J.A.chr (j + 1) (J.A.xr (j + 1) (J.ι (j + 1) γ)) : ℂ))⁻¹) := by ring
        _ = _ := by rw [hqp γ, one_mul, h1]
    · exact ⟨1, ⟨1, one_pos, one_pow 1⟩, fun γ => (hne ⟨γ⟩).elim⟩
  · intro e₀ he₀ j hj α γ Ξ f hf
    have hv := _root_.GlobalTheory.Fam.VacTheta.main_alt_alt W hW u a ha haT j hj
    obtain ⟨Q, hQ, hdis, hsum⟩ := _root_.GlobalTheory.TwPlaces.exists_disjoint_places_isIdemSum hW ha haT hJ he₀
    have key := GlobalTheory.T.rationalDatum_foldr_local_combinations (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ haT.pinX.std _ _ _ Q J.r J.pl hJ.inj hQ hdis
      (fun i => (J.E i).dL j (α i) (γ i)) _ (fun i => (hloc i j hj α γ).1) (a.g.x j).L (a.g.x (j + 1)).L
      (ha.x j (Nat.le_of_succ_le hj)).sd (ha.x (j + 1) hj).sd (Set.ext (haT.pinX.xs j (Nat.le_of_succ_le hj)).2.2)
      (Set.ext (haT.pinX.xs (j + 1) hj).2.2) Ξ (a.g.vac j) f hv.1 hv.2.1
      (fun e₁ he₁ => ((GlobalTheory.ExportSeries.idem_eq he₀).symm.trans (GlobalTheory.ExportSeries.idem_eq he₁)) ▸ hf) _ hsum
    have hfold := GlobalTheory.QFinLaw.comb_aconv_map (_root_.GlobalTheory.Fam.pk_z W).ψ (fun i => (J.G i).q.v)
      (_root_.GlobalTheory.TopVol.TwistPlaces.places_injective_alt W hW u a ha haT t J hJ) (fun i => (J.E i).dL j (α i) (γ i))
      (fun i => (hloc i j hj α γ).2) f _ (List.nodup_finRange J.r)
    rw [List.ofFn_eq_map]
    refine hfold ▸ ?_
    convert key using 2 with z
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
end GlobalTheory.TwPlaces
end
end
