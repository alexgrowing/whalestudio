import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryCommutationProperty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RealPack
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GeoAll
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TopReadAt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.QuadraticExtensionData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadsLow
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TrueW
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowZero

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.Fam.Rebase
open ValuativeRel
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : _root_.GlobalTheory.MiS.RealPackAlt ex} {u : B.Word}
  {a : _root_.GlobalTheory.Fam.GeometricFamily W u} {t : W.P.T}
open Formalism.L2.Col GlobalTheory.StepData GlobalTheory.SymBridge
def QuadraticExtensionCarry (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t) (i : Fin J.r) (β : J.Ch₀ ((J.G i).s + 1))
    (r : Sp B.fields.E (B.R.N ((J.G i).s + 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N ((J.G i).s + 1))) : Prop :=
  ∀ e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1)), IsOrd xPos e →
    ∃ g ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J,
      g.val.toBlocks₁₁ = toLoc ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e e r.toLinearMap ∧
      ∀ y : Sp B.fields.E (B.R.N ((J.G i).s + 1)),
        ((qOf (J.P i).1 : B.fields.E) ^ (J.E i).M)⁻¹ • (r.symm y - repY (J.A.p0 ((J.G i).s + 1) β).1.2) ∈
          stdAt B.fields.E (B.R.N ((J.G i).s + 1)) (J.P i).1 →
        (J.E i).cos (J.π i ((J.G i).s + 1) β) = Submodule.Quotient.mk fun x => (ofSplit (J.G i).q).pr (y (e x))
set_option maxHeartbeats 1000000 in
theorem exists_GLint_carry {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (i : Fin J.r) (β : J.Ch₀ ((J.G i).s + 1)) :
    ∃ r ∈ GLint B.fields.E (B.R.N ((J.G i).s + 1)) (J.P i).1, _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β r := by
  obtain ⟨e, he⟩ := GlobalTheory.QTw.exists_xOrd B.R ((J.G i).s + 1)
  obtain ⟨r, hr, g, hg, h1, h2⟩ := GlobalTheory.QPl.RatOrb.exists_rat_of_sameOrb (E := B.fields.E) (J.P i).1
    ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).ϖ (hJ.tw i).compl e _ ((J.E i).reg.2.2 ((J.G i).s + 1) 0 rfl).1
    ((J.E i).le ((J.G i).s + 1) 0 rfl) (J.E i).M _ (repY (J.A.p0 ((J.G i).s + 1) β).1.2) (hJ.orb i β e he)
  refine ⟨r, hr, fun e' he' => ?_⟩
  obtain rfl : e = e' := Equiv.ext fun y => Fin.ext ((he y).trans (he' y).symm)
  exact ⟨g, hg, h1, h2⟩
theorem exists_index_place_eq_of_readsStd_of_mem (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) {P : HeightOneSpectrum (𝓞 B.fields.E)}
    (hP : P ∈ I.Q (W.P.I.tup t)) : ∃ i, (J.P i).1 = P := by
  obtain ⟨i, hi⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
  exact ⟨i, (hJ.eq i).trans hi⟩
theorem P_mem_Q_of_readsStd {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (i : Fin J.r) : (J.P i).1 ∈ I.Q (W.P.I.tup t) :=
  (Finset.mem_union.1 (J.P i).2).resolve_left (hJ.tw i).nmem
set_option maxHeartbeats 1000000 in
theorem exists_chPt_moves_of_readsStd (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (j : ℕ) (β : J.Ch₀ j) :
    ∃ (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup (W.P.I.tup t)) u j) (κ : TC.GA B (B.R.N j)), j + 1 = B.R.m →
      q.deco = (J.A.p0 j β).1.1.deco ∧ (∀ v, ¬ I.UnderQ (W.P.I.tup t) v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) κ = 1) ∧
      TC.PtOf (J.A.kb j β * κ) (extTo I.SQ q) ∧
      ∀ i β' r', HEq β' β → HEq r' (q.fr ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩) → _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β' r' := by
  by_cases hm : j + 1 = B.R.m
  swap
  · exact ⟨(J.A.p0 j β).1.1, 1, fun h => absurd h hm⟩
  have H : ∀ P : I.Q (W.P.I.tup t), ∃ r ∈ GLint B.fields.E (B.R.N j) P.1,
      ∀ i, (J.P i).1 = P.1 → ∀ β' r', HEq β' β → HEq r' r → _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β' r' := by
    rintro ⟨P, hP⟩
    obtain ⟨i, rfl⟩ := _root_.GlobalTheory.Fam.Rebase.exists_index_place_eq_of_readsStd_of_mem hW hJ hP
    have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
    obtain rfl : j = (J.G i).s + 1 := by omega
    obtain ⟨r, hr, hc⟩ := _root_.GlobalTheory.Fam.Rebase.exists_GLint_carry hJ i β
    refine ⟨r, hr, fun i' hi' β' r' h1 h2 => ?_⟩
    obtain rfl : i' = i := hJ.inj ((hJ.eq i').symm.trans (hi'.trans (hJ.eq i)))
    rw [eq_of_heq h1, eq_of_heq h2]
    exact hc
  choose r hr hc using H
  obtain ⟨hb1, hb2⟩ := hJ.is.base j (by omega) β
  obtain ⟨q, κ, h1, h2, h3, h4⟩ := GlobalTheory.AdForm.Rebase.exists_frames hW.tr.ok (J.A.p0 j β).1.1 (J.A.kb j β) hb1 hb2 r hr
  refine ⟨q, κ, fun _ => ⟨h1, h3, h4, fun i β' r' e1 e2 => hc ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩ i rfl β' r' e1 ?_⟩⟩
  rw [← h2]
  exact e2
set_option maxHeartbeats 1000000 in
theorem frsF_p0_eq_one_of_readsStd (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (i : Fin J.r) (j : ℕ) (hj : j < B.R.m) (β : J.Ch₀ j) :
    frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 (J.P i) = 1 := by
  have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
  have key : ∀ r' b' : Fin (B.R.N j), frsF I.sel (I.tup (W.P.I.tup t)) (J.A.p0 j β).1.1 (J.P i) (Pi.single b' 1) r' =
      if r' = b' then (1 : B.host.E) else 0 := by
    intro r' b'
    apply (algebraMap B.host.E ((J.P i).1.adicCompletion B.host.E)).injective
    rw [← GlobalTheory.Fam.MovedJoin.adAt_kb_eq_frsF J.A hJ.is (J.P i) hPn j hj.le β r' b', hJ.std j hj β,
      GlobalTheory.Fam.MovedJoin.adAt_kStd_of_twist hW.tr.ok _ (J.P i) hPn u _ r' b']
  refine LinearEquiv.toLinearMap_injective ((Pi.basisFun B.fields.E (Fin (B.R.N j))).ext fun b => funext fun r => ?_)
  rw [Pi.basisFun_apply]
  exact (key r b).trans (Pi.single_apply b (1 : B.fields.E) r).symm
set_option maxHeartbeats 1000000 in
theorem cos_pi_eq_mk_pr_repY (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (i : Fin J.r) (β : J.Ch₀ ((J.G i).s + 1))
    (p' : PtAt B.R I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) u ((J.G i).s + 1))
    (hc : cosetIn p' = cosetIn (J.A.p0 ((J.G i).s + 1) β)) (hr : _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β (p'.1.1.fr ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩))
    (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))) (he : IsOrd xPos e) :
    (J.E i).cos (J.π i ((J.G i).s + 1) β) = Submodule.Quotient.mk fun x => (ofSplit (J.G i).q).pr (repY p'.1.2 (e x)) := by
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
  obtain ⟨g, -, -, h⟩ := hr e he
  refine h _ ?_
  have h1 := GlobalTheory.AdForm.Rebase.repY_cong hs (J.A.p0 ((J.G i).s + 1) β) p' hc (J.P i)
  have h2 : frsF I.sel (I.tup (W.P.I.tup t)) p'.1.1 (J.P i) = p'.1.1.fr ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩ := by
    unfold frsF
    exact dif_neg hPn
  rw [_root_.GlobalTheory.Fam.Rebase.frsF_p0_eq_one_of_readsStd hW hJ i _ (by omega) β, h2, if_neg hPn] at h1
  rw [hJ.M i]
  exact h1
set_option maxHeartbeats 1000000 in
theorem pr_repY_sub_mem_integers (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) (n : Fin a.n) {b : I.ι}
    (p p' : PtAt B.R I.sel (I.tup b) (I.cst b) u ((a.G n).s + 1)) (hc : cosetIn p' = cosetIn p) (hd : p'.1.1.deco = p.1.1.deco)
    (hN : p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N ((a.G n).s + 1))) (x : Fin (B.R.N ((a.G n).s + 1))) :
    (ofSplit (a.G n).q).pr (repY p'.1.2 x) - (ofSplit (a.G n).q).pr (repY p.1.2 x) ∈ 𝒪[(a.G n).k] := by
  have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
  have hP : (a.pl n).1 ∈ (B.primes X).vGs := (hW.lev.2.1 _).1 (a.pl n).2
  let P : rowSG (B.primes X) I.sel (I.tup b) := ⟨(a.pl n).1, Finset.mem_union_left _ hP⟩
  have hP' : P.1 ∈ (B.primes X).vGs := hP
  have h1 := GlobalTheory.AdForm.Rebase.repY_cong hs p p' hc P
  have h2 : frsF I.sel (I.tup b) p'.1.1 P = frsF I.sel (I.tup b) p.1.1 P := by
    unfold frsF
    rw [dif_pos hP', dif_pos hP', hd]
  rw [h2, if_pos hP', pow_zero, inv_one, one_smul, ← map_sub] at h1
  have h3 := (isFr_ptFr p.1.1 P.1 _).2 h1
  rw [← frsF_eq_ptFr, LinearEquiv.apply_symm_apply, hN] at h3
  have h4 := (mem_localization_standardLattice P.1 _).1 h3 x
  have h5 := pr_mem_of_intAt (D := I.rec7 l Z) (a.G n).q (_root_.GlobalTheory.Fam.TopLoc.LocalIdempotentDensity.isIdemAt_G_pl hW a ha n) h4
  have h6 := map_sub ((a.G n).q.pr.comp (incA (I.rec7 l Z))) (repY p'.1.2 x) (repY p.1.2 x)
  exact h6 ▸ h5
set_option maxHeartbeats 2000000 in
theorem pen_moved_of_readsStd_at_last (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (ha : a.Is) {J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t} (hJ : J.ReadsStd) (j : ℕ) (hj : j + 1 = B.R.m) (β : J.Ch₀ j)
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup (W.P.I.tup t)) u j) (κ : TC.GA B (B.R.N j))
    (hoff : ∀ v, ¬ I.UnderQ (W.P.I.tup t) v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) κ = 1)
    (hpt : TC.PtOf (J.A.kb j β * κ) (extTo I.SQ q))
    (hc : ∀ i β' r', HEq β' β → HEq r' (q.fr ⟨(J.P i).1, _root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i⟩) → _root_.GlobalTheory.Fam.Rebase.QuadraticExtensionCarry J i β' r')
    (kA : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (h1 : kA ∈ GfC _)
    (h2 : finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) kA = (J.A.kb j β * κ).1) :
    ∃ k₀ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j),
      k₀ ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) j (show j ≤ B.R.m by omega)) k₀ = (TC.kStd X u (B.R.N j)).1 ∧ kA = k₀ * h ∧
      h ∈ GlobalTheory.FinPl.grpAt _ (fun p => ∃ i, (J.G i).q.v = p) ∧
      ∀ i (e : (J.G i).s + 1 = j), ∃ g ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J,
        (mt _ (e ▸ h : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X ((J.G i).s + 1)))).map (J.G i).q.pr =
          ((J.G i).FX ((J.G i).s + 1) le_rfl).β * g.val.toBlocks₁₁ * ((J.G i).FX ((J.G i).s + 1) le_rfl).γ := by
  have hI := hW.tr.ok
  have hle : j ≤ B.R.m := by omega
  obtain ⟨k1, k2, -⟩ := hJ.is.kA j hle β
  have hstd := hJ.std j (by omega) β
  have hidem : ∀ i, Formalism.L2.NTheta.IsIdemAt (J.G i).q.e (J.P i).1 := fun i => by rw [hJ.eq i]; exact (J.G i).idem
  have hfin : finM _ (rankN (I.rec7 l Z) j hle) ((J.A.kA j β)⁻¹ * kA) = κ.1 := by
    have e1 := GlobalTheory.AdForm.StabMove.finM_mul _ (rankN (I.rec7 l Z) j hle) (J.A.kA j β) ((J.A.kA j β)⁻¹ * kA)
    rw [mul_inv_cancel_left, h2, k2] at e1
    exact ((Units.mul_right_inj (J.A.kb j β)).1 e1).symm
  refine ⟨J.A.kA j β, (J.A.kA j β)⁻¹ * kA, k1, by rw [← hstd]; exact k2, (mul_inv_cancel_left _ _).symm,
    mem_grpAt_of_bc _ (rankN (I.rec7 l Z) j hle) _ _ (mul_mem (inv_mem k1) h1) κ hfin fun v hv => hoff v ?_, fun i e => ?_⟩
  · rintro ⟨P, hP, rfl⟩
    obtain ⟨i, rfl⟩ := _root_.GlobalTheory.Fam.Rebase.exists_index_place_eq_of_readsStd_of_mem hW hJ hP
    exact hv ⟨i, GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under _ (hidem i)⟩
  · subst e
    obtain ⟨e, he⟩ := GlobalTheory.QTw.exists_xOrd B.R ((J.G i).s + 1)
    obtain ⟨g, hg, hgm, -⟩ := hc i β _ HEq.rfl HEq.rfl e he
    refine ⟨g, hg, ?_⟩
    rw [hgm]
    refine map_pr_eq (J.G i).q (hidem i) _ (rankN (I.rec7 l Z) _ hle) _ _ (fun r s => ?_) xPos _
      ((ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 _ le_rfl) e he
    have hSQ : (J.P i).1 ∈ I.SQ := I.Q_subset_SQ _ (_root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i)
    have hTn := GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u (J.P i).1 (Finset.mem_union_right _ hSQ)
    have hb := (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) l.pr u (B.R.N ((J.G i).s + 1))).2.1 _ hTn
    have e1 : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) ((J.P i).1.under (𝓞 B.host.F))) κ =
        Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) ((J.P i).1.under (𝓞 B.host.F))) (J.A.kb _ β * κ) := by
      rw [map_mul, hstd, hb, one_mul]
    have e2 := GlobalTheory.Mem.Col2.ZeroMove.adAt_entry_of_bc (F := B.host.F) (E := B.host.E) (J.P i).1 e1 r s
    have e3 := hpt.fr ⟨(J.P i).1, hSQ⟩ r s
    rw [extTo_fr, ptFr_of_mem q (hJ.tw i).nmem (_root_.GlobalTheory.Fam.Rebase.P_mem_Q_of_readsStd hJ i)] at e3
    rw [hfin]
    exact e2.trans e3
end GlobalTheory.Fam.Rebase
namespace GlobalTheory.Fam
open GlobalTheory.Fam.Rebase
set_option maxHeartbeats 2000000 in
theorem readsOfStd_alt : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (a : _root_.GlobalTheory.Fam.GeometricFamily W u), a.Is → a.True → (commOf (_root_.GlobalTheory.Fam.pk_z W) u a.g).Is → ∀ t (J : _root_.GlobalTheory.Fam.QuadraticExtensionData a t), J.ReadsStd → ∃ J' : _root_.GlobalTheory.Fam.QuadraticExtensionData a t, J'.Reads := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ _ t J hJ
  choose q κ hq using fun j β => _root_.GlobalTheory.Fam.Rebase.exists_chPt_moves_of_readsStd hW hJ j β
  obtain ⟨A', hA', hchr, hb0, hne, heq⟩ := GlobalTheory.AdForm.Rebase.exists_moved hW.tr.ok hW.tr.pins.some J.A hJ.is q κ
    (fun j hj β => (hq j β hj).2.1) (fun j hj β => (hq j β hj).2.2.1)
    (fun j hj β => by rw [(hq j β hj).1]; exact (hJ.is.base j (by omega) β).2)
  have hdeco : ∀ j, j + 1 = B.R.m → ∀ β, (A'.p0 j β).1.1.deco = (J.A.p0 j β).1.1.deco := fun j hj β => by
    rw [(heq j hj β).2.1]
    exact (hq j β hj).1
  refine ⟨{ J with A := A' }, hA', hJ.inj, hJ.surj, fun j hj => ?_, hJ.res, hJ.eq, hJ.sg, hJ.tw, hJ.M, fun i j d h hj β => ?_,
    fun i β e he => ?_, fun j hj β => ?_, fun j hj β => ?_, hJ.last, hJ.sec, fun n y e he r => ?_, ?_⟩
  · show A'.chr (j + 1) = _
    rw [hchr]
    exact hJ.chr j hj
  · have h' := hJ.rep i j d h hj β
    rw [← hb0] at h'
    exact h'
  · have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
    refine _root_.GlobalTheory.Fam.Rebase.cos_pi_eq_mk_pr_repY hW hJ i β (A'.p0 _ β) (heq _ hs β).2.2 ?_ e he
    rw [(heq _ hs β).2.1]
    exact (hq _ β hs).2.2.2 i β _ HEq.rfl HEq.rfl
  · show A'.kb j β = _
    rw [(hne j (by omega)).1]
    exact hJ.std j (by omega) β
  · obtain ⟨k1, k2, -⟩ := hA'.kA j (by omega) β
    rw [(heq j hj β).1] at k2
    exact _root_.GlobalTheory.Fam.Rebase.pen_moved_of_readsStd_at_last hW ha hJ j hj β (q j β) (κ j β) (hq j β hj).2.1 (hq j β hj).2.2.1 (hq j β hj).2.2.2 (A'.kA j β) k1 k2
  · have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
    have h1 := _root_.GlobalTheory.Fam.Rebase.pr_repY_sub_mem_integers hW ha n (J.A.p0 _ (J.ι _ y)) (A'.p0 _ (J.ι _ y)) (heq _ hs _).2.2 (hdeco _ hs _)
      (hJ.is.base _ (by omega) _).2 (e r)
    have h2 := add_mem h1 (hJ.cosG n y e he r)
    rw [sub_add_sub_cancel] at h2
    exact h2
  · exact dead_moved hW.tr.ok hJ.live hb0 (fun j hj => (hne j hj).2) fun j hj β => ⟨hdeco j hj β, (heq j hj β).2.2⟩
end GlobalTheory.Fam
end
end
