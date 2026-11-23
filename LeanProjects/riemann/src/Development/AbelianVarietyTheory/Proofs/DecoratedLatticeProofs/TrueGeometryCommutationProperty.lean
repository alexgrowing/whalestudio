import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsLow
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReadsRename
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRatOfSameOrb
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiCpl1EqZeroOfFrames
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitFrameGLFiniteMatrixOffPlaceEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceProjectionEqOfPrimeComponentEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDenomNotMemOfPrInt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointComponentMemSpanOfLatticeGenerators
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NeConjOfIdemSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdAtKStdOfTwist
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntDenseAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam.Rebase
open ValuativeRel

theorem mem_grpAt_of_bc {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (P : GlobalTheory.FinPl.Pl D → Prop) (h : GA D V) (hh : h ∈ GfC V)
    (κ : GL (Fin n) (EF D)) (hκ : finM V hn h = κ.1)
    (hoff : ∀ v, ¬ P v → Formalism.UG.bc (Formalism.UG.prV (E := D.host.E) v) κ = 1) : h ∈ GlobalTheory.FinPl.grpAt V P := by
  subst hn
  refine (GlobalTheory.FinPl.SetCut.mem_grpAt_iff_parts V P h).2 fun i j => ⟨(GlobalTheory.FinPl.SetCut.mem_GfC_iff_entries V h).1 hh i j, fun w hw => ?_⟩
  have e1 : Formalism.UG.prV (E := D.host.E) w (κ.1 i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j :=
    congrArg (fun g => g.1 i j) (hoff w hw)
  rw [← hκ, GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at e1
  have e2 : Formalism.UG.prV (E := D.host.E) w (toEAf D ((Formalism.L2.Theta.mt V h - 1) i j)) = 0 := by
    rw [Matrix.sub_apply, RingHom.map_sub, map_sub, e1, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have e3 := (GlobalTheory.StabOff.prV_comm w (finPart D ((Formalism.L2.Theta.mt V h - 1) i j))).symm.trans e2
  exact (map_eq_zero_iff _ (Algebra.TensorProduct.comm _ _ _).injective).1 e3

theorem pr_mem_of_intAt {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P) {x : D.host.E}
    (hx : Formalism.L2.Col.IntAt P x) : q.pr (incA D x) ∈ 𝒪[k] := by
  obtain ⟨r, s, hs, e⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ P.asIdeal.zero_mem)
  have hsE : (s : D.host.E) ≠ 0 := fun h => hs0 (RingOfIntegers.coe_eq_zero_iff.mp h)
  have h1 := not_not.1 (mt (GlobalTheory.PhiOneVal.mem_prime_iff_pr_inv_notMem q P hP s hs0).2 hs)
  have e' : x = (r : D.host.E) * (s : D.host.E)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq₀ hsE, mul_comm]
    exact e
  rw [e', map_mul, map_mul]
  exact mul_mem (GlobalTheory.LocMod.FullLatFrame.pr_int_mem q r) h1

theorem map_pr_eq {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : Formalism.L2.NTheta.IsIdemAt q.e P)
    (V : HSp D) {n : ℕ} (hn : V.rank = n) (h : GA D V) (r : (Fin n → D.host.E) →ₗ[D.host.E] (Fin n → D.host.E))
    (hr : ∀ i j, adAt D.host.F P (finM V hn h i j) = algebraMap D.host.E _ (r (Pi.single j 1) i))
    {Y : Type} [Fintype Y] [DecidableEq Y] (pos : Y → ℕ) (F : GlobalTheory.LocMod.Frame k V.rank Y) (hF : IsStdFr pos F) (e : Y ≃ Fin n)
    (he : GlobalTheory.SymBridge.IsOrd pos e) :
    (Formalism.L2.Theta.mt V h).map q.pr = F.β * GlobalTheory.SymBridge.toLoc (q.pr.comp (incA D)) e e r * F.γ := by
  subst hn
  obtain ⟨e', he', hF⟩ := hF
  obtain rfl : e = e' := Equiv.ext fun y => Fin.ext ((he y).trans (he' y).symm)
  refine Matrix.ext fun c d => ?_
  obtain ⟨c, rfl⟩ := e.surjective c
  obtain ⟨d, rfl⟩ := e.surjective d
  rw [GlobalTheory.Fam.MovedJoin.mul_frameγ_std _ e hF, GlobalTheory.Fam.MovedJoin.frameβ_mul_std _ e hF]
  have h1 := hr (e c) (e d)
  rw [GlobalTheory.AdForm.CongAtIdem.finM_rfl, Matrix.map_apply] at h1
  exact GlobalTheory.SplitProj.pr_eq_of_adAt q P hP _ _ h1

theorem toHom_surj {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) :
    Function.Surjective (toHom S T hS hT) := fun x =>
  ⟨(Matrix.reindex (finCongr hT) (finCongr hS)).symm (LinearMap.toMatrix' x), by
    unfold toHom
    rw [Equiv.apply_symm_apply, Matrix.toLin'_toMatrix']⟩

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)}
  {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word}
  {a : GeoAll W u} {t : W.P.T}

open Formalism.L2.Col GlobalTheory.StepData GlobalTheory.SymBridge

theorem disjoint_vT (hI : I.Ok) (u : B.Word) (b : I.ι) : Disjoint ((B.primes X).vT u) (rowSG (B.primes X) I.sel (I.tup b)) := by
  refine Finset.disjoint_left.2 fun P h1 h2 => ?_
  obtain ⟨hX, hPr, -⟩ := GlobalTheory.Mem.Col2.base_fields_primes_ok B X
  have h3 := (GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup b) u hX hPr hI.sel_ok
    (hI.T_mem u) hI.g_mem P (Finset.mem_union_left _ h1)).2.2.2.2 h1
  refine GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u P ?_ ?_
  · rcases Finset.mem_union.1 h2 with h | h
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (I.Q_subset_SQ b h)
  · show algebraMap (𝓞 B.host.F) (𝓞 B.host.E) (B.T u : 𝓞 B.host.F) ∈ P.asIdeal
    rw [map_natCast]
    exact h3

def Carry (J : QJ a t) (i : Fin J.r) (β : J.Ch₀ ((J.G i).s + 1))
    (r : Sp B.fields.E (B.R.N ((J.G i).s + 1)) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N ((J.G i).s + 1))) : Prop :=
  ∀ e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1)), IsOrd xPos e →
    ∃ g ∈ (((J.G i).T (J.E i).δ (J.E i).tame (J.E i).η).lev ((J.G i).s + 1) 0 rfl).J,
      g.val.toBlocks₁₁ = toLoc ((J.G i).q.pr.comp (incA (I.rec7 l Z))) e e r.toLinearMap ∧
      ∀ y : Sp B.fields.E (B.R.N ((J.G i).s + 1)),
        ((qOf (J.P i).1 : B.fields.E) ^ (J.E i).M)⁻¹ • (r.symm y - repY (J.A.p0 ((J.G i).s + 1) β).1.2) ∈
          stdAt B.fields.E (B.R.N ((J.G i).s + 1)) (J.P i).1 →
        (J.E i).cos (J.π i ((J.G i).s + 1) β) = Submodule.Quotient.mk fun x => (ofSplit (J.G i).q).pr (y (e x))

set_option maxHeartbeats 1000000 in
theorem exists_carry {J : QJ a t} (hJ : J.ReadsStd) (i : Fin J.r) (β : J.Ch₀ ((J.G i).s + 1)) :
    ∃ r ∈ GLint B.fields.E (B.R.N ((J.G i).s + 1)) (J.P i).1, Carry J i β r := by
  obtain ⟨e, he⟩ := GlobalTheory.QTw.exists_xOrd B.R ((J.G i).s + 1)
  obtain ⟨r, hr, g, hg, h1, h2⟩ := GlobalTheory.QPl.RatOrb.exists_rat_of_sameOrb (E := B.fields.E) (J.P i).1
    ((J.G i).q.pr.comp (incA (I.rec7 l Z))) (J.G i).ϖ (hJ.tw i).compl e _ ((J.E i).reg.2.2 ((J.G i).s + 1) 0 rfl).1
    ((J.E i).le ((J.G i).s + 1) 0 rfl) (J.E i).M _ (repY (J.A.p0 ((J.G i).s + 1) β).1.2) (hJ.orb i β e he)
  refine ⟨r, hr, fun e' he' => ?_⟩
  obtain rfl : e = e' := Equiv.ext fun y => Fin.ext ((he y).trans (he' y).symm)
  exact ⟨g, hg, h1, h2⟩

theorem exists_place (hW : AllTrue W) {J : QJ a t} (hJ : J.ReadsStd) {P : HeightOneSpectrum (𝓞 B.fields.E)}
    (hP : P ∈ I.Q (W.P.I.tup t)) : ∃ i, (J.P i).1 = P := by
  obtain ⟨i, hi⟩ := hJ.surj P ((hW.tq.Q t P).2 hP)
  exact ⟨i, (hJ.eq i).trans hi⟩

theorem mem_Q {J : QJ a t} (hJ : J.ReadsStd) (i : Fin J.r) : (J.P i).1 ∈ I.Q (W.P.I.tup t) :=
  (Finset.mem_union.1 (J.P i).2).resolve_left (hJ.tw i).nmem

set_option maxHeartbeats 1000000 in

theorem exists_moves (hW : AllTrue W) {J : QJ a t} (hJ : J.ReadsStd) (j : ℕ) (β : J.Ch₀ j) :
    ∃ (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup (W.P.I.tup t)) u j) (κ : TC.GA B (B.R.N j)), j + 1 = B.R.m →
      q.deco = (J.A.p0 j β).1.1.deco ∧ (∀ v, ¬ I.UnderQ (W.P.I.tup t) v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) κ = 1) ∧
      TC.PtOf (J.A.kb j β * κ) (extTo I.SQ q) ∧
      ∀ i β' r', HEq β' β → HEq r' (q.fr ⟨(J.P i).1, mem_Q hJ i⟩) → Carry J i β' r' := by
  by_cases hm : j + 1 = B.R.m
  swap
  · exact ⟨(J.A.p0 j β).1.1, 1, fun h => absurd h hm⟩
  have H : ∀ P : I.Q (W.P.I.tup t), ∃ r ∈ GLint B.fields.E (B.R.N j) P.1,
      ∀ i, (J.P i).1 = P.1 → ∀ β' r', HEq β' β → HEq r' r → Carry J i β' r' := by
    rintro ⟨P, hP⟩
    obtain ⟨i, rfl⟩ := exists_place hW hJ hP
    have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
    obtain rfl : j = (J.G i).s + 1 := by omega
    obtain ⟨r, hr, hc⟩ := exists_carry hJ i β
    refine ⟨r, hr, fun i' hi' β' r' h1 h2 => ?_⟩
    obtain rfl : i' = i := hJ.inj ((hJ.eq i').symm.trans (hi'.trans (hJ.eq i)))
    rw [eq_of_heq h1, eq_of_heq h2]
    exact hc
  choose r hr hc using H
  obtain ⟨hb1, hb2⟩ := hJ.is.base j (by omega) β
  obtain ⟨q, κ, h1, h2, h3, h4⟩ := GlobalTheory.AdForm.Rebase.exists_frames hW.tr.ok (J.A.p0 j β).1.1 (J.A.kb j β) hb1 hb2 r hr
  refine ⟨q, κ, fun _ => ⟨h1, h3, h4, fun i β' r' e1 e2 => hc ⟨(J.P i).1, mem_Q hJ i⟩ i rfl β' r' e1 ?_⟩⟩
  rw [← h2]
  exact e2

set_option maxHeartbeats 1000000 in

theorem frsF_std (hW : AllTrue W) {J : QJ a t} (hJ : J.ReadsStd) (i : Fin J.r) (j : ℕ) (hj : j < B.R.m) (β : J.Ch₀ j) :
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

theorem cos_moved (hW : AllTrue W) {J : QJ a t} (hJ : J.ReadsStd) (i : Fin J.r) (β : J.Ch₀ ((J.G i).s + 1))
    (p' : PtAt B.R I.sel (I.tup (W.P.I.tup t)) (I.cst (W.P.I.tup t)) u ((J.G i).s + 1))
    (hc : cosetIn p' = cosetIn (J.A.p0 ((J.G i).s + 1) β)) (hr : Carry J i β (p'.1.1.fr ⟨(J.P i).1, mem_Q hJ i⟩))
    (e : XIx (Fin B.R.k) (Fin B.R.t) ((J.G i).s + 1) ≃ Fin (B.R.N ((J.G i).s + 1))) (he : IsOrd xPos e) :
    (J.E i).cos (J.π i ((J.G i).s + 1) β) = Submodule.Quotient.mk fun x => (ofSplit (J.G i).q).pr (repY p'.1.2 (e x)) := by
  have hs : (J.G i).s + 1 + 1 = B.R.m := (J.G i).hs
  have hPn : (J.P i).1 ∉ (B.primes X).vGs := (hJ.tw i).nmem
  obtain ⟨g, -, -, h⟩ := hr e he
  refine h _ ?_
  have h1 := GlobalTheory.AdForm.Rebase.repY_cong hs (J.A.p0 ((J.G i).s + 1) β) p' hc (J.P i)
  have h2 : frsF I.sel (I.tup (W.P.I.tup t)) p'.1.1 (J.P i) = p'.1.1.fr ⟨(J.P i).1, mem_Q hJ i⟩ := by
    unfold frsF
    exact dif_neg hPn
  rw [frsF_std hW hJ i _ (by omega) β, h2, if_neg hPn] at h1
  rw [hJ.M i]
  exact h1

set_option maxHeartbeats 1000000 in

theorem cosG_moved (hW : AllTrue W) (ha : a.Is) (n : Fin a.n) {b : I.ι}
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
  have h5 := pr_mem_of_intAt (D := I.rec7 l Z) (a.G n).q (GlobalTheory.Fam.TopLoc.LocalIdempotentDensity.idem_at hW a ha n) h4
  have h6 := map_sub ((a.G n).q.pr.comp (incA (I.rec7 l Z))) (repY p'.1.2 x) (repY p.1.2 x)
  exact h6 ▸ h5

set_option maxHeartbeats 1000000 in

theorem dead_moved (hI : I.Ok) {b : I.ι} {Ch₀ Ch : ℕ → Type} {A A' : TwDat I l Z u b Ch₀} {ι : ∀ j, Ch j → Ch₀ j} (hl : A.Live ι)
    (hb : A'.b0 = A.b0) (hne : ∀ i, i + 1 ≠ B.R.m → A'.p0 i = A.p0 i)
    (heq : ∀ i, i + 1 = B.R.m → ∀ β, (A'.p0 i β).1.1.deco = (A.p0 i β).1.1.deco ∧ cosetIn (A'.p0 i β) = cosetIn (A.p0 i β)) :
    A'.Live ι := by
  refine ⟨hl.inj, hl.first, hl.last, fun j hj γ hγ α z => ?_⟩
  by_cases h1 : j + 1 = B.R.m
  · refine absurd ?_ hγ
    have : ∀ k, k = B.R.m → Function.Surjective (ι k) := by
      rintro _ rfl
      exact hl.last
    exact this _ h1 γ
  by_cases h2 : j + 2 = B.R.m
  swap
  · have h := hl.dead j hj γ hγ α z
    unfold TwDat.xi at h ⊢
    rw [hb, hne j h1, hne (j + 1) h2]
    exact h
  have hL : (I.idx b).Ok I.Ch I.sel (I.tup b) (I.cst b) I.glob j := by
    have := hI.idx_ok b
    rwa [show B.R.m - 2 = j by omega] at this
  obtain ⟨hd, hc⟩ := heq (j + 1) h2 γ
  have key := GlobalTheory.CplDead.xiCpl1_eq_zero_of_frames I.Ch I.sel (I.tup b) (I.cst b) (I.idx b) I.glob j hL u (disjoint_vT hI u b)
    ((A.b0 j α).get (by omega)) (A.p0 j α).1.1 (A.p0 (j + 1) γ).1.1 (A'.p0 (j + 1) γ).1.1 (A.p0 (j + 1) γ).1.2 (A'.p0 (j + 1) γ).1.2 hd
    (GlobalTheory.AdForm.Rebase.repY_cong h2 _ _ hc) (fun x => ?_)
  · unfold TwDat.xi
    rw [hb, hne j h1]
    unfold xiAt
    rw [dif_neg (by omega), dif_pos h2]
    exact (congrArg B.embLL (key _)).trans (map_zero _)
  · obtain ⟨z', hz'⟩ := toHom_surj _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) x
    have h := hl.dead j hj γ hγ α z'
    unfold TwDat.xi xiAt at h
    rw [dif_neg (by omega), dif_pos h2] at h
    subst hz'
    exact (map_eq_zero_iff _ B.embLL.injective).1 h

set_option maxHeartbeats 2000000 in

theorem pen_moved (hW : AllTrue W) (ha : a.Is) {J : QJ a t} (hJ : J.ReadsStd) (j : ℕ) (hj : j + 1 = B.R.m) (β : J.Ch₀ j)
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup (W.P.I.tup t)) u j) (κ : TC.GA B (B.R.N j))
    (hoff : ∀ v, ¬ I.UnderQ (W.P.I.tup t) v → Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) v) κ = 1)
    (hpt : TC.PtOf (J.A.kb j β * κ) (extTo I.SQ q))
    (hc : ∀ i β' r', HEq β' β → HEq r' (q.fr ⟨(J.P i).1, mem_Q hJ i⟩) → Carry J i β' r')
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
    obtain ⟨i, rfl⟩ := exists_place hW hJ hP
    exact hv ⟨i, GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under _ (hidem i)⟩
  · subst e
    obtain ⟨e, he⟩ := GlobalTheory.QTw.exists_xOrd B.R ((J.G i).s + 1)
    obtain ⟨g, hg, hgm, -⟩ := hc i β _ HEq.rfl HEq.rfl e he
    refine ⟨g, hg, ?_⟩
    rw [hgm]
    refine map_pr_eq (J.G i).q (hidem i) _ (rankN (I.rec7 l Z) _ hle) _ _ (fun r s => ?_) xPos _
      ((ha.stdQ (J.pl i) ⟨t, J.mem i⟩).1 _ le_rfl) e he
    have hSQ : (J.P i).1 ∈ I.SQ := I.Q_subset_SQ _ (mem_Q hJ i)
    have hTn := GlobalTheory.Mem.LevTwist.T_notMem_under_uSG B X I hI u (J.P i).1 (Finset.mem_union_right _ hSQ)
    have hb := (GlobalTheory.Mem.Col2.MemChart.kStd_spec (X := X) l.pr u (B.R.N ((J.G i).s + 1))).2.1 _ hTn
    have e1 : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) ((J.P i).1.under (𝓞 B.host.F))) κ =
        Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) ((J.P i).1.under (𝓞 B.host.F))) (J.A.kb _ β * κ) := by
      rw [map_mul, hstd, hb, one_mul]
    have e2 := GlobalTheory.Mem.Col2.ZeroMove.adAt_entry_of_bc (F := B.host.F) (E := B.host.E) (J.P i).1 e1 r s
    have e3 := hpt.fr ⟨(J.P i).1, hSQ⟩ r s
    rw [extTo_fr, ptFr_of_mem q (hJ.tw i).nmem (mem_Q hJ i)] at e3
    rw [hfin]
    exact e2.trans e3

end GlobalTheory.Fam.Rebase

namespace GlobalTheory.Fam
open GlobalTheory.Fam.Rebase

set_option maxHeartbeats 2000000 in

theorem readsOfStd : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → (commOf (pk W) u a.g).Is → ∀ t (J : QJ a t), J.ReadsStd → ∃ J' : QJ a t, J'.Reads := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha _ _ t J hJ
  choose q κ hq using fun j β => exists_moves hW hJ j β
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
    refine cos_moved hW hJ i β (A'.p0 _ β) (heq _ hs β).2.2 ?_ e he
    rw [(heq _ hs β).2.1]
    exact (hq _ β hs).2.2.2 i β _ HEq.rfl HEq.rfl
  · show A'.kb j β = _
    rw [(hne j (by omega)).1]
    exact hJ.std j (by omega) β
  · obtain ⟨k1, k2, -⟩ := hA'.kA j (by omega) β
    rw [(heq j hj β).1] at k2
    exact pen_moved hW ha hJ j hj β (q j β) (κ j β) (hq j β hj).2.1 (hq j β hj).2.2.1 (hq j β hj).2.2.2 (A'.kA j β) k1 k2
  · have hs : (a.G n).s + 1 + 1 = B.R.m := (a.G n).hs
    have h1 := cosG_moved hW ha n (J.A.p0 _ (J.ι _ y)) (A'.p0 _ (J.ι _ y)) (heq _ hs _).2.2 (hdeco _ hs _)
      (hJ.is.base _ (by omega) _).2 (e r)
    have h2 := add_mem h1 (hJ.cosG n y e he r)
    rw [sub_add_sub_cancel] at h2
    exact h2
  · exact dead_moved hW.tr.ok hJ.live hb0 (fun j hj => (hne j hj).2) fun j hj β => ⟨hdeco j hj β, (heq j hj β).2.2⟩

end GlobalTheory.Fam

end
