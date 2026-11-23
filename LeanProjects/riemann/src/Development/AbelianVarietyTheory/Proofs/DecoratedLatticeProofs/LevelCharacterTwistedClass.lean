import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodSingle
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MovedReadingSameMapsBaseReadingAgrees
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevIsReadsTw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterEqOneOfDeepAtSplitBadPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterTrivialNearOneOfLocalBadPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EventuallyNhdsOneAdelicMatrixCongruentOneAtPrime
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColsStdOfBWit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBadPrimeOverBadPlaceOfChain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAfMemIntUIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SubOneMemMapOfEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq

noncomputable section

namespace GlobalTheory.TopVal.LevTw

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

set_option maxHeartbeats 1000000 in

theorem chi_deep (hc : CMData F E) {n T f : ℕ} {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1) {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E hc.sig J T f bad) (m : ℕ) (hm : 0 < m) (hchi : ∀ κ : S.U, S.chi κ ^ m = 1) (P : HeightOneSpectrum (𝓞 E))
    (hne : conjPrime₂ P ≠ P) (hcj : (conjPrime₂ P).under (𝓞 F) = P.under (𝓞 F))
    (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ)) (v : HeightOneSpectrum (𝓞 F))
    (hv : IsOver v P) :
    ∃ N : ℕ, ∀ x : S.U, (∀ v', v' ≠ v → bc (prV (E := E) v') x.1 = 1) → ∀ w : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F),
      GlobalTheory.TwU.CongAt P N w → bc (prV (E := E) v) x.1 = bc (prV (E := E) v) w → S.chi x = 1 := by
  obtain ⟨N₀, hN₀⟩ := Opn.exists_depth_step hc hJ S P v hv
  subst hJ
  have hd : ∀ (N : ℕ) (z : GL (Fin n) (AfE F E)), GlobalTheory.TwU.CongAt P N z ↔ ∀ r s,
      Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)) :=
    fun N z => forall_congr' fun r => forall_congr' fun s => AdelicValuationDictionary.entry_iff P hq N z r s
  have hu : P.under (𝓞 F) = v := HeightOneSpectrum.ext (Eq.symm hv)
  have hover : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w = P ∨ w = conjPrime₂ P := fun w hw =>
    rll_over_cases hc hv (show IsOver v w from (congrArg HeightOneSpectrum.asIdeal hw).symm)
  haveI : CharZero (P.adicCompletion E) := algebraRat.charZero _
  set c : P.adicCompletion E := ((qOf P : ℕ) : P.adicCompletion E) ^ (N₀ + 1) with hcdef
  have hcv : Valued.v c = WithZero.exp (-((N₀ : ℤ) + 1)) := by
    rw [hcdef, map_pow, hq, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hc1 : Valued.v c < 1 := by
    rw [hcv, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by omega)
  have hn1 : Valued.v (m : P.adicCompletion E) ≤ 1 := GlobalTheory.MatNthRoot.v_natCast_le_one m
  have hε : Valued.v ((m : P.adicCompletion E) ^ 2 * c) ≠ 0 := by
    rw [map_mul, hcv]
    refine mul_ne_zero ?_ WithZero.exp_ne_zero
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 hm.ne')
  set e := WithZero.log (Valued.v ((m : P.adicCompletion E) ^ 2 * c)) with he
  refine ⟨(-e).toNat, fun x hxv w hw hxw => ?_⟩
  have hxP : ∀ r s, adAt F P (x.1.1 r s) = adAt F P (w.1 r s) := fun r s => by
    have h := congrArg (fun g : GL (Fin n) _ => g.1 r s) hxw
    refine LocSplice.adAt_eq_of_prV P ?_
    rw [hu]
    exact h
  have hwP := (hd (-e).toNat w).1 hw
  have hA : ∀ r s, Valued.v (adAt F P (x.1.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤
      Valued.v ((m : P.adicCompletion E) ^ 2 * c) := fun r s => by
    rw [hxP]
    refine (hwP r s).trans ?_
    rw [← WithZero.exp_log hε, ← he]
    exact WithZero.exp_le_exp.2 (by omega)
  let x' : GL (Fin n) (AfE F E) := x.1
  obtain ⟨Mu, hMun, hMu1⟩ := SplitChi.exists_root_GL P n m hm c hc1 (Matrix.GeneralLinearGroup.map (adAt F P) x') hA
  obtain ⟨z, hzU, hz1, hzP⟩ := AdLift.exists_unitary (F := F) hc hne Mu
  have hzv : ∀ v', v' ≠ v → bc (prV (E := E) v') z = 1 := fun v' hv' =>
    AdPlace.bc_prV_eq_one_of_adAt F E n v' z fun w hw =>
      hz1 w (fun e => hv' (by rw [← hw, e, hu])) fun e => hv' (by rw [← hw, e, hcj, hu])
  have hz : z ∈ S.U := hN₀ z hzU hzv ((hd N₀ z).2 fun r s => by
    rw [hzP]
    refine (hMu1 r s).trans ?_
    rw [map_mul, hcv]
    exact (mul_le_of_le_one_left' hn1).trans (WithZero.exp_le_exp.2 (by omega)))
  have hgU : (z ^ m)⁻¹ * x.1 ∈ S.U := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ hz m)) x.2
  have hyU := ((S.U_eq _).1 hgU).1
  have hzmap : Matrix.GeneralLinearGroup.map (adAt F P) z = Mu := Units.ext (Matrix.ext hzP)
  have key : Matrix.GeneralLinearGroup.map (adAt F P) ((z ^ m)⁻¹ * x') = 1 := by
    rw [map_mul, map_inv, map_pow, hzmap, hMun, inv_mul_cancel]
  have hyP : ∀ r s, adAt F P (((z ^ m)⁻¹ * x.1).1 r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s :=
    fun r s => congrArg (fun g : GL (Fin n) (P.adicCompletion E) => g.1 r s) key
  have hyv : ∀ v', bc (prV (E := E) v') ((z ^ m)⁻¹ * x.1) = 1 := by
    intro v'
    by_cases hv' : v' = v
    · rw [hv']
      exact SplitChi.bc_prV_eq_one_of_split hc rfl hyU P v hover hyP
    · exact SplitChi.map_inv_pow_mul_eq_one _ m (hzv v' hv') (hxv v' hv')
  exact SplitChi.chi_eq_one_of_pow S.chi x ⟨z, hz⟩ m (hchi _) (S.chi_triv _ fun v' _ => hyv v')

end Gen

section Cols

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.AdT Matrix GlobalTheory.EX
open Formalism.IndefR Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

set_option maxHeartbeats 1000000 in

theorem chi_near_one (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι)
    {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    (hbad : ∀ v ∈ bad, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ a v) (hfin : ∃ n : ℕ, 0 < n ∧ ∀ κ, S.chi κ ^ n = 1) :
    letI := Formalism.BasicNotions.tensTopL (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
      (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)
    ∀ᶠ (u : GL (Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E
      (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))) in nhds 1, ∀ κ : S.U, κ.1 = u → S.chi κ = 1 := by
  obtain ⟨n, hn, hfin⟩ := hfin
  obtain ⟨-, gP, -, -⟩ := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z
  let Vs : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) := {v | ∃ P : SBof I a, IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)}
  have hVs : Vs.Finite := by
    have e : Vs = ⋃ P : SBof I a, {v | IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1)} := by
      ext v; simp [Vs]
    rw [e]
    refine Set.finite_iUnion fun P => Set.Subsingleton.finite ?_
    intro v hv w hw
    exact HeightOneSpectrum.ext (hv.trans hw.symm)
  have hb : ∀ v ∈ bad, v ∈ Vs := fun v hv => by
    obtain ⟨P, h1, h2⟩ := exists_SBof_over I hI l Z a v (hbad v hv)
    exact ⟨⟨P, h1⟩, h2⟩
  refine GlobalTheory.ChiCont.main (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E) (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1
    (I.rec7 l Z).R.f bad S Vs hVs hb ?_
  rintro v ⟨P, hv⟩
  obtain ⟨hs, hq, -⟩ := AdelicValuationDictionary.main I hI l Z a 0 0 P 1
  rw [hs] at hv
  have hne : conjPrime₂ P.1 ≠ P.1 := fun e =>
    GlobalTheory.Proof.NarrowJetMoments.conjP_notMem_rowSG (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 hI.sel_ok hI.g_mem P.2
      (by rw [e]; exact P.2)
  obtain ⟨N, hN⟩ := chi_deep (I.rec7 l Z).sp.cm gP S n hn hfin P.1 hne ((under_eq_iff B.host P.1 _).2 (Or.inr rfl)) hq v hv
  have h2 := GlobalTheory.TwU.NearOne.congAt_eventually_nhds_one (F := (I.rec7 l Z).host.F) (E := (I.rec7 l Z).host.E)
    ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) N (GlobalTheory.TwU.seamP (sm I l Z) P.1)
  rw [hs] at h2
  exact h2.mono fun w hw x hx hxw => hN x hx w hw hxw

theorem underQ_of_ram {I : TC B X} (hI : I.Ok) (a : I.ι) (v : HeightOneSpectrum (𝓞 B.host.F))
    (h : ∃ w ∈ Formalism.L2.Host.aboveF (L := B.host.E) B.host.F v, ¬ (I.xi a).UnrAt w) : I.UnderQ a v := by
  have hq := GlobalTheory.Mem.ReadTwist.mem_qprime_iff (hI.xi_reads a) v
  have hab : ∀ w : HeightOneSpectrum (𝓞 B.host.E), w ∈ Formalism.L2.Host.aboveF (L := B.host.E) B.host.F v ↔
      w.under (𝓞 B.host.F) = v := fun w => by
    unfold Formalism.L2.Host.aboveF
    rw [Set.Finite.mem_toFinset]
    rfl
  obtain ⟨w, hw, hu⟩ := h
  have hv := hq.2 ⟨w, (hab w).1 hw, hu⟩
  exact ⟨I.sel v, (_root_.Formalism.L2.Col.mem_QE I.sel (I.tup a) _).2 ⟨v, hv, rfl⟩, GlobalTheory.TwistPlaces.under_eq_iff.2 (hI.sel_ok v)⟩

theorem exists_rep {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (x : (𝓞 E ⧸ P.asIdeal)ˣ) :
    ∃ (b : 𝓞 E) (k : Eˣ), (k : E) = b ∧ (x : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal b := by
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (x : 𝓞 E ⧸ P.asIdeal)
  have h0 : (b : E) ≠ 0 := fun e => by
    have : b = 0 := by exact_mod_cast e
    exact x.ne_zero (by rw [← hb, this, map_zero])
  exact ⟨b, Units.mk0 _ h0, rfl, hb.symm⟩

def LevRead (l : I.Laws) (Z : TC.Later B (I.cols l)) {T : Type} (L : LevCh (I.rec7 l Z) T) (P : LevelP L.Pg (I.rec7 l Z).R.r ℂ)
    (tup : T → I.ι) : Prop :=
  ∀ t, tup t ≠ I.mu0 → ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)))
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad) y lat st,
    (∀ v ∈ bad, v ∈ badG (I.rec7 l Z) ∨ I.UnderQ (tup t) v) → (∃ n : ℕ, 0 < n ∧ ∀ κ, S.chi κ ^ n = 1) →
    I.ReadsP (tup t) S.Lb S.U S.chi y lat st →
    LevIs S (levS _ L.βX (Lev.datY _ (I.rec7 l Z).R.r (I.rec7 l Z).R.t (I.rec7 l Z).R.m r_le_X L.Pg (L.Q t) P L.chi (L.xiR t) Lev.Frm.B))
      (Lev.levChi _ L.βX (Lev.datY _ (I.rec7 l Z).R.r (I.rec7 l Z).R.t (I.rec7 l Z).R.m r_le_X L.Pg (L.Q t) P L.chi (L.xiR t) Lev.Frm.B))

set_option maxHeartbeats 2000000 in

theorem levRead_of (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) {T : Type} (L : LevCh (I.rec7 l Z) T)
    (μ0 : T) (hL : L.Is μ0) (hC : ∀ j, L.C.mu0 j = I.C.mu0 j) (tup : T → I.ι) (hxi : ∀ t, L.xiH t = I.xi (tup t))
    (hPg : L.Pg = (B.primes X).vGs) (hQ : ∀ t, L.Q t = I.Q (tup t)) (hβ : L.βX = 1)
    (eG : R3.Gc B X ≃* Formalism.L2.DIV.G0 L.Pg (I.rec7 l Z).R.r)
    (hG : ∀ (g : R3.Gc B X) (P : Pl (I.rec7 l Z).host.E) (h : P ∈ (B.primes X).vGs) (h' : P ∈ L.Pg), eG g ⟨P, h'⟩ = g ⟨P, h⟩) :
    LevRead I l Z L (levPOf eG B.embLL (R3.lev1 I) (R3.chr1 I)) tup := by
  classical
  intro t ht bad S y lat st hbad hfin hK
  have hchi := hL.chi
  have hxiR := hL.xiR t
  rw [hxi, hQ] at hxiR
  simp only [hC] at hchi
  rw [hβ, hQ]
  clear hL hC hxi hQ hβ
  obtain ⟨C, xiH, mu0, eta, xi, Pg, Q, chi, xiR, ΛY, ΛX, ΛV, ΛW, βY, βX, βV, βW⟩ := L
  dsimp only at hPg hchi hxiR eG hG ⊢
  subst hPg
  obtain rfl : eG = MulEquiv.refl _ := MulEquiv.ext fun g => funext fun w => hG g w.1 w.2 w.2
  let cg : ℕ → ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ := fun c PP => if c ≤ B.R.m then chi c PP else 1
  have key := GlobalTheory.SeeSaw.TwLev.levIs_reads_tw I hI hP l Z (tup t) ht S (chi_near_one I hI hP l Z (tup t) S hbad hfin) hK
    (levPOf (D := I.rec7 l Z) (MulEquiv.refl (R3.Gc B X)) B.embLL (R3.lev1 I) (R3.chr1 I))
    (fun g => ⟨fun h w => h w (Set.mem_univ w), fun h w _ => h w⟩)
    (fun g hg => by
      refine (congrArg (fun x : B.LLˣ => B.embLL (x : B.LL)) (LevFam.chr_apply (X := B.fields) I.Ps ⟨g.1, g.2⟩)).trans ?_
      rw [Units.coe_prod, map_prod])
    cg
    (fun c w x => by
      by_cases hc : c < B.R.m
      · obtain ⟨b, k, h1, h2⟩ := exists_rep w.1 x
        have e1 : cg (c + 1) w.1 = chi (c + 1) w.1 := if_pos hc
        have e2 : chiAt I.Ch w c = I.Ch.chi ⟨c, hc⟩ w := dif_pos hc
        have e3 := hchi ⟨c, hc⟩ w.1 w.2 b k x h1 h2
        have e4 := (hI.ch_tied.mu0 ⟨c, hc⟩).atg w k b x h1 h2
        have e5 := (congrArg (fun z : ℂˣ => (z : ℂ)) e3).trans e4
        rw [e1, e2]
        refine inv_injective ?_
        exact (Units.val_inv_eq_inv_val _).symm.trans (e5.trans ((congrArg B.embLL (Units.val_inv_eq_inv_val _)).trans (map_inv₀ _ _)))
      · have e1 : cg (c + 1) w.1 = 1 := if_neg hc
        have e2 : chiAt I.Ch w c = 1 := dif_neg hc
        rw [e1, e2]
        exact (map_one B.embLL).symm)
    (xiR t)
    (fun PP hPP x => by
      obtain ⟨b, k, h1, h2⟩ := exists_rep PP x
      have e1 := hxiR PP hPP b k x h1 h2
      have e2 := GlobalTheory.NormOneUnit.resChar_eq (hI.xi_reads (tup t))
        (GlobalTheory.Mem.ReadTwist.tameAt (hI.xi_reads (tup t)) fun v => Subgroup.mem_iInf.1 (I.tup (tup t)).2.1.2 v) PP x b k h1 h2.symm
      exact (congrArg (fun z : ℂˣ => (z : ℂ)) e1).trans e2.symm)
    (r_le_X (D := I.rec7 l Z))
  refine ⟨key.1, fun h κ hκ => Eq.trans ?_ (key.2 h κ hκ)⟩
  refine congrArg (fun z : ℂˣ => (z : ℂ)) (congrArg₂ (· * ·) (congrArg₂ (· * ·) rfl ?_) rfl)
  refine Finset.prod_congr rfl fun PP _ => Finset.prod_congr rfl fun c hc => ?_
  have e1 : cg (c + 1) PP = chi (c + 1) PP := if_pos (Finset.mem_range.1 hc)
  exact congrArg (fun f : (kP PP)ˣ →* ℂˣ => f _) e1.symm

end Cols

section Pack

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc GlobalTheory.MiS GlobalTheory.Fam
open Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem.Col2
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

theorem levRead_rows (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : Bl.RowsT K w Z Wt p0) :
    LevRead w.I w.l Z t.r.z.R.toLevCh (t.r.z.R.toRealDat.levR t.r.z.F.lv2 true) t.r.Y.tup :=
  levRead_of w.I w.ok w.pins w.l Z t.r.z.R.toLevCh _ t.r.z.lev.is (fun j => congrArg (fun C => C.mu0 j) t.r.z.lev.C) t.r.Y.tup
    (fun s => (t.r.z.lev.xiH s).trans (congrArg w.I.xi (t.r.tup_ix s).symm)) t.r.z.lev.Pg
    (fun s => (t.r.z.lev.Q s).trans (congrArg w.I.Q (t.r.tup_ix s).symm)) t.r.z.lev.beta.2 t.r.z.R.eG t.r.z.idG

set_option maxHeartbeats 1000000 in

theorem levRead_twArgs (K : Ctx) (B : GlobalTheory.Mem.Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : Bl.ColW B f T) (Z : w.Lt)
    (Wt : Set B.places.Pl) (L : SizeData₂ (w.st Z).toD7) (hT : GatTies (w.st Z).toD7) (Gi : G.Inst (w.st Z).toD7 L)
    (Gl : G.LatInst (w.st Z).toD7) (Kc : G.Consts) (Yd : DivX (w.st Z).toD7) (cX : ExtraC)
    (ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX) (t : Bl.RowsT K w Z Wt ex.p0) (a : R3.TwArgs ex t) :
    LevRead w.I w.l Z a.x.R.toLevCh (a.x.R.toRealDat.levR a.x.F.lv2 true) a.x.Y.tup := by
  have h := levRead_rows K B f T w Z Wt ex.p0 t
  cases a with
  | mk Dc Sp Zsc lam err lam_eq x pack intersectionNumber_baseChange hκ hv hfw htup htupT hjA hjA0 heMt hPY hPW heFT hIL heE heW hjW heRR =>
  cases x with
  | mk G Pl0 I0 T' A3 core R F cG geo pins err' Y Z' C' sEE div JA amb0 JM mjH =>
  cases pack
  have hT' : Y.tup = t.r.Y.tup := eq_of_heq htup
  rw [← hT'] at h
  exact (h)

set_option maxHeartbeats 1000000 in

theorem levRead_of_bWit {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c) (hw : Bl.BWit q b) :
    LevRead q.w.I q.w.l q.Z (pk (packB b)).toLevCh (lvP (packB b)) (packB b).P.I.tup := by
  obtain ⟨x, a, ax, y, -⟩ := hw
  have hx : a.x = x := eq_of_heq ax
  have h0 := levRead_twArgs _ _ _ _ q.w q.Z _ _ _ _ _ _ _ _ _ _ a
  have h1 : LevRead q.w.I q.w.l q.Z x.R.toLevCh (x.R.toRealDat.levR x.F.lv2 true) x.Y.tup := by
    subst hx
    exact h0
  have h2 : (fun k : Bl.RPk b.R b.S => LevRead q.w.I q.w.l q.Z k.B.Q.Rl.toRealDat.toLevCh
      (k.B.Q.Rl.toRealDat.levR k.B.Q.F.lv2 true) k.P.I.tup) (Bl.rpkB b) := by
    rw [y.eq]
    exact h1
  exact h2

set_option maxHeartbeats 1000000 in

theorem levIs_of_bWit {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ}
    (b : Bundle (q.w.D q.Z) q.O c) (hw : Bl.BWit q b) (u : (q.w.D q.Z).what₂.Word) (t : (packB b).P.T)
    (h : (packB b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) :
    LevIs ((packB b).R.T.tw.pt.cls u ((packB b).P.I.tup t) h).lev
      (levS _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t))
      (levChi _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) := by
  have hxi : b.R.T.n.tp.xi = q.w.I.xi := (congrArg (fun s => s.2.xi) hw.recPin.s.chr).trans q.x.n.xi
  obtain ⟨l0, s, he, hs, -, -, hP⟩ := (colsStd_of_bWit q b hw).2.2.2.2
  have key : ∀ (Tw : TwForms (q.w.D q.Z)) (s' : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes b.R.T.n.tp b.R.T.cols Tw), Tw = TC.tw q.w.I q.w.l l0 q.Z →
      HEq s' s → LevIs (s'.pt.cls u ((packB b).P.I.tup t) h).lev
        (levS _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t))
        (levChi _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) := by
    rintro _ s' rfl rfl
    refine levRead_of_bWit q b hw t h _ _ _ _ _ (fun v hv => hv.imp id fun hv => ?_) (s'.pt.chi_fin u _ h) (hP.what₂ u _ h)
    have h1 := (s'.ch.Q_iff _ v).1 hv
    unfold Formalism.L2.Host.TupTied.InQ' at h1
    rw [hxi] at h1
    exact underQ_of_ram q.w.ok _ v h1
  exact key _ _ he hs

theorem levChi_of_bWit : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {p : Bl.Prm hL} {K : Ctx} (q : Bl.WPt p.s K) {c : ℝ} (b : Bundle (q.w.D q.Z) q.O c), Bl.BWit q b → ∀ (u : (q.w.D q.Z).what₂.Word) (t : (packB b).P.T) (h : (packB b).P.I.tup t ≠ (q.w.D q.Z).what₂.mu0) (g : GA (q.w.D q.Z) (q.w.D q.Z).sp.X') (κ : ((packB b).R.T.tw.pt.cls u ((packB b).P.I.tup t) h).lev.U), GlobalTheory.Core.Rk.Top.HasMat g κ.1 → (levChi _ (pk (packB b)).βX (datXP (pk (packB b)) (lvP (packB b)) t)) g = star ((((packB b).R.T.tw.pt.cls u ((packB b).P.I.tup t) h).lev.chi κ : ℂˣ) : ℂ) :=
  fun q _ b hw u t h g κ hm => (levIs_of_bWit q b hw u t h).2 g κ hm

end Pack

end GlobalTheory.TopVal.LevTw

end
