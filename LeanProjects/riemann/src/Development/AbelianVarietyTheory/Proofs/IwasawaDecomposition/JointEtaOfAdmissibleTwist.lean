import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicFormsLevelGroupEqTwistLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePlaceLevelPlacesDistinctUnderlying
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSplitTwistPlaceOverProductCharacterRamifie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.JointLevel

open scoped TensorProduct
open Formalism.IndefR Formalism.BasicNotions.TH GlobalTheory.MtRead GlobalTheory.MtLev
open Formalism.L2.DIV (redFn rTup levFn kP blockTri blk2 blkOf dBlk upperLeftBlock ext1 G0 Pl)

section Loc

variable {D : D7} {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V n}

theorem locM_eq_one {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} {κ : GAf D.host.E n} (h : TrivOutside {v} κ)
    (s : SplitPlace D.host.E) (hs : s.v ≠ v) : NX.locM s κ = 1 := by
  have h1 := h s.v hs
  let π : D.host.E ⊗[maximalRealSubfield D.host.E] s.v.adicCompletion (maximalRealSubfield D.host.E) →+*
      s.v.adicCompletion (maximalRealSubfield D.host.E) :=
    (Algebra.TensorProduct.lift s.i (AlgHom.id _ _) (fun _ _ => Commute.all _ _)).toRingHom
  have hπ : ∀ z, s.proj z = π (compAt D.host.E s.v z) := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul a b => rfl
  refine Matrix.ext fun a b => ?_
  have h2 := congrFun (congrFun h1 a) b
  change s.proj (κ.1.1 a b) = _
  rw [hπ]
  rw [Matrix.map_apply] at h2
  rw [h2]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem red_eq_one (hP : IdFrame hF P) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} {κ : GAf D.host.E n}
    (hU : κ ∈ Umax D.host.E n) (h : TrivOutside {v} κ) (s : SplitPlace D.host.E) (hs : ¬ NG.OverPl s.w v) :
    redFn 1 s.w (Lev.finE V (P.ψ κ)) = 1 := by
  obtain ⟨hn, -⟩ := id hP
  have h1 := locM_eq_one h s fun e => hs (e ▸ s.w_under)
  ext a c
  by_cases hac : a = c
  · subst hac
    rw [(loc_one hP hn hU s a).1 (by rw [h1]; simp)]
    simp
  · rw [(loc_zero hP hn hU s a c).1 (by
      rw [h1, Matrix.one_apply_ne (fun e => hac (Fin.cast_injective _ e))]; simp)]
    simp [Matrix.one_apply_ne hac]

theorem umax_of_para {s : SplitPlace D.host.E} {r : ℕ} {κ : GAf D.host.E n} (h : TrivOutside {s.v} κ)
    (hp : NG.ParaRT s r (s.loc n κ)) : κ ∈ Umax D.host.E n := by
  obtain ⟨h1, h2⟩ := GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hp.1
  refine GlobalTheory.HeckeScalarSph.mem_Umax_of_loc s κ h h1 fun i j => ?_
  rw [map_inv]
  exact h2 i j

theorem inParah_of_para {s : SplitPlace D.host.E} {r : ℕ} {κ : GAf D.host.E n} (hp : NG.ParaRT s r (s.loc n κ)) :
    NX.InParah s.v r (NX.locM s κ) :=
  ⟨(GlobalTheory.HeckeScalarSph.mem_GLint_iff.1 hp.1).1, hp.2⟩

theorem inLevG_of_uni {s : SplitPlace D.host.E} {r : ℕ} {κ : GAf D.host.E n} (hp : NG.UniRT s r (s.loc n κ)) :
    NX.InLevG s.v r (NX.locM s κ) :=
  ⟨inParah_of_para hp.1, hp.2⟩

end Loc

variable {D : D7}

def UniDat (iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv))
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (f : Formalism.IndefR.NX.U D.nd → ℂ) {n : ℕ}
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ n) : Prop :=
  ∃ hr : L.r = D.R.r, blkOf (n := n) L.r L.t = blk2 L.r ∧ (∀ PP, PP ∈ L.Pg ↔ ∃ kv, PP = NX.pG D kv) ∧
    (∀ PP ∈ L.Q, PP ∈ Set.range Pq ∧ IsSplitPl D.host PP ∧ ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) ∧
    ∃ eG : G0g D.nd ≃* G0 L.Pg L.r,
      (∀ (g : G0g D.nd) kv (h : NX.pG D kv ∈ L.Pg) (a c : Fin L.r),
        (eG g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val (Fin.cast hr a) (Fin.cast hr c))) ∧
      (∀ g, eG g ∈ L.P.H ↔ g ∈ Formalism.IndefR.NX.U D.nd) ∧
      ∀ g (h : eG g ∈ L.P.H) (h' : g ∈ Formalism.IndefR.NX.U D.nd), ((L.P.chi ⟨eG g, h⟩ : ℂˣ) : ℂ) = f ⟨g, h'⟩

section Dat

variable {iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {f : Formalism.IndefR.NX.U D.nd → ℂ}

theorem ut_one {m r : ℕ} {k : Type} [CommRing k] : UT r (1 : Matrix (Fin m) (Fin m) k) := fun a c _ _ =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq a⟩

theorem mem_lev_of_red {V : HSp D} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : UniDat iso Pq f L) (g : Formalism.L2.Theta.GA D V)
    (hSt : Lev.finE V g ∈ Formalism.L2.DIV.St (1 : GL (Fin V.rank) (Lev.EAf D)))
    (hg : ∀ kv, redFn 1 (NX.pG D kv) (Lev.finE V g) ∈ blockTri (blk2 D.R.r) ∧
      UT D.R.r (redFn 1 (NX.pG D kv) (Lev.finE V g)).val)
    (hq : ∀ PP ∈ L.Q, redFn 1 PP (Lev.finE V g) ∈ blockTri (blk2 D.R.r)) :
    Lev.finE V g ∈ Formalism.L2.DIV.lev D.sp.cm V.gram 1 L := by
  obtain ⟨r, hrn, t, s, Pg, Q, PL, cg, xq⟩ := L
  obtain rfl : r = D.R.r := hL.choose
  obtain ⟨hr, hb, hPg, -, eG, he, hH, -⟩ := hL
  refine Formalism.L2.DIV.mem_lev.2 ⟨Formalism.L2.DIV.mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V g, hSt, fun PP hPP => ?_, hq⟩, ?_⟩
  · obtain ⟨kv, rfl⟩ := (hPg PP).1 hPP
    rw [hb]
    exact (hg kv).1
  · set y : G0 Pg D.R.r := rTup 1 ⟨D.R.r, hrn, t, s, Pg, Q, PL, cg, xq⟩ (Lev.finE V g) with hy
    have h1 := hH (eG.symm y)
    rw [MulEquiv.apply_symm_apply] at h1
    refine h1.2 (Formalism.IndefR.NX.mem_U.2 fun kv => ?_)
    have key : ∀ a c, iso kv ((eG.symm y kv).val a c) =
        (redFn 1 (NX.pG D kv) (Lev.finE V g)).val (Fin.castLE hrn a) (Fin.castLE hrn c) := fun a c => by
      have e := he (eG.symm y) kv ((hPg _).2 ⟨kv, rfl⟩) a c
      rw [MulEquiv.apply_symm_apply] at e
      exact e.symm.trans (congrFun (congrFun (Formalism.L2.DIV.upper_block_val_submatrix hrn (hg kv).1) a) c)
    have hu := (UT_iff hrn _).1 (hg kv).2
    exact ⟨fun a c h => (iso kv).injective (by rw [key, (hu a c).1 h, map_zero]),
      fun a => (iso kv).injective (by rw [key, (hu a a).2 rfl, map_one])⟩

theorem unipotentBlockLevel_unipotentFactor_independent_of_datum {n : ℕ} {J : Matrix (Fin n) (Fin n) D.host.E} {L L' : Formalism.L2.DIV.LevDat D.host.E ℂ n} (hL : UniDat iso Pq f L)
    (hL' : UniDat iso Pq f L') {x : GL (Fin n) (Lev.EAf D)} (hx : x ∈ Formalism.L2.DIV.lev D.sp.cm J 1 L)
    (hx' : x ∈ Formalism.L2.DIV.lev D.sp.cm J 1 L') :
    ext1 L.P.H L.P.chi (rTup 1 L x) = ext1 L'.P.H L'.P.chi (rTup 1 L' x) := by
  obtain ⟨r, hrn, t, s, Pg, Q, PL, cg, xq⟩ := L
  obtain rfl : r = D.R.r := hL.choose
  obtain ⟨hr, hb, hPg, -, eG, he, hH, hc⟩ := hL
  obtain ⟨r', hrn', t', s', Pg', Q', PL', cg', xq'⟩ := L'
  obtain rfl : r' = D.R.r := hL'.choose
  obtain ⟨hr', hb', hPg', -, eG', he', hH', hc'⟩ := hL'
  have h1 := hx.2
  have h2 := hx'.2
  rw [Formalism.L2.DIV.extendOne_of_mem _ h1, Formalism.L2.DIV.extendOne_of_mem _ h2]
  generalize hy : rTup 1 ⟨D.R.r, hrn, t, s, Pg, Q, PL, cg, xq⟩ x = y at h1
  generalize hy' : rTup 1 ⟨D.R.r, hrn', t', s', Pg', Q', PL', cg', xq'⟩ x = y' at h2
  obtain ⟨u, rfl⟩ := eG.surjective y
  obtain ⟨u', rfl⟩ := eG'.surjective y'
  obtain rfl : u = u' := by
    funext kv
    ext a c
    refine (iso kv).injective ?_
    have e := he u kv ((hPg _).2 ⟨kv, rfl⟩) a c
    have e' := he' u' kv ((hPg' _).2 ⟨kv, rfl⟩) a c
    rw [← hy] at e
    rw [← hy'] at e'
    exact e.symm.trans e'
  exact Units.ext ((hc u h1 ((hH u).1 h1)).trans (hc' u h2 ((hH u).1 h1)).symm)

theorem levFn_pow {n : ℕ} {L : Formalism.L2.DIV.LevDat D.host.E ℂ n} (hL : UniDat iso Pq f L) {x : GL (Fin n) (Lev.EAf D)}
    (kv : Σ kk : Fin 2, D.nd.PlG kk) (hg : ∀ kv', NX.pG D kv' ≠ NX.pG D kv → redFn 1 (NX.pG D kv') x = 1)
    (hq : ∀ PP ∈ L.Q, redFn 1 PP x = 1) :
    levFn 1 L x ^ (D.host.g kv.1 - 1) = ext1 L.P.H L.P.chi (rTup 1 L x) ^ (D.host.g kv.1 - 1) := by
  obtain ⟨-, -, hPg, -⟩ := hL
  unfold levFn
  rw [Finset.prod_eq_one (s := L.Q) fun PP hPP => by rw [hq PP hPP, dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one], mul_one, mul_pow,
    ← Finset.prod_pow, Finset.prod_eq_one (s := L.Pg), mul_one]
  intro PP hPP
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun c _ => ?_
  obtain ⟨kv', rfl⟩ := (hPg PP).1 hPP
  by_cases h : NX.pG D kv' = NX.pG D kv
  · generalize dBlk (blkOf L.r L.t) (c + 1) (redFn 1 (NX.pG D kv') x) = z
    generalize NX.pG D kv' = PP at h z
    subst h
    haveI : Fact (D.host.g kv.1).Prime := ⟨D.host.g_prime _⟩
    obtain ⟨y, rfl⟩ := (Units.mapEquiv (iso kv).toMulEquiv).surjective z
    rw [← map_pow, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one, map_one]
  · rw [hg kv' h, dBlk, Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one, map_one, one_pow]

end Dat

section Shape

variable {iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv)}
  {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {f : Formalism.IndefR.NX.U D.nd → ℂ}
  {V : HSp D} {hF : D.host.F = maximalRealSubfield D.host.E} {P : principalLevelFrame.RowPsi V D.R.nV}

theorem over_unique {PP : PlE D.host} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (h : NG.OverPl PP v)
    (h' : NG.OverPl PP v') : v = v' := HeightOneSpectrum.ext (h.symm.trans h')

theorem natCast_mem_of_over {PP PP' : PlE D.host} {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} (h : NG.OverPl PP v)
    (h' : NG.OverPl PP' v) {p : ℕ} (hp : (p : 𝓞 D.host.E) ∈ PP.asIdeal) : (p : 𝓞 D.host.E) ∈ PP'.asIdeal := by
  have h1 : (p : 𝓞 (maximalRealSubfield D.host.E)) ∈ v.asIdeal := by
    rw [← h, Ideal.mem_comap, map_natCast]; exact hp
  rw [← h', Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem red_one' (hP : IdFrame hF P) {v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))} {κ : GAf D.host.E D.R.nV}
    (hU : κ ∈ Umax D.host.E D.R.nV) (h : TrivOutside {v} κ) {PP : PlE D.host} (hs : ∃ s : SplitPlace D.host.E, s.w = PP)
    (hv : ¬ NG.OverPl PP v) : redFn 1 PP (Lev.finE V (P.ψ κ)) = 1 := by
  obtain ⟨s, rfl⟩ := hs
  exact red_eq_one hP hU h s hv

theorem para_mem (hP : IdFrame hF P) (hPq : ∀ v, NG.OverPl (Pq v) v) (hsp : ∀ kv, ∃ s : SplitPlace D.host.E, s.w = NX.pG D kv)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : UniDat iso Pq f L) {s : SplitPlace D.host.E} (hs : s.w ∈ Set.range Pq)
    (hg : s.v ∉ Formalism.L2.gPl D) {κ : GAf D.host.E D.R.nV} (h : TrivOutside {s.v} κ) (hp : NG.ParaRT s D.R.r (s.loc _ κ)) :
    Lev.finE V (P.ψ κ) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram 1 L := by
  obtain ⟨hn, -⟩ := id hP
  have hU := umax_of_para h hp
  refine mem_lev_of_red hL _ ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V _ hF P hP hn κ).1.1 hU) (fun kv => ?_) fun PP hPP => ?_
  · rw [red_one' hP hU h (hsp kv) fun ho => hg ⟨_, ho, kv.1, D.naut.plGw_over kv.1 kv.2⟩]
    exact ⟨one_mem _, ut_one⟩
  · obtain ⟨-, -, -, hQ, -⟩ := hL
    obtain ⟨⟨v, rfl⟩, h2, -⟩ := hQ PP hPP
    by_cases ho : NG.OverPl (Pq v) s.v
    · obtain ⟨v', hv'⟩ := hs
      have e1 : v = s.v := over_unique (hPq v) ho
      have e2 : v' = s.v := over_unique (hPq v') (hv' ▸ s.w_under)
      rw [e1, ← e2, hv']
      exact (inParah_iff hP hn hU s _).1 (inParah_of_para hp)
    · rw [red_one' hP hU h (GlobalTheory.OffBad.splitPlace_of_isSplitPl D _ h2) ho]
      exact one_mem _

theorem red_Q (hP : IdFrame hF P) {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : UniDat iso Pq f L) {s : SplitPlace D.host.E}
    {kv : Σ kk : Fin 2, D.nd.PlG kk} (hs : s.w = NX.pG D kv) {κ : GAf D.host.E D.R.nV} (hU : κ ∈ Umax D.host.E D.R.nV)
    (h : TrivOutside {s.v} κ) : ∀ PP ∈ L.Q, redFn 1 PP (Lev.finE V (P.ψ κ)) = 1 := by
  intro PP hPP
  obtain ⟨-, -, -, hQ, -⟩ := hL
  obtain ⟨-, h2, h3⟩ := hQ PP hPP
  refine red_one' hP hU h (GlobalTheory.OffBad.splitPlace_of_isSplitPl D _ h2) fun ho => h3 kv.1 ?_
  exact natCast_mem_of_over (PP := s.w) s.w_under ho (hs ▸ D.naut.plGw_over kv.1 kv.2)

theorem uni_mem (hP : IdFrame hF P) (hsp : ∀ kv, ∃ s : SplitPlace D.host.E, s.w = NX.pG D kv)
    {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : UniDat iso Pq f L) {s : SplitPlace D.host.E}
    {kv : Σ kk : Fin 2, D.nd.PlG kk} (hs : s.w = NX.pG D kv) (hoff : ∀ kv', NX.pG D kv' ≠ s.w → ¬ NG.OverPl (NX.pG D kv') s.v)
    {κ : GAf D.host.E D.R.nV} (h : TrivOutside {s.v} κ) (hp : NG.UniRT s D.R.r (s.loc _ κ)) :
    Lev.finE V (P.ψ κ) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram 1 L := by
  obtain ⟨hn, -⟩ := id hP
  have hU := umax_of_para h hp.1
  refine mem_lev_of_red hL _ ((GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V _ hF P hP hn κ).1.1 hU) (fun kv' => ?_) fun PP hPP => ?_
  · by_cases e : NX.pG D kv' = s.w
    · rw [e]
      exact (inLevG_iff hP hn hU s _).1 (inLevG_of_uni hp)
    · rw [red_one' hP hU h (hsp kv') (hoff kv' e)]
      exact ⟨one_mem _, ut_one⟩
  · rw [red_Q hP hL hs hU h PP hPP]
    exact one_mem _

theorem chr_pow (hP : IdFrame hF P) (hsp : ∀ kv, ∃ s : SplitPlace D.host.E, s.w = NX.pG D kv)
    {L L' : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank} (hL : UniDat iso Pq f L) (hL' : UniDat iso Pq f L') {s : SplitPlace D.host.E}
    {kv : Σ kk : Fin 2, D.nd.PlG kk} (hs : s.w = NX.pG D kv) (hoff : ∀ kv', NX.pG D kv' ≠ s.w → ¬ NG.OverPl (NX.pG D kv') s.v)
    {κ : GAf D.host.E D.R.nV} (h : TrivOutside {s.v} κ) (hκ : Lev.finE V (P.ψ κ) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram 1 L)
    (hκ' : Lev.finE V (P.ψ κ) ∈ Formalism.L2.DIV.lev D.sp.cm V.gram 1 L') :
    Lev.levChi V 1 L (P.ψ κ) ^ (D.host.g kv.1 - 1) = Lev.levChi V 1 L' (P.ψ κ) ^ (D.host.g kv.1 - 1) := by
  obtain ⟨hn, -⟩ := id hP
  have hU := (GlobalTheory.T.frameKeepsMatrices_splitPlace_reduction_local D V _ hF P hP hn κ).1.2 (Formalism.L2.DIV.parLev_St hκ.1)
  have hg : ∀ kv', NX.pG D kv' ≠ NX.pG D kv → redFn 1 (NX.pG D kv') (Lev.finE V (P.ψ κ)) = 1 := fun kv' e =>
    red_one' hP hU h (hsp kv') (hoff kv' (hs ▸ e))
  unfold Lev.levChi
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, levFn_pow hL kv hg (red_Q hP hL hs hU h),
    levFn_pow hL' kv hg (red_Q hP hL' hs hU h), unipotentBlockLevel_unipotentFactor_independent_of_datum hL hL' hκ hκ']

end Shape

theorem ek_toKk {ρ : GlobalTheory.SeriesTie.Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (b : Bool) (k : ℕ) (x : FractionRing (D.ntw.O i)) :
    ρ.ek i b k (NX.toKk D i k x) = ρ.e i b x := by
  have : (ρ.ek i b k).comp (NX.toKk D i k) = ρ.e i b := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (D.ntw.O i)) (RingHom.ext fun y => ?_)
    simp only [RingHom.comp_apply, NX.toKk, IsFractionRing.map, IsLocalization.map_eq]
    exact hρ.ek_e i b k y
  exact RingHom.congr_fun this x

theorem hasLaw_one {S T : HSp D} (B : GlobalTheory.ExportSeries.Base S T) {t : GlobalTheory.ExportSeries.Twist D Circle}
    {F : Bridge.Gf S → Formalism.IndefR.Links.PolF D T.rank S.rank} (hF : B.HasLaw t F) (h : Bridge.Gf S) (k : B.levJ t) :
    F (h * k) = ((B.levLam t k : ℂˣ) : ℂ) • F h := by
  have := hF 1 h k
  rwa [map_one, one_mul, OneMemClass.coe_one, map_one, Module.End.one_apply] at this

theorem rdV_law {ρ : GlobalTheory.SeriesTie.Setup D.ntw} {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool}
    {rd : GlobalTheory.SeriesTie.Rd ρ D.nexp i j b} (T : GlobalTheory.SeriesTie.CellTie hρ D.nexp rd) {k Q ψ} (h : IntegralHeckeForms.TwOK i k Q ψ)
    (φ : D.nexp.MtV i (j.1 + 1) b k Q ψ) : T.rdV k Q ψ φ ∈ (ρ.B i j b).formsC (ρ.tw i b k Q ψ) := by
  have h1 : φ ∈ Submodule.span (FractionRing (D.ntw.Ok i k)) (D.nexp.MtLat i (j.1 + 1) b k Q ψ : Set _) := by
    rw [D.nexp.MtLat_span]; trivial
  induction h1 using Submodule.span_induction with
  | mem x hx => exact ((T.rdV_mem h).1 hx).1
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ hx

section Rows

open Formalism.IndefR.Links Formalism.IndefR.RecTie Formalism.L2.DIV

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd}

theorem exists_iso (hK : Keep (A3 := A3) R.toRealDat F.lv2 cG) :
    (∀ PP, PP ∈ R.Pg ↔ ∃ kv, PP = NX.pG D kv) ∧
    ∃ iso : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv),
      ∀ kv (g : G0g D.nd) (h : NX.pG D kv ∈ R.Pg) a c, (cG.symm g ⟨NX.pG D kv, h⟩).val a c = iso kv ((g kv).val a c) := by
  obtain ⟨plg, iso, hplg, -, -, hiso⟩ := hK.grp
  have hplg' : ∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = NX.pG D kv := hplg
  refine ⟨fun PP => ⟨fun h => ⟨plg.symm ⟨PP, h⟩, by rw [← hplg', Equiv.apply_symm_apply]⟩,
    fun ⟨kv, h⟩ => h ▸ hplg' kv ▸ (plg kv).2⟩, ?_⟩
  have key : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (PP : R.Pg) (_ : (PP : Pl D.host.E) = NX.pG D kv)
      (is : ZMod (D.host.g kv.1) ≃+* kP PP.1), (∀ g, R.eG g PP = Formalism.UG.bc (is : ZMod (D.host.g kv.1) →+* kP PP.1)
        ((R.eG.trans cG) g kv)) → ∃ is' : ZMod (D.host.g kv.1) ≃+* kP (NX.pG D kv), ∀ (g : G0g D.nd) (h : NX.pG D kv ∈ R.Pg) a c,
          (cG.symm g ⟨NX.pG D kv, h⟩).val a c = is' ((g kv).val a c) := by
    rintro kv ⟨PP, hPP⟩ rfl is h
    refine ⟨is, fun g _ a c => ?_⟩
    have := h (R.eG.symm (cG.symm g))
    rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
    exact congrArg (fun x => x.val a c) this
  choose is his using fun kv => key kv (plg kv) (hplg' kv) (iso kv) fun g => hiso g kv
  exact ⟨is, his⟩

theorem joint_of {Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0} {M : MtFam D} (ad : MtAd Y M) {kKs : Ks →+* ↥D.LL0} {hk}
    {In : RatIn D (ratDatR R cG kKs hk)} (rat : RatAd Y cG kKs hk In) {cf : CharFrame D} {Rw low Pq}
    (Bs : SideB D cf Rw low Pq (ratDatR R cG kKs hk) In.hL In.eig In.θ) {YS : NExpRealS R cG (ratDatR R cG kKs hk)} {v₀}
    (ser : SerAt YS v₀ Bs.exp ad.PV cf Pq) (hlev : R.toLevCh.Is A3.A.μ0) (hK : Keep (A3 := A3) R.toRealDat F.lv2 cG)
    (hPq : ∀ v, NG.OverPl (Pq v) v) (hel : Elem D) (hQ : ∀ t, ∀ PP ∈ R.Q t, PP ∈ Set.range Pq)
    {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) {η : HChar D.host.E} (hη : η = R.C.mu0 j * R.xiH (Y.tupT μ))
    {i : D.ntw.Tw} (b : Bool) {k : ℕ} {Q : Finset (PlE D.host)} {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ}
    (hA : NX.AdmTw D i k Q ψ) (hT : IntegralHeckeForms.TwOK i k Q ψ) :
    Joint η (M μ (j.1 + 1) (by omega) (by omega)) Bs.exp b hA j := by
  classical
  obtain ⟨hPg, iso, hiso⟩ := exists_iso hK
  have hPg' : ∀ PP, PP ∈ R.Pg ↔ ∃ k v, PP = D.naut.plGw k v := fun PP =>
    (hPg PP).trans ⟨fun ⟨kv, h⟩ => ⟨kv.1, kv.2, h⟩, fun ⟨k, v, h⟩ => ⟨⟨k, v⟩, h⟩⟩
  have hP : IdFrame Y.hF (ad.PV j) := ad.id j
  obtain ⟨hn, -⟩ := id hP
  have hρ := ser.ex.good
  have hp := ser.ex.pin
  have hsp : ∀ kv, ∃ s : SplitPlace D.host.E, s.w = NX.pG D kv := fun kv =>
    ⟨_, (cell Bs.exp b hA j).sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))⟩
  let f : Formalism.IndefR.NX.U D.nd → ℂ := fun u => embLL0 D ((psiUOf D.nd (NX.xiRed D) In.θ u : (↥D.LL0)ˣ) : ↥D.LL0)
  have h1 : UniDat iso Pq f (datVP R.toRealDat j (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) := by
    refine ⟨rfl, ?_, hPg, fun PP hPP => ⟨hQ _ PP hPP,
      GlobalTheory.TwistSplitPlace.isSplitPl_of_not_isConjPl D PP ((hlev.Q_pl _ PP hPP).2 PP hPP), fun k hk => ?_⟩, cG.symm,
      fun g kv h a c => hiso kv g h a c, fun g => ?_, fun g h h' => ?_⟩
    · have e : D.R.t = (Vc D j).rank - D.R.r := by
        rw [hn]; exact (Nat.add_sub_cancel_left _ _).symm
      change blkOf D.R.r D.R.t = blk2 D.R.r
      rw [e]
      exact blockSizes_sub_eq_twoBlock _
    · obtain ⟨q, hq, hcard, -, hqg⟩ := (hlev.Q_pl _ PP hPP).1
      exact GlobalTheory.LevelTypePlace.not_two_primes PP.asIdeal (D.host.g_prime k) hq (hqg k).symm hk
        (GlobalTheory.LevelTypePlace.natCast_mem_of_card PP hcard hq.ne_zero)
    · have := rat.lvl (R.eG.symm (cG.symm g))
      rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this
      exact this
    · have e : (R.eG.trans cG) (R.eG.symm (cG.symm g)) = g := by
        rw [MulEquiv.trans_apply, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      have := rat.psi ⟨R.eG.symm (cG.symm g), h⟩ (e.symm ▸ h')
      simp only [e] at this
      change _ = D.what₂.embLL _
      have e2 := congrArg D.what₂.embLL this
      refine Eq.trans ?_ e2.symm
      rw [map_units_inv]
      have key : ∀ (L : Formalism.L2.DIV.LevelP R.Pg D.R.r ℂ) (hL : L = (R.toRealDat.levR F.lv2 false).conj) (x) (hx : x ∈ L.H),
          ((L.chi ⟨x, hx⟩ : ℂˣ) : ℂ) = (((R.toRealDat.levR F.lv2 false).chi ⟨x, by rw [hL] at hx; exact hx⟩ : ℂˣ) : ℂ)⁻¹ := by
        rintro _ rfl x hx
        exact Units.val_inv_eq_inv_val _
      exact (key _ (if_neg (by decide)) _ _).trans rfl
  have h2 : UniDat iso Pq f ((ser.ex.ρ.B i j b).levS (ser.ex.ρ.tw i b k Q ψ)) := by
    refine ⟨FWT.rank_Wc j, blockSizes_sub_eq_twoBlock _, fun PP => (hp.Pg i j b ▸ hPg PP :), fun PP hPP => ?_, ser.ex.ρ.eG i j b,
      fun g kv h a c => (hp.grp i j b g _ h (hp.Pg i j b ▸ h) a c).trans (hiso kv g _ _ _), fun g => ?_, fun g h h' => ?_⟩
    · rcases Finset.mem_union.1 (show PP ∈ (ser.ex.ρ.B i j b).de.Q ∪ (ser.ex.ρ.tw i b k Q ψ).Q from hPP) with h | h
      · rw [hρ.delta] at h
        obtain ⟨h3, h4⟩ := GlobalTheory.SeriesTie.mem_half.1 h
        have h5 : PP ∈ (D.ntw.pD i : Set _) := h3
        rw [D.ntw.pD_eq] at h5
        have h6 : PP ∈ placesOver D.host.E D.host.pde ∨ PP ∈ placesOver D.host.E D.host.pde' := by
          split_ifs at h5
          exacts [Or.inr h5, Or.inl h5]
        refine ⟨(ser.ch i PP (hel.split PP h6)).1 h4, hel.split PP h6, fun k hk => ?_⟩
        rcases h6 with h6 | h6
        · exact GlobalTheory.LevelTypePlace.not_two_primes PP.asIdeal D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h6 hk
        · exact GlobalTheory.LevelTypePlace.not_two_primes PP.asIdeal D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h6 hk
      · obtain ⟨h3, h4⟩ := GlobalTheory.SeriesTie.mem_half.1 h
        exact ⟨(ser.ch i PP (hT.1 PP h3)).1 h4, hT.1 PP h3, (hA.2.1 PP h3).2⟩
    · exact ((ser.ex.tie i j b).U_eq g).trans (by rw [Bs.exp.U_eq]; rfl)
    · have hu : g ∈ D.nexp.U := ((ser.ex.tie i j b).U_eq g).1 h
      refine ((ser.ex.tie i j b).psiU_eq ⟨g, hu⟩ h).trans ?_
      rw [Bs.psiU i b g hu h']
      exact hρ.e_LL0 i b _
  have hβ : (ser.ex.ρ.B i j b).F.βS = 1 := (hp.frS i j b).trans (hK.beta.1 j)
  obtain ⟨ω, hω, hjoin⟩ := ser.join i j b k Q ψ hA hT
  have hoff : ∀ (s : SplitPlace D.host.E) kv, s.w = NX.pG D kv → ∀ kv', NX.pG D kv' ≠ s.w → ¬ NG.OverPl (NX.pG D kv') s.v :=
    fun s kv hs kv' => (GlobalTheory.LevelTypePlace.offPlace D T R.toLevCh _ hlev hPg' (Y.tupT μ) s ((hPg _).2 ⟨kv, hs⟩)).1 _
      ((hPg _).2 ⟨kv', rfl⟩)
  refine ⟨MulEquiv.refl _,
    (lev D.sp.cm (Vc D j).gram 1 (datVP R.toRealDat j (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) ⊓
      lev D.sp.cm (Vc D j).gram 1 ((ser.ex.ρ.B i j b).levS (ser.ex.ρ.tw i b k Q ψ))).comap ((Lev.finE _).comp (ad.PV j).ψ),
    ser.ex.ρ.ek i b k, _, inferInstance, inferInstance, ω, ⟨fun _ => Iff.rfl, fun _ _ => Iff.rfl⟩,
    fun x => (ek_toKk hρ i b k _).trans (hρ.e_LL0 i b x), hω, fun v hv => ?_, fun kk v s hs κ h hu => ?_, fun κ hκ => ?_⟩
  · obtain ⟨s, rfl, hs⟩ := GlobalTheory.TwistSplitPlace.exists_splitPlace_of_mem_qPl D T R.toLevCh _ hlev j (Y.tupT μ) v (hη ▸ hv)
    exact ⟨s, rfl, fun κ h hu => ⟨para_mem hP hPq hsp h1 (hQ _ _ hs) hv.1 h hu, para_mem hP hPq hsp h2 (hQ _ _ hs) hv.1 h hu⟩⟩
  · exact ⟨uni_mem hP hsp h1 (kv := ⟨kk, v⟩) hs (hoff s ⟨kk, v⟩ hs) h hu,
      uni_mem hP hsp h2 (kv := ⟨kk, v⟩) hs (hoff s ⟨kk, v⟩ hs) h hu⟩
  · obtain ⟨hκ1, hκ2⟩ := hκ
    refine ⟨Lev.levChi (Vc D j) 1 (datVP R.toRealDat j (Y.tupT μ) (R.toRealDat.levR F.lv2 false)) ((ad.PV j).ψ κ),
      Lev.levChi (Vc D j) 1 ((ser.ex.ρ.B i j b).levS (ser.ex.ρ.tw i b k Q ψ)) ((ad.PV j).ψ κ), fun x g => ?_, fun φ g => ?_,
      fun kk v s hs h => chr_pow hP hsp h1 h2 (kv := ⟨kk, v⟩) hs (hoff s ⟨kk, v⟩ hs) h hκ1 hκ2⟩
    · refine (ad.eW μ hμ j).injective ?_
      rw [map_smul, ad.read μ hμ, ad.read μ hμ, map_mul]
      have h3 := (Y.IL.jMt μ hμ j x).2.2 ((ad.PV j).ψ κ)
      rw [← hK.beta.1 j] at hκ1 ⊢
      exact h3 ⟨(ad.PV j).into κ, hκ1⟩ _
    · beta_reduce
      rw [← hjoin, ← hjoin, MulEquiv.refl_apply, MonoidHom.map_mul, MonoidHom.map_mul]
      have h3 := (GlobalTheory.ExportSeries.Base.mem_formsC _).1 (rdV_law (ser.ex.tie i j b) hT φ)
      rw [← hβ] at hκ2
      have hk : GlobalTheory.FormInner.frameEquiv (ad.PV j) κ ∈ (ser.ex.ρ.B i j b).levJ (ser.ex.ρ.tw i b k Q ψ) :=
        (mem_levJ_iff _ _ _ κ).2 hκ2
      have h4 := hasLaw_one _ h3.2 (GlobalTheory.FormInner.frameEquiv (ad.PV j) g) ⟨_, hk⟩
      have e3 : (((ser.ex.ρ.B i j b).levLam (ser.ex.ρ.tw i b k Q ψ) ⟨_, hk⟩ : ℂˣ) : ℂ) =
          Lev.levChi (Vc D j) 1 ((ser.ex.ρ.B i j b).levS (ser.ex.ρ.tw i b k Q ψ)) ((ad.PV j).ψ κ) := by
        rw [← hβ]; rfl
      rw [← e3]
      simp only [GlobalTheory.FormInner.frameEquiv_apply] at h4
      exact h4

end Rows

theorem joint : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AllSt fun _ B _ T w P x => ∀ (l : StrictHenselianAcyclic hL x) (v : B.places.Pl) (i : (Dof x).ntw.Tw) (b : Bool) (ψ : G (Dof x).host.E (Dof x).nd.Om →* ((Dof x).ntw.Ok i (T.k v))ˣ) (hA : NX.AdmTw (Dof x) i (T.k v) (QOf P v) ψ) (j : Fin (Dof x).R.m), TwistedAt (Dof x) v → (Dof x).ntw.l i = B.places.resChar v → IntegralHeckeForms.TwOK i (T.k v) (QOf P v) ψ → Joint (D := Dof x) (eta (D := Dof x) (cfOf x) w.I.xi v j) (mtAt (D := Dof x) l.mt.M v j) l.b.Bs.exp b hA j := by
  intro _ hL
  refine StepW.of_all ?_
  intro K B f T w _ _ _ P x l v i b ψ hA j hv _ hT
  have hon : (Dof x).what₂.muTw v = (Dof x).what₂.muAt v := (P.q.mu.on v (GlobalTheory.HeightCounting.Up.Model.mem_of_twisted x v hv)).symm
  have hμ : Formalism.IndefR.RecTie.Used0 (Dof x) ((Dof x).what₂.muTw v) := Or.inr ⟨v, hon⟩
  refine joint_of (D := Dof x) l.mt.ad l.rat.rat l.b.Bs l.b.ser x.m.z.lev.is x.m.z.pins.keep l.Pq_over l.a.elem (fun t PP hPP => ?_)
    hμ j ?_ b hA hT
  · rw [x.m.z.lev.Q] at hPP
    rw [l.sel]
    obtain ⟨u, -, e⟩ := (Formalism.L2.Col.mem_QE _ _ _).1 hPP
    exact ⟨u, e⟩
  · have e1 := x.m.z.lev.xiH (x.r.Y.tupT ((Dof x).what₂.muTw v))
    have e2 := x.m.tup (x.r.Y.tupT ((Dof x).what₂.muTw v))
    rw [← x.r.tup, x.r.Y.tupTie _ hμ] at e2
    rw [e1, ← e2, x.m.z.lev.C]
    rfl

end GlobalTheory.JointLevel
end
