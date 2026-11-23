import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesOfLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroIndexPlacesAdelicDataResizedEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapExtensionOverEnlargedBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFamilyCoefficientMapsMulRootOfUnity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapEnlargedBaseEqComplexMultiple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapsAgreeRootOfUnityEnlarged

set_option autoImplicit false

noncomputable section

section Lemmas

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.SerMove.Io

theorem cx_form {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
    {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (b : Bool) (hp : (lv (fc X.zs) b).Pos) (h2 : X.H2 cr b) (h5 : X.H5 cr b)
    (hE : X.PartsE b) (hD : X.DimParts b) (j : Bs.J) : ∃ x : A.FL j Bs.μ0, x ≠ 0 := by
  by_contra hn
  push Not at hn
  have ht : X.tC cr b j Bs.μ0 = 0 := by
    have e : (fun k => X.θ' j Bs.μ0 (X.jL j Bs.μ0 (cr.toL X.zs b j Bs.μ0 (Pi.single k 1)))) = fun _ => 0 :=
      funext fun k => by rw [hn (cr.toL X.zs b j Bs.μ0 _), map_zero, map_zero]
    unfold CxData.tC
    rw [e]
    ext k
    simp [lin]
  have hw : LinearMap.range (X.w0C b j) = ⊥ := by rw [← (h5 j Bs.μ0).2, ht, LinearMap.range_zero]
  have hE0 : X.EEl b = ⊥ := by
    rw [← hE.2, iSup_eq_bot]
    intro p
    rw [← Submodule.finrank_eq_zero, ← hD j p, hw, inf_bot_eq, finrank_bot]
  have h0 : X.iC cr b Bs.μ0 = 0 := LinearMap.range_eq_bot.1 (h2.2.2.trans hE0)
  have h1 : (fun _ => 1 : Fin ((lv (fc X.zs) b).dQ Bs.μ0) → ℂ) = 0 := h2.1 (by rw [h0]; rfl)
  exact one_ne_zero (congrFun h1 ⟨0, hp⟩)

theorem exists_form {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (hP : Pins R F cG) (hH : Holds R F) (i : Fin D.R.m) :
    ∃ x : A3.A.fam.amb.FL i A3.A.μ0, x ≠ 0 :=
  have hRw := complex_data_conditions_base_level_of_primitive_links hH.ok hH.sep hP.char hH.prim
  cx_form (R.toCx3 F) F.cr false (hH.prim.pos false) (hRw.what₂ false).1 hRw.lifts0.1 (hH.prim.sumE false) hH.prim.dimParts i

set_option maxHeartbeats 1000000 in

theorem coefFam_roots {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (c0L : ∀ i : Fin D.R.m, Formalism.IndefR.FWT.VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (hc : OmExt.CoefFam R c0L) (a : Fin D.R.m → D.what₂.LL) (n : Fin D.R.m → ℕ) (hn : ∀ i, n i ≠ 0) (ha : ∀ i, a i ^ n i = 1) :
    OmExt.CoefFam R fun i => D.what₂.embLL (a i) • c0L i := by
  choose u hu h1 h2 using fun i => OmExt.RootUpd.exists_unit_of_pow (a i) (n i) (hn i) (ha i)
  obtain ⟨gramR, c0R, ht⟩ := hc
  exact ⟨gramR, c0R, ⟨ht.ranks, ht.v0, ht.tauL_ok, ht.pl_inj, ht.q, ht.S_fin, ht.ok, ht.gramR_eq, ht.mapR,
    fun j => OmExt.RootUpd.coefMapTie_smul (ht.mapL j) ((map_ne_zero _).2 (right_ne_zero_of_mul_eq_one (h2 j))),
    ht.coefR, fun j t => OmExt.RootUpd.coefTie_smul (ht.coefL j t) (a j) (u j) (hu j) (h1 j) (h2 j)⟩⟩

theorem sameModel_of_eq {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) {σ σ' : D.what₂.LL →+* ℂ} (h : σ = σ') :
    GlobalTheory.TwInputs.Move.SameModel (R.MW i σ) (R.MW i σ') := by
  subst h
  exact .refl _

variable {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}

set_option maxHeartbeats 4000000 in

theorem heq_io (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (hM : GlobalTheory.TwInputs.Move.SameModel M M') {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W]
    [nW' : NormedAddCommGroup W'] [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hiW : HEq iW' iW)
    (io : LowT M →ₗ[ℂ] W →ₗ[ℂ] PolF (w.st Z).toD7 (Wc (w.st Z).toD7 i).rank (Vc (w.st Z).toD7 i).rank)
    (io' : LowT M' →ₗ[ℂ] W' →ₗ[ℂ] PolF (w'.st Z').toD7 (Wc (w'.st Z').toD7 i').rank (Vc (w'.st Z').toD7 i').rank)
    (hio : HEq io' io) (u : ∀ τ, lowT M τ) (u' : ∀ τ, lowT M' τ)
    (hu : GlobalTheory.TwInputs.Move.SameVec (M := M) (M' := M') (fun τ => u τ) (fun τ => u' τ)) (y : W) (y' : W') (hy : HEq y' y) :
    HEq (io (PiTensorProduct.tprod ℂ u) y) (io' (PiTensorProduct.tprod ℂ u') y') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  subst hW
  cases hn
  cases hiW
  cases hy
  obtain ⟨a, b, c, d, l, e, g⟩ := hM
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e1 : u = u' := funext fun τ => Subtype.ext (Subtype.ext (eq_of_heq (hu τ τ HEq.rfl)))
  have e2 : io' = io := eq_of_heq hio
  subst e1
  subst e2
  exact HEq.rfl

set_option maxHeartbeats 4000000 in

theorem heq_pol (q : B'.toPre = B.toPre) (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    (ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hι : ∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y)
    (F : Formalism.L2.DIV.Pol (w.st Z).toD7.what₂.LL (w.st Z).toD7.what₂.Tau (Vc (w.st Z).toD7 i).rank)
    (F' : Formalism.L2.DIV.Pol (w'.st Z').toD7.what₂.LL (w'.st Z').toD7.what₂.Tau (Vc (w'.st Z').toD7 i').rank)
    (hF : HEq (MvPolynomial.map ι F) F') :
    HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL F') (MvPolynomial.map (w.st Z).toD7.what₂.embLL F) := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  have e1 : MvPolynomial.map ι F = F' := eq_of_heq hF
  subst e1
  exact heq_of_eq ((MvPolynomial.map_map _ _ _).trans (congrArg (fun s => MvPolynomial.map s F) (RingHom.ext hι)))

section Lift
open OmExt LiftUnit Formalism.DivisionValues Formalism.L2.Col

set_option maxHeartbeats 4000000 in

theorem coef_schur (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hii : (i : ℕ) = i')
    (c0L) (hc : OmExt.CoefFam z.R.toRealDat c0L) (c0L'') (hc'' : OmExt.CoefFam z'.R.toRealDat c0L'') :
    ∃ μ : ℂ, ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L'' i' v') (μ • c0L i v) := by
  obtain ⟨gR, c0R, ht⟩ := hc
  obtain ⟨gR', c0R', ht'⟩ := hc''
  obtain ⟨hW, hρ, -⟩ := hN.BV i i' hii
  obtain ⟨hnW, hiW⟩ := hN.cV i i' hii
  have hcI := z.pins.char.base.models.cV i
  have hmapL := ht.mapL i
  have hmapL' := ht'.mapL i'
  have htau := ht.tauL_ok
  have htau' := ht'.tauL_ok
  clear hN
  obtain ⟨hpre, -, -, hR⟩ := hE
  cases B with | mk P => cases B' with | mk P' =>
  dsimp only at hpre
  subst hpre
  obtain rfl : i = i' := Fin.ext hii
  let ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL := (by with_unfolding_all exact ((enlEmb hR) :))
  have hι : ∀ x, (w'.st Z').toD7.what₂.embLL (ι x) = (w.st Z).toD7.what₂.embLL x := (by with_unfolding_all exact ((enlEmb_spec hR) :))
  let c'' : CoefA (Vc (w.st Z).toD7 i) :=
    { W := (z'.R.cV i).W, nW := (z'.R.cV i).nW, iW := (z'.R.cV i).iW, fW := (z'.R.cV i).fW, ρ := (z'.R.cV i).ρ }
  have hcc : c'' = z.R.cV i := coefA_eq _ _ hW hρ hnW hiW
  obtain ⟨μ, hμ⟩ := exists_smul_eq_enl (z.R.cV i) hcI ι (w'.st Z').toD7.what₂.embLL hι (labLL (w.st Z).toD7)
    (labLL (w'.st Z').toD7) (fun τ => (htau' τ).trans (htau τ).symm) (c0L i) hmapL c'' hcc (c0L'' i) hmapL'.1
  exact ⟨μ, fun v v' hv => hμ v v' (eq_of_heq hv)⟩

set_option maxHeartbeats 8000000 in

theorem agree_root (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (hstd : z.Std) (hB : z'.Std) (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hii : (i : ℕ) = i')
    (c0L) (hc : OmExt.CoefFam z.R.toRealDat c0L) (c0L'') (hc'' : OmExt.CoefFam z'.R.toRealDat c0L'')
    (x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (hx : x ≠ 0) :
    ∃ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL)
      (u : (w.st Z).toD7.what₂.LL) (u' : (w'.st Z').toD7.what₂.LL) (n n' : ℕ), n ≠ 0 ∧ u ^ n = 1 ∧ n' ≠ 0 ∧ u' ^ n' = 1 ∧
      HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) ∧ c0L i v ≠ 0 ∧
      HEq ((w'.st Z').toD7.what₂.embLL u' • c0L'' i' v') ((w.st Z).toD7.what₂.embLL u • c0L i v) := by
  obtain ⟨φ, rfl⟩ := ((mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
    ((i : ℕ) + 1)).res (mtKOk _ _ _ _ hX _)).surjective x
  have hφ : φ ≠ 0 := fun h0 => hx (h0 ▸ map_zero _)
  obtain ⟨h, hh⟩ : ∃ h, z.R.B.jL i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))
      ((mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1
        ((i : ℕ) + 1)).res (mtKOk _ _ _ _ hX _) φ) h ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (GlobalTheory.PresBasic.extL_injective (z.R.B.L i (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt)))).pres
      ((funext hn).trans (map_zero _).symm))
  obtain ⟨φ', hφφ⟩ := exists_form_enl w w' Wt Wt' hE hf hpx ((i : ℕ) + 1) ((i' : ℕ) + 1) (by rw [hii]) φ
  have hj := hN.jL i i' hii (mtKOk _ _ _ _ hX _) (mtKOk _ _ _ _ hX' _) φ φ' hφφ
  have hW := (hN.BV i i' hii).1
  obtain ⟨u, n, hn, hu, H⟩ := exists_root_reading (w.st Z) w.I hX _ z.Xg z.tr z.R.toRealDat w.ok z.lev i
    (z.pins.char.base.models.cV i) c0L hc (hstd.2 i) _ φ hφ
  obtain ⟨y, hy⟩ := RowCoord.exists_matEq (D := (w.st Z).toD7) (Vc (w.st Z).toD7 i) (LiftBrg.rkEq (w.st Z) i).symm
    (gram_eq_one (w.st Z) w.I w.ok i) h
  obtain ⟨v, hv1, hv2⟩ := H φ h y hy
  have H' := exists_root_reading (w'.st Z') w'.I hX' _ z'.Xg z'.tr z'.R.toRealDat w'.ok z'.lev i'
    (z'.pins.char.base.models.cV i') c0L'' hc'' (hB.2 i') _ φ'
  have hS := rowLevelPrimes_colTuples_eq_vGs w Wt
  have hS' := rowLevelPrimes_colTuples_eq_vGs w' Wt'
  clear H hN hB hstd hc hc''
  obtain ⟨hpre, -, -, -⟩ := hE
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  obtain rfl : i' = i := Fin.ext hii.symm
  have ep : w'.px = w.px := eq_of_heq hpx
  have hvG : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [ep]
    rfl
  have hjh := heq_apply (eq_of_heq hW) hj h
  have hSS := hS'.trans (hvG.trans hS.symm)
  have hd := hφφ _ _ (heq_decoOf (X := (baseOfColW w).fields) hSS y.1)
  have h0 : c0L i' v ≠ 0 := fun e => hh (hv2.trans ((congrArg _ e).trans (smul_zero (A := (z.R.cV i').W) _)))
  have hφ' : φ' ≠ 0 := fun e => hφ (Subtype.ext (funext fun d => Subtype.ext (by
    have e1 := eq_of_heq (hφφ d (cast (congrArg (DecoSet (baseOfColW w).fields.E (baseOfColW w).R.nV ∅) hSS.symm) d) (cast_heq _ _))
    rw [e] at e1
    exact MvPolynomial.map_injective _ (baseOfColW w).embLL.injective (e1.symm.trans ((map_zero _).trans (map_zero _).symm)))))
  obtain ⟨u', n', hn', hu', H⟩ := H' hφ'
  obtain ⟨v', hv1', hv2'⟩ := H φ' h y hy
  exact ⟨v, v', u, u', n, n', hn, hu, hn', hu', hv1'.trans (hd.trans hv1.symm), h0,
    (heq_of_eq hv2'.symm).trans (hjh.trans (heq_of_eq hv2))⟩

set_option maxHeartbeats 4000000 in

theorem one_lift (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (hstd : z.Std) (hB : z'.Std) (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hii : (i : ℕ) = i')
    (c0L) (hc : OmExt.CoefFam z.R.toRealDat c0L) (c0L'') (hc'' : OmExt.CoefFam z'.R.toRealDat c0L'')
    (x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (hx : x ≠ 0) :
    ∃ (a : (w'.st Z').toD7.what₂.LL) (n : ℕ), n ≠ 0 ∧ a ^ n = 1 ∧
      ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
        HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) →
          HEq ((w'.st Z').toD7.what₂.embLL a • c0L'' i' v') (c0L i v) := by
  obtain ⟨μ, hμ⟩ := coef_schur z z' hE hN i i' hii c0L hc c0L'' hc''
  obtain ⟨v, v', u, u', n, n', hn, hun, hn', hun', hvv, hv0, hrel⟩ :=
    agree_root z z' hE hf hpx hstd hB hN i i' hii c0L hc c0L'' hc'' x hx
  have hW := (hN.BV i i' hii).1
  obtain ⟨hnW, hiW⟩ := hN.cV i i' hii
  have key := OmCoef.smul_eq_of_heq (eq_of_heq hW) hnW hiW (hμ v v' hvv) hrel
  have hμe : (w'.st Z').toD7.what₂.embLL u' * μ = (w.st Z).toD7.what₂.embLL u := smul_left_injective ℂ hv0 key
  have hu0 : (w.st Z).toD7.what₂.embLL u ≠ 0 := (map_ne_zero _).2 fun h => by
    rw [h, zero_pow hn] at hun
    exact zero_ne_one hun
  obtain ⟨b, hb⟩ : (w.st Z).toD7.what₂.embLL u ∈ Set.range (w'.st Z').toD7.what₂.embLL := hE.2.2.2 ⟨u, rfl⟩
  have hb1 : b ^ n = 1 := (w'.st Z').toD7.what₂.embLL.injective (by rw [map_pow, hb, ← map_pow, hun, map_one, map_one])
  have ha : (u' * b⁻¹) ^ (n * n') = 1 := by
    have e1 : u' ^ (n * n') = 1 := by rw [mul_comm, pow_mul, hun', one_pow]
    have e2 : b ^ (n * n') = 1 := by rw [pow_mul, hb1, one_pow]
    rw [mul_pow, inv_pow, e1, e2, inv_one, mul_one]
  refine ⟨u' * b⁻¹, n * n', mul_ne_zero hn hn', ha, fun v1 v1' h => ?_⟩
  refine (OmCoef.heq_smul (eq_of_heq hW) hnW hiW (hμ v1 v1' h) _).trans (heq_of_eq ?_)
  have e1 : (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = 1 := by
    calc (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = ((w'.st Z').toD7.what₂.embLL u' * μ) * ((w.st Z).toD7.what₂.embLL u)⁻¹ := by
          rw [map_mul, map_inv₀, hb]; ring
      _ = 1 := by rw [hμe, mul_inv_cancel₀ hu0]
  rw [e1, one_smul]

end Lift

set_option maxHeartbeats 2000000 in

theorem exists_roots (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (hstd : z.Std) (hB : z'.Std) (hN : ExtN z z') (hH : Holds z.R z.F)
    (c0L) (hc : OmExt.CoefFam z.R.toRealDat c0L) (c0L'') (hc'' : OmExt.CoefFam z'.R.toRealDat c0L'') (i' : Fin (w'.st Z').toD7.R.m) :
    ∃ (a : (w'.st Z').toD7.what₂.LL) (n : ℕ), n ≠ 0 ∧ a ^ n = 1 ∧
      ∀ i : Fin (w.st Z).toD7.R.m, (i : ℕ) = i' → ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
        HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) →
          HEq ((w'.st Z').toD7.what₂.embLL a • c0L'' i' v') (c0L i v) := by
  by_cases h : ∃ i : Fin (w.st Z).toD7.R.m, (i : ℕ) = i'
  · refine h.elim fun i hi => (exists_form z.pins hH i).elim fun x hx => ?_
    refine (one_lift z z' hE hf hpx hstd hB hN i i' hi c0L hc c0L'' hc'' x hx).imp fun a h1 => h1.imp fun n h2 =>
      ⟨h2.1, h2.2.1, fun j hj => ?_⟩
    have e : j = i := Fin.ext (hj.trans hi.symm)
    subst e
    exact h2.2.2
  · exact ⟨1, 1, one_ne_zero, one_pow _, fun i hi => absurd ⟨i, hi⟩ h⟩

set_option maxHeartbeats 2000000 in

theorem sameModel_extN (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i') :
    GlobalTheory.TwInputs.Move.SameModel (z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) (z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) := by
  have s := sameModel_of_eq z.R.toRealDat i (ExtModel.sign_at_base_place_eq_embedding z)
  have s' := sameModel_of_eq z'.R.toRealDat i' (ExtModel.sign_at_base_place_eq_embedding z')
  have m := hN.MW i i' hi
  exact ⟨s.H.trans (m.1.symm.trans s'.H.symm), s.nacg.trans (m.2.1.symm.trans s'.nacg.symm), s.ips.trans (m.2.2.1.symm.trans s'.ips.symm),
    s.σ.trans (m.2.2.2.1.symm.trans s'.σ.symm), s.lam.trans (m.2.2.2.2.1.symm.trans s'.lam.symm),
    s.ε.trans (m.2.2.2.2.2.1.symm.trans s'.ε.symm), s.fr.trans (m.2.2.2.2.2.2.1.symm.trans s'.fr.symm)⟩

set_option maxHeartbeats 2000000 in

theorem io_at (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hN : ExtN z z')
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    (u : ∀ τ, lowT (z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) τ) (u' : ∀ τ, lowT (z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) τ)
    (hu : GlobalTheory.TwInputs.Move.SameVec (M := z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) (M' := z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) (fun τ => u τ) (fun τ => u' τ))
    (y : (z.R.cV i).W) (y' : (z'.R.cV i').W) (hy : HEq y' y) :
    HEq (z.R.ioP i (PiTensorProduct.tprod ℂ u) y) (z'.R.ioP i' (PiTensorProduct.tprod ℂ u') y') := by
  have hM := sameModel_extN z z' hN i i' hi
  have h1 := hN.BV i i' hi
  have h2 := hN.cV i i' hi
  have k := @heq_io B B' f f' T T' w w' Z Z' hE.1 i i' hi _ _ _ _ hM (z.R.cV i).W (z'.R.cV i').W (z.R.cV i).nW (z.R.cV i).iW
    (z'.R.cV i').nW (z'.R.cV i').iW (eq_of_heq h1.1) h2.1 h2.2 ((by with_unfolding_all exact ((z.R.ioP i) :))) ((by with_unfolding_all exact ((z'.R.ioP i') :))) ((by with_unfolding_all exact (h1.2.2.2.1 :))) u u' ((by with_unfolding_all exact (hu :))) y y' hy
  exact (by with_unfolding_all exact (k :))

set_option maxHeartbeats 4000000 in

theorem io_of_extN (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt') (hE : Enl0 B B') (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (hstd : z.Std) (hB : z'.Std) (hN : ExtN z z') (hH : Holds z.R z.F)
    (ι : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hι : ∀ y, (w'.st Z').toD7.what₂.embLL (ι y) = (w.st Z).toD7.what₂.embLL y) :
    ∃ c0L c0L', OmExt.CoefFam z.R.toRealDat c0L ∧ OmExt.CoefFam z'.R.toRealDat c0L' ∧
      ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
        ∀ (u : ∀ τ, lowT (z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A)) τ)
          (u' : ∀ τ, lowT (z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) τ),
          GlobalTheory.TwInputs.Move.SameVec (M := z.R.MW i (sg0 _ (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A))
            (M' := z'.R.MW i' (sg0 _ (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') z'.Xg z'.tr).A)) (fun τ => u τ) (fun τ => u' τ) →
        ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
          HEq (MvPolynomial.map ι v.1) v'.1 →
          HEq (z.R.ioP i (PiTensorProduct.tprod ℂ u) (c0L i v)) (z'.R.ioP i' (PiTensorProduct.tprod ℂ u') (c0L' i' v')) := by
  refine z.pins.char.base.fam.tie.elim fun g₁ h => h.elim fun c₁ h => h.elim fun c0L hT => ?_
  refine z'.pins.char.base.fam.tie.elim fun g₂ h => h.elim fun c₂ h => h.elim fun c0L'' hT'' => ?_
  have hc : OmExt.CoefFam z.R.toRealDat c0L := ⟨g₁, c₁, hT⟩
  have hc'' : OmExt.CoefFam z'.R.toRealDat c0L'' := ⟨g₂, c₂, hT''⟩
  have key := exists_roots z z' hE hf hpx hstd hB hN hH c0L hc c0L'' hc''
  choose a n hn ha H using key
  refine ⟨c0L, fun i => (w'.st Z').toD7.what₂.embLL (a i) • c0L'' i, hc, coefFam_roots z'.R.toRealDat c0L'' hc'' a n hn ha,
    fun i i' hi u u' hu v v' hv => ?_⟩
  have hy := H i' i hi v v' (heq_pol (w := w) (w' := w') (Z := Z) (Z' := Z') hE.1 i i' hi ι hι v.1 v'.1 hv)
  exact (by with_unfolding_all exact ((io_at z z' hE hN i i' hi u u' hu (c0L i v) ((w'.st Z').toD7.what₂.embLL (a i') • c0L'' i' v') hy) :))

end GlobalTheory.HeightCounting.SerMove.Io

end Lemmas

section Main

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr

theorem GlobalTheory.HeightCounting.SerMove.ioCl_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), IoCl (sideAt x g hg a) (sideAt x' g' hg' a') ι := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  exact (by with_unfolding_all exact (Io.io_of_extN (datAt x g) (datAt x' g') (isBaseEnlargementFixedCoefField_of_coeffEnlargement l.enl) l.fr l.px (StateChecks.St.std x) (StateChecks.St.std x') l.extN
    x.m.intersectionNumber_baseChange ι l.cp.embLL :))

end Main

end
