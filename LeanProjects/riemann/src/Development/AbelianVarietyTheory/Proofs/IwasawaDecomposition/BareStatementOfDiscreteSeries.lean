import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasBareOfHasPk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalizationFreeStageTrueGroupColumnChoiceStep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FittingLaterStagesRowIsConstructionStateStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalGaloisDataShaLengthEqStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Bare

open GlobalTheory.MemN GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.Mem.TypePl Polynomial

attribute [local instance] GlobalTheory.Mem.Top.factType

def bareLayer (B : Base) (C : Cols B) (W : RowsRest B C) {rows₁ : Rows.Data B.R} (Y : NData B.R B.host rows₁)
    (χ : ∀ k, Y.PlG k → Fin B.R.m → (ZMod (B.host.g k))ˣ)
    (ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E Y.Om p)
    (h : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → W.shaLen p e = (n : ℚ)) :
    NData B.R B.host W.what₂ where
  Om := Y.Om
  instOm := Y.instOm
  algOm := Y.algOm
  acOm := Y.acOm
  plOm := Y.plOm
  ldat := ldat
  sha_eq := h
  Loc := Empty
  l := fun i => i.elim
  lPrime := fun i => i.elim
  j := fun i => i.elim
  j_range := fun i => i.elim
  mu := fun i => i.elim
  w := fun i => i.elim
  w_l := fun i => i.elim
  mu_w := fun i => i.elim
  w_tw := fun i => i.elim
  locs := fun _ _ => ∅
  locs_mem := fun _ _ i => i.elim
  O := fun i => i.elim
  instO := fun i => i.elim
  domO := fun i => i.elim
  dvrO := fun i => i.elim
  algO := fun i => i.elim
  finO := fun i => i.elim
  topO := fun i => i.elim
  trO := fun i => i.elim
  O_adic := fun i => i.elim
  O_complete := fun i => i.elim
  embK := fun i => i.elim
  embK_w := fun i => i.elim
  X := fun i => i.elim
  finX := fun i => i.elim
  neX := fun i => i.elim
  T := fun i => i.elim
  T_local := fun i => i.elim
  T_sep := fun i => i.elim
  Mt := fun i => i.elim
  acgMt := fun i => i.elim
  modMt := fun i => i.elim
  freeMt := fun i => i.elim
  finMt := fun i => i.elim
  act := fun i => i.elim
  act_inj := fun i => i.elim
  prMt := fun i => i.elim
  prMt_span := fun i => i.elim
  prMt_lat := fun i => i.elim
  eig_ne := fun i => i.elim
  chi := fun i => i.elim
  chi_cont := fun i => i.elim
  chi_def := fun i => i.elim
  Z := fun i => i.elim
  Zgood := fun i => i.elim
  s0 := fun i => i.elim
  restNLevelExponent_of_odd := fun i => i.elim
  restNLevelExponent_of_two := fun i => i.elim
  S := fun i => i.elim
  Q := fun i => i.elim
  SQ_split := fun i => i.elim
  SQ_disj := fun i => i.elim
  SQ_l := fun i => i.elim
  S_def := fun i => i.elim
  hT := fun i => i.elim
  T_gen := fun i => i.elim
  gam0 := fun i => i.elim
  locNd_chebotarevPlace_mem := fun i => i.elim
  restN_tameGenerator_generates := fun i => i.elim
  chi_ram_Q := fun i => i.elim
  Bj := fun i => i.elim
  acgBj := fun i => i.elim
  modBj := fun i => i.elim
  freeBj := fun i => i.elim
  finBj := fun i => i.elim
  g_split := Y.g_split
  PlG := Y.PlG
  finPlG := Y.finPlG
  card_PlG := Y.card_PlG
  lab := fun _ _ _ => (Polynomial.X - 1) ^ B.R.r
  lab_monic := fun k _ _ => by
    have h1 : (Polynomial.X - 1 : Polynomial (ZMod (B.host.g k))) = Polynomial.X - Polynomial.C 1 := by simp
    rw [h1]
    exact ⟨(Polynomial.monic_X_sub_C _).pow _, by
      rw [(Polynomial.monic_X_sub_C _).natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]⟩
  chiT := χ
  restN_card_levelGroup_eq := rfl

set_option maxHeartbeats 4000000 in

theorem exists_nStage_over {B : Base} {C C₀ : Cols B} {W₀ : RowsRest B C₀} (N₀ : NStage B C₀ W₀) {f : Fr B.toPre}
    (h₀ : GrpTrue N₀ f) (W : RowsRest B C) (heta : ∀ j w, W.etaJ j w = 0)
    {rows₁ : Rows.Data B.R} (Y : NData B.R B.host rows₁) (A₁ : NAut Y) (hpl : ∀ k v, f.P.Div k (A₁.plGw k v)) (L : LocStage)
    (ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E Y.Om p)
    (hsha : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → W.shaLen p e = (n : ℚ))
    {G : Type} [Group G] (e₀ : G ≃* G0g N₀.nd)
    (a : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Amb μ))
    (b : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ G) →ₐ[ℂ] Module.End ℂ (W.Mt μ j))
    (ha : ∀ z : Subalgebra.center ℂ (MonoidAlgebra ℂ G),
      (∀ g, (z : MonoidAlgebra ℂ G).coeff g = N₀.ntypes.e0.coeff (e₀ g)) → (∀ μ, W.eOp μ = a μ z) ∧ ∀ μ j, W.eMt μ j = b μ j z) :
    ∃ N : NStage B C W, IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      (∀ μ z, N.ntypes.cenAmb μ z = a μ (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z)) ∧
      (∀ μ j z, N.ntypes.cenMt μ j z = b μ j (cenPull (e₀.trans (grpEquiv N₀.naut N.naut)) z)) ∧
      N.toLocStage = L ∧ HEq N.nd.Om Y.Om ∧ HEq N.nd.instOm Y.instOm ∧ HEq N.nd.algOm Y.algOm ∧ HEq N.nd.plOm Y.plOm ∧
      HEq N.nd.PlG Y.PlG ∧ HEq N.naut.plGw A₁.plGw := by
  let nd := bareLayer B C W Y (fun k _ j => omLab f.W k ^ (2 * (j.1 + 1))) ldat hsha
  haveI hE : IsEmpty nd.Loc := ⟨fun i : Empty => i.elim⟩
  let A : NAut nd := GaloisStage.nAut nd A₁.plGw A₁.plGw_over A₁.plGw_inj A₁.plGw_nconj
  have hl : ∀ k w (p : A.LP w), A.items₂ k w p = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  have hi : ∀ w (p : A.LP w) σ, A.inePol p σ = (X - 1) ^ A.lpDim p := fun _ _ _ => rfl
  choose tg htg using fun (k : Fin 2) (v : nd.PlG k) =>
    GlobalTheory.TameInertiaGen.exists_tameGenAt B.host.E nd.Om (A.plGw k v) (nd.plOm.1 (A.plGw k v)) (nd.plOm.2 _)
  choose s hs using fun k : Fin 2 => SerInhab.exists_isSer B.R.r (B.host.g k) B.toPre.restRowsFiniteGroupCard (B.host.g_prime k)
    B.toPre.restRowsFiniteGroupCard_pos ((dvd_pow_self _ (GaloisStage.f_pos B.R).ne').trans
      (Finset.dvd_prod_of_mem (fun k : Fin 2 => (Nat.card (GL (Fin B.R.r) (ZMod (B.host.g k)))) ^ B.R.f)
        (Finset.mem_univ k)))
  obtain ⟨T₀⟩ : Nonempty (NTypes A) := ⟨TypesInhab.types0 hl hi B.g_cond B.BB_disj tg htg s hs⟩
  obtain ⟨ω, -⟩ := TypesInhab.exists_char (A := MonoidAlgebra ℂ (G0g nd)) 0 one_ne_zero (by simp)
  let eR : G ≃* G0g nd := e₀.trans (grpEquiv N₀.naut A)
  let T : NTypes A := reser (retype T₀ hl hi (fun k => labDat (B.host.g k)) ω) N₀.ntypes
    (fun μ => (a μ).comp (cenPull eR)) (fun μ j => (b μ j).comp (cenPull eR))
  have hT : TypesTrue T f.P f.W :=
    ⟨fun k v => hpl k v, fun _ => rfl, fun _ _ _ => rfl, fun k p => h₀.ser k p⟩
  have hco : ∀ g, T.e0.coeff (grpEquiv N₀.naut A g) = N₀.ntypes.e0.coeff g := TypesTrue.typeIdempotent_coeff_across_layers h₀ hT
  have hc : T.e0 ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g nd)) := goodElement_mem_center_groupAlgebra T
  have hz := ha (cenPull eR ⟨T.e0, hc⟩) fun g => (coeff_cenPull eR _ g).trans (hco (e₀ g))
  have htie : T.IdempotentMatchesAction := by
    refine ⟨fun μ => ?_, fun μ j => ?_⟩
    · rw [NTypes.onAmb, dif_pos hc]
      exact hz.1 μ
    · rw [NTypes.onMt, dif_pos hc]
      exact hz.2 μ j
  have hy : ∀ x, ∃ y : ↥B.LL0, B.embLL (y : B.LL) = T.e0.coeff x := fun x => by
    obtain ⟨g, rfl⟩ := (grpEquiv N₀.naut A).surjective x
    exact ⟨_, (N₀.nStage_trivialCharacter_coeff_eq g).trans (hco g).symm⟩
  choose e hee using hy
  let tw := GaloisStage.nTw B.LL0 nd
  have hT' : IsEmpty tw.Tw := ⟨fun i : Empty => i.elim⟩
  obtain ⟨Y', hY, ⟨th⟩⟩ := exists_nexp_nth_of_isEmpty B C W nd tw hT' e
  exact ⟨{
    toLocStage := L
    nd := nd
    ntw := tw
    naut := A
    nbc := GaloisStage.nBC A
    nexp := Y'
    ntypes := T
    nStage_trivialCharacter_compat := htie
    nStage_trivialCharacter_coeff_eq := fun g => by rw [hY]; exact hee g
    nth := th
    nbr := fun i => hE.elim i
    nbr_ind := fun i => hE.elim i
    self_good := fun i => hE.elim i
    ntwbr := fun i => hT'.elim i
    ntwbr_ind := fun i => hT'.elim i
    loc_tie := fun i => hE.elim i
    bc_tie := fun i => hE.elim i
    rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i
    Z_tie := fun i => hE.elim i
    Zgood_tie := fun i => hE.elim i
    etaJ_tie := fun j w _ _ => (heta j w).trans (Finset.sum_eq_zero fun i _ => hE.elim i).symm },
    hE, hT, fun _ _ => rfl, fun _ _ _ => rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩

variable {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}

set_option maxHeartbeats 4000000 in

theorem exists_bare_over {K : Ctx} (P : Pre2 K w) {rows₁ : Rows.Data B.R} (Y : NData B.R B.host rows₁) (A₁ : NAut Y)
    (hpl : ∀ k v, f.P.Div k (A₁.plGw k v)) (L : LocStage) :
    ∃ N : NStage B w.C (P.q.W (fun _ _ => 0) fun _ _ => le_rfl), IsEmpty N.nd.Loc ∧ GrpTrue N f ∧
      (∀ V S G, GrpAt (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.I ∧
        ∀ eR, StdIso (w.st (RowPk.Over.Z ⟨_, _, V, S, N, G⟩)) w.px eR → CenIs P.q.p N eR) ∧
      N.toLocStage = L ∧ HEq N.nd.Om Y.Om ∧ HEq N.nd.instOm Y.instOm ∧ HEq N.nd.algOm Y.algOm ∧ HEq N.nd.plOm Y.plOm ∧
      HEq N.nd.PlG Y.PlG ∧ HEq N.naut.plGw A₁.plGw := by
  letI := P.z.alg
  obtain ⟨ldat₀, hsha₀⟩ := P.q.sha
  have hD := fun (p : ℕ) [Fact p.Prime] => GlobalTheory.T.exists_localGaloisData_shaLength_eq (Ω' := Y.Om) p (ldat₀ p)
  let ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData B.host.E Y.Om p := fun p _ => (hD p).choose
  have hsha : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < B.R.t → ∀ n : ℕ,
      Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → (P.q.W (fun _ _ => 0) fun _ _ => le_rfl).shaLen p e = (n : ℚ) :=
    fun p _ e h1 h2 n hn => hsha₀ p e h1 h2 n (((hD p).choose_spec (e : ℤ)).symm.trans hn)
  let e₀ : Gc B w.px ≃* G0g P.Z₀.N.nd := P.z.R.eG.trans P.z.cG
  have hgood : ∀ g, B.embLL ((idemOf P.z.Xg).coeff g) = P.Z₀.N.ntypes.e0.coeff (e₀ g) := P.z.good.2
  obtain ⟨N, hE, hN, hA, hM, hL, h1, h2, h3, h4, h5, h6⟩ := exists_nStage_over P.Z₀.N P.grp
    (P.q.W (fun _ _ => 0) fun _ _ => le_rfl) (fun _ _ => rfl) Y A₁ hpl L ldat hsha e₀
    (fun μ => (P.q.p.sA true μ).act) (fun μ j => (P.q.p.sL μ j).act) fun z hz =>
      ⟨fun μ => e_eq_act (P.q.t.tA true μ) (P.q.t.lawsA true μ) z fun g => (hgood g).trans (hz g).symm,
       fun μ j => e_eq_act (P.q.p.tL μ j) (P.q.t.lawsL μ j) z fun g => (hgood g).trans (hz g).symm⟩
  have hpl' : ∀ k v, P.Z₀.N.naut.plGw k ((plEquiv P.Z₀.N.naut N.naut k).symm v) = N.naut.plGw k v := fun k v => by
    rw [← TypesTrue.plGw_plEquiv P.grp hN, Equiv.apply_symm_apply]
  refine ⟨N, hE, hN, fun V S G => ⟨?_, fun eR hR => ?_⟩, hL, h1, h2, h3, h4, h5, h6⟩
  · obtain ⟨plg, hp⟩ := P.grpAt.pl
    obtain ⟨hc, hi⟩ := GlobalTheory.GoodLatCompare.goodSeriesIdempotent_central_idempotent
      (w.st (RowPk.Over.Z (q := P.q) ⟨_, _, V, S, N, G⟩)).toD7
    refine ⟨⟨(Equiv.sigmaCongrRight fun k => (plEquiv P.Z₀.N.naut N.naut k).symm).trans plg, fun kv => ?_⟩, hi, hc⟩
    exact ⟨(hp ⟨kv.1, _⟩).1.trans (hpl' kv.1 kv.2), (hp ⟨kv.1, _⟩).2⟩
  · have he : e₀.trans (grpEquiv P.Z₀.N.naut N.naut) = eR := by
      obtain ⟨plg, iso, h1, h2⟩ := hR
      obtain ⟨plg₀, iso₀, k1, -, -, k2⟩ := P.z.pins.keep.grp
      refine MulEquiv.ext fun g => funext fun kv => ?_
      exact (read_unique g (P.z.R.eG g) (P.z.idG g) (plg kv) (plg₀ ⟨kv.1, (plEquiv P.Z₀.N.naut N.naut kv.1).symm kv.2⟩)
        ((h1 kv).trans ((k1 ⟨kv.1, _⟩).trans (hpl' kv.1 kv.2)).symm) (iso kv) (iso₀ ⟨kv.1, _⟩) (h2 g kv) (k2 g ⟨kv.1, _⟩)).symm
    subst he
    exact ⟨fun μ z z' hz x => by rw [hA, cenPull_eq _ hz], fun μ j z z' hz x => by rw [hM, cenPull_eq _ hz]⟩

end GlobalTheory.Mem.R3.Rw.Bare

namespace GlobalTheory.HeightCounting.Up

open Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice GlobalTheory.Mem.R3.Rw.Bare

set_option maxHeartbeats 4000000 in

theorem bareStatement_of_known_theorems : PrN → GlobalTheory.Published.DiscreteSeriesExists → BareK := by
  intro hP hD
  refine StepW.of_all fun K B' f' T' w' hO _ _ P' X f hB hf hg => ?_
  obtain ⟨B₀, C₀, W₀, V₀, S₀, N₀, G₀⟩ := X
  cases B'
  cases B₀
  dsimp only at hB
  subst hB
  obtain rfl := eq_of_heq hf
  obtain ⟨N, hE, hN, hN', hL, h1, h2, h3, h4, h5, h6⟩ := exists_bare_over P' N₀.nd N₀.naut hg.pl N₀.toLocStage
  obtain ⟨V, hV, -, -, hη, -, hB⟩ := exists_divStage_of_pk _ w'.C (Gc _ w'.px) P'.q.p P'.q.e P'.q.W₀ P'.q.n
    (fun _ _ => 0) (fun _ _ => le_rfl) (frames_unit P'.q.t) (fun u => ((w'.C.fm u).lat 0).L) (fun _ => 0)
    (6 * K.s.x ^ (-K.C.P.CF))
  obtain ⟨S, -⟩ := GlobalTheory.Mem.SProv.exists_sStage_true K _ w'.C (P'.q.W (fun _ _ => 0) fun _ _ => le_rfl) P'.Z₀.G.cd hO
    (GlobalTheory.Mem.Df.cols_pos w'.I w'.ok w'.pins w'.l P'.hX) (rows_le P'.q.t)
  obtain ⟨x, hx⟩ := GlobalTheory.T.fittingLaterStages_row_is_constructionState GlobalTheory.weilRepresentationUnitaryPair hD hP.hc hP.decay K _ _ T' w' P' ⟨_, _, V, S, N, P'.Z₀.G⟩
    ⟨hV, hN, (hN' V S P'.Z₀.G).1, (hN' V S P'.Z₀.G).2⟩ rfl hη (fun hr => hB hr)
  have hDx : Dof x = (w'.st (RowPk.Over.Z (q := P'.q) ⟨_, _, V, S, N, P'.Z₀.G⟩)).toD7 := by
    unfold Dof
    rw [hx]
  have hE' : IsEmpty x.o.N.nd.Loc := by
    rw [hx]
    exact hE
  refine ⟨x, hE', ?_⟩
  rw [hDx]
  exact ⟨⟨rfl, HEq.rfl, congrArg LocStage.loc hL.symm, h1.symm, h2.symm, h3.symm, h4.symm, h5.symm⟩, h6.symm⟩

end GlobalTheory.HeightCounting.Up

end
