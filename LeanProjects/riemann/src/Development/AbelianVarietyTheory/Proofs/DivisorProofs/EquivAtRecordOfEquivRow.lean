import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Formalism.LocalToGlobal.ProjectiveLattices.FnDefC
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ColumnDataLaws
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ActLevAndActBC
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsEmbExt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelEquivCompare

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.FieldBC GlobalTheory.IndefiniteRowSideFullHecke.ColumnDataLaws

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Field

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ}

theorem isBC_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c a n) :
    IsBC hle (rulBC hle f) (fun _ : Fin 1 => (1 : c'.F)) (fun _ => f) := by
  intro S _ _ _ h y
  rw [((GlobalTheory.T.ruleBaseChange_section_values_semilinear E H Dw l Xo c c' hle).1 a n f hf).2 S h y]
  simp

theorem mem_cusp_of_isBC (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {f' : Rul Xo c'}
    {as : Fin m → c'.F} {fs : Fin m → Rul Xo c} (hf' : f' ∈ sec Xo c' a n) (hfs : ∀ i, fs i ∈ cusp Xo c U a n)
    (h : IsBC hle f' as fs) : f' ∈ cusp Xo c' (unfBC hle U) a n := by
  rw [mem_cusp]
  refine ⟨hf', fun σ' hσ' => ?_⟩
  rw [rdU_unfBC hle U σ' h, laU_unfBC]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (((mem_cusp _ _ _ _ _ _).1 (hfs i)).2 _ hσ')

theorem mem_cusp_of_isBC_one (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f' : Rul Xo c'}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) (hf' : f' ∈ cusp Xo c' (unfBC hle U) a n)
    (h : IsBC hle f' (fun _ : Fin 1 => (1 : c'.F)) (fun _ => f)) : f ∈ cusp Xo c U a n := by
  rw [mem_cusp] at hf' ⊢
  refine ⟨hf, fun σ hσ => ?_⟩
  obtain ⟨σ', rfl⟩ := exists_emb_ext hle σ
  have := hf'.2 σ' (goodEmb_ext hle hσ rfl)
  rw [rdU_unfBC hle U σ' h, laU_unfBC, Fin.sum_univ_one, map_one, one_smul] at this
  exact this

end Field

section Action

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {r : ℕ} {G : Type} [Group G]
  {lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}

theorem actLev_mem_sec (hL : ActLev (Xo := Xo) c lev) (g : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
    (hf : f ∈ sec Xo c a n) : actLev c lev g f ∈ sec Xo c a n :=
  actL_mem _ _ _ _ hL.total hL.nat hL.bor _ g hf

theorem keeps_iff (hL : ActLev (Xo := Xo) c lev) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (g : G)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    (∀ f ∈ cusp Xo c U a n, actLev c lev g f ∈ cusp Xo c U a n) ↔
      ∀ f' ∈ cusp Xo c' (unfBC hle U) a n, actLev c' lev g f' ∈ cusp Xo c' (unfBC hle U) a n := by
  obtain ⟨hL', hB⟩ := actLev_and_actBC D H Dw l Xo c c' hle G lev hL
  constructor
  · intro h f' hf'
    obtain ⟨m, as, fs, hfs, hBC⟩ := GlobalTheory.SecFieldChange.cuspBC_holds hle U a n f' hf'
    exact mem_cusp_of_isBC hle U (actLev_mem_sec hL' g hf'.1) (fun i => h _ (hfs i))
      (hB a n g m as fs f' hf'.1 (fun i => (hfs i).1) hBC)
  · intro h f hf
    have h1 := ((rulBC_cusp _ H Dw l Xo c c' hle r U a n f hf.1).2).2 hf
    exact mem_cusp_of_isBC_one hle U (actLev_mem_sec hL g hf.1) (h _ h1)
      (hB a n g 1 _ _ _ h1.1 (fun _ => hf.1) (isBC_rulBC hle hf.1))

theorem reading_iff (hL : ActLev (Xo := Xo) c lev) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (g : G)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (Φ Ψ : FDSec (U (σ'.comp (incF c c' hle))).X →ₗ[ℂ] ℂ) :
    (∀ f ∈ cusp Xo c U a n, Φ (rdU (U _) (actLev c lev g f)) = Ψ (rdU (U _) f)) ↔
      ∀ f' ∈ cusp Xo c' (unfBC hle U) a n,
        Φ (rdU (unfBC hle U σ') (actLev c' lev g f')) = Ψ (rdU (unfBC hle U σ') f') := by
  obtain ⟨hL', hB⟩ := actLev_and_actBC D H Dw l Xo c c' hle G lev hL
  constructor
  · intro h f' hf'
    obtain ⟨m, as, fs, hfs, hBC⟩ := GlobalTheory.SecFieldChange.cuspBC_holds hle U a n f' hf'
    rw [rdU_unfBC hle U σ' hBC, rdU_unfBC hle U σ' (hB a n g m as fs f' hf'.1 (fun i => (hfs i).1) hBC), map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, map_smul, h _ (hfs i)]
  · intro h f hf
    have h1 := ((rulBC_cusp _ H Dw l Xo c c' hle r U a n f hf.1).2).2 hf
    have h2 := h _ h1
    have hBC := isBC_rulBC hle hf.1
    rw [rdU_unfBC hle U σ' hBC, rdU_unfBC hle U σ' (hB a n g 1 _ _ _ h1.1 (fun _ => hf.1) hBC), Fin.sum_univ_one,
      Fin.sum_univ_one, map_one, one_smul, one_smul] at h2
    exact h2

theorem levR_iff (hA : l.A = 1) {g g' : (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)} (h : g.1 = g'.1)
    {S : Type} [CommRing S] [Algebra c.F S] (y y' : FrPt Xo c S) : levR g y y' ↔ levR g' y y' := by
  have h1 : ∀ a, Xo.univ.etaA (g.2 a) = Xo.univ.etaA (g'.2 a) := fun a => by
    have e := Xo.univ.etaA_ker (g.2 a)
    have e' := Xo.univ.etaA_ker (g'.2 a)
    rw [hA, one_smul] at e e'
    exact e.trans e'.symm
  unfold levR IsLevMove
  simp only [h, h1]

theorem levActR_eq (hA : l.A = 1) {lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ g, (lev g).1 = (lev' g).1) :
    (fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev g y y') =
      fun {S : Type} [CommRing S] [Algebra c.F S] (g : G) (y y' : FrPt Xo c S) => levActR (Xo := Xo) (c := c) lev' g y y' := by
  funext S _ _ g y y'
  exact propext (levR_iff hA (h g) y y')

theorem actLev_congr (hA : l.A = 1) {lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ g, (lev g).1 = (lev' g).1) : actLev (Xo := Xo) c lev = actLev c lev' := by
  funext g
  unfold actLev
  rw [levActR_eq hA h]

theorem actLaws_congr (hA : l.A = 1) {lev' : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)}
    (h : ∀ g, (lev g).1 = (lev' g).1) : ActLev (Xo := Xo) c lev ↔ ActLev (Xo := Xo) c lev' := by
  unfold ActLev
  rw [levActR_eq hA h]

end Action

section Weights

variable {D : D7}

theorem cuspA_congr {T : Core D} (h : LawsM T) {j : ℕ} (hj : InR D j) {a a' : (D.host.E →+* ℂ) × ℕ → ℕ} (n : ℕ)
    (ha : ∀ τ i, i < (T.Q.Dw j).mult τ → a (τ, i) = a' (τ, i)) : T.cuspA j a n = T.cuspA j a' n := by
  have hex : ex (T.Q.Dw j) a n = ex (T.Q.Dw j) a' n := by
    funext x
    rcases x with _ | ⟨τ, i⟩
    · rfl
    · exact ha τ i i.2
  have hla : ∀ σ, GoodEmb T.Q.c σ → laU (T.U j σ) a n = laU (T.U j σ) a' n := by
    intro σ hσ
    obtain ⟨h1, h2, -⟩ := h.unf j hj σ hσ
    have hs : Function.Surjective (relab (E := D.host.E) T.Q.c σ) :=
      Finite.injective_iff_surjective.1 (relab_injective _ σ)
    funext k τ i
    have hp0 := (h2 k).1
    have hi := i.2
    have hτ : τ.1 (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := ((h2 k).2 τ.1).1 τ.2
    unfold laU
    split_ifs with hh
    · rw [ha]
      rw [Datum.mult, if_pos ((relab_rt_iff _ σ hσ _).1 (by rw [Function.rightInverse_invFun hs]; exact hτ))]
      omega
    · rw [ha]
      rw [Datum.mult, if_neg fun h' => ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both T.Q.H τ.1 ⟨hτ, by
        have := (relab_rt_iff _ σ hσ _).2 h'
        rw [Function.rightInverse_invFun hs] at this
        exact this⟩]
      omega
  ext f
  rw [mem_cusp, mem_cusp, sec, sec, hex]
  exact and_congr_right fun _ => forall_congr' fun σ => forall_congr' fun hσ => by rw [hla σ hσ]

def wtOf (j : ℕ) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (ha : Dom a n) : WeightFamilies.Wt D j where
  aP t i := a (DV.tauEmb D t, i)
  aM t i := a (ComplexEmbedding.conjugate (DV.tauEmb D t), i)
  aPlus_antitone _ _ _ hik := ha.1 _ hik
  aM_anti _ _ _ hik := ha.1 _ hik
  n := n
  n_even := ha.2

theorem cuspA_wtOf {T : Core D} (h : LawsM T) {j : ℕ} (hj : InR D j) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (ha : Dom a n) :
    T.cuspA j (wtA (wtOf j ha)) n = T.cuspA j a n := by
  obtain ⟨-, -, h1, h2, h3⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q h.pins j hj (wtOf j ha)
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  refine cuspA_congr h hj n fun τ i hi => ?_
  by_cases hτ : InPsi T.Q.H τ
  · obtain ⟨t, rfl⟩ := (h1 τ).1 hτ
    rw [Datum.mult, if_pos (show _ = _ from hτ), hp] at hi
    rw [(h3 t i).1, ext0, dif_pos hi]
    rfl
  · obtain ⟨t, rfl⟩ := (h2 τ).1 hτ
    rw [Datum.mult, if_neg (show ¬ _ = _ from hτ), hq] at hi
    rw [(h3 t i).2, ext0, dif_pos hi]
    rfl

end Weights

section Compare

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} {i : Fin D.R.m}

theorem inR (i : Fin D.R.m) : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩

section Second

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Y : RowDat T G i) (R : RealDat D A Ks)

def ClauseBig (cc : Y.U.Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ g : G, ∀ f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) Y.c' Y.U' a n, Y.act' g f ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) Y.c' Y.U' a n ∧
    ∀ κ, IsLift R i g κ → ∀ x, Y.phi cc (Y.act' g f) x = chiDetW R i g * Y.phi cc f (x * κ)

def phiSmall (cc : Y.U.Comp → ℂ) (f : T.R ((i : ℕ) + 1)) : GA D (Wc D i) → ℂ :=
  adel (Wc D i) Y.dict (muPin (Wc D i) Y.dict Y.mu cc) (rdU Y.U f)

def ClauseSmall (cc : Y.U.Comp → ℂ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ g : G, ∀ f ∈ T.cuspA ((i : ℕ) + 1) a n, actLev T.Q.c Y.lev g f ∈ T.cuspA ((i : ℕ) + 1) a n ∧
    ∀ κ, IsLift R i g κ → ∀ x, phiSmall Y cc (actLev T.Q.c Y.lev g f) x = chiDetW R i g * phiSmall Y cc f (x * κ)

theorem levelEquiv_iff_forall (cc : Y.U.Comp → ℂ) :
    Y.LevelEquiv R cc ↔ ∀ a, Dom a (Vc D i).rank → ClauseBig Y R cc a (Vc D i).rank := Iff.rfl

theorem clauseSmall_iff_big (hL : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c Y.lev) (cc : Y.U.Comp → ℂ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : ClauseSmall Y R cc a n ↔ ClauseBig Y R cc a n := by
  have h1 := fun g => keeps_iff Y.hle hL (T.U ((i : ℕ) + 1)) g a n
  have h2 := fun g (κ x : GA D (Wc D i)) => reading_iff Y.hle hL (T.U ((i : ℕ) + 1)) Y.σ' g a n
    (LinearMap.proj x ∘ₗ adel (Wc D i) Y.dict (muPin (Wc D i) Y.dict Y.mu cc))
    (chiDetW R i g • (LinearMap.proj (x * κ) ∘ₗ adel (Wc D i) Y.dict (muPin (Wc D i) Y.dict Y.mu cc)))
  exact ⟨fun h g f hf => ⟨(h1 g).1 (fun f hf => (h g f hf).1) f hf,
      fun κ hκ x => (h2 g κ x).1 (fun f hf => (h g f hf).2 κ hκ x) f hf⟩,
    fun h g f hf => ⟨(h1 g).2 (fun f hf => (h g f hf).1) f hf,
      fun κ hκ x => (h2 g κ x).2 (fun f hf => (h g f hf).2 κ hκ x) f hf⟩⟩

theorem ties_iff (F : Face D A) : Y.Ties R F ↔
    LawsJ T ∧ R.Char F ∧ VStd D i ∧ T.chiW ((i : ℕ) + 1) T.σ₀ = R.mu0 ((i : ℕ) + 1) ∧
      IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) ∧ T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧
      LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) (fun g => (Y.lev g).1) ∧ ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c Y.lev :=
  ⟨fun h => ⟨h.laws, h.char, h.std, h.chi, h.base, h.half, h.lev, h.act⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8, actLev_of_le Y.hle _ h8,
      GlobalTheory.SecFieldChange.cuspBC_holds Y.hle _, (actLev_and_actBC D _ _ _ _ _ _ Y.hle G _ h8).2⟩⟩

end Second

variable [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {Tp : Type} {tup : Tp → T0}

def Match (O : OMDat T.toCore R i Tp tup) (Y : RowDat T G i) : Prop := ∀ g, (Y.lev g).1 = O.lev g

def rowOf (O : OMDat T.toCore R i Tp tup) : RowDat T G i where
  c' := O.c'
  hle := O.hle
  lev := O.lev2
  hV := O.hV

theorem match_rowOf (O : OMDat T.toCore R i Tp tup) : Match O (rowOf O) := fun _ => rfl

def bigCoeff {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {l : Level H} (c : Coeff l) : Coeff l where
  F := c.F ⊔ D.what₂.embLL.toRatAlgHom.fieldRange
  fin := by
    haveI := c.fin
    haveI : FiniteDimensional ℚ D.what₂.embLL.toRatAlgHom.fieldRange :=
      (AlgEquiv.ofInjectiveField D.what₂.embLL.toRatAlgHom).toLinearEquiv.finiteDimensional
    infer_instance
  conj τ a := (le_sup_left : c.F ≤ _) (c.conj τ a)
  zeta_mem := (le_sup_left : c.F ≤ _) c.zeta_mem
  le := c.le.trans le_sup_left

variable (R) in

def omOf (Y : RowDat T G i) : OMDat T.toCore R i Empty Empty.elim where
  c' := bigCoeff Y.c'
  hle := Y.hle.trans le_sup_left
  jL := D.what₂.embLL.codRestrict (bigCoeff Y.c').F fun x =>
    (le_sup_right : D.what₂.embLL.toRatAlgHom.fieldRange ≤ _) ⟨x, rfl⟩
  hV := Y.hV
  c0' := 0
  lev g := (Y.lev g).1
  dδ t := t.elim
  Cl' t := t.elim
  fCl t := t.elim
  bad t := t.elim
  Lh t := t.elim
  La t := t.elim
  Nc t := t.elim
  gam t := t.elim
  vol t := t.elim
  ep t := t.elim
  B t := t.elim
  epF t := t.elim
  io := 0
  hw := 0
  φ t := t.elim
  w t := t.elim
  U₂ t := t.elim
  dict₂ t := t.elim
  xi t := t.elim
  thAd t := t.elim
  Plc t := t.elim

theorem match_omOf (Y : RowDat T G i) : Match (omOf R Y) Y := fun _ => rfl

variable {O : OMDat T.toCore R i Tp tup} {Y : RowDat T G i}

theorem phi_eq (cc : Y.U.Comp → ℂ) (f : T.R ((i : ℕ) + 1)) : O.phi cc f = phiSmall Y cc f := rfl

theorem equivAt_iff_small (hA : T.Q.l.A = 1) (hM : Match O Y) (hlift : ∀ g, ∃ k, IsLift R i g k)
    (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (cc : Y.U.Comp → ℂ) : O.EquivAt κ cc ↔ ClauseSmall Y R cc (wtA κ) κ.n := by
  have e : actLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c Y.lev = actLev T.Q.c O.lev2 := actLev_congr hA hM
  unfold ClauseSmall
  rw [e]
  exact ⟨fun h g f hf => ⟨(h g _ (hlift g).choose_spec f hf).1, fun k hk x => (h g k hk f hf).2 x⟩,
    fun h g k hk f hf => ⟨(h g f hf).1, fun x => (h g f hf).2 k hk x⟩⟩

theorem equivAt_iff_big (hA : T.Q.l.A = 1) (hM : Match O Y) (hlift : ∀ g, ∃ k, IsLift R i g k)
    (hL : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c Y.lev) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) (cc : Y.U.Comp → ℂ) :
    O.EquivAt κ cc ↔ ClauseBig Y R cc (wtA κ) κ.n :=
  (equivAt_iff_small hA hM hlift κ cc).trans (clauseSmall_iff_big Y R hL cc _ _)

theorem forall_equivAt_iff (h : LawsM T.toCore) (hM : Match O Y) (hlift : ∀ g, ∃ k, IsLift R i g k)
    (hL : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c Y.lev) (cc : Y.U.Comp → ℂ) :
    (∀ κ : WeightFamilies.Wt D ((i : ℕ) + 1), κ.n = (Vc D i).rank → O.EquivAt κ cc) ↔ Y.LevelEquiv R cc := by
  have hA : T.Q.l.A = 1 := h.pins.2.1.2
  rw [levelEquiv_iff_forall]
  constructor
  · intro H a ha
    have h1 := (equivAt_iff_small hA hM hlift _ cc).1 (H (wtOf _ ha) rfl)
    refine (clauseSmall_iff_big Y R hL cc _ _).1 ?_
    unfold ClauseSmall at h1 ⊢
    rw [← cuspA_wtOf h (inR i) ha]
    exact h1
  · intro H κ hκ
    rw [equivAt_iff_big hA hM hlift hL, hκ]
    exact H _ (hκ ▸ dom_wtA κ)

variable (O) in

def TiesFirst (F : Face D A) : Prop :=
  LawsJ T ∧ R.Char F ∧ VStd D i ∧ T.chiW ((i : ℕ) + 1) T.σ₀ = R.mu0 ((i : ℕ) + 1) ∧
    IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) ∧ T.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧
    LevIs R i (iotaW T i) T.Q.l.M (Mfr T.Q.l) O.lev ∧ ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c O.lev2

theorem tiesFirst_of_pins [Nonempty Tp] {F : Face D A} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ} (hP : O.Pins κ v₀ (iotaW T i) x₀) (h1 : LawsJ T)
    (h2 : R.Char F) (h3 : T.chiW ((i : ℕ) + 1) T.σ₀ = R.mu0 ((i : ℕ) + 1))
    (h4 : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀)) : TiesFirst O F :=
  ⟨h1, h2, hP.lift.std, h3, h4, (hP.tuple (Classical.arbitrary Tp)).half.1, hP.lift.lev, hP.act.1⟩

theorem tiesFirst_iff (hM : Match O Y) (F : Face D A) : TiesFirst O F ↔ Y.Ties R F := by
  rw [ties_iff]
  have e : (fun g => (Y.lev g).1) = O.lev := funext hM
  unfold TiesFirst
  rw [e]
  refine and_congr_right fun h => ?_
  rw [actLaws_congr (lev := Y.lev) (lev' := O.lev2) h.pins.2.1.2 hM]

theorem forall_equivAt_iff_of_ties (hM : Match O Y) {F : Face D A} (h : Y.Ties R F) (cc : Y.U.Comp → ℂ) :
    (∀ κ : WeightFamilies.Wt D ((i : ℕ) + 1), κ.n = (Vc D i).rank → O.EquivAt κ cc) ↔ Y.LevelEquiv R cc :=
  forall_equivAt_iff h.laws.toLawsM hM (fun g => (h.lev g).imp fun _ hk => hk.1) h.act cc

theorem tiesFirst_of_record [Nonempty Tp] {F : Face D A} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (hC : R.Char F)
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ} (hP : O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) x₀) :
    TiesFirst O F ∧ (κ i).n = (Vc D i).rank := by
  have e0 : D.what₂.embLL.comp (algebraMap T.Q.c.F D.what₂.LL) = T.σ₀ :=
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 T.Q.c.F)) (RingHom.ext fun x =>
      (congrArg D.what₂.embLL (fw.alg_eq x)).trans (fw.laws.pins.2.2.1 x))
  have e1 : (sg0 D A).comp (algebraMap T.Q.c.F D.what₂.LL) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, e0]
  refine ⟨tiesFirst_of_pins hP fw.laws hC ?_ ?_, ?_⟩
  · have := (fw.chiR i D.what₂.embLL (e0 ▸ T.good_σ₀)).2.2.2.2 rfl
    rwa [e0] at this
  · have := fw.x0 i (sg0 D A) (e1 ▸ T.good_σ₀)
    rwa [e1] at this
  · rw [D.sp.V_rank _ (inR i).1 (inR i).2]
    exact (fw.kap i (D.eTau.symm 1)).2.2

end Compare

def RowFirst : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0)
    (O : OMDat T.toCore R i Tp tup), TiesFirst O F →
      ∃ cc, CUnit cc ∧ ∀ κ : WeightFamilies.Wt D ((i : ℕ) + 1), κ.n = (Vc D i).rank → O.EquivAt κ cc

def RowFirstFrame : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0)
    (O : OMDat T.toCore R i Tp tup), TiesFirst O F →
      ∃ cc, CUnit cc ∧ (rowOf O).FrameConst R cc ∧ ∀ κ : WeightFamilies.Wt D ((i : ℕ) + 1), κ.n = (Vc D i).rank → O.EquivAt κ cc

def RowSecond : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (i : Fin D.R.m) (Y : RowDat T G i),
    Y.Ties R F → Y.EquivAt R

def RowSecondFrame : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
    [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (i : Fin D.R.m) (Y : RowDat T G i),
    Y.Ties R F → Y.EquivFrameAt R

theorem rowFirst_iff : RowFirst ↔ RowSecond := by
  constructor
  · intro h D G _ _ Pl0 T0 A T _ R F i Y hY
    obtain ⟨cc, h1, h2⟩ := h D G Pl0 T0 A T R F i _ _ (omOf R Y) ((tiesFirst_iff (match_omOf Y) F).2 hY)
    exact ⟨cc, h1, (forall_equivAt_iff_of_ties (match_omOf Y) hY cc).1 h2⟩
  · intro h D G _ _ Pl0 T0 A T _ R F i Tp tup O hO
    have hY := (tiesFirst_iff (match_rowOf O) F).1 hO
    obtain ⟨cc, h1, h2⟩ := h D G Pl0 T0 A T R F i _ hY
    exact ⟨cc, h1, (forall_equivAt_iff_of_ties (match_rowOf O) hY cc).2 h2⟩

theorem rowFirstFrame_iff : RowFirstFrame ↔ RowSecondFrame := by
  constructor
  · intro h D G _ _ Pl0 T0 A T _ R F i Y hY
    obtain ⟨cc, h1, h0, h2⟩ := h D G Pl0 T0 A T R F i _ _ (omOf R Y) ((tiesFirst_iff (match_omOf Y) F).2 hY)
    exact ⟨cc, h1, h0, (forall_equivAt_iff_of_ties (match_omOf Y) hY cc).1 h2⟩
  · intro h D G _ _ Pl0 T0 A T _ R F i Tp tup O hO
    have hY := (tiesFirst_iff (match_rowOf O) F).1 hO
    obtain ⟨cc, h1, h0, h2⟩ := h D G Pl0 T0 A T R F i _ hY
    exact ⟨cc, h1, h0, (forall_equivAt_iff_of_ties (match_rowOf O) hY cc).2 h2⟩

theorem rowFirstFrame_of_equivRow (h : EquivRow) : RowFirstFrame :=
  rowFirstFrame_iff.2 fun D G _ _ Pl0 T0 A T _ R F i Y hY => h D G Pl0 T0 A _ R F T i Y hY

theorem rowFirst_of_equivRowBare (h : EquivRowBare) : RowFirst :=
  rowFirst_iff.2 fun D G _ _ Pl0 T0 A T _ R F i Y hY => h D G Pl0 T0 A _ R F T i Y hY

theorem equivariance_typings_equiv :
    (∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D)
      [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (i : Fin D.R.m),
      (∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), Match O (rowOf O)) ∧
      (∀ Y : RowDat T G i, Match (omOf R Y) Y) ∧
      ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup) (Y : RowDat T G i), Match O Y →
        (TiesFirst O F ↔ Y.Ties R F) ∧
        (Y.Ties R F →
          (∀ (cc : Y.U.Comp → ℂ) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)), O.EquivAt κ cc ↔ ClauseBig Y R cc (wtA κ) κ.n) ∧
          (∀ cc : Y.U.Comp → ℂ,
            (∀ κ : WeightFamilies.Wt D ((i : ℕ) + 1), κ.n = (Vc D i).rank → O.EquivAt κ cc) ↔ Y.LevelEquiv R cc) ∧
          ((∃ cc : Y.U.Comp → ℂ, CUnit cc ∧ ∀ κ : WeightFamilies.Wt D ((i : ℕ) + 1), κ.n = (Vc D i).rank → O.EquivAt κ cc) ↔
            Y.EquivAt R) ∧
          ((∃ cc : Y.U.Comp → ℂ, CUnit cc ∧ Y.FrameConst R cc ∧
            ∀ κ : WeightFamilies.Wt D ((i : ℕ) + 1), κ.n = (Vc D i).rank → O.EquivAt κ cc) ↔ Y.EquivFrameAt R))) ∧
    (RowFirst ↔ RowSecond) ∧ (RowFirstFrame ↔ RowSecondFrame) ∧
    (EquivRowBare → RowFirst) ∧ (EquivRow → RowFirstFrame) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ F _ => ⟨fun _ _ O => match_rowOf O, match_omOf, fun _ _ _ _ hM => ⟨tiesFirst_iff hM F, fun h =>
      ⟨fun cc κ => equivAt_iff_big h.laws.pins.2.1.2 hM (fun g => (h.lev g).imp fun _ hk => hk.1) h.act κ cc,
        forall_equivAt_iff_of_ties hM h,
        exists_congr fun cc => and_congr_right fun _ => forall_equivAt_iff_of_ties hM h cc,
        exists_congr fun cc => and_congr_right fun _ => and_congr_right fun _ => forall_equivAt_iff_of_ties hM h cc⟩⟩⟩,
    rowFirst_iff, rowFirstFrame_iff, rowFirst_of_equivRowBare, rowFirstFrame_of_equivRow⟩

theorem equivAt_record_of_equivRow (h : EquivRow) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {F : Face D A}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (fw : FWTie T R κ v₀) (hC : R.Char F) {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} {i : Fin D.R.m}
    (hP : OMPins T R κ v₀ O i) : ∃ cc, CUnit cc ∧ (rowOf (O i)).FrameConst R cc ∧ (O i).EquivAt (κ i) cc := by
  obtain ⟨h1, h2⟩ := tiesFirst_of_record fw hC hP.2
  obtain ⟨cc, h3, h4, h5⟩ := rowFirstFrame_of_equivRow h D G Pl0 T0 A T R F i _ _ (O i) h1
  exact ⟨cc, h3, h4, h5 _ h2⟩

end GlobalTheory.LevelEquivCompare
