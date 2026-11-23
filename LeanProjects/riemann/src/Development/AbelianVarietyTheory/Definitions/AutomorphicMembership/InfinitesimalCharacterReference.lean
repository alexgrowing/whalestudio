import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DirectSumCancelRight
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin

noncomputable section

namespace GlobalTheory.HeightCounting.Up.RowModel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

theorem overRows_imp {p q : RowP} (h : OverRows p)
    (hpq : ∀ K B f T w Z Wt hX z p0 Y, p K B f T w Z Wt hX z p0 Y → q K B f T w Z Wt hX z p0 Y) : OverRows q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w c Z Wt hX z p0 Y a b d e g =>
    hpq _ B f T w Z Wt hX z p0 Y (H kp w c Z Wt hX z p0 Y a b d e g)

theorem overRows_and {p q : RowP} (h : OverRows p) (h' : OverRows q) :
    OverRows fun K B f T w Z Wt hX z p0 Y => p K B f T w Z Wt hX z p0 Y ∧ q K B f T w Z Wt hX z p0 Y :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w c Z Wt hX z p0 Y a b d e g =>
    ⟨H.1 kp w c Z Wt hX z p0 Y a b d e g, H.2 kp w c Z Wt hX z p0 Y a b d e g⟩

theorem overRows_atMem {hL : GlobalTheory.Published.LocalLanglandsGL} {p : RowP} (h : OverRows p) :
    AtMem hL fun K B f T w Z Wt p0 t _ _ _ => p K B f T w Z Wt t.hX t.r.z p0 t.r.Y :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp w Z Wt p0 t _ _ _ _ _ _ c =>
    H kp w c Z Wt t.hX t.r.z p0 t.r.Y t.r.intersectionNumber_baseChange t.exAt t.inGeo t.grp t.grpAt

theorem overRows_allSt {p : RowP} (h : OverRows p) :
    AllSt fun K B f T w P x => p K B f T w x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ _ _ H kp _ _ w s P x =>
    s.1.elim fun c => H kp w c x.o.Z P.Wt P.hX x.m.z x.s.p0 x.r.Y x.m.intersectionNumber_baseChange x.m.exAt x.m.inGeo x.fits.grp x.fits.grpAt

theorem cenLoc_of_cenUsed {D : D7} {M : MtFam D} (h : CenUsed D M) : CenLoc D M := fun i =>
  h _ (Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩) _
    (D.nd.j_range i).1 (D.nd.j_range i).2

theorem sumTw_of_sumUsed {D : D7} {M : MtFam D} (h : SumUsed D M) : SumTw D M := fun w hw j h1 h2 =>
  h _ (Or.inr ⟨w, ((D.what₂.muAt_or w).resolve_left hw).symm⟩) j h1 h2

open Classical in

def reset {D : D7} (Rw : RowSide D) (a : ∀ w, D.naut.LP w) : RowSide D where
  locR σ w := if ∃ k : Fin 2, w ∈ placesOver D.host.E (D.host.g k) then Rw.locR σ w else a w
  satR := Rw.satR
  lab_eq k σ v := by rw [if_pos ⟨k, D.naut.plGw_over k v⟩]; exact Rw.lab_eq k σ v

theorem one_lt_norm {D : D7} (w : PlE D.host) : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w

theorem rowLoc_reset {D : D7} (Rw : RowSide D) (σ : D.what₂.FT) :
    RowLoc D (reset Rw fun w => D.naut.lpUnr w (Multiset.replicate D.R.r 1)) σ := by
  intro w _ hw
  have e : (reset Rw fun w => D.naut.lpUnr w (Multiset.replicate D.R.r 1)).locR σ w = D.naut.lpUnr w (Multiset.replicate D.R.r 1) :=
    if_neg (not_exists.2 hw)
  have s := D.naut.lpUnr_spec w (Multiset.replicate D.R.r 1) (fun h => zero_ne_one (Multiset.eq_of_mem_replicate h))
  rw [e, s.2.1]
  refine ⟨s.1, fun α hα => ?_⟩
  rw [Multiset.eq_of_mem_replicate hα, norm_one]
  have ht : 1 < D.R.t := by have := D.R.three_m_lt_t; have := D.R.two_le_m; omega
  have : (1 : ℝ) < D.R.t := by exact_mod_cast ht
  exact Real.one_lt_rpow (one_lt_norm w) (by linarith)

theorem not_rowLoc_reset {D : D7} (Rw : RowSide D) (σ : D.what₂.FT) (w : PlE D.host) (hs : IsSplitPl D.host w)
    (hw : ∀ k : Fin 2, w ∉ placesOver D.host.E (D.host.g k)) :
    ¬ RowLoc D (reset Rw fun w => D.naut.lpUnr w
      {((((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) : ℝ) : ℂ)}) σ := by
  intro h
  have hp : 0 < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans (one_lt_norm w)) _
  have e : (reset Rw fun w => D.naut.lpUnr w
      {((((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) : ℝ) : ℂ)}).locR σ w = D.naut.lpUnr w
      {((((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) : ℝ) : ℂ)} := if_neg (not_exists.2 hw)
  have s := D.naut.lpUnr_spec w {((((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) : ℝ) : ℂ)}
    (fun h => hp.ne' (by exact_mod_cast (Multiset.mem_singleton.1 h).symm))
  have h2 := (h w hs hw).2
  rw [e, s.2.1] at h2
  have h3 := h2 _ (Multiset.mem_singleton_self _)
  rw [Complex.norm_real, Real.norm_of_nonneg hp.le] at h3
  exact lt_irrefl _ h3

theorem isoInf_string {D : D7} (χ : D.naut.CG 1) (d : ℕ) (τ : D.host.E →+* ℂ) (s : ℂ) (h : D.naut.infG χ τ = {s}) :
    isoInf D.nd D.naut [⟨1, χ, d⟩] τ = (Multiset.range d).map fun c : ℕ => s + ((d : ℂ) - 1 - 2 * c) / 2 := by
  simp only [isoInf, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, h, Multiset.map_singleton]
  have : ∀ (n : ℕ) (g : ℂ → ℂ), (List.map (fun k : ℂ => ({g k} : Multiset ℂ)) (List.range n)).sum =
      (Multiset.range n).map fun c : ℕ => g c := by
    intro n g
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Multiset.range_succ, Multiset.map_cons, ← ih, List.range_succ]
      simp [add_comm]
  rw [this d fun k => s + (((d : ℂ) - 1) / 2 - k)]
  refine Multiset.map_congr rfl fun c _ => by ring

theorem eta_of_charSide {D : D7} {cf : CharFrame D} (C : CharSide D cf) (τ : D.what₂.Tau) :
    D.naut.infG D.naut.etaTinv (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(1 / 2 : ℂ)} ∧ D.naut.infG D.naut.etaTinv (embTauBar D τ) = {(1 / 2 : ℂ)} := by
  have h : (C.e1 D.naut.etaTinv).1.HasInfQ (embPsi D.host) fun _ => -(1 / 2) := by
    refine ⟨fun _ => -1, fun _ => by norm_num, fun k => ?_⟩
    rw [C.etaTinv]
    have := cf.isEta.inf k
    have e : (cf.eta⁻¹).inf k = (cf.eta.inf k)⁻¹ := rfl
    rw [e, Units.val_inv_eq_inv_val, this, ← Finset.prod_inv_distrib]
    simp
  have := C.infG _ _ h (D.eTau τ)
  refine ⟨this.1.trans (by simp), this.2.trans (by simp)⟩

theorem inf_eq_paramV {D : D7} {cf : CharFrame D} (C : CharSide D cf) (j : Fin D.R.m) (μ : D.naut.CG 1) (τ : D.what₂.Tau)
    (hμ : D.naut.infG μ (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(((D.hc τ).e j : ℚ) : ℂ)} ∧ D.naut.infG μ (embTauBar D τ) = {(((D.hc τ).e j : ℚ) : ℂ)}) :
    (hcSigma (D.hc τ)).map (· - 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
      NG.paramV D.R (D.hc τ) j (1 / 2) ∧
    (hcSigma (D.hc τ)).map (fun y => -y + 1 / 2) + isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (embTauBar D τ) =
      (NG.paramV D.R (D.hc τ) j (1 / 2)).map fun y => -y := by
  have e := eta_of_charSide C τ
  have h1 := D.naut.infG_tw μ _ _ _ e.1
  have h2 := D.naut.infG_tw μ _ _ _ e.2
  rw [hμ.1, Multiset.map_singleton] at h1
  rw [hμ.2, Multiset.map_singleton] at h2
  rw [isoInf_string _ _ _ _ h1, isoInf_string _ _ _ _ h2]
  constructor
  · simp only [hcSigma, NG.paramV, Multiset.map_add, Multiset.map_map, Function.comp_def]
    congr 1
  · simp only [hcSigma, NG.paramV, Multiset.map_add, Multiset.map_map, Function.comp_def]
    congr 1
    · congr 1 <;> exact Multiset.map_congr rfl fun _ _ => by ring
    · have hr : Multiset.range D.R.t = (Multiset.range D.R.t).map fun c => D.R.t - 1 - c := by
        have := congrArg Finset.val (Finset.range_image_pred_top_sub D.R.t)
        rw [Finset.image_val_of_injOn (fun a ha b hb h => by
          simp only [Finset.coe_range, Set.mem_Iio] at ha hb; omega)] at this
        exact this.symm
      conv_rhs => rw [hr]
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun c hc => ?_
      have hc' : c < D.R.t := Multiset.mem_range.1 hc
      have : ((D.R.t - 1 - c : ℕ) : ℂ) = (D.R.t : ℂ) - 1 - c := by
        rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
      simp only [Function.comp_apply, this]; ring

theorem infinitesimal_character_reference {D : D7} {cf : CharFrame D} (C : CharSide D cf) (j : Fin D.R.m) (τ : D.what₂.Tau) :
    D.naut.infG (C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = {-(((D.hc τ).e j : ℚ) : ℂ)} ∧
      D.naut.infG (C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩) (embTauBar D τ) = {(((D.hc τ).e j : ℚ) : ℂ)} := by
  have := C.infG (C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩) _ (by rw [Equiv.apply_symm_apply]; exact (cf.isMu0 j).inf) (D.eTau τ)
  refine ⟨this.1.trans ?_, this.2.trans ?_⟩ <;> simp [eExp]

theorem tieLab_of_parIn {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    {Rw : RowSide D} (P : ParIn hL D cf rep Rw) : SumRepresentations.tieLab D := by
  refine ⟨fun k v a s => ?_, fun k v a => ?_⟩
  · haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    rw [P.lab k v, P.lab k v, P.T.tw, GlobalTheory.WeilDeligne.WD.lab_lpTw]
  · haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    rw [P.lab k v, ← P.T.dim]
    exact GlobalTheory.WeilDeligne.WD.natDegree_lab_le _ _ _

theorem liftAt_int {D : D7} {Rw : RowSide D} {j : ℕ} {σ : D.what₂.FT} {π : D.nbc.AU j} {μ : D.naut.CG 1}
    (h : LiftAt D Rw j σ π μ) (τ : D.what₂.Tau) : ∀ z ∈ D.naut.infG μ (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ), ∃ n : ℤ, z = n := by
  obtain ⟨s, hs⟩ := Multiset.card_eq_one.1 (D.naut.infG_card μ (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ))
  have h1 := D.naut.infG_tw μ _ _ _ (h.eta τ).1
  rw [hs, Multiset.map_singleton] at h1
  have h2 := (h.inf τ).1
  rw [isoInf_string _ _ _ _ h1] at h2
  obtain ⟨a, ha⟩ := D.R.t_odd
  obtain ⟨b, hb⟩ : Odd D.R.r := by
    obtain ⟨x, hx⟩ := D.R.k_even
    obtain ⟨y, hy⟩ := D.R.m_even
    have h2 := D.R.two_le_m
    exact ⟨x + y - 1, by simp only [Ranks.r]; omega⟩
  have hn : D.R.nV = D.R.r + D.R.t := rfl
  obtain ⟨k, hk⟩ := (D.nbc.infW_alg j (D.nbc.wtAU j π) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).2 (s + -(1 / 2) + ((D.R.t : ℂ) - 1 - 2 * (0 : ℕ)) / 2)
    (by rw [h2]; exact Multiset.mem_add.2 (Or.inr (Multiset.mem_map.2 ⟨0, Multiset.mem_range.2 (by omega), rfl⟩)))
  intro z hz
  rw [hs, Multiset.mem_singleton] at hz
  refine ⟨k + b + 1, ?_⟩
  rw [hn, hb] at hk
  push_cast at hk ⊢
  rw [hz]
  linear_combination hk

theorem plGw_split (D : D7) (k : Fin 2) (v : D.nd.PlG k) : IsSplitPl D.host (D.naut.plGw k v) :=
  (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) _ (D.naut.plGw_over k v)).2.2.1

theorem cancel_of_parIn {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r}
    {Rw : RowSide D} (P : ParIn hL D cf rep Rw) (w : PlE D.host) (a b c : D.naut.LP w)
    (h : D.naut.lpSum a c = D.naut.lpSum b c) : a = b :=
  (P.T.e w).injective (GlobalTheory.WeilDeligne.WD.lpSum_cancel_right _ _ _ _ _ _ _ (P.T.e w c) (by rw [← P.T.sum, ← P.T.sum, h]))

theorem local_lift_at_reference {D : D7} {cf : CharFrame D} (C : CharSide D cf) (Rw : RowSide D) (j : Fin D.R.m) (σ : D.what₂.FT)
    (π : D.nbc.AU (j.1 + 1)) (hs : SphericalInertData.SphInert D.nd D.naut D.nbc (j.1 + 1) π)
    (hl : ∀ w, IsSplitPl D.host w → D.nbc.locAU (j.1 + 1) π w = D.naut.lpChar (D.naut.lpSum (Rw.locR σ w)
      (spehLoc D.nd D.naut ⟨1, C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩, D.R.t⟩ w)) (D.naut.locG D.naut.etaTinv w))
    (hi : ∀ τ, D.nbc.infW (j.1 + 1) (D.nbc.wtAU (j.1 + 1) π) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) = NG.paramV D.R (D.hc τ) j (1 / 2) ∧
      D.nbc.infW (j.1 + 1) (D.nbc.wtAU (j.1 + 1) π) (embTauBar D τ) = (NG.paramV D.R (D.hc τ) j (1 / 2)).map fun y => -y) :
    LiftAt D Rw (j.1 + 1) σ π (C.e1.symm ⟨cf.mu0 j, (cf.isMu0 j).unitary⟩) where
  csd := (C.csd _).2 (by rw [Equiv.apply_symm_apply]; exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ (cf.isMu0 j).triv)
  unr w hw := ⟨(C.unr_iff _ w).2 (by
    rw [Equiv.apply_symm_apply]
    exact (cf.isMu0 j).unr w fun k hk =>
      hw (GlobalTheory.Mem.Chr.splitsC_main D.R D.host _ (D.host.g_prime k) (D.nd.g_split k) w hk).2.2.1), (D.naut.etaTinv_def w).1⟩
  sph := hs
  loc := hl
  eta := eta_of_charSide C
  inf τ := ⟨(hi τ).1.trans (inf_eq_paramV C j _ τ (infinitesimal_character_reference C j τ)).1.symm,
    (hi τ).2.trans (inf_eq_paramV C j _ τ (infinitesimal_character_reference C j τ)).2.symm⟩

end GlobalTheory.HeightCounting.Up.RowModel

end
