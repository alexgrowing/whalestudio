import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApxGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfSqNormEqExpGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormPotentialSumSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorRelationIntegralScaling
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPotentialOfMetricExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjInvGradedReferenceLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpAndLogPowerLeLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulLogInvSqDivLeSmall
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal

namespace GlobalTheory.CovHt.Link.GapEst

open AlgebraicGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.CxPts GlobalTheory.Toroidal

section Gen

variable {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ}

private noncomputable abbrev lv (y : Pts Y σ) (f : Y.Fn) : ℝ := Real.log ‖ratVal f y‖

omit [NumberField F] in
private theorem lv_mul {y : Pts Y σ} {f g : Y.Fn} (hf : UnitAt (under y) f) (hg : UnitAt (under y) g) :
    lv y (f * g) = lv y f + lv y g := by
  unfold lv
  rw [ratVal_mul hf.regAt hg.regAt, norm_mul,
    Real.log_mul (norm_ne_zero_iff.2 (ratVal_ne_zero hf)) (norm_ne_zero_iff.2 (ratVal_ne_zero hg))]

omit [NumberField F] in
private theorem lv_zpow {y : Pts Y σ} {f : Y.Fn} (hf : UnitAt (under y) f) (n : ℤ) : lv y (f ^ n) = n * lv y f := by
  unfold lv
  rw [LeviRelation.ratVal_zpow hf, norm_zpow, Real.log_zpow]

omit [NumberField F] in
private theorem lv_pow {y : Pts Y σ} {f : Y.Fn} (hf : UnitAt (under y) f) (n : ℕ) : lv y (f ^ n) = n * lv y f := by
  simpa using lv_zpow hf n

omit [NumberField F] in
private theorem lv_div {y : Pts Y σ} {f g : Y.Fn} (hf : UnitAt (under y) f) (hg : UnitAt (under y) g) :
    lv y (f / g) = lv y f - lv y g := by
  have h := lv_zpow hg (-1)
  rw [zpow_neg_one] at h
  rw [div_eq_mul_inv, lv_mul hf hg.inv, h]
  push_cast
  ring

omit [NumberField F] in
private theorem unit_div {x : Y.X} {f g : Y.Fn} (hf : UnitAt x f) (hg : UnitAt x g) : UnitAt x (f / g) :=
  (div_eq_mul_inv f g).symm ▸ hf.mul hg.inv

omit [NumberField F] in
private theorem unit_prod {ι : Type} [Fintype ι] {x : Y.X} {u : ι → Y.Fn} (hu : ∀ i, UnitAt x (u i)) (k : ι → ℤ) :
    UnitAt x (∏ i, u i ^ k i) := CombUnit.unitAt_prod _ _ fun i _ => CombUnit.unitAt_zpow (hu i) _

omit [NumberField F] in
private theorem lv_prod {ι : Type} [Fintype ι] {y : Pts Y σ} {u : ι → Y.Fn} (hu : ∀ i, UnitAt (under y) (u i))
    (k : ι → ℤ) : lv y (∏ i, u i ^ k i) = ∑ i, k i * lv y (u i) := by
  unfold lv
  rw [LeviRelation.ratVal_prod _ _ fun i _ => CombUnit.unitAt_zpow (hu i) _, norm_prod,
    Real.log_prod fun i _ => norm_ne_zero_iff.2 (ratVal_ne_zero (CombUnit.unitAt_zpow (hu i) _))]
  exact Finset.sum_congr rfl fun i _ => lv_zpow (hu i) _

omit [NumberField F] in
private theorem gen_ne {Δ : Y.Dv} {x : Y.X} {f : Y.Fn} (hf : Δ.GeneratesAt x f) : f ≠ 0 :=
  have ⟨_, _, hu⟩ := hf; left_ne_zero_of_mul hu.ne_zero

omit [NumberField F] in
private theorem unit_gen {Δ : Y.Dv} {x : Y.X} {f g : Y.Fn} (hf : Δ.GeneratesAt x f) (hg : Δ.GeneratesAt x g) :
    UnitAt x (f / g) := by
  have h := unit_div ((Base.isEqn_eqn Δ x).generatesAt_iff.1 hf) ((Base.isEqn_eqn Δ x).generatesAt_iff.1 hg)
  rwa [mul_div_mul_right _ _ (Units.ne_zero _)] at h

private theorem lnN_change {C : CxSt F} {Δ : Y.Dv} (m : C.Met Y σ Δ) {y : Pts Y σ} {f g : Y.Fn}
    (hf : Δ.GeneratesAt (under y) f) (hg : Δ.GeneratesAt (under y) g) (hp : PosAt m y) :
    lnN m f y = lnN m g y + lv y (f / g) := by
  have h₁ := LeviRelation.neg_lnN_genAt m hf hp
  have h₂ := LeviRelation.neg_lnN_genAt m hg hp
  have h₃ := lv_div ((Base.isEqn_eqn Δ _).generatesAt_iff.1 hf) ((Base.isEqn_eqn Δ _).generatesAt_iff.1 hg)
  rw [mul_div_mul_right _ _ (Units.ne_zero _)] at h₃
  unfold lv at h₃ ⊢
  linarith

private theorem unit_rel {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} {k : ι → ℤ} {Δ₀ : Y.Dv} {k₀ : ℤ}
    (h : k₀ • Δ₀ + ∑ i, k i • Δ i = 0) {x : Y.X} {e : Y.Fnˣ} (he : Δ₀.IsEqn x e) {f : ι → Y.Fn}
    (hf : ∀ i, (Δ i).GeneratesAt x (f i)) : UnitAt x ((∏ i, f i ^ k i) / (e : Y.Fn) ^ k₀) := by
  have h0 : (0 : Y.Dv).GeneratesAt x 1 := by
    simpa using CartierDiv.isEqn_iff_generatesAt_inv.1 (CartierDiv.isEqn_zero x)
  have h1 := CombUnit.unitAt_quot_of_relation F Y (Option ι) 0 (fun o => o.elim Δ₀ Δ) 1 (fun o => o.elim k₀ k) x 1
    (fun o => o.elim (e : Y.Fn)⁻¹ f) (by simp [Fintype.sum_option, h]) h0 (by
      rintro (_ | i)
      exacts [CartierDiv.isEqn_iff_generatesAt_inv.1 he, hf i])
  have h2 := h1.inv
  simp only [Fintype.prod_option, Option.elim, one_pow, one_div, inv_inv, inv_zpow] at h2
  rwa [div_eq_inv_mul]

omit [NumberField F] in
private theorem continuousAt_lv {y : Pts Y σ} {h : Y.Fn} (hx : UnitAt (under y) h) :
    ContinuousAt (fun z : Pts Y σ => lv z h) y := by
  obtain ⟨U0, hU0, hU0u⟩ := hx.exists_nhds
  obtain ⟨b, hb⟩ := exists_unit_fnOf_eq hU0u
  have hb' := hb (gen_mem hU0)
  have hx0 : y ∈ ptsIn Y.str σ U0 := mem_ptsIn.2 hU0
  have hn := (isOpen_ptsIn (p := Y.str) (σ := σ) U0).mem_nhds hx0
  have hc : ContinuousAt (ev Y.str σ U0 b.1) y := (continuousOn_ev b.1).continuousAt hn
  refine (hc.norm.log (norm_ne_zero_iff.2 (ev_ne_zero hx0 b.isUnit))).congr ?_
  filter_upwards [hn] with z hz
  unfold lv
  rw [← hb', ratVal_fnOf hz]

private theorem bound_gen {X : Type} [TopologicalSpace X] [CompactSpace X] {h : X → Pts Y σ} (hh : Continuous h)
    {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i, (cxSt F).Met Y σ (Δ i)) {k : ι → ℤ} {Δ₀ : Y.Dv} {k₀ : ℤ}
    (hk : 0 ≤ k₀) (hrel : k₀ • Δ₀ + ∑ i, k i • Δ i = 0) {Q : ι → LocPot X} (hQ : ∀ i, IsPot h (m i) (Q i))
    (hQc : ∀ i x, ContinuousAt ((Q i).φ x) x) (ν : Pts Y σ → ℝ)
    (hν : ∀ y : Pts Y σ, ∃ (e : Y.Fnˣ) (ψ : Pts Y σ → ℝ), ContinuousAt ψ y ∧ ∀ᶠ z in 𝓝 y, Δ₀.IsEqn (under z) e ∧
      (UnitAt (under z) (e : Y.Fn) → lv z e ≤ ν z + ψ z)) :
    ∃ K : ℝ, ∀ x, under (h x) ∉ Δ₀.supp → lv (h x) (∏ i, genAt (Δ i) (under (h x)) ^ k i) -
      ∑ i, k i * lnN (m i) (genAt (Δ i) (under (h x))) (h x) ≤ k₀ * ν (h x) + K := by
  have loc : ∀ x₀, ∃ K : ℝ, ∀ᶠ x in 𝓝 x₀, under (h x) ∉ Δ₀.supp → lv (h x) (∏ i, genAt (Δ i) (under (h x)) ^ k i) -
      ∑ i, k i * lnN (m i) (genAt (Δ i) (under (h x))) (h x) ≤ k₀ * ν (h x) + K := fun x₀ => by
    obtain ⟨e, ψ, hψ, he⟩ := hν (h x₀)
    choose f hf using fun i => hQ i x₀
    have hw₀ := unit_rel hrel he.self_of_nhds.1 fun i => (hf i x₀ ((Q i).mem_U x₀)).1
    have hc : ContinuousAt (fun x => k₀ * ψ (h x) + lv (h x) ((∏ i, f i ^ k i) / (e : Y.Fn) ^ k₀) +
        ∑ i, k i * (Q i).φ x₀ x) x₀ :=
      ((continuousAt_const.mul (hψ.comp hh.continuousAt)).add ((continuousAt_lv hw₀).comp hh.continuousAt)).add
        (tendsto_finset_sum _ fun i _ => continuousAt_const.mul (hQc i x₀))
    refine ⟨k₀ * ψ (h x₀) + lv (h x₀) ((∏ i, f i ^ k i) / (e : Y.Fn) ^ k₀) + ∑ i, k i * (Q i).φ x₀ x₀ + 1, ?_⟩
    filter_upwards [hc.eventually (gt_mem_nhds (lt_add_one _)), hh.continuousAt.eventually he,
      Filter.eventually_all.2 fun i => ((Q i).isOpen_U x₀).mem_nhds ((Q i).mem_U x₀)] with x h₁ h₂ h₃ hx
    have hu : UnitAt (under (h x)) (e : Y.Fn) := by
      by_contra hc
      exact hx (h₂.1.mem_supp_iff.2 hc)
    have hw := unit_rel hrel h₂.1 fun i => (hf i x (h₃ i)).1
    have hq := fun i => unit_gen (generatesAt_genAt (Δ i) (under (h x))) (hf i x (h₃ i)).1
    have e₁ : (∏ i, genAt (Δ i) (under (h x)) ^ k i) = (e : Y.Fn) ^ k₀ * ((∏ i, f i ^ k i) / (e : Y.Fn) ^ k₀) *
        ∏ i, (genAt (Δ i) (under (h x)) / f i) ^ k i := by
      rw [mul_div_cancel₀ _ (zpow_ne_zero _ e.ne_zero), ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← mul_zpow, mul_div_cancel₀ _ (gen_ne (hf i x (h₃ i)).1)]
    have e₂ : ∑ i, k i * lnN (m i) (genAt (Δ i) (under (h x))) (h x) =
        ∑ i, k i * lv (h x) (genAt (Δ i) (under (h x)) / f i) - ∑ i, k i * (Q i).φ x₀ x := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [lnN_change (m i) (generatesAt_genAt _ _) (hf i x (h₃ i)).1 (hf i x (h₃ i)).2.1, (hf i x (h₃ i)).2.2]
      ring
    rw [e₁, e₂, lv_mul ((CombUnit.unitAt_zpow hu _).mul hw) (unit_prod hq _), lv_mul (CombUnit.unitAt_zpow hu _) hw,
      lv_zpow hu, lv_prod hq]
    have := mul_le_mul_of_nonneg_left (h₂.2 hu) (Int.cast_nonneg (R := ℝ) hk)
    refine le_trans ?_ (add_le_add le_rfl h₁.le)
    linarith
  choose K hK using loc
  obtain ⟨T, hT⟩ := CompactSpace.elim_nhds_subcover _ hK
  refine ⟨∑ x ∈ T, |K x|, fun x hx => ?_⟩
  obtain ⟨x₀, h₀, h₁⟩ := Set.mem_iUnion₂.1 (hT.ge (Set.mem_univ x))
  exact (h₁ hx).trans (add_le_add le_rfl ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x => |K x|) (fun _ _ => abs_nonneg _) h₀)))

end Gen

section Flag

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

private theorem bd_local {x : ToroidalCompactificationData s} {Φ : s.Flag} (P : Mean4O.PolOf x Φ) (c : s.Comp) (σ : D.what₂.LL →+* ℂ)
    (y : Pts (Φ.C c).Y σ) : ∃ (e : (Φ.C c).Y.Fnˣ) (ψ : Pts (Φ.C c).Y σ → ℝ), ContinuousAt ψ y ∧ ∀ᶠ z in 𝓝 y,
      (P.bd c).IsEqn (under z) e ∧
      (UnitAt (under z) (e : (Φ.C c).Y.Fn) → lv z e ≤ (Real.exp 1 - rFlag x Φ c σ z) / 2 + ψ z) := by
  have hπ := GlobalTheory.T.flag_component_projection_smooth D _ _ _ _ _ s Φ c
  have : Smooth (GlobalTheory.Toroidal.genStr s.T.Z) := SmoothOfRelativeDimension.smooth S.Dw.dim _
  have : IsLocallyNoetherian (GlobalTheory.Toroidal.gen s.T.Z : Scheme.{0}) :=
    LocallyOfFiniteType.isLocallyNoetherian (GlobalTheory.Toroidal.genStr s.T.Z)
  have := GlobalTheory.Toroidal.isProper_genStr s.T.Z
  have : CompactSpace (GlobalTheory.Toroidal.gen s.T.Z : Scheme.{0}) :=
    QuasiCompact.compactSpace_of_compactSpace (GlobalTheory.Toroidal.genStr s.T.Z)
  have : IsNoetherian (GlobalTheory.Toroidal.gen s.T.Z : Scheme.{0}) := {}
  have hsnc := GlobalTheory.SncLocal.lSncAt_of_snc _ _ _ _ s.T.snc x.cpt_list
  have hsupp : ((s.T.BD.idealSheaf.comap (GlobalTheory.Toroidal.genι s.T.Z)).support : Set (GlobalTheory.Toroidal.gen s.T.Z : Scheme.{0})) =
      GlobalTheory.Toroidal.genBd s.T.Z := by
    rw [Scheme.IdealSheafData.support_comap]
    ext y
    exact ⟨fun h => GlobalTheory.Toroidal.mem_genBd_iff.2 (s.T.BD_supp _ h), s.T.BD_pos _⟩
  obtain ⟨mu, hmu₁, hmu⟩ := BdSec.exists_mult (s.T.BD.idealSheaf.comap (GlobalTheory.Toroidal.genι s.T.Z)) (hsupp ▸ x.cpt_list)
    hsnc fun y => by
      obtain ⟨j, hj⟩ := s.T.BD.exists_mem (GlobalTheory.Toroidal.genι s.T.Z y)
      rw [GlobalTheory.VanStalk.stalkId_comap, s.T.BD.stalkId_idealSheaf j _ hj, Ideal.map_span, Set.image_singleton]
      exact ⟨_, rfl⟩
  have hn := fun i => GlobalTheory.DivPullback.isDivNorm_flag D _ _ _ _ _ s Φ c σ _ _ hπ (x.nrm_div _ i)
  obtain ⟨e, he⟩ := BdSec.exists_eqn (Δ := P.bd c) (mu := fun i => mu i * P.b) hn
    (BdSec.eqn_pullDiv (GlobalTheory.Toroidal.genStr s.T.Z) (Φ.C c).π _ s.T.BD _ hsnc hmu P.b) y
  have hU := ((DivSec.divPot hn).isOpen_U y).mem_nhds ((DivSec.divPot hn).mem_U y)
  refine ⟨e, (BdSec.wPot hn fun i => mu i * P.b).φ y,
    ((BdSec.smoothOn_wPot hn _ y).continuousOn ((DivSec.divPot hn).isOpen_U y)).continuousAt hU, ?_⟩
  filter_upwards [hU] with z hz
  refine ⟨(he z hz).1, fun hu => ?_⟩
  have h₁ := BdSec.norm_wSec_mul hn (fun i => mu i * P.b) hz
  rw [← (he z hz).2] at h₁
  have h₂ := norm_pos_iff.2 (ratVal_ne_zero hu)
  have h₃ : ∏ i, x.nrm _ i ((Φ.C c).down z) ^ (mu i * P.b) ≤ ∏ i, x.nrm _ i ((Φ.C c).down z) :=
    Finset.prod_le_prod (fun i _ => pow_nonneg ((hn i).1 z).1 _) fun i _ =>
      pow_le_of_le_one ((hn i).1 z).1 ((hn i).1 z).2 (Nat.mul_pos (hmu₁ i) P.b_pos).ne'
  have h₄ := Real.log_le_log (mul_pos h₂ (Real.exp_pos _)) (h₁.trans_le h₃)
  rw [Real.log_mul h₂.ne' (Real.exp_ne_zero _), Real.log_exp] at h₄
  have h₅ : rFlag x Φ c σ z = Real.exp 1 - Real.log ((∏ i, x.nrm _ i ((Φ.C c).down z)) ^ 2) := rfl
  rw [h₅, Real.log_pow]
  unfold lv
  push_cast
  linarith

private theorem lnN_met_sum {Φ : s.Flag} {k : s.Comp} {σ : D.what₂.LL →+* ℂ} (G : EigMet s.T.Z (embOf κ.e σ))
    {ι : Type} [Fintype ι] (n : ι → Letter S.Dw → ℤ) (c : ι → ℤ) {n₀ : Letter S.Dw → ℤ}
    (h₀ : ∀ z, n₀ z = ∑ i, c i * n i z) {y : Pts (Φ.C k).Y σ} {f : (Φ.C k).Y.Fn} {g : ι → (Φ.C k).Y.Fn}
    (hf : (divOf (Φ.C k) n₀).GeneratesAt (under y) f) (hg : ∀ i, (divOf (Φ.C k) (n i)).GeneratesAt (under y) (g i)) :
    UnitAt (under y) (f / ∏ i, g i ^ c i) ∧ lnN (C := cxSt D.what₂.LL) ((Φ.C k).met G n₀) f y =
      lv y (f / ∏ i, g i ^ c i) + ∑ i, c i * lnN (C := cxSt D.what₂.LL) ((Φ.C k).met G (n i)) (g i) y := by
  obtain ⟨q, h1, h2⟩ := (Φ.C k).exists_adapted y
  let T : (Letter S.Dw → ℤ) → (Φ.C k).Y.Fn := fun n => ((prodPow q.1 n)⁻¹ : (Φ.C k).Y.Fnˣ)
  have hT : ∀ n, (divOf (Φ.C k) n).GeneratesAt (under y) (T n) := fun n => by
    have := CartierDiv.isEqn_iff_generatesAt_inv.1 (FlagCpt.prodPow_mem n h1)
    rwa [← Units.val_inv_eq_inv_val] at this
  have hL : ∀ n, lnN (C := cxSt D.what₂.LL) ((Φ.C k).met G n) (T n) y =
      ∑ z : Letter S.Dw, n z * (Real.log (GradedNorm.grSq (G.gram _ q.2 z.1) z.2) / 2) := fun n => by
    have e : (cxSt D.what₂.LL).pn _ σ _ ((Φ.C k).met G n) ((cxSt D.what₂.LL).cx _ σ (T n)) y = _ :=
      (Var.pn_frame (FlagCpt.prodPow_mem n h1)).trans (FlagCpt.met_h G n h2)
    unfold Mean4O.lnN
    rw [e]
    simp only [prodPow, Pi.one_apply, one_zpow, Finset.prod_const_one, Units.val_one, norm_one, one_pow, div_one,
      FlagCpt.genSq]
    rw [Real.log_prod fun z _ => (zpow_pos (GradedNorm.grSq_pos (G.pos _ _ _) _) _).ne', Finset.sum_div]
    exact Finset.sum_congr rfl fun z _ => by rw [Real.log_zpow]; ring
  have hp : ∀ n, PosAt (C := cxSt D.what₂.LL) ((Φ.C k).met G n) y := fun n => posAt_of_posSet (FlagCpt.posSet_met _ _) y
  have hTe : T n₀ = ∏ i, T (n i) ^ c i := by
    simp only [T, ← Units.val_zpow_eq_zpow_val, ← Units.coe_prod, prodPow, inv_zpow, Finset.prod_inv_distrib, h₀,
      ← Finset.prod_zpow, ← zpow_mul]
    congr 2
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun z _ => ?_
    rw [← toAdd_ofAdd (∑ i, c i * n i z), ← zpowersHom_apply, ofAdd_sum, map_prod]
    simp [mul_comm]
  have hu := fun i => unit_gen (hg i) (hT (n i))
  have e₁ : f / ∏ i, g i ^ c i = f / T n₀ / ∏ i, (g i / T (n i)) ^ c i := by
    rw [div_div, hTe, ← Finset.prod_mul_distrib]
    refine congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
    rw [← mul_zpow, mul_div_cancel₀ _ (gen_ne (hT _))]
  rw [e₁]
  refine ⟨unit_div (unit_gen hf (hT _)) (unit_prod hu _), ?_⟩
  rw [lv_div (unit_gen hf (hT _)) (unit_prod hu _), lv_prod hu, lnN_change _ hf (hT _) (hp _), hL]
  simp only [fun i => lnN_change _ (hg i) (hT _) (hp _), hL, h₀, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Int.cast_sum, Int.cast_mul, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  ring

private theorem zpow_alg {K ι : Type} [Field K] [Fintype ι] {gu gM gA : K} {g : ι → K} (hu : gu ≠ 0) (hM : gM ≠ 0)
    (hA : gA ≠ 0) (hg : ∀ i, g i ≠ 0) (q n : ℕ) (c b kx : ι → ℤ) (bA ka α β : ℤ) (h₁ : bA * α = ka * β)
    (h₂ : ∀ i, (b i - c i * (q * n : ℕ)) * α = kx i * β) :
    ((gu / ∏ i, g i ^ c i) ^ (q * n) / (gu ^ n / gM) ^ q / (gM ^ q / (gA ^ bA * ∏ i, g i ^ b i))) ^ α =
      (gA ^ ka * ∏ i, g i ^ kx i) ^ β := by
  have hc : (∏ i, g i ^ c i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hg i)
  have hb : (∏ i, g i ^ b i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ (hg i)
  have ha := zpow_ne_zero bA hA
  have e₁ : ∏ i, g i ^ (b i - c i * (q * n : ℕ)) = (∏ i, g i ^ b i) / (∏ i, g i ^ c i) ^ (q * n) := by
    rw [← Finset.prod_pow, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [zpow_sub₀ (hg i), zpow_mul, zpow_natCast]
  have e₂ : (gu / ∏ i, g i ^ c i) ^ (q * n) / (gu ^ n / gM) ^ q / (gM ^ q / (gA ^ bA * ∏ i, g i ^ b i)) =
      gA ^ bA * ∏ i, g i ^ (b i - c i * (q * n : ℕ)) := by
    rw [e₁, div_pow, div_pow, ← pow_mul, mul_comm n q]
    field_simp
  rw [e₂]
  simp only [mul_zpow, ← Finset.prod_zpow, ← zpow_mul, h₁, h₂]

private noncomputable def bdL {x : ToroidalCompactificationData s} {Φ : s.Flag} (P : Mean4O.PolOf x Φ) (k : s.Comp) (d : ℕ) (ka : ℤ)
    (kx : DV.Rt D.what₂.Tau N → ℤ) (σ : D.what₂.LL →+* ℂ) (y : Pts (Φ.C k).Y σ) : ℝ :=
  lv y (genAt (P.ab k).D (under y) ^ ka * ∏ z, genAt (divOf (Φ.C k) (rootExp S z)) (under y) ^ kx z) / d -
    ∑ z : DV.Rt D.what₂.Tau N, P.dir z.1 z.2 *
      lnN (refMet x Φ k σ (rootExp S z)) (genAt (divOf (Φ.C k) (rootExp S z)) (under y)) y -
    lnAdl (P.ab k) σ y / (((P.ab k).n : ℕ) : ℝ)

private theorem real_alg {ι : Type} [Fintype ι] {q n nA d r α β l₁ l₂ l₃ lW bA LA LM g : ℝ} {u dir b H H₀ : ι → ℝ}
    (hq : q ≠ 0) (hn : n ≠ 0) (hnA : nA ≠ 0) (hd : d ≠ 0) (hα : α ≠ 0) (hβ : β * d = q * n * r * α)
    (h₁ : α * (q * n * l₁ - q * l₂ - l₃) = β * lW) (hA : q * n * r = bA * nA)
    (hb : ∀ i, b i = q * n * -(u i - r * dir i))
    (h₂ : q * LM = l₃ + (bA * LA + ∑ i, b i * H₀ i) - q * n * g) :
    l₁ + ∑ i, -u i * H i - (LM + l₂) / n =
      r * (lW / d - ∑ i, dir i * H₀ i - LA / nA) + g - 2 * (∑ i, u i * (H i - H₀ i)) / 2 := by
  have e₁ : ∑ i, b i * H₀ i = q * n * (r * ∑ i, dir i * H₀ i - ∑ i, u i * H₀ i) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hb]; ring
  have e₂ : β = q * n * r * α / d := eq_div_of_mul_eq hd hβ
  have e₃ : bA = q * n * r / nA := eq_div_of_mul_eq hnA hA.symm
  have e₄ : l₃ = q * n * l₁ - q * l₂ - q * n * r / d * lW := by
    have : α * (q * n * l₁ - q * l₂ - l₃) = α * (q * n * r / d * lW) := by rw [h₁, e₂]; ring
    linarith [mul_left_cancel₀ hα this]
  have e₅ : LM = (l₃ + (bA * LA + ∑ i, b i * H₀ i) - q * n * g) / q := eq_div_of_mul_eq hq (by linarith)
  simp only [mul_sub, neg_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  rw [e₅, e₁, e₃, e₄]
  field_simp
  ring

private theorem gap_eq {x : ToroidalCompactificationData s} {Φ : s.Flag} (P : Mean4O.PolOf x Φ) (k : s.Comp) {d : ℕ} {kb ka : ℤ}
    {kx : DV.Rt D.what₂.Tau N → ℤ} (hd : 0 < d) (hka : (ka : ℝ) = d * (((P.ab k).n : ℕ) : ℝ)⁻¹)
    (hkx : ∀ z, (kx z : ℝ) = d * P.dir z.1 z.2)
    (hrel : kb • P.bd k + ka • (P.ab k).D + ∑ z, kx z • divOf (Φ.C k) (rootExp S z) = 0)
    (L : CmList A) (B : ℝ) (u : AllWt.Weight S.Dw) {r : ℚ} (hr : 0 < r) (σ : D.what₂.LL →+* ℂ) {y : Pts (Φ.C k).Y σ}
    (hy : y ∈ offBd Φ k σ) : apxGap Φ L x P B u r k σ y = r * bdL P k d ka kx σ y +
      P.reg k σ (fun τ i => wtR L u τ i - r * P.dir τ i) (Real.exp (-((r : ℝ) ^ 2)⁻¹)) y / 2 -
      phW (metsOf x Φ) (refMet x Φ) k σ (wtR L u) y / 2 := by
  have hgen := ApxAlg.gen_mbar Φ L x P B u r hr k σ y hy
  have hu : ∀ τ i, ∃ q : ℚ, wtR L u τ i = q := fun τ i => ⟨_, congrFun (congrFun (ApxAlg.wtR_eq L u) τ) i⟩
  obtain ⟨q, b, hq, hc, hD, hpos, -⟩ := isComb_mbarOf P B hu hr k
  obtain ⟨hp, hM⟩ := hpos σ y
  have hci := ApxAlg.ci_mbarOf Φ x P B (wtR L u) r k
  unfold apxGap
  generalize mbarOf P B (wtR L u) r k = M at *
  have eD (z : DV.Rt D.what₂.Tau N) : (P.gens k B (some z)).D = divOf (Φ.C k) (rootExp S z) :=
    congrArg (divOf (Φ.C k)) (expo_rootSym _ _ _ _ _)
  have eL (z : DV.Rt D.what₂.Tau N) : lnAdl (P.gens k B (some z)) σ y =
      lnN (refMet x Φ k σ (rootExp S z)) (genAt (divOf (Φ.C k) (rootExp S z)) (under y)) y := by
    have key : ∀ n n' : Pad.Letter S.Dw → ℤ, n = n' →
        lnN (refMet x Φ k σ n) (genAt (divOf (Φ.C k) n) (under y)) y - ((1 : ℕ+) : ℕ) * (0 : ℝ) =
          lnN (refMet x Φ k σ n') (genAt (divOf (Φ.C k) n') (under y)) y := by
      rintro _ _ rfl
      simp
    exact key _ _ (expo_rootSym _ _ _ _ _)
  have u₃ := CombUnit.unitAt_quot_of_relation _ _ _ _ _ q b (under y) _ _ hD (generatesAt_genAt _ _)
    fun i => generatesAt_genAt _ _
  simp only [Fintype.prod_option, Fintype.sum_option, eD, eL] at hM u₃
  rw [lnAdl, hci, Pi.zero_apply, mul_zero, sub_zero] at hM
  rw [show P.gens k B none = P.ab k from rfl] at hM u₃
  have hΛ := DeKeyTrue.divOf_neg_exOf Φ k u
  obtain ⟨u₁, e₁⟩ := lnN_met_sum (Φ := Φ) (k := k) (x.eigMetAt (embOf κ.e σ) none) (rootExp S)
    (fun z : DV.Rt D.what₂.Tau N => -u (L.ψ z.1) (Fin.cast S.rank_eq.symm z.2))
    (n₀ := fun z => -exOf S.Dw u 0 (some z)) (fun z => by simp [← ApproxSec.sum_rootExp L u z])
    (y := y) (f := genAt ((Φ.C k).Lw u) (under y)) (hΛ ▸ generatesAt_genAt _ _) fun i => generatesAt_genAt _ _
  have e₂ : lnN (DeKeyTrue.hodgeLw x Φ k σ u) (genAt ((Φ.C k).Lw u) (under y)) y = _ :=
    (congrArg (Real.log · / 2) (congrFun (congrFun (ApxAlg.pn_hodgeLw x Φ k σ u) _) y)).trans e₁
  have u₂ := unit_gen hgen (generatesAt_genAt _ _)
  have hb := Base.isEqn_eqn (P.bd k) (under y)
  have hbu : UnitAt (under y) (eqn (P.bd k) (under y) : (Φ.C k).Y.Fn) := by
    by_contra hc
    exact hy ((P.mem_supp_bd k (under y)).1 (hb.mem_supp_iff.2 hc))
  have uW := (unit_rel (Δ := fun o : Option (DV.Rt D.what₂.Tau N) => o.elim (P.ab k).D fun z => divOf (Φ.C k) (rootExp S z))
    (k := fun o => o.elim ka kx) (k₀ := kb) (by rw [Fintype.sum_option, ← add_assoc]; exact hrel) hb
    fun i => generatesAt_genAt _ _).mul (CombUnit.unitAt_zpow hbu kb)
  rw [div_mul_cancel₀ _ (zpow_ne_zero _ (Units.ne_zero _)), Fintype.prod_option] at uW
  simp only [Option.elim] at uW
  have hnA : (((P.ab k).n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (P.ab k).n.ne_zero
  have hrn : ((r.num : ℤ) : ℝ) = r * r.den := by exact_mod_cast (Rat.mul_den_eq_num r).symm
  have hcA : (q : ℝ) * (M.n : ℕ) * r = b none * ((P.ab k).n : ℕ) := hc none
  have hcx (z : DV.Rt D.what₂.Tau N) : (b (some z) : ℝ) = q * (M.n : ℕ) * -(wtR L u z.1 z.2 - r * P.dir z.1 z.2) := by
    have : _ = (b (some z) : ℝ) * ((1 : ℕ+) : ℕ) := hc (some z)
    simpa using this.symm
  have e₃ := congrArg (lv y) (zpow_alg (gen_ne (generatesAt_genAt ((Φ.C k).Lw u) (under y)))
    (gen_ne (generatesAt_genAt M.D (under y))) (gen_ne (generatesAt_genAt (P.ab k).D (under y)))
    (fun z => gen_ne (generatesAt_genAt (divOf (Φ.C k) (rootExp S z)) (under y))) q M.n
    (fun z : DV.Rt D.what₂.Tau N => -u (L.ψ z.1) (Fin.cast S.rank_eq.symm z.2)) (fun z => b (some z)) kx (b none) ka
    (d * r.den) (q * (M.n : ℕ) * r.num)
    (by
      refine Int.cast_injective (α := ℝ) ?_
      push_cast
      rw [hka, hrn, eq_div_of_mul_eq hnA hcA.symm]
      field_simp)
    fun z => by
      refine Int.cast_injective (α := ℝ) ?_
      push_cast
      rw [hkx, hrn, hcx, wtR]
      ring)
  have v₁ := CombUnit.unitAt_pow u₁ (q * M.n)
  have v₂ := CombUnit.unitAt_pow u₂ q
  rw [lv_zpow (unit_div (unit_div v₁ v₂) u₃), lv_zpow uW, lv_div (unit_div v₁ v₂) u₃, lv_div v₁ v₂, lv_pow u₁,
    lv_pow u₂] at e₃
  rw [e₂, lnN_change _ hgen (generatesAt_genAt _ _) hp]
  simp only [Nat.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_neg] at e₃ ⊢
  unfold bdL phW lnRatio
  exact real_alg (u := fun z : DV.Rt D.what₂.Tau N => wtR L u z.1 z.2) (dir := fun z => P.dir z.1 z.2)
    (H := fun z => lnN (metsOf x Φ k none σ (rootExp S z)) (genAt (divOf (Φ.C k) (rootExp S z)) (under y)) y)
    (Nat.cast_ne_zero.2 hq.ne') (Nat.cast_ne_zero.2 M.n.ne_zero) hnA (Nat.cast_ne_zero.2 hd.ne')
    (mul_ne_zero (Nat.cast_ne_zero.2 hd.ne') (Nat.cast_ne_zero.2 r.den_ne_zero)) (by rw [hrn]; ring) e₃ hcA hcx hM

end Flag

private theorem mul_log_le {a r : ℝ} (ha : 0 ≤ a) (hr : 0 < r) : a * Real.log r ≤ r / 4 + a * Real.log (4 * a + 1) := by
  have h1 : 0 < 4 * a + 1 := by positivity
  have h2 := Real.log_le_sub_one_of_pos (div_pos hr h1)
  rw [Real.log_div hr.ne' h1.ne'] at h2
  have h3 : a * (r / (4 * a + 1)) ≤ r / 4 := by
    rw [← mul_div_assoc, div_le_div_iff₀ h1 (by norm_num)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h2 ha]

private theorem continuousAt_pot {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {L : LocPot X}
    (hL : IsPotential A L) (x : X) : ContinuousAt (L.φ x) x := by
  obtain ⟨j, hj⟩ := A.cover x
  have h2 : ContinuousAt (L.φ x ∘ (A.chart j).symm) (A.chart j x) :=
    (hL.1 x j).continuousOn.continuousAt (((A.chart j).isOpen_inter_preimage_symm (L.isOpen_U x)).mem_nhds
      ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using L.mem_U x⟩)
  refine (h2.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with z hz
  simp [(A.chart j).left_inv hz]

private theorem bdL_le {D : D7} {O : Setup D} {x : ToroidalCompactificationData O.s} {P : Mean4O.PolOf x O.Φ} (hc : O.CoreWith x P)
    {A : SlopeTestRemainingChoices O.Y} {T : Real0 O.Y} {H : Ht O.Y} (R : O.Reads A T H) (k : O.s.Comp) {d : ℕ} {kb ka : ℤ}
    {kx : DV.Rt D.what₂.Tau O.N → ℤ} (hd : 0 < d) (hkb : (kb : ℝ) = d) (hka : (ka : ℝ) = d * (((P.ab k).n : ℕ) : ℝ)⁻¹)
    (hkx : ∀ z, (kx z : ℝ) = d * P.dir z.1 z.2)
    (hrel : kb • P.bd k + ka • (P.ab k).D + ∑ z, kx z • divOf (O.Φ.C k) (rootExp O.S z) = 0) :
    ∃ K : ℝ, ∀ (σ : D.what₂.LL →+* ℂ), ∀ y ∈ offBd O.Φ k σ,
      bdL P k d ka kx σ y ≤ (Real.exp 1 - rFlag x O.Φ k σ y) / 2 + K := by
  have one : ∀ σ : D.what₂.LL →+* ℂ, ∃ K : ℝ, ∀ y ∈ offBd O.Φ k σ,
      bdL P k d ka kx σ y ≤ (Real.exp 1 - rFlag x O.Φ k σ y) / 2 + K := fun σ => by
    obtain ⟨a, rfl⟩ := (R.man k).ε.surjective σ
    obtain ⟨Qx, hQx, -⟩ := (R.an k).th A.dir a
    obtain ⟨Qa, hQa, -⟩ := (R.an k).a a
    rw [hc.h0_eq] at hQx
    have hQa' := hQa ()
    rw [hc.ab_eq] at hQa'
    have : CompactSpace ((T.M k).X a) := ((R.man k).pt a).symm.compactSpace
    let Δ : Option (DV.Rt D.what₂.Tau O.N) → (O.Φ.C k).Y.Dv := fun o =>
      o.elim (P.ab k).D fun z => divOf (O.Φ.C k) (rootExp O.S z)
    let mm : ∀ o, (cxSt D.what₂.LL).Met (O.Φ.C k).Y ((R.man k).ε a) (Δ o) := fun o => match o with
      | none => (P.ab k).m _
      | some z => refMet x O.Φ k _ (rootExp O.S z)
    have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
    obtain ⟨K, hK⟩ := bound_gen ((R.man k).pt a).continuous mm (k := fun o => o.elim ka kx) (Δ₀ := P.bd k) (k₀ := kb)
      (Int.cast_nonneg_iff.1 (hd'.le.trans_eq hkb.symm)) (by rw [Fintype.sum_option, ← add_assoc]; exact hrel)
      (Q := fun o => o.elim (Qa ()) Qx) (by rintro (_ | z); exacts [hQa'.1, (hQx z).1])
      (by rintro (_ | z); exacts [continuousAt_pot hQa'.2, continuousAt_pot (hQx z).2])
      (fun y => (Real.exp 1 - rFlag x O.Φ k _ y) / 2) (bd_local P k _)
    refine ⟨K / d + (P.ab k).ci (InfinitePlace.mk ((R.man k).ε a)), fun y hy => ?_⟩
    obtain ⟨z, rfl⟩ := ((R.man k).pt a).surjective y
    have h₁ := hK z fun h => hy ((P.mem_supp_bd k _).1 h)
    simp only [Fintype.prod_option, Fintype.sum_option, Δ, mm, Option.elim, hkb, hka, hkx, mul_assoc,
      ← Finset.mul_sum] at h₁
    have hnA : (((P.ab k).n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (P.ab k).n.ne_zero
    have h₂ := div_le_div_of_nonneg_right h₁ hd'.le
    rw [sub_div, add_div, add_div, mul_div_cancel_left₀ _ hd'.ne', mul_div_cancel_left₀ _ hd'.ne',
      mul_div_cancel_left₀ _ hd'.ne'] at h₂
    rw [bdL, lnAdl, sub_div, mul_div_cancel_left₀ _ hnA, div_eq_inv_mul _ (((P.ab k).n : ℕ) : ℝ)]
    linarith
  choose K hK using one
  exact ⟨∑ σ, |K σ|, fun σ y hy => (hK σ y hy).trans (add_le_add le_rfl ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun σ => |K σ|) (fun _ _ => abs_nonneg _) (Finset.mem_univ σ))))⟩

private theorem eventually_dom {ι : Type} [Finite ι] {N : ℕ} {w : ι → Fin N → ℝ} (hw : FlagPoly.RegDom w) (d : ι → Fin N → ℝ) :
    ∀ᶠ s : ℝ in 𝓝 0, FlagPoly.Dom (w - s • d) := by
  refine Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => ?_
  by_cases hab : a < b
  · have hc : ContinuousAt (fun s : ℝ => w τ a - s * d τ a - (w τ b - s * d τ b)) 0 := by fun_prop
    have h0 : (0 : ℝ) < w τ a - 0 * d τ a - (w τ b - 0 * d τ b) := by linarith [hw τ a b hab]
    filter_upwards [hc.eventually (lt_mem_nhds h0)] with s hs _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith
  · exact Filter.Eventually.of_forall fun s h => by rw [le_antisymm h (not_lt.1 hab)]

private theorem an_est {e : ℕ} {M : Man e} {ι : Type} [Fintype ι] {N : ℕ} (F : An M ι N) (hS : F.Size) (hI : F.InS)
    {w : ι → Fin N → ℝ} (hw : FlagPoly.RegDom w) (d : ι → Fin N → ℝ) (K : ℝ) :
    ∃ C : ℝ, ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ σ, ∀ x ∉ M.Z σ, ∀ l : ℝ, l ≤ (Real.exp 1 - M.r σ x) / 2 + K →
      s * l + F.phS (w - s • d) s σ x - F.ph w σ x ≤ C * s := by
  obtain ⟨hlin, -, -, C₁, hC₁⟩ := hS
  obtain ⟨s₁, hs₁, C₂, hC₂⟩ := hI
  obtain ⟨C₃, hC₃⟩ := exp_neg_and_log_pow_div_le_mul 1
  obtain ⟨s₂, hs₂, hs₂', h₂⟩ := mul_log_inv_sq_div_le_small |C₂| (‖w‖ + ‖d‖) 1 one_pos
  refine ⟨K + Real.exp 1 / 2 + |C₂| * (‖w‖ + ‖d‖) * C₃ + |C₁| * ‖d‖ * Real.log (4 * (|C₁| * ‖d‖) + 1), ?_⟩
  filter_upwards [Ioo_mem_nhdsGT (lt_min hs₁ hs₂), (eventually_dom hw d).filter_mono nhdsWithin_le_nhds]
    with s hs0 hdom σ x hx l hl0
  have hs : 0 < s := hs0.1
  have hss : s ≤ min s₁ s₂ := hs0.2.le
  have hs1 : s ≤ 1 := by linarith [min_le_right s₁ s₂]
  have hrx : Real.exp 1 ≤ M.r σ x := (M.bd σ).2.2.2.2.2.1 x hx
  have hr1 : 1 ≤ M.r σ x := le_trans (by linarith [Real.add_one_le_exp 1]) hrx
  have hlog : 0 ≤ Real.log (M.r σ x) := Real.log_nonneg hr1
  have a4 := (((hC₂ _ hdom s hs (hss.trans (min_le_left _ _)) _ rfl σ).2.2 x).2 hx).2.2
  have hn : ‖w - s • d‖ ≤ ‖w‖ + ‖d‖ := by
    refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
    rw [norm_smul, Real.norm_of_nonneg hs.le]
    nlinarith [norm_nonneg d]
  have hcn : C₂ * ‖w - s • d‖ ≤ |C₂| * (‖w‖ + ‖d‖) :=
    mul_le_mul (le_abs_self _) hn (norm_nonneg _) (abs_nonneg _)
  have hc0 : 0 ≤ |C₂| * (‖w‖ + ‖d‖) := by positivity
  have a5 : C₂ * ‖w - s • d‖ * Real.exp (-(s ^ 2)⁻¹ / 3) ≤ |C₂| * (‖w‖ + ‖d‖) * (C₃ * s) :=
    mul_le_mul hcn (hC₃ s hs hs1).1 (Real.exp_pos _).le hc0
  have hl : 0 ≤ Real.log (s ^ 2)⁻¹ / (s ^ 2)⁻¹ :=
    div_nonneg (Real.log_nonneg ((one_le_inv₀ (by positivity)).2 (by nlinarith))) (by positivity)
  have a6 : C₂ * ‖w - s • d‖ * (Real.log (s ^ 2)⁻¹ / (s ^ 2)⁻¹) * M.r σ x ≤ s * (1 / 4) * M.r σ x := by
    refine mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_right hcn hl).trans
      ((h₂ s hs (hss.trans (min_le_right _ _))).trans ?_)) (by linarith)
    exact mul_le_mul_of_nonneg_left (min_le_right _ _) hs.le
  have a7 : F.ph (w - s • d) σ x = F.ph w σ x - s * F.ph d σ x := by
    have h := hlin σ x hx
    have := (h.map_sub w (s • d)).trans (congrArg _ (h.map_smul s d))
    simpa using this
  have a8 : -F.ph d σ x ≤ M.r σ x / 4 + |C₁| * ‖d‖ * Real.log (4 * (|C₁| * ‖d‖) + 1) := by
    refine (neg_le_abs _).trans ((hC₁ d σ x hx).1.trans
      (le_trans ?_ (mul_log_le (by positivity) (by linarith))))
    gcongr
    exact le_abs_self _
  have a9 : l - F.ph d σ x + M.r σ x / 4 ≤ K + Real.exp 1 / 2 +
      |C₁| * ‖d‖ * Real.log (4 * (|C₁| * ‖d‖) + 1) := by linarith
  have := mul_le_mul_of_nonneg_left a9 hs.le
  linarith

private theorem tendsto_cast : Tendsto (fun r : ℚ => (r : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_mem_nhdsWithin.mono fun r hr => ?_⟩
  · have h := (Rat.continuous_coe_real.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℚ)))
    rwa [Rat.cast_zero] at h
  · exact (Rat.cast_pos (K := ℝ)).2 hr

end GlobalTheory.CovHt.Link.GapEst

open GlobalTheory.CovHt.Link.GapEst in
theorem _root_.GlobalTheory.T.approx_gap_le_const_mul : Hypotheses2 → HypothesesH → RegSt → ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (P : Mean4O.PolOf x O.Φ), O.CoreWith x P → 2 < D.R.f * (O.N - 1) → ∀ u : AllWt.Weight O.S.Dw, (∀ τ, StrictAnti (u τ)) → ∀ B : ℝ, 2 ≤ B → ∀ k : O.s.Comp, ∃ C : ℝ, ∀ᶠ r : ℚ in 𝓝[>] 0, ∀ (σ : D.what₂.LL →+* ℂ), ∀ y ∈ offBd O.Φ k σ, apxGap O.Φ O.L x P B u r k σ y ≤ C * r := by
  intro h2 hH hReg D O x P hc hf u hu B _ k
  obtain ⟨A, T, H, ⟨R⟩, -⟩ := ReadsEx.main h2.p4 D O ⟨x, P, hc⟩
  have hI := hReg D O ⟨x, P, hc⟩ hf A T H R k
  have hS := (GlobalTheory.T.fibre_size_and_range_bound h2 hH D O ⟨x, P, hc⟩ hf A T H R k).1
  obtain ⟨d, kb, ka, kx, hd, hkb, hka, hkx, hrel⟩ := P.exists_intRel_bd_ab_roots k
  obtain ⟨K, hK⟩ := bdL_le hc R k hd hkb hka hkx hrel
  have hw : FlagPoly.RegDom (wtR O.L u) := fun τ a b hab => Int.cast_lt.2 (hu _ hab)
  obtain ⟨C, hC⟩ := an_est (T.F k) hS hI hw P.dir K
  refine ⟨C, ?_⟩
  filter_upwards [tendsto_cast.eventually hC, self_mem_nhdsWithin] with r hr hr0 σ y hy
  obtain ⟨a, rfl⟩ := (R.man k).ε.surjective σ
  obtain ⟨z, rfl⟩ := ((R.man k).pt a).surjective y
  have hz : z ∉ (T.M k).Z a := fun h => hy (((R.an k).Z a z).1 h)
  have h₁ := hr a z hz (bdL P k d ka kx _ ((R.man k).pt a z))
    (by rw [(R.an k).r a z hz, hc.r_eq]; exact hK _ _ hy)
  have e₁ := (R.an k).phS (wtR O.L u - (r : ℝ) • P.dir) r ((Rat.cast_pos (K := ℝ)).2 hr0) a z
  have e₂ := (R.an k).ph (wtR O.L u) a z hz
  have e₃ := hc.two_mul_chg k (wtR O.L u) _ ((R.man k).pt a z)
  have e₄ := gap_eq P k hd hka hkx hrel O.L B u hr0 _ hy
  rw [hc.reg_eq] at e₁
  have e₅ : P.reg k _ (fun τ i => wtR O.L u τ i - r * P.dir τ i) (Real.exp (-((r : ℝ) ^ 2)⁻¹)) ((R.man k).pt a z) / 2 =
      (T.F k).phS (wtR O.L u - (r : ℝ) • P.dir) r a z := e₁.symm
  have e₆ : phW (metsOf x O.Φ) (refMet x O.Φ) k _ (wtR O.L u) ((R.man k).pt a z) / 2 = (T.F k).ph (wtR O.L u) a z := by
    refine Eq.trans ?_ e₂.symm
    rw [← e₃, mul_div_cancel_left₀ _ two_ne_zero]
  refine e₄.trans_le ?_
  rw [e₅, e₆]
  exact h₁
