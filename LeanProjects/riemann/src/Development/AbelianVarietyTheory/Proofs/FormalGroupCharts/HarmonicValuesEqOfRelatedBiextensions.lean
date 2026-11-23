import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermExpAddAndEvConst
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.MvPowerSeriesJetEqCalculusStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetEqFormalExpIffAndExistsLogStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ConstantCoeffInvariantPolyOperatorJetEqStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.InvariantPolyOperatorCopiesTransportedLawStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalChartJetRelUnitOneOnAxesStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CanonicalGaugeDifferenceBiadditiveJetStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsBiadditiveSeriesJetEqOfBiadditiveJetStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsCanonicalGaugeSubBiadditiveStatement
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValueCopiesGaugeIndependentStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartVal

section SlopeTestRemainingChoices
variable {k : Type} [CommRing k] {d : ℕ}

theorem jeq_sum {σ J : Type} {m : ℕ} (s : Finset J) {f g : J → MvPowerSeries σ k} (h : ∀ i, JEq m (f i) (g i)) :
    JEq m (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro e he
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => h i e he

theorem jeq_smul {σ : Type} {m : ℕ} (c : k) {f g : MvPowerSeries σ k} (h : JEq m f g) : JEq m (c • f) (c • g) := by
  intro e he
  rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, h e he]

theorem expS_zero [Algebra ℚ k] {n : ℕ} : FB.expS k (0 : PS k n d) = 1 := by
  unfold FB.expS
  have hs : PowerSeries.HasSubst (0 : PS k n d) := PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
  ext e
  rw [PowerSeries.coeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro j hj
    simp [hj]

theorem expS_sum [Algebra ℚ k] {n : ℕ} {J : Type} (s : Finset J) (f : J → PS k n d)
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) : FB.expS k (∑ i ∈ s, f i) = ∏ i ∈ s, FB.expS k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [expS_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, gt_expS_add _ _ (hf a) (by simp [map_sum, hf]), ih]

theorem expS_natSmul [Algebra ℚ k] {n : ℕ} (q : ℕ) (f : PS k n d)
    (hf : MvPowerSeries.constantCoeff f = 0) : FB.expS k ((q : k) • f) = FB.expS k f ^ q := by
  have h := expS_sum (Finset.range q) (fun _ => f) (fun _ => hf)
  rw [Finset.sum_const, Finset.prod_const, Finset.card_range] at h
  rw [← h, Nat.cast_smul_eq_nsmul]

theorem ev_sum {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) {J : Type} (s : Finset J) (f : J → PS k m d) :
    ev a (∑ i ∈ s, f i) = ∑ i ∈ s, ev a (f i) := by
  unfold ev
  rw [← MvPowerSeries.coe_substAlgHom (gt_hasSubst a ha), map_sum]

theorem ev_smul {m n : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j, GP (a j)) (c : k) (f : PS k m d) :
    ev a (c • f) = c • ev a f := by
  unfold ev
  rw [← MvPowerSeries.coe_substAlgHom (gt_hasSubst a ha), map_smul]

theorem ev_pt_self {n : ℕ} (f : PS k n d) : ev (fun b => pt k (n := n) d b) f = f := by
  change MvPowerSeries.subst (MvPowerSeries.X) f = f
  rw [MvPowerSeries.subst_self]
  rfl

theorem ev_diag {n : ℕ} (a : Pt k 1 d) (x : Pt k n d) (ha : GP a) (hx : GP x) (g : PS k 2 d) :
    ev ![x] (ev (n := 1) ![pt k d 0, comp1 a (pt k d 0)] g) = ev ![x, comp1 a x] g := by
  rw [gt_ev_ev' _ _ (single_point_zero_constant hx) (pair_points_zero_constant (gp_pt 0) (gp_comp1 _ _ ha (gp_pt 0))), eval_pair_points,
    evP_comp1 _ (single_point_zero_constant hx) _ _ (gp_pt 0), evP_pt _ (single_point_zero_constant hx)]
  rfl

theorem ev_pair {n : ℕ} (φ : Pt k 1 d) (hφ : GP φ) (a b : Pt k n d) (ha : GP a) (hb : GP b) (h : PS k 2 d) :
    ev ![a, b] (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) =
      ev ![comp1 φ a, comp1 φ b] h := by
  rw [gt_ev_ev' ![a, b] _ (pair_points_zero_constant ha hb)
      (pair_points_zero_constant (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1))), eval_pair_points,
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 0),
    evP_comp1 _ (pair_points_zero_constant ha hb) φ _ (gp_pt 1), evP_pt _ (pair_points_zero_constant ha hb), evP_pt _ (pair_points_zero_constant ha hb)]
  rfl

theorem jeq_main [Algebra ℚ k] {n : ℕ} (m q : ℕ) (φ φi a : Pt k 1 d) (hinv : IsInvPair φ φi) (ha : GP a)
    (h h' lam : PS k 2 d) (hh : MvPowerSeries.constantCoeff h = 0) (hh' : MvPowerSeries.constantCoeff h' = 0)
    (hl : MvPowerSeries.constantCoeff lam = 0)
    (hj : JEq m h' (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h + lam)) (f' : PS k n d) :
    JEq m (f' * FB.expS k ((q : k) • ∑ b : Fin n, ev (n := n) ![pt k d b]
        (ev (n := 1) ![pt k d 0, comp1 (comp1 φi (comp1 a φ)) (pt k d 0)] h')))
      (ev (n := n) (fun b => comp1 φ (pt k (n := n) d b))
        (ev (n := n) (fun b => comp1 φi (pt k (n := n) d b))
          (f' * ∏ b : Fin n, (ev ![pt k (n := n) d b, comp1 (comp1 φi (comp1 a φ)) (pt k (n := n) d b)]
            (FB.expS k lam)) ^ q) *
        FB.expS k ((q : k) • ∑ b : Fin n, ev (n := n) ![pt k d b]
          (ev (n := 1) ![pt k d 0, comp1 a (pt k d 0)] h)))) := by
  have hφ : GP φ := hinv.1
  have hφi : GP φi := hinv.2.1
  have ha' : GP (comp1 φi (comp1 a φ)) := gp_comp1 _ _ hφi (gp_comp1 _ _ ha hφ)
  have hp : ∀ b : Fin n, GP (pt k (n := n) d b) := fun b => gp_pt b
  have hΦ : ∀ b : Fin n, GP (comp1 φ (pt k (n := n) d b)) := fun b => gp_comp1 _ _ hφ (hp b)
  have hΦi : ∀ b : Fin n, GP (comp1 φi (pt k (n := n) d b)) := fun b => gp_comp1 _ _ hφi (hp b)
  set a' := comp1 φi (comp1 a φ) with ha'def
  have hL : ∀ b : Fin n, ∀ j, GP (![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] j) :=
    fun b => pair_points_zero_constant (hp b) (gp_comp1 _ _ ha' (hp b))
  have hLa : ∀ b : Fin n, ∀ j, GP (![pt k (n := n) d b, comp1 a (pt k (n := n) d b)] j) :=
    fun b => pair_points_zero_constant (hp b) (gp_comp1 _ _ ha (hp b))
  have hcomp : ∀ g : PS k n d, ev (n := n) (fun b => comp1 φ (pt k (n := n) d b))
      (ev (n := n) (fun b => comp1 φi (pt k (n := n) d b)) g) = g := by
    intro g
    rw [gt_ev_ev' _ _ hΦ hΦi]
    have : (fun j => evP (fun b => comp1 φ (pt k (n := n) d b)) (comp1 φi (pt k (n := n) d j))) =
        fun b => pt k (n := n) d b := by
      funext j
      rw [evP_comp1 _ hΦ _ _ (hp j), evP_pt _ hΦ, gt_comp_inv' hinv _ (hp j)]
    rw [this, ev_pt_self]
  have hφa : ∀ b : Fin n, comp1 φ (comp1 a' (pt k (n := n) d b)) = comp1 a (comp1 φ (pt k (n := n) d b)) := by
    intro b
    rw [ha'def, gt_comp1_comp1 φi _ (gp_comp1 _ φ ha hφ) _ (hp b), gt_comp1_comp1 a φ hφ _ (hp b),
      gt_comp_inv hinv _ (gp_comp1 _ _ ha (hΦ b))]
  have hterm : ∀ b : Fin n, ev (n := n) (fun b => comp1 φ (pt k (n := n) d b))
      (ev ![pt k (n := n) d b, comp1 a (pt k (n := n) d b)] h) =
      ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)]
        (ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h) := by
    intro b
    rw [ev_pair φ hφ _ _ (hp b) (gp_comp1 _ _ ha' (hp b)), hφa, gt_ev_ev' _ _ hΦ (hLa b), eval_pair_points,
      evP_comp1 _ hΦ _ _ (hp b), evP_pt _ hΦ]
  set h0 := ev ![comp1 φ (pt k (n := 2) d 0), comp1 φ (pt k (n := 2) d 1)] h with h0def
  have hh0 : MvPowerSeries.constantCoeff h0 = 0 :=
    gt_const_ev _ (pair_points_zero_constant (gp_comp1 _ _ hφ (gp_pt 0)) (gp_comp1 _ _ hφ (gp_pt 1))) _ hh
  have cS : ∀ (V : Fin n → Fin 2 → Pt k n d), (∀ b j, GP (V b j)) → ∀ g : PS k 2 d,
      MvPowerSeries.constantCoeff g = 0 → MvPowerSeries.constantCoeff (∑ b, ev (V b) g) = 0 := by
    intro V hV g hg
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => gt_const_ev _ (hV b) _ hg
  have cS' : ∀ (V : Fin n → Fin 2 → Pt k n d), (∀ b j, GP (V b j)) → ∀ g : PS k 2 d,
      MvPowerSeries.constantCoeff g = 0 → MvPowerSeries.constantCoeff ((q : k) • ∑ b, ev (V b) g) = 0 := by
    intro V hV g hg
    rw [MvPowerSeries.constantCoeff_smul, cS V hV g hg, smul_zero]
  simp only [ev_diag _ _ ha' (hp _), ev_diag _ _ ha (hp _)]
  rw [gt_ev_mul _ hΦ, hcomp, gt_ev_expS _ hΦ _ (cS' _ hLa h hh), ev_smul _ hΦ, ev_sum _ hΦ]
  simp only [hterm]
  have hE : ∏ b : Fin n, (ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] (FB.expS k lam)) ^ q =
      FB.expS k ((q : k) • ∑ b : Fin n, ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] lam) := by
    rw [expS_natSmul _ _ (cS _ hL lam hl), expS_sum _ _ (fun b => gt_const_ev _ (hL b) _ hl), Finset.prod_pow]
    congr 1
    exact Finset.prod_congr rfl fun b _ => gt_ev_expS _ (hL b) _ hl
  rw [hE, _root_.mul_assoc, ← gt_expS_add _ _ (cS' _ hL lam hl) (cS' _ hL h0 hh0), ← smul_add, ← Finset.sum_add_distrib]
  refine ((GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).1 _ _ _ _ _ (JEq.refl m f') ?_).2.2
  have hsum : (∑ b : Fin n, (ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] lam +
      ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] h0)) =
      ∑ b : Fin n, ev ![pt k (n := n) d b, comp1 a' (pt k (n := n) d b)] (h0 + lam) :=
    Finset.sum_congr rfl fun b _ => by rw [gt_ev_add _ (hL b), add_comm]
  rw [hsum]
  refine ((GlobalTheory.T.jetEq_formalExp_iff_and_exists_log k n d m).1 _ _ (cS' _ hL h' hh') (cS' _ hL _ (by rw [map_add, hh0, hl, add_zero]))).1 ?_
  exact jeq_smul _ (jeq_sum _ fun b => (GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).2.2.2.1 d 2 n _ _ _ _ (hL b) (hL b)
    (fun _ _ => JEq.refl _ _) hj)

end SlopeTestRemainingChoices

open GlobalTheory.FBMap in

theorem exists_nabValN_eq : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B B' : FB R d O) (φ φi : Pt R 1 d), (∀ m, ∃ ε : PS R 2 d, JRel m B B' φ φi ε) → ∀ h h' : PS k 2 d, B.IsCanonGauge k h → B'.IsCanonGauge k h' → ∀ (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k), (∀ τ, cc (cc τ) = τ) → (∀ τ, isX τ ∨ isX (cc τ)) → (∀ τ a, σ (cc τ) a = σ τ (star a)) → (∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) → ∀ u u' : (Σ τ : T, Fin (r τ)) → Fin d → k, (∀ l a, (dAct k B' a).mulVec (u' l) = σ l.1 a • u' l) → (∀ l, u l = ((dLin φ).map (algebraMap R k)).mulVec (u' l)) → ∀ (n : ℕ) (P : MvPolynomial (Letter T r n) k), P ∈ harmK r n k cc isX (fun _ => 1) → ∀ (w0 : O) (q : ℕ) (f' : PS R n d), ∃ f : PS R n d, nabValN B k h w0 q (MvPowerSeries.map (algebraMap R k) f) (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P = nabValN B' k h' w0 q (MvPowerSeries.map (algebraMap R k) f') (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u' ⟨ℓ.1, ℓ.2.1⟩) P := by
  intro R _ d O _ _ _ _ _ k _ _ _ B B' φ φi hrel h h' hh hh' T _ r cc isX σ h1 h2 h3 h4 u u' hu' hu n P hP w0 q f'
  obtain ⟨ε, hε⟩ := hrel (P.totalDegree + 2)
  set m := P.totalDegree + 2 with hm
  have hε1 := (GlobalTheory.T.formalChartJetRel_unit_one_on_axes R d O m B B' φ φi ε hε).1
  obtain ⟨lam, hl0, hle⟩ := (GlobalTheory.T.jetEq_formalExp_iff_and_exists_log k 2 d m).2 (FB.toK k ε) (by simp [FB.toK, hε1])
  have hbi := GlobalTheory.T.canonicalGauge_difference_biadditive_jet R d O m B B' φ φi ε hε k h h' lam hh hh' hl0 hle
  obtain ⟨g', hg', hgg⟩ := GlobalTheory.T.exists_biadditive_series_jetEq_of_biadditiveJet R d O B' k m (by omega) _ hbi
  have hcan := GlobalTheory.T.isCanonicalGauge_sub_biadditive R d O B' k h' g' hh' hg'
  have c0 : ∀ {C : FB R d O} {g : PS k 2 d}, C.IsCanonGauge k g → MvPowerSeries.constantCoeff g = 0 := by
    intro C g hg
    have := congrArg MvPowerSeries.constantCoeff hg.ax0
    rwa [gt_const_ev_eq _ (pair_points_zero_constant gp_zero₂ (gp_pt 0)), map_zero] at this
  have hφ : NoConst φ := hε.inv.1
  have hφi : NoConst φi := hε.inv.2.1
  have hinv : IsInvPair (mapPt (algebraMap R k) φ) (mapPt (algebraMap R k) φi) := by
    refine ⟨fun i => by simp [mapPt, hφ i], fun i => by simp [mapPt, hφi i], ?_, ?_⟩
    · rw [← mapPt_comp1 _ _ hφi, hε.inv.2.2.1, mapPt_pt]
    · rw [← mapPt_comp1 _ _ hφ, hε.inv.2.2.2, mapPt_pt]
  have hact : B'.actK k w0 = comp1 (mapPt (algebraMap R k) φi) (comp1 (B.actK k w0) (mapPt (algebraMap R k) φ)) := by
    change mapPt (algebraMap R k) (B'.A.act w0) = comp1 _ (comp1 (mapPt (algebraMap R k) (B.A.act w0)) _)
    rw [hε.act w0, mapPt_comp1 _ _ (nc_comp1 (nc_act _ _) hφ), mapPt_comp1 _ _ hφ]
  have hF : B'.FK k = transF (mapLaw (algebraMap R k) B.G).F (mapPt (algebraMap R k) φ) (mapPt (algebraMap R k) φi) := by
    funext i
    change MvPowerSeries.map (algebraMap R k) (B'.G.F i) = _
    rw [hε.law i]
    unfold transF
    rw [map_ev1 _ (nc_addOf (nc_law _) (nc_comp1 hφ (nc_pt _)) (nc_comp1 hφ (nc_pt _))),
      mapPt_addOf _ _ (nc_comp1 hφ (nc_pt _)) (nc_comp1 hφ (nc_pt _)), mapPt_comp1 _ _ (nc_pt _),
      mapPt_comp1 _ _ (nc_pt _), mapPt_pt, mapPt_pt]
    rfl
  have hd : dLin (mapPt (algebraMap R k) φ) = (dLin φ).map (algebraMap R k) := by
    ext i j
    simp [dLin, mapPt]
  have hj : JEq m (h' - g') (ev ![comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 0),
      comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 1)] h + lam) := by
    intro e he
    have := hgg e he
    rw [map_sub, map_sub] at this
    rw [map_sub, map_add, ← this]
    change _ - (_ - MvPowerSeries.coeff e (ev ![comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 0),
      comp1 (mapPt (algebraMap R k) φ) (pt k (n := 2) d 1)] h) - _) = _
    ring
  have haK : GP (B.actK k w0) := fun i => by simp [FB.actK, B.A.const w0 i]
  have key := jeq_main (n := n) m q _ _ (B.actK k w0) hinv haK h (h' - g') lam (c0 hh) (c0 hcan) hl0 hj
    (MvPowerSeries.map (algebraMap R k) f')
  refine ⟨ev (n := n) (fun b => comp1 φi (pt R (n := n) d b))
    (f' * ∏ b : Fin n, (ev ![pt R (n := n) d b, comp1 (B'.A.act w0) (pt R (n := n) d b)] ε) ^ q), ?_⟩
  rw [GlobalTheory.T.harmonicValueCopies_gauge_independent R d O k B' h' (h' - g') hh' hcan T r cc isX σ h1 h2 h3 h4 u' hu' n P hP w0 q]
  have hmap : MvPowerSeries.map (algebraMap R k) (ev (n := n) (fun b => comp1 φi (pt R (n := n) d b))
      (f' * ∏ b : Fin n, (ev ![pt R (n := n) d b, comp1 (B'.A.act w0) (pt R (n := n) d b)] ε) ^ q)) =
      ev (n := n) (fun b => comp1 (mapPt (algebraMap R k) φi) (pt k (n := n) d b))
        (MvPowerSeries.map (algebraMap R k) f' * ∏ b : Fin n, (ev ![pt k (n := n) d b,
          comp1 (B'.actK k w0) (pt k (n := n) d b)] (FB.expS k lam)) ^ q) := by
    rw [map_ev _ (fun b => nc_comp1 hφi (nc_pt b)), map_mul, map_prod]
    congr 1
    · funext b
      rw [mapPt_comp1 _ _ (nc_pt _), mapPt_pt]
    · congr 1
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [map_pow, map_ev2 _ (nc_pt _) (nc_comp1 (nc_act _ _) (nc_pt _)), mapPt_comp1 _ _ (nc_pt _), mapPt_pt, hle]
      rfl
  unfold nabValN FB.hL
  rw [hmap, hF, hact, GlobalTheory.T.constantCoeff_invariantPolyOperator_jetEq k d n _ _ _ _ P m _ _ (by omega) key,
    GlobalTheory.T.invariantPolyOperatorCopies_transportedLaw k d n (mapLaw (algebraMap R k) B.G) _ _ hinv,
    gt_const_ev_eq _ (fun b => gp_comp1 _ _ hinv.1 (gp_pt b)), hd]
  simp only [hu]
  rfl

end GlobalTheory.ChartVal
