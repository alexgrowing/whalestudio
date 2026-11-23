import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.AdditionLawSecondIdentity
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicValuesEqOfRelatedBiextensions
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameRatioAdjointnessSeries
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr

set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
open GlobalTheory.ChartCmp GlobalTheory.ChartVal GlobalTheory.FrameBiextId
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.ChartField

open GlobalTheory.FBMap in

theorem nabValN_transport (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O]
    [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] [Algebra R k] (B B' : FB R d O)
    (φ φi : Pt R 1 d) (h h' : PS k 2 d) (hh : B.IsCanonGauge k h) (hh' : B'.IsCanonGauge k h')
    (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k) (h1 : ∀ τ, cc (cc τ) = τ)
    (h2 : ∀ τ, isX τ ∨ isX (cc τ)) (h3 : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (h4 : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) (u u' : (Σ τ : T, Fin (r τ)) → Fin d → k)
    (hu' : ∀ l a, (dAct k B' a).mulVec (u' l) = σ l.1 a • u' l)
    (hu : ∀ l, u l = ((dLin φ).map (algebraMap R k)).mulVec (u' l)) (n : ℕ) (P : MvPolynomial (Letter T r n) k)
    (hP : P ∈ harmK r n k cc isX (fun _ => 1)) (w0 : O) (q : ℕ) (f' : PS R n d) (m : ℕ) (hm : m = P.totalDegree + 2)
    (ε : PS R 2 d) (hε : JRel m B B' φ φi ε) :
    nabValN B k h w0 q (MvPowerSeries.map (algebraMap R k) (ev (n := n) (fun b => comp1 φi (pt R (n := n) d b))
        (f' * ∏ b : Fin n, (ev ![pt R (n := n) d b, comp1 (B'.A.act w0) (pt R (n := n) d b)] ε) ^ q)))
      (fun ℓ : Letter T r n => ℓ.2.2) (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P =
    nabValN B' k h' w0 q (MvPowerSeries.map (algebraMap R k) f') (fun ℓ : Letter T r n => ℓ.2.2)
      (fun ℓ : Letter T r n => u' ⟨ℓ.1, ℓ.2.1⟩) P := by
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

section Box
variable {k : Type} [CommRing k] {d n : ℕ}

theorem boxSer_eq (f : Fin n → PS k 1 d) : GlobalTheory.PowGerm.boxSer f = ∏ b, sb ![(gen b : Q k d n)] (f b) := by
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [MvPowerSeries.rename_eq_subst, sb_apply, ev]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  rfl

theorem jeq_prod {σ J : Type} {m : ℕ} (s : Finset J) {f g : J → MvPowerSeries σ k} (h : ∀ i, JEq m (f i) (g i)) :
    JEq m (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using JEq.refl m _
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact ((GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).1 _ _ _ _ _ (h a) ih).2.2

theorem sb_one (u : Q k d n) (f : PS k 1 d) : sb ![u] f = ev ![u.1] f :=
  (sb_apply _ _).trans (congrArg (ev · f) (funext fun j => by fin_cases j; rfl))

theorem sb_sb_one {l : ℕ} (b : Fin n → Q k d l) (u : Q k d n) (f : PS k 1 d) : sb b (sb ![u] f) = sb ![sq b u] f :=
  (sb_sb _ _ _).trans (congrArg (sb · f) (funext fun j => by fin_cases j; rfl))

theorem jeq_box {m q : ℕ} (Φ Ψ A : Q k d 1) (hΦΨ : ac Φ Ψ = gen 0) (ε : PS k 2 d) (f f' : Fin n → PS k 1 d)
    (h : ∀ b, JEq m (ev ![Φ.1] (f b)) (f' b * ev (n := 1) ![pt k d 0, comp1 A.1 (pt k d 0)] ε ^ q)) :
    JEq m (GlobalTheory.PowGerm.boxSer f) (ev (n := n) (fun b => comp1 Ψ.1 (pt k (n := n) d b))
      (GlobalTheory.PowGerm.boxSer f' * ∏ b : Fin n, (ev ![pt k (n := n) d b, comp1 A.1 (pt k (n := n) d b)] ε) ^ q)) := by
  have e1 : ∀ g : PS k n d, ev (n := n) (fun b => comp1 Ψ.1 (pt k (n := n) d b)) g =
      sb (fun b => ac Ψ (gen b : Q k d n)) g := fun g => by
    rw [sb_apply]; simp only [ac_val, gen_val]
  have e2 : ∀ b : Fin n, ev ![pt k (n := n) d b, comp1 A.1 (pt k (n := n) d b)] ε =
      sb ![(gen b : Q k d n)] (ev (n := 1) ![pt k d 0, comp1 A.1 (pt k d 0)] ε) := fun b => by
    rw [← gen_val, ← gen_val, ← ac_val, ← ac_val, ← formalSeriesValueAtTwoPoints_eq_ev, ← formalSeriesValueAtTwoPoints_eq_ev, formalPointSubstitutionSeries_valueAtTwoPoints, sq_ac, sq_gen]
    rfl
  rw [e1, boxSer_eq, boxSer_eq, ← Finset.prod_mul_distrib, map_prod]
  refine jeq_prod _ fun b => ?_
  rw [e2, ← map_pow, ← map_mul, sb_sb_one, sq_gen]
  have e3 : sb ![(gen b : Q k d n)] (f b) = sb ![ac Ψ (gen b : Q k d n)] (ev ![Φ.1] (f b)) := by
    rw [← sb_one, sb_sb_one]
    change _ = sb ![ac Φ (ac Ψ (gen b))] (f b)
    rw [← FrameRatioAdj.ac_ac, hΦΨ]
    exact congrArg (fun u => sb ![u] (f b)) (sq_gen ![gen b] 0).symm
  rw [e3, sb_apply, sb_apply]
  exact (GlobalTheory.T.mvPowerSeriesJetEq_calculus k m).2.2.2.1 d 1 n _ _ _ _ (fun i j => (_ : Q k d n).2 j) (fun i j => (_ : Q k d n).2 j)
    (fun _ _ => JEq.refl _ _) (h b)

theorem ac_gen (Φ : Q k d 1) : ac Φ (gen 0 : Q k d 1) = Φ := Subtype.ext ((ac_val _ _).trans (gt_comp1_pt_right _))

theorem gen_ac (u : Q k d n) : ac (gen 0) u = u := sq_gen _ _

theorem coord_of_exp (α β α' β' : Q k d 1) (h : IsInvPair α.1 β.1) (h' : IsInvPair α'.1 β'.1) :
    IsInvPair (ac α β').1 (ac α' β).1 ∧ ac (ac α β') α' = α ∧
    (∀ F F' L : Q k d 2, op F (ac α (gen 0 : Q k d 2)) (ac α (gen 1)) = ac α L →
      op F' (ac α' (gen 0 : Q k d 2)) (ac α' (gen 1)) = ac α' L → ∀ i, F'.1 i = transF F.1 (ac α β').1 (ac α' β).1 i) ∧
    ∀ A A' D : Q k d 1, ac A α = ac α D → ac A' α' = ac α' D →
      A'.1 = comp1 (ac α' β).1 (comp1 A.1 (ac α β').1) := by
  have i1 : ∀ {l} (u : Q k d l), ac α (ac β u) = u := fun u => Subtype.ext (by
    rw [ac_val, ac_val]; exact gt_comp_inv h _ u.2)
  have i2 : ∀ {l} (u : Q k d l), ac β (ac α u) = u := fun u => Subtype.ext (by
    rw [ac_val, ac_val]; exact gt_comp_inv' h _ u.2)
  have i1' : ∀ {l} (u : Q k d l), ac α' (ac β' u) = u := fun u => Subtype.ext (by
    rw [ac_val, ac_val]; exact gt_comp_inv h' _ u.2)
  have i2' : ∀ {l} (u : Q k d l), ac β' (ac α' u) = u := fun u => Subtype.ext (by
    rw [ac_val, ac_val]; exact gt_comp_inv' h' _ u.2)
  have j : ∀ {a b : Q k d 1}, (∀ u : Q k d 1, ac a (ac b u) = u) → ac a b = gen 0 := fun {a b} e => by
    rw [← e (gen 0), ac_gen]
  refine ⟨⟨(ac α β').2, (ac α' β).2, ?_, ?_⟩, ?_, fun F F' L e e' => ?_, fun A A' D e e' => ?_⟩
  · rw [← ac_val, FrameRatioAdj.ac_ac, ← FrameRatioAdj.ac_ac β', j i2', gen_ac, j i1, gen_val]
  · rw [← ac_val, FrameRatioAdj.ac_ac, ← FrameRatioAdj.ac_ac β, j i2, gen_ac, j i1', gen_val]
  · rw [FrameRatioAdj.ac_ac, j i2', ac_gen]
  · have c := congrArg (sq ![ac β' (gen 0 : Q k d 2), ac β' (gen 1)]) e
    have c' := congrArg (sq ![ac β' (gen 0 : Q k d 2), ac β' (gen 1)]) e'
    simp only [sq_op, sq_ac, sq_gen, Matrix.cons_val, i1'] at c c'
    have : F' = ac (ac α' β) (op F (ac (ac α β') (gen 0 : Q k d 2)) (ac (ac α β') (gen 1))) := by
      simp only [FrameRatioAdj.ac_ac, c, i2, ← c']
      exact Subtype.ext (funext fun i => (formalSeriesValueAtTwoPoints_genericPoints _).symm)
    intro i
    rw [this]
    simp only [ac_val (ac α' β), op_val, ac_val (ac α β'), gen_val]
    rfl
  · rw [← ac_val, ← ac_val, ← FrameRatioAdj.ac_ac A, e, FrameRatioAdj.ac_ac, FrameRatioAdj.ac_ac, i2,
      ← FrameRatioAdj.ac_ac, ← e', FrameRatioAdj.ac_ac, j i1', ac_gen]

end Box

theorem nabValN_box_eq (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O]
    [Module.Finite ℤ O] [IsReduced O] (k : Type) [Field k] [Algebra ℚ k] (B B' : FB k d O)
    (Φ Ψ : Q k d 1) (h h' : PS k 2 d) (hh : B.IsCanonGauge k h) (hh' : B'.IsCanonGauge k h')
    (T : Type) [Fintype T] (r : T → ℕ) (cc : T → T) (isX : T → Prop) (σ : T → O →+* k) (h1 : ∀ τ, cc (cc τ) = τ)
    (h2 : ∀ τ, isX τ ∨ isX (cc τ)) (h3 : ∀ τ a, σ (cc τ) a = σ τ (star a))
    (h4 : ∀ τ τ', τ ≠ τ' → ∃ a, IsUnit (σ τ a - σ τ' a)) (u u' : (Σ τ : T, Fin (r τ)) → Fin d → k)
    (hu' : ∀ l a, (dAct k B' a).mulVec (u' l) = σ l.1 a • u' l)
    (hu : ∀ l, u l = (dLin Φ.1).mulVec (u' l)) (n : ℕ) (P : MvPolynomial (Letter T r n) k)
    (hP : P ∈ harmK r n k cc isX (fun _ => 1)) (w0 : O) (q : ℕ) (f f' : Fin n → PS k 1 d)
    (ε : PS k 2 d) (hε : JRel (P.totalDegree + 2) B B' Φ.1 Ψ.1 ε)
    (hf : ∀ b, JEq (P.totalDegree + 2) (ev ![Φ.1] (f b))
      (f' b * ev (n := 1) ![pt k d 0, comp1 (B'.A.act w0) (pt k d 0)] ε ^ q)) :
    nabValN B k h w0 q (GlobalTheory.PowGerm.boxSer f) (fun ℓ : Letter T r n => ℓ.2.2)
      (fun ℓ : Letter T r n => u ⟨ℓ.1, ℓ.2.1⟩) P =
    nabValN B' k h' w0 q (GlobalTheory.PowGerm.boxSer f') (fun ℓ : Letter T r n => ℓ.2.2)
      (fun ℓ : Letter T r n => u' ⟨ℓ.1, ℓ.2.1⟩) P := by
  have key := nabValN_transport k d O k B B' Φ.1 Ψ.1 h h' hh hh' T r cc isX σ h1 h2 h3 h4 u u' hu'
    (fun l => by rw [hu l]; rfl) n P hP w0 q (GlobalTheory.PowGerm.boxSer f') _ rfl ε hε
  rw [gt_map_id, gt_map_id] at key
  rw [← key]
  have hb := jeq_box Φ Ψ (⟨B'.A.act w0, B'.A.const w0⟩ : Q k d 1) (Subtype.ext ((ac_val Φ Ψ).trans hε.inv.2.2.1)) ε f f' hf
  exact (GlobalTheory.PowGerm.nabJet k d O B k h w0 q n _ _ _).1 P _ _ fun e he => hb e (by omega)

end GlobalTheory.ChartField
