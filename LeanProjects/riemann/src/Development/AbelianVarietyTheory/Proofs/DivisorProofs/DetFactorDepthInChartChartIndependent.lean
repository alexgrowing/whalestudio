import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.NuAlgLeOfCharts
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsExpEqOfSubstLg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermLinearPartCoordinatePointZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TangentEqLcZero

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FactorDepth

section Series
open MvPowerSeries ReciprocityTheory.PGsh GlobalTheory.FGDepth

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

theorem exp_eq_of_log_hom {d : ℕ} (G G' : LogFGL v d) (Φ : Fin d → MvPowerSeries (Fin d) C)
    (h0 : ∀ e, constantCoeff (Φ e) = 0) (M : Matrix (Fin d) (Fin d) C)
    (hl : ∀ e, subst Φ (G.lg e) = ∑ f, M e f • G'.lg f) {τ : Type} (w w' : Fin d → MvPowerSeries τ C)
    (hw' : ∀ e, constantCoeff (w' e) = 0) (hw : ∀ e, w e = ∑ f, M e f • w' f) (e : Fin d) :
    subst w (expOf G e) = subst (fun f => subst w' (expOf G' f)) (Φ e) := by
  have s1 : HasSubst w' := hasSubst_of_constantCoeff_zero hw'
  have c2 : ∀ f, constantCoeff (subst w' (expOf G' f) : MvPowerSeries τ C) = 0 := fun f =>
    constantCoeff_subst_eq_zero s1 hw' ((isExp_expOf G').1 f)
  have s2 := hasSubst_of_constantCoeff_zero c2
  have s3 : HasSubst (fun e => (subst (fun f => (subst w' (expOf G' f) : MvPowerSeries τ C)) (Φ e) :
      MvPowerSeries τ C)) :=
    hasSubst_of_constantCoeff_zero fun e => constantCoeff_subst_eq_zero s2 c2 (h0 e)
  have key : (fun j => subst (fun e => (subst (fun f => (subst w' (expOf G' f) : MvPowerSeries τ C)) (Φ e) :
      MvPowerSeries τ C)) (G.lg j)) = w := by
    funext j
    rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) s2, hl, hw, ← coe_substAlgHom s2, map_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [map_smul, coe_substAlgHom,
      ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G').1) s1, (isExp_expOf G').2,
      subst_X s1]
  have := subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.lg_const) s3 (expOf G e)
  rw [subst_lg_expOf, subst_X s3, key] at this
  exact this.symm

theorem depth_le_of_log_hom {κ : Type} [Finite κ] {d : κ → ℕ} (G G' : ∀ b, LogFGL v (d b)) {ι : κ → Type}
    [∀ b, Fintype (ι b)] (u u' : ∀ b, ι b → Fin (d b) → C) (Φ : ∀ b, Fin (d b) → MvPowerSeries (Fin (d b)) C)
    (h0 : ∀ b e, constantCoeff (Φ b e) = 0) (hI : ∀ b e, MvIsInt v (Φ b e))
    (M : ∀ b, Matrix (Fin (d b)) (Fin (d b)) C)
    (hl : ∀ b e, subst (Φ b) ((G b).lg e) = ∑ f, M b e f • (G' b).lg f)
    (hu : ∀ b a, u b a = (M b).mulVec (u' b a)) (P : MvPolynomial (Σ b, ι b) C) :
    depth G' u' P ≤ depth G u P := by
  classical
  have cX : ∀ b (e : Fin (d b)), constantCoeff (X ⟨b, e⟩ : MvPowerSeries (Σ b, Fin (d b)) C) = 0 := fun b e => by simp
  let Ψ : (Σ b, Fin (d b)) → MvPowerSeries (Σ b, Fin (d b)) C :=
    fun x => subst (fun e : Fin (d x.1) => (X ⟨x.1, e⟩ : MvPowerSeries (Σ b, Fin (d b)) C)) (Φ x.1 x.2)
  have cΨ : ∀ x, constantCoeff (Ψ x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (cX x.1)) (cX x.1) (h0 x.1 x.2)
  have iΨ : ∀ x, MvIsInt v (Ψ x) := fun x =>
    ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hI x.1 x.2)
      (fun e α => by rw [coeff_X]; split_ifs <;> simp [IsIntV]) (cX x.1)
  have cw : ∀ b (e : Fin (d b)),
      constantCoeff (∑ a, u' b a e • (X ⟨b, a⟩ : MvPowerSeries (Σ b, ι b) C)) = 0 := fun b e => by simp
  have cE : ∀ x, constantCoeff (expAlong G' u' x) = 0 := fun x =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero (cw x.1)) (cw x.1) ((isExp_expOf _).1 _)
  have sE := hasSubst_of_constantCoeff_zero cE
  have key : expAlong G u = fun x => subst (expAlong G' u') (Ψ x) := by
    funext x
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (cX x.1)) sE]
    simp only [subst_X sE]
    refine exp_eq_of_log_hom (G x.1) (G' x.1) (Φ x.1) (h0 x.1) (M x.1) (hl x.1) _ _ (cw x.1) (fun e => ?_) x.2
    simp only [hu, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum, smul_smul]
    exact Finset.sum_comm
  refine le_iInf fun f => iInf_le_of_le
    ⟨subst Ψ f.1, ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v f.2 iΨ cΨ⟩ (le_of_eq ?_)
  rw [key, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero cΨ) sE]

end Series

section Law
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.LawLog

variable {C : Type} [Field C] [CharZero C] {d : ℕ}

theorem logOf_spec (G : FGLaw C d) : GP (GlobalTheory.FormalLog.logOf G) ∧ dLin (GlobalTheory.FormalLog.logOf G) = 1 ∧
    comp1 (GlobalTheory.FormalLog.logOf G) (addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1)) =
      comp1 (GlobalTheory.FormalLog.logOf G) (pt C (n := 2) d 0) + comp1 (GlobalTheory.FormalLog.logOf G) (pt C (n := 2) d 1) := by
  refine ⟨fun i => GlobalTheory.FormalLog.constantCoeff_prim _, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    show coeff (Finsupp.single ((0 : Fin 1), j) 1) (GlobalTheory.FormalLog.logOf G i) = (1 : Matrix (Fin d) (Fin d) C) i j
    have h := congrArg constantCoeff (GlobalTheory.FormalLog.pderiv_logOf G i j)
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add] at h
    have h2 := congrFun (congrFun (GlobalTheory.FormalLog.cc_om G) i) j
    simp only [Matrix.map_apply] at h2
    simpa [h2] using h
  · have e : addOf G.F (pt C (n := 2) d 0) (pt C (n := 2) d 1) = G.F := add_pt G
    rw [e]
    funext i
    exact GlobalTheory.FormalLog.logOf_add G i

theorem logOf_comp_hom (G G' : FGLaw C d) (φ : Pt C 1 d) (hφ : GP φ)
    (hhom : comp1 φ G'.F = addOf G.F (comp1 φ (pt C (n := 2) d 0)) (comp1 φ (pt C (n := 2) d 1))) :
    comp1 (GlobalTheory.FormalLog.logOf G) φ = fun i => ∑ j : Fin d, dLin φ i j • GlobalTheory.FormalLog.logOf G' j := by
  obtain ⟨a0, a1, a2⟩ := logOf_spec G
  obtain ⟨b0, b1, b2⟩ := logOf_spec G'
  obtain ⟨ε, hi⟩ := ChartInv.exists_isInvPair C d _ b0 (by rw [b1, Matrix.det_one]; exact isUnit_one)
  have p0 : GP (pt C (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) d 1) := gp_pt 1
  have e : addOf G'.F (pt C (n := 2) d 0) (pt C (n := 2) d 1) = G'.F := add_pt G'
  have e1 := additive_eq_lin _ G'.const _ ε (comp1 (GlobalTheory.FormalLog.logOf G) φ) b1 b2 hi
    (gp_comp1 _ _ a0 hφ) (by
    rw [e, gt_comp1_comp1 _ _ hφ _ G'.const, hhom,
      additive_at _ G.const _ a2 _ _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1),
      gt_comp1_comp1 _ _ hφ _ p0, gt_comp1_comp1 _ _ hφ _ p1])
  rw [dLin_comp _ _ hφ, a1, one_mul] at e1
  rw [e1]
  funext i
  rw [germComp_matrixLinearMap_apply _ _ b0]
  simp only [MvPowerSeries.smul_eq_C_mul]

open ReciprocityTheory.PGsh GlobalTheory.FGDepth in

theorem detDepth_le_of_transF {R : Type} [CommRing R] (v : AddValuation C (WithTop ℝ)) (j : R →+* C)
    (hj : ∀ r, IsIntV v (j r)) (F F' : Fin d → PS R 2 d) (hF : ∀ a, constantCoeff (F a) = 0)
    (φ φi : Pt R 1 d) (hi : IsInvPair φ φi)
    (ht : ∀ a, F' a = transF F φ φi a) (L L' : FGLaw C d) (hL : ∀ a, L.F a = MvPowerSeries.map j (F a))
    (hL' : ∀ a, L'.F a = MvPowerSeries.map j (F' a))
    (hI : ∀ a, MvIsInt v (subst (twoVars C d) (L.F a))) (hI' : ∀ a, MvIsInt v (subst (twoVars C d) (L'.F a)))
    {i : ℕ} (u u' : Fin i → Fin d → R) (hu : ∀ a, u a = (dLin φ).mulVec (u' a)) (k : ℕ) :
    detDepth (logFGLOf v L' hI') (fun a e => j (u' a e)) k ≤ detDepth (logFGLOf v L hI) (fun a e => j (u a e)) k := by
  have hφ : GP φ := hi.1
  have p0 : GP (pt R (n := 2) d 0) := gp_pt 0
  have p1 : GP (pt R (n := 2) d 1) := gp_pt 1
  have q := gp_addOf F hF _ _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1)
  have e0 : F' = comp1 φi (addOf F (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1))) := funext ht
  have hF' : GP F' := e0 ▸ gp_comp1 _ _ hi.2.1 q
  have e1 : comp1 φ F' = addOf F (comp1 φ (pt R (n := 2) d 0)) (comp1 φ (pt R (n := 2) d 1)) := by
    rw [e0, gt_comp_inv hi _ q]
  have e2 := congrArg (GlobalTheory.FBMap.mapPt j) e1
  rw [GlobalTheory.FBMap.mapPt_comp1 j _ hF', GlobalTheory.FBMap.mapPt_addOf j _ (gp_comp1 _ _ hφ p0) (gp_comp1 _ _ hφ p1),
    GlobalTheory.FBMap.mapPt_comp1 j _ p0, GlobalTheory.FBMap.mapPt_comp1 j _ p1, GlobalTheory.FBMap.mapPt_pt, GlobalTheory.FBMap.mapPt_pt,
    show GlobalTheory.FBMap.mapPt j F = L.F from (funext hL).symm, show GlobalTheory.FBMap.mapPt j F' = L'.F from (funext hL').symm] at e2
  have hψ : GP (GlobalTheory.FBMap.mapPt j φ) := fun a => by simp [GlobalTheory.FBMap.mapPt, hφ a]
  have e3 := logOf_comp_hom L L' _ hψ e2
  refine depth_le_of_log_hom _ _ _ _ (fun _ a => subst (oneVar C d) (GlobalTheory.FBMap.mapPt j φ a))
    (fun _ a => constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hψ a)) (fun _ a α => ?_)
    (fun _ => dLin (GlobalTheory.FBMap.mapPt j φ)) (fun _ a => ?_) (fun _ a => ?_) _
  · have e : subst (oneVar C d) (GlobalTheory.FBMap.mapPt j φ a) = MvPowerSeries.map j (subst (oneVar R d) (φ a)) := by
      rw [MvPowerSeries.map_subst hs_oneVar]
      congr 1
      funext q
      simp [oneVar]
    rw [e, coeff_map]
    exact hj _
  · show subst _ (subst (oneVar C d) (GlobalTheory.FormalLog.logOf L a)) =
      ∑ f, _ • subst (oneVar C d) (GlobalTheory.FormalLog.logOf L' f)
    rw [subst_oneVar _ cc_oneVar _ hψ]
    refine (congrArg (subst (oneVar C d)) (congrFun e3 a)).trans ?_
    rw [← coe_substAlgHom hs_oneVar, map_sum]
    simp only [map_smul]
  · funext e
    rw [hu, RingHom.map_mulVec]
    rfl

end Law

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp GlobalTheory.CharDepth ReciprocityTheory.PGsh GlobalTheory.FGDepth GlobalTheory.LawLog

theorem detDepth_le_of_charts {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = H.bar a)
    (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V)))
    (hsurj : Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom) (d d' : ℕ)
    (B : FB V d (𝓞 E)) (B' : FB V d' (𝓞 E))
    (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : Fin d' → (Sp (DualNumber V) ⟶ t'.G.left))
    (uv : Fin d → Fin d → V) (uv' : Fin d' → Fin d' → V)
    (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d' m 1 ⟶ t'.G)
    (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d' x' m)
    (hc : IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x)
    (hc' : IsChartG t' (𝟙 (Sp V)) d' B'.G.F B'.A.act tg' uv' x')
    (hu : GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x) (hu' : GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d') x')
    (hf : IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e)
    (hf' : IsFrameG t' (𝟙 (Sp V)) d' x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e')
    {i : ℕ} (u : Fin i → Fin d → V) (u' : Fin i → Fin d' → V)
    (w : Fin i → (Sp (DualNumber V) ⟶ t.G.left))
    (hw : ∀ ℓ, IsCombAtG t (𝟙 (Sp V)) (dirs x) (u ℓ) (w ℓ))
    (hw' : ∀ ℓ, IsCombAtG t' (𝟙 (Sp V)) (dirs x') (u' ℓ) (w ℓ ≫ n.φ))
    {C : Type} [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (j : V →+* C) (hj : ∀ r, IsIntV v (j r))
    (L : FGLaw C d) (L' : FGLaw C d') (hL : ∀ a, L.F a = MvPowerSeries.map j (B.G.F a))
    (hL' : ∀ a, L'.F a = MvPowerSeries.map j (B'.G.F a))
    (hI : ∀ a, MvIsInt v (MvPowerSeries.subst (twoVars C d) (L.F a)))
    (hI' : ∀ a, MvIsInt v (MvPowerSeries.subst (twoVars C d') (L'.F a))) (k : ℕ) :
    detDepth (logFGLOf v L' hI') (fun a e => j (u' a e)) k ≤ detDepth (logFGLOf v L hI) (fun a e => j (u a e)) k := by
  have hd : d = d' := by
    obtain ⟨x'', -, h2, -⟩ := GlobalTheory.T.pushChartAlt E H V t t' n d x
    exact GlobalTheory.T.universalJetCoordinates_dim_unique V t'.G d d' x'' x' (h2 hu) hu'
  subst hd
  obtain ⟨φ, φi, hJ, hdir⟩ := GlobalTheory.T.formal_biextensions_related_of_triple_map_over_id E H hs V t t' n hsurj d B B' (Fin d) (Fin d) tg tg' uv uv' x x' e e'
    hc hc' hu hu' hf hf'
  obtain ⟨ε, hε⟩ := hJ 0
  exact detDepth_le_of_transF v j hj _ _ B.G.const φ φi hε.inv hε.law L L' hL hL' hI hI' u u'
    (fun a => hdir _ _ _ (hw a) (hw' a)) k

theorem nuFacC_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    letI := H.starRing
    ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io)
      (C C' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ), nuFacC C' X f k ≤ nuFacC C X f k := by
  letI := H.starRing
  intro p _ T io y C C' X f k
  letI := io.toAlgebra
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_iso_integralModels_matching_lieBases E H Dw l Xo c T io y.1 C.I C'.I
  obtain ⟨B, b1, b2, b3, b4, b5, b6, -⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C
  obtain ⟨B', b1', b2', b3', b4', b5', b6', -⟩ := GlobalTheory.integralChart_formalBiext E H Dw l Xo c T io y C'
  refine detDepth_le_of_charts (fun _ => rfl) T.V C.I.G C'.I.G n (GlobalTheory.T.surjective_appTop_integralModel_square E H Dw l Xo c T io y.1 C'.I) _ _ B B'
    C.tgT C'.tgT (fun j => Pi.single j 1) (fun j => Pi.single j 1) C.xT C'.xT C.eT C'.eT ?_ ?_
    (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C) (GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C') ?_ ?_
    (fun a => C.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩) (fun a => C'.uvecT ⟨f.1, Fin.castLE (rk_le f) a⟩)
    (fun a => (C.I.ub f.1 (Fin.castLE (rk_le f) a)).left) (fun a => C.dirT ⟨f.1, Fin.castLE (rk_le f) a⟩) ?_
    (vX_vp X) (jX X) (isIntV_jX X) (lawX C X) (lawX C' X) ?_ ?_ (fgl C X).F_int (fgl C' X).F_int k
  · rw [b1, b2]; exact C.chartT
  · rw [b1', b2']; exact C'.chartT
  · rw [b1, b2, b3, b4, b5, b6]; exact C.frameT
  · rw [b1', b2', b3', b4', b5', b6']; exact C'.frameT
  · intro a
    rw [hn]
    exact C'.dirT ⟨f.1, Fin.castLE (rk_le f) a⟩
  · intro a; rw [b1]; exact lawX_F C X a
  · intro a; rw [b1']; exact lawX_F C' X a

theorem nuFacC_chart_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR)
    (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch Ch' : IntegralChartA3 Xo c T io y) (X : ValExt T p) (f : Lt1 Dw) (k : ℕ),
    nuFacC Ch X f k = nuFacC Ch' X f k :=
  fun _ _ _ _ _ _ _ Xo c p _ T io y Ch Ch' X f k =>
    le_antisymm (nuFacC_le Xo c p T io y Ch' Ch X f k) (nuFacC_le Xo c p T io y Ch Ch' X f k)

end GlobalTheory.FactorDepth
