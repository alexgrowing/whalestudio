import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormExistsBelowFrameBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
namespace UpperTheory.Dv.Thin
private theorem covers_and_of_covers_of_imp {Q₁ Q₂ Q₃ : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
    (i : Fin (Fm.D x ι).R.m) (_Y : Cov p i) (PP C : ℝ), Prop}
    (h₁ : Covers Q₁) (h₂ : Covers Q₂)
    (h : ∀ {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (p : Pt Fm x hx ι)
      (i : Fin (Fm.D x ι).R.m) (Y : Cov p i) (PP C C' : ℝ),
      Q₁ Fm x hx ι p i Y PP C → Q₂ Fm x hx ι p i Y PP C' → (i : ℕ) + 1 < (Fm.D x ι).R.m → GoodCov p i Y →
        Q₃ Fm x hx ι p i Y PP C) : Covers Q₃ := by
  unfold Covers Lifts at *
  refine (h₁.and h₂).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨C, hC, h1⟩, ⟨C', _, h2⟩⟩ := hh
  obtain ⟨a, h3⟩ := h1.and h2
  exact ⟨C, hC, a, fun x hx hle ι p hp i hi Y hY =>
    h Fm x hx ι p i Y _ C C' ((h3 x hx hle ι p hp).1 i hi Y hY) ((h3 x hx hle ι p hp).2 i hi Y hY) hi hY⟩
private theorem card_mul_succ_le_two_mul_ncol {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H) :
    Fintype.card (Psi H) * (Dw.p + Dw.q) * (Dw.p + Dw.q + 1) ≤ 2 * GlobalTheory.RefSum.nCol Dw := by
  refine le_trans ?_ (Nat.mul_le_mul_left 2 GlobalTheory.RefSum.sum_le_nCol)
  have h1 : ∀ m : ℕ, ∑ i : Fin m, 2 * (i.val + 1) = m * (m + 1) := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [Fin.sum_univ_castSucc]; simp only [Fin.val_castSucc, Fin.val_last, ih]; ring
  rw [Fintype.sum_sigma]
  simp only [h1]
  rw [GlobalTheory.RawThetaSup.sum_emb_eq H, Finset.mul_sum, mul_assoc, ← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_le_sum fun τ _ => ?_
  rw [Datum.mult, if_pos τ.2, Datum.mult, if_neg (conj_not_mem τ)]
  nlinarith [sq_nonneg ((Dw.p : ℤ) - Dw.q)]
private theorem one_le_dimension_function {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (hp : 1 ≤ Dw.p) (hne : 0 < Fintype.card (Psi H)) {a : (E →+* ℂ) × ℕ → ℕ} (h : LastPos Dw a) :
    1 ≤ Formalism.L2.Pj.DF Dw a := by
  obtain ⟨τ⟩ := Fintype.card_pos_iff.1 hne
  have hm : 0 < Dw.mult τ.1 := by rw [Datum.mult, if_pos τ.2]; exact hp
  refine (h τ.1 τ.2 hm).trans_le ?_
  unfold Formalism.L2.Pj.DF
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ : E →+* ℂ => ∑ i : Fin (Dw.mult τ), a (τ, i))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ.1))
  exact Finset.single_le_sum (f := fun i : Fin (Dw.mult τ.1) => a (τ.1, i)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨Dw.mult τ.1 - 1, by omega⟩)
private theorem frn_le_pow_of_bounds {f r n t : ℝ} (ht : 11 ≤ t) (hf0 : 0 ≤ f) (hr0 : 0 ≤ r) (hf : f ≤ t) (hr : r ≤ t)
    (hn : n ≤ 2 * r * (f * r) + 8 * (f * r) + 8) : f * r * n ≤ t ^ 150 := by
  have h1 : n ≤ 2 * t * (t * t) + 8 * (t * t) + 8 := hn.trans (by gcongr)
  have h2 : n ≤ t ^ 4 := by
    have : 11 * t ^ 3 ≤ t ^ 4 := by rw [pow_succ' t 3]; gcongr
    have : 11 * t ^ 2 ≤ t ^ 3 := by rw [pow_succ' t 2]; gcongr
    nlinarith
  calc f * r * n ≤ f * r * t ^ 4 := by gcongr
    _ ≤ t * t * t ^ 4 := by gcongr
    _ = t ^ 6 := by ring
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by norm_num)
set_option maxHeartbeats 1000000 in
private theorem cover_dimension_size_bounds : Size → Covers fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → (Dom (GlobalTheory.RefSum.aOf p i u1) (GlobalTheory.RefSum.nCol (dat p i)) ∧ LastPos (dat p i) (GlobalTheory.RefSum.aOf p i u1) ∧ Nonempty (ErrX (Fm.D x ι))) ∧ 1000 ≤ (Fm.L x ι).sc.b ∧ (Fm.D x ι).R.r ≤ GlobalTheory.RefSum.nCol (dat p i) ∧ (Fm.D x ι).R.f * (Fm.D x ι).R.r * ((Fm.D x ι).R.r + 1) ≤ 2 * GlobalTheory.RefSum.nCol (dat p i) ∧ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * GlobalTheory.RefSum.nCol (dat p i) ≤ (Fm.L x ι).sc.b ∧ (Fm.D x ι).host.rdE ^ 7 ≤ (Fm.L x ι).sc.b ∧ (Fm.L x ι).sc.b ^ 16 ≤ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ∧ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) ≤ (Fm.L x ι).sc.b ^ 70 ∧ 1 ≤ Formalism.L2.Pj.DF (dat p i) (GlobalTheory.RefSum.aOf p i u1) ∧ ((Formalism.L2.Pj.DF (dat p i) (GlobalTheory.RefSum.aOf p i u1) : ℕ) : ℝ) ≤ (Fm.L x ι).sc.b ^ 2 ∧ (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * (Fm.L x ι).sc.b ≤ (Y.d.l₂.M : ℝ) := by
  intro hS
  refine (Formalism.MainNotions.Closed.and (Formalism.MainNotions.Closed.and (GlobalTheory.CovTop.Sizes.hostN 6) GlobalTheory.CovTop.WtShape.wtN)
    (GlobalTheory.RefSum.QuoShape.quo_shape hS)).imp fun Fm CH _ hh => ?_
  obtain ⟨⟨⟨A, -, h1⟩, ⟨C2, -, h2⟩⟩, ⟨C3, -, h3⟩⟩ := hh
  obtain ⟨a, ha⟩ := h1.and (h2.and h3)
  refine ⟨0, le_rfl, a, fun x hx hle ι p hp i hi Y hY u1 hu => ?_⟩
  have hN : HostNum (Fm.D x ι) (Fm.L x ι) (Fm.parT x hx ι).PP A 6 := (ha x hx hle ι p hp).1 i
  have hW : WtNum p i (Fm.parT x hx ι).PP := (ha x hx hle ι p hp).2.1 i
  obtain ⟨q1, -, q3, q4, q5, q6, q7, q8, -⟩ := (ha x hx hle ι p hp).2.2 i hi u1 hu
  have S := Fm.sizes x hx ι
  obtain ⟨-, -, -, -, -, sC, sQD, -, -, -, -, -, -, -, -, -, -, -, -, -, sG, -⟩ := S
  obtain ⟨-, -, -, -, -, -, h1, h2⟩ := sQD
  have a1 := (Fm.D x ι).R.two_le_m
  have a2 := (Fm.D x ι).R.m_add_three_le_k
  have a3 : (Fm.D x ι).R.r + 5 ≤ (Fm.D x ι).R.t := (Fm.D x ι).R.rank_add_five_le
  have a4 : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.k := (Fm.D x ι).R.f_le_k
  have a5 : (Fm.D x ι).R.k ≤ (Fm.D x ι).R.r ∧ (Fm.D x ι).R.m ≤ (Fm.D x ι).R.r ∧ 6 ≤ (Fm.D x ι).R.r := by
    unfold Formalism.BasicNotions.Ranks.r; omega
  have hf8 := hN.f8
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hfR : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
  have hrR : (6 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast a5.2.2
  have ht : (11 : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : 11 ≤ (Fm.D x ι).R.t)
  have hft : ((Fm.D x ι).R.f : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.f ≤ (Fm.D x ι).R.t)
  have hrt : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.D x ι).R.t := by exact_mod_cast (by omega : (Fm.D x ι).R.r ≤ (Fm.D x ι).R.t)
  have hb : 1000 ≤ (Fm.L x ι).sc.b := by
    have e1 : Real.exp 10 ≤ (Fm.L x ι).sc.b := Real.exp_le_exp.2 hL10
    have e2 : (2 : ℝ) ^ 10 ≤ Real.exp 1 ^ 10 := by gcongr; linarith [Real.add_one_le_exp 1]
    rw [← Real.exp_nat_mul] at e2
    norm_num at e2
    linarith
  have hb1 : 1 ≤ (Fm.L x ι).sc.b := by linarith
  have hc : (Fm.D x ι).host.rdE ≤ szCond (Fm.L x ι) := by
    unfold szCond
    exact UpperTheory.Ram.Rd.rdE_le_cond _
  have hc1 : (1 : ℝ) ≤ szCond (Fm.L x ι) := h1.trans hc
  have hsb : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b :=
    Real.sqrt_le_iff.2 ⟨by linarith, le_self_pow₀ hb1 (by norm_num)⟩
  have hrdb : (Fm.D x ι).host.rdE ^ 7 ≤ (Fm.L x ι).sc.b := by
    have e1 : (Fm.D x ι).host.rdE ^ 7 ≤ szCond (Fm.L x ι) ^ 36 * ((Fm.D x ι).R.t : ℝ) ^ 150 :=
      (pow_le_pow_left₀ (by linarith) hc 7).trans ((pow_le_pow_right₀ hc1 (by norm_num)).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by linarith))))
    exact (e1.trans sC).trans hsb
  have htb : ((Fm.D x ι).R.t : ℝ) ^ 150 ≤ (Fm.L x ι).sc.b :=
    ((le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)).trans sC).trans hsb
  have hcard : Fintype.card (Psi p.T.Q.H) = (Fm.D x ι).R.f := Nat.card_eq_fintype_card.symm.trans hW.card
  have hcol := card_mul_succ_le_two_mul_ncol (dat p i)
  rw [hcard, q3] at hcol
  have h2r := GlobalTheory.RefSum.NumPt.two_mul_rank_le_nCol (dat p i)
  rw [q3] at h2r
  have hnle : (GlobalTheory.RefSum.nCol (dat p i) : ℝ) ≤ 2 * (Fm.D x ι).R.r * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) +
      8 * ((Fm.D x ι).R.f * (Fm.D x ι).R.r) + 8 := by exact_mod_cast GlobalTheory.LiftGaps.nCol_le p i _ _ _ hW hN
  have hfrn : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * GlobalTheory.RefSum.nCol (dat p i) ≤ (Fm.L x ι).sc.b :=
    (frn_le_pow_of_bounds ht (by positivity) (by positivity) hft hrt hnle).trans htb
  have hk : (1 : ℝ) ≤ (Fm.D x ι).R.k := by exact_mod_cast (by omega : 1 ≤ (Fm.D x ι).R.k)
  have hg : ∀ k, (Fm.L x ι).sc.b ^ 8 ≤ ((Fm.D x ι).host.g k : ℝ) := fun k =>
    (pow_le_pow_left₀ (by linarith) (le_mul_of_one_le_left (by linarith) hk) 8).trans (sG k k).1
  have hg' : ∀ k, ((Fm.D x ι).host.g k : ℝ) ≤ (Fm.L x ι).sc.b ^ 35 := fun k => by
    have h0 : (0 : ℝ) < (Fm.D x ι).host.g k := by exact_mod_cast ((Fm.D x ι).host.g_prime k).pos
    unfold Formalism.BasicNotions.Scale.b
    rw [← Real.exp_nat_mul, ← Real.log_le_iff_le_exp h0]
    push_cast
    linarith only [hN.logg k, hL10]
  have hev : Even (GlobalTheory.RefSum.nCol (dat p i)) := q7.2
  have hDF := (GlobalTheory.RefSum.thA_dominant_lastPos_degree _ _ (dat p i) u1 (GlobalTheory.RefSum.nCol (dat p i)) _ q1 hev q4 q5 q6).2.2.2.2
  rw [hN.deg, q3, Nat.mul_div_cancel_left _ two_pos] at hDF
  refine ⟨⟨q7, q8, ⟨(Fm.ex x hx ι).errX⟩⟩, hb, by omega, hcol, hfrn, hrdb, ?_, ?_,
    one_le_dimension_function _ q1 (by rw [hcard]; omega) q8, hDF.trans ?_, GlobalTheory.ThetaSizeBounds.level_ge p i Y hY (by linarith)⟩
  · push_cast
    rw [show 16 = 8 + 8 from rfl, pow_add]
    exact mul_le_mul (hg 0) (hg 1) (by positivity) (by positivity)
  · push_cast
    rw [show 70 = 35 + 35 from rfl, pow_add]
    exact mul_le_mul (hg' 0) (hg' 1) (by positivity) (by positivity)
  · have h5 : (5 : ℝ) ≤ GlobalTheory.RefSum.nCol (dat p i) := by exact_mod_cast (by omega : 5 ≤ GlobalTheory.RefSum.nCol (dat p i))
    have h6 : ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * 5 ≤ (Fm.L x ι).sc.b :=
      (mul_le_mul_of_nonneg_left h5 (by positivity)).trans hfrn
    calc ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (2 * (2 * (Fm.L x ι).sc.b) + 1)
        ≤ ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * (5 * (Fm.L x ι).sc.b) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ((Fm.D x ι).R.f : ℝ) * (Fm.D x ι).R.r * 5 * (Fm.L x ι).sc.b := by ring
      _ ≤ (Fm.L x ι).sc.b * (Fm.L x ι).sc.b := mul_le_mul_of_nonneg_right h6 (by linarith)
      _ = _ := by ring
set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.thin_divisor_pivot_bound : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ∃ f ∈ cuspW Y.d.Xo₂ Y.d.c₂ Y.U (GlobalTheory.RefSum.GOf p i u1), rdU (Y.U σ) f y.1 y.2.1 ≠ 0 ∧ ∀ z : FPt (Y.U σ).X, (⟨z.1, z.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 1250)) * ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨z.1, z.2.1⟩ ≤ ptN (modelWt (Y.U σ) (GlobalTheory.RefSum.GOf p i u1)) (rdU (Y.U σ) f) ⟨y.1, y.2.1⟩ := by
  intro _ _ _ hS _
  refine covers_and_of_covers_of_imp (cover_dimension_size_bounds hS) (GlobalTheory.ThetaSizeBounds.params_sqrt_bounds hS) ?_
  intro eps Fm x hx ι p i Y PP C C' hA hB hi hY u1 hu Z σ hσ y hy hM
  obtain ⟨⟨hD, hLP, ⟨EX⟩⟩, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10⟩ := hA u1 hu
  obtain ⟨r1, -, -, r4⟩ := hB
  obtain ⟨hrun, -⟩ := r4 _ s8 s9
  have hj : InR (Fm.D x ι) ((i : ℕ) + 1) := ⟨by omega, hi.le⟩
  have hl : p.T.Q.l.M = (Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 := p.fw.laws.toLawsM.pins.2.1.1
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split _ p.T.toCore p.fw.laws.toLawsM EX
  obtain ⟨φ, hφ, hg⟩ := cover_transport _ p.T _ Y _ _ p.fw.laws hj hY.1 _ _ hD σ hσ
  have hd := hφ ⟨y.1, y.2.1⟩ y.2.2
  have hσ' : GoodEmb p.T.Q.c (Y.resEmb σ) := Y.good_resEmb hσ
  have hla : ((p.T.U ((i : ℕ) + 1) (Y.resEmb σ)).X (φ ⟨y.1, y.2.1⟩).1).la1 (φ ⟨y.1, y.2.1⟩).2 =
      ((Y.U σ).X y.1).la1 y.2.1 := congrArg Real.sqrt hd.2
  have h0 : 0 ≤ ((Y.U σ).X y.1).firstMinimumSq y.2.1 := ReciprocityTheory.ChartRestriction.G.FD.MinimumGrowthBounds.minimumSq_nonneg _ y.2.2
  have hs1 : (((Fm.D x ι).host.g 0 * (Fm.D x ι).host.g 1 : ℕ) : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 ≤ 1 := by
    have h1 := (mul_le_mul_of_nonneg_right s10 h0).trans hM.le
    rw [mul_right_comm] at h1
    exact le_of_mul_le_mul_right (h1.trans_eq (one_mul _).symm) (by linarith only [s1])
  obtain ⟨f, hf, hf0, hfz⟩ := core_ratio (GlobalTheory.LevGeo.laws_core _ p.T _ p.fw.laws hj) α hα1 hα2 hD hLP s1 s2 s3 s4 s5
    (by rw [hl]; exact s6) (by rw [hl]; exact s7) s9 (by rw [hl]; exact hrun) r1 hσ' (φ ⟨y.1, y.2.1⟩).1
    (φ ⟨y.1, y.2.1⟩).2 hd.1 (by rw [hl, hd.2]; exact hs1)
  obtain ⟨g, hg', hgy⟩ := hg f hf
  refine ⟨g, hg', (hgy ⟨y.1, y.2.1⟩ y.2.2).2.mpr hf0, fun z hz => ?_⟩
  rw [(hgy ⟨z.1, z.2.1⟩ z.2.2).1, (hgy ⟨y.1, y.2.1⟩ y.2.2).1, ← hla]
  exact hfz ⟨(φ ⟨z.1, z.2.1⟩).1, (φ ⟨z.1, z.2.1⟩).2, (hφ ⟨z.1, z.2.1⟩ z.2.2).1⟩
end UpperTheory.Dv.Thin
end
