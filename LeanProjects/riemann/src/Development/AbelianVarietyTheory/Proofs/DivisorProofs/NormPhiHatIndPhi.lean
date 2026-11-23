import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThFamMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormRawThetaSeriesIndexBoundLeSqrt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstMinAtHalfMax
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGalois
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWeightSpreadLeExponentNormAdd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogExpMulLeOfGeneratorSupBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTotallyComplexExt

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

namespace GlobalTheory.RawThetaSup

section Sizes

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem sum_emb_eq (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) {M : Type} [AddCommMonoid M] (g : (E →+* ℂ) → M) :
    ∑ τ, g τ = ∑ τ : Psi H, (g τ.1 + g (conjEmb τ.1)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
    Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_subtype _ (by simp) _
  rw [Finset.sum_subtype (p := fun τ : E →+* ℂ => ¬ τ (H.rt : E) = H.rt0) (F := inferInstance) _ (by simp)]
  refine Fintype.sum_equiv
    ⟨fun τ => ⟨conjEmb τ.1, AllWt.conj_mem τ.2⟩, fun τ => ⟨conjEmb τ.1, AllWt.conj_not_mem τ⟩,
      fun τ => Subtype.ext (AllWt.conjEmb_conjEmb _), fun τ => Subtype.ext (AllWt.conjEmb_conjEmb _)⟩ _ _ fun τ => ?_
  simp [AllWt.conjEmb_conjEmb]

theorem two_mul_card_psi (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : 2 * Fintype.card (Psi H) = Module.finrank ℚ E := by
  have := sum_emb_eq H (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, NumberField.Embeddings.card] at this
  omega

theorem sum_mult : ∑ τ, Dw.mult τ = Fintype.card (Psi H) * (Dw.p + Dw.q) := by
  rw [sum_emb_eq H, ← Finset.card_univ, ← smul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Datum.mult, if_pos τ.2, Datum.mult, if_neg (AllWt.conj_not_mem τ)]

theorem sizeK_eq (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    sizeK Dw a n = (Formalism.L2.Pj.DF Dw a : ℕ) + ((n / 2 : ℕ) : ℝ) * (Fintype.card (Psi H) * (Dw.p + Dw.q) : ℕ) := by
  have h1 : ((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) + ((n / 2 : ℕ) : ℝ) * (Fintype.card (Psi H) * (Dw.p + Dw.q) : ℕ) =
      ∑ τ : E →+* ℂ, ∑ i ∈ Finset.range (Dw.mult τ), ((a (τ, i) : ℝ) + ((n / 2 : ℕ) : ℝ)) := by
    rw [← sum_mult]
    simp only [Formalism.L2.Pj.DF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_sum,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun τ _ => Fin.sum_univ_eq_sum_range (fun i => (a (τ, i) : ℝ)) _
    · exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
  rw [h1, sum_emb_eq H, sizeK]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Datum.mult, if_pos τ.2, Datum.mult, if_neg (AllWt.conj_not_mem τ), Fin.sum_univ_add,
    ← Finset.sum_range_reflect _ Dw.q, ← Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ) + ((n / 2 : ℕ) : ℝ)),
    ← Fin.sum_univ_eq_sum_range (fun i => (a (conjEmb τ.1, Dw.q - 1 - i) : ℝ) + ((n / 2 : ℕ) : ℝ))]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [laOf, AllWt.weightOf, Fin.val_castAdd, i.2, if_true]
    rw [Int.cast_add, Int.cast_natCast, Int.cast_natCast, abs_of_nonneg (by positivity)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [laOf, AllWt.weightOf, Fin.val_natAdd, Nat.not_lt.2 (Nat.le_add_right _ _), if_false,
      Nat.add_sub_cancel_left]
    rw [Int.cast_sub, Int.cast_neg, Int.cast_natCast, Int.cast_natCast, ← neg_add', abs_neg,
      abs_of_nonneg (by positivity)]

theorem card_letters (n : ℕ) : Fintype.card (LtN Dw n) = Fintype.card (Psi H) * (Dw.p + Dw.q) * n := by
  rw [← sum_mult, Finset.sum_mul]
  simp [LtN, Formalism.L2.Pj.Letter]

end Sizes

theorem card_support_le {ι R : Type} [Fintype ι] [CommSemiring R] {P : MvPolynomial ι R} {d : ℕ}
    (h : P.IsHomogeneous d) : P.support.card ≤ (d + 1) ^ Fintype.card ι := by
  classical
  have : (Fintype.piFinset fun _ : ι => Finset.range (d + 1)).card = (d + 1) ^ Fintype.card ι := by simp
  rw [← this]
  refine Finset.card_le_card_of_injOn (fun m => (m : ι → ℕ)) (fun m hm => ?_) fun _ _ _ _ e => DFunLike.coe_injective e
  simp only [Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
  intro i
  have h1 := h (MvPolynomial.mem_support_iff.1 hm)
  have h2 := Finsupp.le_degree i m
  rw [Finsupp.degree_eq_weight_one] at h2
  exact Nat.lt_succ_of_le (h1 ▸ h2)

theorem sum_coeff_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : Coeff l) {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F)
    (σ : c.F →+* ℂ) :
    ∑ m ∈ P.support, ‖σ (P.coeff m)‖ ≤ Real.sqrt P.support.card * GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm c P := by
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm, ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine Real.le_sqrt_of_sq_le (sq_sum_le_card_mul_sum_sq.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)))
  exact Finset.single_le_sum (f := fun s : c.F →+* ℂ => ∑ m ∈ P.support, ‖s (P.coeff m)‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ σ)

theorem inv_pow_le_epStar {e M s f w : ℝ} (he : 2 ≤ e) (hM0 : 0 < M) (hM : M ≤ e ^ 30) (hs0 : 0 < s) (hs : s ≤ e ^ 3)
    (hf0 : 0 ≤ f) (hf : f ≤ e) (hw0 : 0 ≤ w) (hw : w ≤ 3 * e ^ 20) :
    (e ^ 57)⁻¹ ≤ ReciprocityTheory.ChartRestriction.G.FD.epStar (2 * M * s) f w 1 := by
  have he1 : 1 ≤ e := by linarith
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  refine le_min (inv_le_one_of_one_le₀ (one_le_pow₀ he1)) ?_
  have h1 : f * w + 2 ≤ e ^ 24 := by
    have a1 : f * w ≤ e * (3 * e ^ 20) := by gcongr
    have a2 : 1 ≤ e ^ 21 := one_le_pow₀ he1
    have a3 : 2 ^ 3 ≤ e ^ 3 := by gcongr
    have a4 : e ^ 21 * 2 ^ 3 ≤ e ^ 21 * e ^ 3 := by gcongr
    nlinarith
  rw [le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
  calc 2 * M * s * (f * w + 2) * 1 * Real.log 2 ≤ 2 * e ^ 30 * e ^ 3 * e ^ 24 * 1 * 1 := by gcongr
    _ = e ^ 57 * 2 := by ring
    _ ≤ e ^ 57 * Real.pi := by gcongr; linarith [Real.pi_gt_three]

theorem numbers (f r n d N : ℕ) (L κ rd t J p ρ S v : ℝ) (hL : 1 ≤ L) (hf : 1 ≤ f) (hr : 1 ≤ r) (hrn : r ≤ n)
    (hd : (d : ℝ) ≤ κ) (hn : (f : ℝ) * r * n ≤ 2 * κ) (hκ : Real.log κ ≤ 20 * L) (hfr : Real.log (f * r) ≤ L)
    (hrd1 : 1 ≤ rd) (hrd : Real.log rd ≤ 3 * L) (ht : 0 < t) (hJ : 0 ≤ J) (hp0 : 0 ≤ p) (hρ : 0 ≤ ρ)
    (hN : N ≤ (d + 1) ^ (f * r * n)) (hp : p ≤ Real.sqrt N * ρ) (hS0 : 0 < S) (hS : S ≤ 2 * v)
    (hv : v ≤ J * (p * (Real.pi * Real.exp 1 * t * d) ^ ((d : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (f * r : ℕ) * n) * (2 * (f : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rd) / (Real.sqrt Real.pi * (Real.exp L ^ 40)⁻¹)) ^ (f * r * n))) :
    Real.exp (-((d : ℝ) / 2) * Real.log (Real.pi * t)) * S ≤ J * ρ * Real.exp (9000 * ((f : ℝ) * r * L) ^ 2 * κ) := by
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hr.trans hrn
  have hfr1 : (1 : ℝ) ≤ f * r := one_le_mul_of_one_le_of_one_le hf1 hr1
  have hn2 : (n : ℝ) ≤ 2 * κ := (le_mul_of_one_le_left (by linarith) hfr1).trans hn
  have hκ0 : 0 < κ := by linarith
  have hl2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hl3 : Real.log 3 ≤ 2 := by have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  have h1κ : Real.log (1 + κ) ≤ 22 * L := by
    have := Real.log_le_log (by linarith) (show 1 + κ ≤ 3 * κ by linarith)
    rw [Real.log_mul (by norm_num) hκ0.ne'] at this
    linarith
  have hln : Real.log n ≤ 21 * L := by
    have := Real.log_le_log (by linarith) hn2
    rw [Real.log_mul (by norm_num) hκ0.ne'] at this
    linarith
  have hlf : Real.log f ≤ 2 * (21 * L) := by
    have := Real.log_le_log (by linarith) (le_mul_of_one_le_right (by linarith) hr1 : (f : ℝ) ≤ f * r)
    linarith
  have hK : 0 < J * p := by
    rcases (mul_nonneg hJ hp0).eq_or_lt with h | h
    · rw [mul_assoc p, mul_assoc p, ← mul_assoc J, ← h, zero_mul] at hv
      linarith
    · exact h
  have hlam : Real.log (1 / ((Real.exp L ^ 40)⁻¹) ^ 2) ≤ 80 * (21 * L) := by
    rw [inv_pow, one_div, inv_inv, ← pow_mul, Real.log_pow, Real.log_exp]
    push_cast
    linarith
  have key := GlobalTheory.log_exp_mul_le_of_generator_sup_bound f r n d (21 * L) 0 κ rd (Real.exp L ^ 40)⁻¹ t 1 (S / (J * p))
    (v / (J * p)) 1 (by linarith) hf hr hrn hd (by linarith) hln hlf hrd1 (by linarith) (by positivity) hlam ht le_rfl
    zero_le_one (by rw [Real.exp_zero]) zero_le_one (Real.one_le_exp (by positivity)) (by positivity)
    (by rw [← mul_div_assoc]; gcongr) (by
      rw [div_le_iff₀ hK]
      refine hv.trans_eq ?_
      ring)
  rw [Real.log_le_iff_le_exp (by positivity), ← mul_div_assoc, div_le_iff₀ hK] at key
  have hsq : Real.sqrt N ≤ Real.exp (22 * L * κ) := by
    refine Real.sqrt_le_iff.2 ⟨(Real.exp_pos _).le, ?_⟩
    have a1 : (d : ℝ) + 1 ≤ Real.exp (22 * L) := by
      have := (Real.log_le_iff_le_exp (by linarith)).1 h1κ
      linarith
    calc (N : ℝ) ≤ ((d : ℝ) + 1) ^ (f * r * n) := by exact_mod_cast hN
      _ ≤ Real.exp (22 * L) ^ (f * r * n) := by gcongr
      _ = Real.exp (((f : ℝ) * r * n) * (22 * L)) := by rw [← Real.exp_nat_mul]; push_cast; rfl
      _ ≤ Real.exp (2 * κ * (22 * L)) := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hLsq : L ≤ ((f : ℝ) * r * L) ^ 2 := by
    have a1 : L ≤ f * r * L := le_mul_of_one_le_left (by linarith) hfr1
    nlinarith
  calc _ ≤ _ := key
    _ ≤ Real.exp (0 + 10 * (21 * L) * κ + 200 * f * r * n * (21 * L)) * (J * (Real.exp (22 * L * κ) * ρ)) := by
        gcongr
        exact hp.trans (by gcongr)
    _ = J * ρ * Real.exp (10 * (21 * L) * κ + 200 * (f * r * n) * (21 * L) + 22 * L * κ) := by
        rw [Real.exp_add _ (22 * L * κ)]
        have : 0 + 10 * (21 * L) * κ + 200 * f * r * n * (21 * L) = 10 * (21 * L) * κ + 200 * (f * r * n) * (21 * L) := by
          ring
        rw [this]; ring
    _ ≤ _ := by
        gcongr J * ρ * Real.exp ?_
        have a1 : 200 * ((f : ℝ) * r * n) * (21 * L) ≤ 200 * (2 * κ) * (21 * L) := by gcongr
        have a2 : L * κ ≤ ((f : ℝ) * r * L) ^ 2 * κ := by gcongr
        have a3 : 0 ≤ L * κ := by positivity
        nlinarith

theorem norm_phiHat_indPhi {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (c : Coeff l) (hA : l.A = 1) {n : ℕ} (x0 : Fin n → LevQc Dw l)
    (σ : c.F →+* ℂ) (q : Fin n → LevQ Dw l) : ‖σ (phiHat c (indPhi c x0) q)‖ = 1 := by
  have hM : l.M' ≠ 0 := by
    have := l.three_le
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.M', hA, Nat.lcm_one_right]
    omega
  have hz : (⟨zeta l.M', c.zeta_mem⟩ : c.F) ^ l.M' = 1 :=
    Subtype.ext (by simpa [zeta] using (Complex.isPrimitiveRoot_exp l.M' hM).pow_eq_one)
  have h1 : ‖σ ⟨zeta l.M', c.zeta_mem⟩‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (by rw [← map_pow, hz, map_one]) hM
  unfold phiHat indPhi
  rw [finsum_eq_single _ x0 (fun x hx => by simp [hx])]
  rw [if_pos rfl, one_mul, map_zpow₀, norm_zpow, zetaM, map_pow, norm_pow, h1, one_pow, one_zpow]

set_option maxHeartbeats 1000000 in

theorem homN_raw_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (ρ : ℝ) (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), La.Unimod → La.TrivAt Y.d.l₂.M → La.LevOK N Y.d.l₂.M → P ∈ harmL Y.d.c₂ La a → GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm Y.d.c₂ P ≤ ρ → ∀ y : Y.V (wtZ a n), (∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R), thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')) → ∀ (σ : Y.d.c₂.F →+* ℂ) (z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X k).Ψ D.R.r), z.2 ∈ ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X z.1).dom → AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) (wtZ a n) (y : Rul Y.d.Xo₂ Y.d.c₂) z ≤ Real.sqrt (((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^ ((T.Q.Dw j).p + (T.Q.Dw j).q)) * ρ * Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  refine ⟨9000, by norm_num, ?_⟩
  intro D T j Y e o Lb a n hH _ nab hnab ρ x0 La N P hU hT hO hP hρ y hy σ z hz
  obtain ⟨hJ, -, -, -, hj, hG, hL, hM, hE, hfr, -, hDom, hev, hn, -, hsz⟩ := hH
  obtain ⟨hLw, -, -⟩ := GlobalTheory.DeepLaws.laws_galois_pull D T j Y e o hJ hj hG hG.unit hG.modelW
  have hσ : GoodEmb Y.d.c₂ (goodOf Y.d.c₂ σ) := goodEmb_goodOf _ σ
  generalize goodOf Y.d.c₂ σ = σ' at hσ z hz ⊢
  have hρ0 : 0 ≤ ρ := (Real.sqrt_nonneg _).trans hρ
  have hfin := GlobalTheory.SupDict.finrank_host D
  have hfd : ReciprocityTheory.ChartRestriction.G.FD.fdeg D.host.E = D.R.f := by unfold ReciprocityTheory.ChartRestriction.G.FD.fdeg; omega
  have hf1 : 1 ≤ D.R.f := by have := Module.finrank_pos (R := ℚ) (M := D.host.E); omega
  have hr1 : 1 ≤ D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hrn : D.R.r ≤ n := by nlinarith
  have hpq : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (hLw.unf σ' hσ).1
  have hcard : Fintype.card (Psi T.Q.H) = D.R.f := by have := two_mul_card_psi T.Q.H; omega
  have hsize := sizeK_eq (T.Q.Dw j) a n
  rw [hcard, ← hpq] at hsize
  have hn2 : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by exact_mod_cast (Nat.two_mul_div_two_of_even hev).symm
  have hd0 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF (T.Q.Dw j) a : ℕ) := Nat.cast_nonneg _
  have hh0 : (0 : ℝ) ≤ ((n / 2 : ℕ) : ℝ) * (D.R.f * D.R.r : ℕ) := by positivity
  have hdκ : ((Formalism.L2.Pj.DF (T.Q.Dw j) a : ℕ) : ℝ) ≤ sizeK (T.Q.Dw j) a n := by linarith
  have hnκ : (D.R.f : ℝ) * D.R.r * n ≤ 2 * sizeK (T.Q.Dw j) a n := by
    rw [hsize]; push_cast at hh0 ⊢; rw [hn2]; push_cast; nlinarith
  have hfrn : (0 : ℝ) < (D.R.f : ℝ) * D.R.r * n := by
    have : 0 < D.R.f * D.R.r * n := Nat.mul_pos (Nat.mul_pos hf1 hr1) (hr1.trans hrn)
    exact_mod_cast this
  have hd1 := GlobalTheory.SupDict.one_le_dE D.host.E
  have hrd1 : 1 ≤ ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E := Real.one_le_rpow hd1 (by positivity)
  have hrdL : Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) ≤ 3 * Lb := by
    refine le_trans (le_of_eq ?_) ((log_rd_le_fieldSz D.host.E).trans hE)
    unfold ReciprocityTheory.ChartRestriction.G.FD.rdE
    rw [Real.log_rpow (by linarith)]
    unfold ReciprocityTheory.ChartRestriction.G.FD.dE
    ring
  have hcusp := AllWt.mem_cuspW.1 y.2
  have hsec : (y : Rul Y.d.Xo₂ Y.d.c₂) ∈ sec Y.d.Xo₂ Y.d.c₂ a n := by
    have := hcusp.1
    rwa [AllWt.exZ_wtZ, AllWt.secZ_nat] at this
  have hhol := hcusp.2 σ' hσ
  unfold AllWt.homN
  rw [AllWt.modelWt_wtZ] at hhol ⊢
  have hle : AllWt.ptN (laU (Y.U σ') a n) (rdU (Y.U σ') y.1) z ≤ supN (Y.U σ').X (laU (Y.U σ') a n) (rdU (Y.U σ') y.1) :=
    (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hhol)).1
      (le_iSup (fun q : Formalism.L2.Pj.FPt (Y.U σ').X => ENNReal.ofReal (((Y.U σ').X q.1).pnorm (laU (Y.U σ') a n q.1)
        (rdU (Y.U σ') y.1 q.1) q.2)) ⟨z.1, z.2, hz⟩)
  refine (mul_le_mul_of_nonneg_left hle (AllWt.lieFacZ_pos _ _).le).trans ?_
  rcases (supN_nonneg (Y.U σ').X (laU (Y.U σ') a n) (rdU (Y.U σ') y.1)).eq_or_lt with h0 | hpos
  · rw [← h0, mul_zero]; positivity
  have hx := GlobalTheory.SupDict.xiR_pos D
  have habs : LevGeo.absA (T.Q.Dw j) a = Formalism.L2.Pj.DF (T.Q.Dw j) a := rfl
  obtain ⟨k, xf, hort, hhalf, hla⟩ := half_sup_at_ortho hLw hσ (laU (Y.U σ') a n)
    (w := 3 * sizeK (T.Q.Dw j) a n) (by linarith)
    (fun k => (GlobalTheory.LamSpread.sum_spread_laU_le D j _ _ _ _ _ _ _ hLw σ' hσ a n k).trans (by
      rw [habs, hfd]; push_cast; linarith))
    (hLw.chiTriv σ' hσ a n hDom) hhol hpos
  have he2 : 2 ≤ Real.exp Lb := by have := Real.add_one_le_exp Lb; linarith
  have hpow : ∀ (x : ℝ) (m : ℕ), 0 < x → Real.log x ≤ m * Lb → x ≤ Real.exp Lb ^ m := fun x m h1 h2 => by
    rw [← Real.exp_nat_mul]; exact (Real.log_le_iff_le_exp h1).1 h2
  have hM0 : (0 : ℝ) < Y.d.l₂.M := by have := Y.d.l₂.three_le; exact_mod_cast (by omega : 0 < Y.d.l₂.M)
  have hdd : (0 : ℝ) < D.host.d := by have := D.host.qd_big.2; exact_mod_cast (by omega : 0 < D.host.d)
  have hrde := hpow (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) 3 (by linarith) (by exact_mod_cast hrdL)
  have hep : (Real.exp Lb ^ 57)⁻¹ ≤ LevGeo.epsLev D.host.E D.host.d Y.d.l₂.M (3 * sizeK (T.Q.Dw j) a n) := by
    refine inv_pow_le_epStar he2 hM0 (hpow _ 30 hM0 (by exact_mod_cast hM)) (Real.sqrt_pos.2 hdd)
      (hpow _ 3 (Real.sqrt_pos.2 hdd) ?_) (Nat.cast_nonneg _) ?_ (by linarith) ?_
    · have h1 : Real.log D.host.d ≤ 2 * Real.log (ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E) := GlobalTheory.NormSum.Compare.log_d_le D
      rw [Real.log_sqrt hdd.le]
      push_cast
      linarith
    · rw [hfd]
      have h1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1
      have h2 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast hr1
      have := hpow (D.R.f * D.R.r) 1 (by positivity) (by simpa using hfr)
      rw [pow_one] at this
      nlinarith
    · have := hpow (sizeK (T.Q.Dw j) a n) 20 (by linarith) (by exact_mod_cast hsz)
      linarith
  have hlam : ((Real.exp Lb ^ 40)⁻¹) ^ 2 ≤ ((Y.U σ').X k).firstMinimumSq xf.1 := by
    refine le_trans ?_ hla
    rw [le_div_iff₀ (by positivity)]
    have h1 : 1 ≤ Real.exp Lb ^ 17 := one_le_pow₀ (by linarith)
    calc ((Real.exp Lb ^ 40)⁻¹) ^ 2 * ReciprocityTheory.ChartRestriction.G.FD.rdE D.host.E ^ 2
        ≤ ((Real.exp Lb ^ 40)⁻¹) ^ 2 * ((Real.exp Lb ^ 3) ^ 2 * Real.exp Lb ^ 17) :=
          mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (by linarith) hrde 2).trans
            (le_mul_of_one_le_right (by positivity) h1)) (by positivity)
      _ = (Real.exp Lb ^ 57)⁻¹ := by field_simp
      _ ≤ _ := by
          have : 0 < (Real.exp Lb ^ 57)⁻¹ := by positivity
          linarith
  have hv := norm_evR_le D.host.E _ (T.Q.Dw j) Y.d.l₂ Y.d.Xo₂ Y.d.c₂ σ' D.R.r (Formalism.L2.PjFree.Unf.ofPj (Y.U σ')) hσ
    (hLw.unf σ' hσ) hr1 (2 * xiR D) (by linarith)
    (fun k τ => congrArg (2 * ·) (hLw.xiAbs σ' hσ k τ.1)) a n hDom nab hnab La N _
    (fun q => (norm_phiHat_indPhi Y.d.c₂ hLw.levA x0 σ' q).le) P y.1 hU hT hO hP hsec hy k xf hort _ (by positivity) hlam
  rw [hfd] at hv
  have hrdv : rdU (Y.U σ') y.1 k xf.1 = Formalism.L2.PjFree.toC (evR Y.d.Xo₂ Y.d.c₂ y.1 ((Y.U σ').un k xf)) := dif_pos xf.2
  rw [hrdv] at hhalf
  have hlie : AllWt.lieFacZ (T.Q.Dw j) (xiR D) (wtZ a n) =
      Real.exp (-(((Formalism.L2.Pj.DF (T.Q.Dw j) a : ℕ) : ℝ) / 2) * Real.log (Real.pi * (2 * xiR D))) := by
    rw [AllWt.lieFacZ_wtZ, lieFac, show 2 * Real.pi * xiR D = Real.pi * (2 * xiR D) by ring]
    simp [Formalism.L2.Pj.DF]
  have hsupp := card_support_le ((GlobalTheory.T.exists_integralHarmonic_ne_zero_and_isHomogeneous _ _ (T.Q.Dw j) Y.d.l₂ Y.d.c₂ a n).2 P hP.1)
  rw [card_letters, hcard, ← hpq] at hsupp
  rw [hlie, ← hpq]
  exact numbers D.R.f D.R.r n _ _ Lb _ _ _ _ _ ρ _ _ hL hf1 hr1 hrn hdκ hnκ hsz hfr hrd1 hrdL (by linarith)
    (Real.sqrt_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _) hρ0 hsupp
    ((sum_coeff_le Y.d.c₂ P σ').trans (mul_le_mul_of_nonneg_left hρ (Real.sqrt_nonneg _))) hpos hhalf hv

theorem homN_smul {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}
    (U : Unf Xo c σ r) (x : ℝ) (G : WTZ E) (s : c.F) (f : Rul Xo c) (z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r) :
    AllWt.homN U x G (s • f) z = ‖σ s‖ * AllWt.homN U x G f z := by
  unfold AllWt.homN AllWt.ptN
  rw [map_smulₛₗ, mul_left_comm]
  exact congrArg _ (pnorm_smul _ _ _ _ _)

theorem homN_smul_raw_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), GlobalTheory.CovGmin.Hyp D T j Y e o Lb a n → ∀ [StarRing (𝓞 D.host.E)] (nab : NabV Y.d.Xo₂ Y.d.c₂), IsNab Y.d.Xo₂ Y.d.c₂ nab → ∀ (ρ : ℝ) (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ) (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F), La.Unimod → La.TrivAt Y.d.l₂.M → La.LevOK N Y.d.l₂.M → P ∈ harmL Y.d.c₂ La a → GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm Y.d.c₂ P ≤ ρ → ∀ y : Y.V (wtZ a n), (∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R), thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')) → ∀ (s : Y.d.c₂.F) (B : ℝ), 0 ≤ B → (∀ σ : Y.d.c₂.F →+* ℂ, ‖σ s‖ ^ 2 * ((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^ ((T.Q.Dw j).p + (T.Q.Dw j).q) ≤ B ^ 2) → ∀ (σ : Y.d.c₂.F →+* ℂ) (z : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X k).Ψ D.R.r), z.2 ∈ ((Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)).X z.1).dom → AllWt.homN (Y.U (Formalism.L2.Pj.goodOf Y.d.c₂ σ)) (xiR D) (wtZ a n) (s • (y : Rul Y.d.Xo₂ Y.d.c₂)) z ≤ B * ρ * Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 2 * sizeK (T.Q.Dw j) a n) := by
  obtain ⟨C, hC, h⟩ := homN_raw_le
  refine ⟨C, hC, ?_⟩
  intro D T j Y e o Lb a n hH _ nab hnab ρ x0 La N P hU hT hO hP hρ y hy s B hB hs σ z hz
  have hρ0 : 0 ≤ ρ := (Real.sqrt_nonneg _).trans hρ
  have h1 := h D T j Y e o Lb a n hH nab hnab ρ x0 La N P hU hT hO hP hρ y hy σ z hz
  have h2 : ‖goodOf Y.d.c₂ σ s‖ * Real.sqrt (((La.Ln.toAddSubgroup.addSubgroupOf La.La.toAddSubgroup).index : ℝ) ^
      ((T.Q.Dw j).p + (T.Q.Dw j).q)) ≤ B := by
    refine (pow_le_pow_iff_left₀ (by positivity) hB two_ne_zero).1 ?_
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact hs _
  rw [homN_smul]
  refine (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)).trans ?_
  rw [← mul_assoc, ← mul_assoc]
  gcongr

end GlobalTheory.RawThetaSup
