import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.CurveAsm
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.AxHInst
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NumericalConsequencesOfPins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompat
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.EqZeroOfHermOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

namespace GlobalTheory.RunWts

open ReciprocityTheory.ChartRestriction.G.AR.Inst in

theorem nd_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r)
    {f p q : ℕ} (hf : Module.finrank ℚ E = 2 * f) (hr : p + q = r) :
    nd X = f * (p * q + p * (p - 1) / 2 + q * (q - 1) / 2) := by
  classical
  have h1 := GlobalTheory.TwoLines.two_mul_card_cmType X
  have h2 : X.Ψ.card = f := by omega
  have h3 : Fintype.card {x : Fin r × Fin r // x.2 < x.1} = r.choose 2 := by
    rw [Nat.choose_two_right, ← GlobalTheory.FlagDim.card_pairs_lt, Nat.card_eq_fintype_card]
    exact Fintype.card_congr ((Equiv.prodComm _ _).subtypeEquiv fun _ => Iff.rfl)
  unfold nd
  rw [Fintype.card_prod, Fintype.card_coe, h2, h3, ← hr, ← Nat.choose_two_right, ← Nat.choose_two_right,
    Nat.add_choose_eq]
  simp [Finset.Nat.antidiagonal_succ]
  left
  ring

theorem extendByZero_strictAnti_of_positive_gaps {p : ℕ} (l : Fin p → ℕ) (hl : Antitone l) (hg : ∀ i : Fin p, i.1 + 1 < p → 0 < gapZ l i)
    {a b : ℕ} (hab : a < b) (hb : b < p) : ext0 l b < ext0 l a := by
  have h1 := hg ⟨a, by omega⟩ (by show a + 1 < p; omega)
  have h2 : a + 1 < p := by omega
  unfold gapZ at h1
  rw [dif_pos h2] at h1
  have h3 : l ⟨b, hb⟩ ≤ l ⟨a + 1, h2⟩ := hl (show a + 1 ≤ b by omega)
  unfold ext0
  rw [dif_pos hb, dif_pos (by omega : a < p)]
  simp only at h1
  omega

theorem fdiv_pos {c : ℤ} {t s : ℕ} (ht : 0 < t) (h : ((t * (t + s) : ℕ) : ℤ) ≤ c) : 0 < Int.fdiv c t := by
  have ht' : (0 : ℤ) < t := by exact_mod_cast ht
  rw [Int.fdiv_eq_ediv_of_nonneg _ ht'.le]
  have : (1 : ℤ) ≤ c / t := by
    refine Int.le_ediv_of_mul_le ht' ?_
    push_cast at h
    nlinarith [Int.natCast_nonneg s]
  omega

theorem wtA_lt_upper {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) {a b : ℕ} (hab : a < b)
    (h : ext0 (w.aP t) b < ext0 (w.aP t) a) : wtA w (DV.tauEmb D t, b) < wtA w (DV.tauEmb D t, a) := by
  classical
  simp only [wtA]
  refine Finset.sum_lt_sum (fun s _ => add_le_add ?_ ?_) ⟨t, Finset.mem_univ _, add_lt_add_of_lt_of_le ?_ ?_⟩
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone s) hab.le
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti s) hab.le
    · exact le_rfl
  · simpa using h
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti t) hab.le
    · exact le_rfl

theorem wtA_lt_lower {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) {a b : ℕ} (hab : a < b)
    (h : ext0 (w.aM t) b < ext0 (w.aM t) a) :
    wtA w (conjEmb (DV.tauEmb D t), b) < wtA w (conjEmb (DV.tauEmb D t), a) := by
  classical
  simp only [wtA]
  refine Finset.sum_lt_sum (fun s _ => add_le_add ?_ ?_) ⟨t, Finset.mem_univ _, add_lt_add_of_le_of_lt ?_ ?_⟩
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone s) hab.le
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aM_anti s) hab.le
    · exact le_rfl
  · split_ifs
    · exact partitionExtendByZero_antitone (w.aPlus_antitone t) hab.le
    · exact le_rfl
  · simpa using h

theorem strictDom_smul_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (a z : (E →+* ℂ) × ℕ → ℕ) (hz : ∀ x, z x = 0) (n m s : ℕ) (k : U.Comp) (hs : 0 < s) (hm : m / 2 < s * (n / 2))
    (hu : ∀ τ : (U.X k).Ψ, ∀ x y, x < y → (U.X k).p0 + y < r →
      a (Function.invFun (relab c σ) τ.1, y) < a (Function.invFun (relab c σ) τ.1, x))
    (hl : ∀ τ : (U.X k).Ψ, ∀ x y, x < y → y < (U.X k).p0 →
      a (Function.invFun (relab c σ) (conjEmb τ.1), y) < a (Function.invFun (relab c σ) (conjEmb τ.1), x)) :
    ReciprocityTheory.ChartRestriction.G.AR.Inst.IsStrictDom (U.X k) (s • laU U a n k - laU U z m k) := by
  have hs' : (0 : ℤ) < s := by exact_mod_cast hs
  have hm' : ((m / 2 : ℕ) : ℤ) < s * ((n / 2 : ℕ) : ℤ) := by exact_mod_cast hm
  intro τ
  refine ⟨fun i j hij hj => ?_, fun i j hi hij => ?_, fun i j hi hj => ?_⟩
  · have hij' : (i : ℕ) < j := hij
    have h1 : ¬ (U.X k).p0 ≤ (j : ℕ) := by omega
    have h2 : ¬ (U.X k).p0 ≤ (i : ℕ) := by omega
    have h3 := hl τ ((U.X k).p0 - 1 - j) ((U.X k).p0 - 1 - i) (by omega) (by omega)
    have h4 := mul_lt_mul_of_pos_left (Int.ofNat_lt.2 h3) hs'
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [laU, h1, h2, if_false, hz, nsmul_eq_mul]
    linarith
  · have hij' : (i : ℕ) < j := hij
    have h1 : (U.X k).p0 ≤ (j : ℕ) := by omega
    have h3 := hu τ (i - (U.X k).p0) (j - (U.X k).p0) (by omega) (by omega)
    have h4 := mul_lt_mul_of_pos_left (Int.ofNat_lt.2 h3) hs'
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [laU, h1, hi, if_true, hz, nsmul_eq_mul]
    linarith
  · have h1 : ¬ (U.X k).p0 ≤ (i : ℕ) := by omega
    simp only [Pi.sub_apply, Pi.smul_apply]
    simp only [laU, h1, hj, if_true, if_false, hz, nsmul_eq_mul]
    have h3 := mul_nonneg hs'.le (Int.natCast_nonneg
      (a (Function.invFun (relab c σ) (conjEmb τ.1), (U.X k).p0 - 1 - (i : ℕ))))
    have h4 := mul_nonneg hs'.le (Int.natCast_nonneg
      (a (Function.invFun (relab c σ) τ.1, (j : ℕ) - (U.X k).p0)))
    push_cast at hm' ⊢
    linarith

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem weights_of_run : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (ka wL wF : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CK C1 A1 h0 : ℝ) (Tn nP nW : ℕ), SetC large₂ (recPlus h j hj) CK C1 A1 ka wL wF Tn nP nW h0 → ∀ σ, GoodEmb T.Q.c σ → ∀ k : (T.U j σ).Comp, ReciprocityTheory.ChartRestriction.G.AR.Inst.nd ((T.U j σ).X k) = WeightFamilies.dimY D j ∧ ReciprocityTheory.ChartRestriction.G.AR.Inst.IsStrictDom ((T.U j σ).X k) (laU (T.U j σ) (wtA wL) (wL).n k) ∧ (∀ i : ℕ, 0 < i → ReciprocityTheory.ChartRestriction.G.AR.Inst.IsStrictDom ((T.U j σ).X k) ((i * g0 D) • (laU (T.U j σ) (wtA wL) (wL).n k) - (laU (T.U j σ) (wtA (etWt D j i)) ((etWt D j i)).n k))) ∧ (j = D.R.m → ((T.U j σ).X k).p0 = 0 ∨ D.R.r ≤ ((T.U j σ).X k).p0) := by
  intro D T h j hj ka wL wF large₂ CK C1 A1 h0 Tn nP nW hS σ hσ k
  obtain ⟨-, hgP, hgM, -, -, -, -, -, -, -, -, -, -, -, ⟨hn, hLP, hLM⟩, -, -, -, -, -, -, h40, -⟩ := hS
  obtain ⟨-, -, -, -, -, hf, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  obtain ⟨hpq, hr1, -⟩ := hnum j hj
  obtain ⟨hp, hq, -⟩ := h.pins.2.2.2 j hj
  obtain ⟨-, hk, -⟩ := h.unf j hj σ hσ
  obtain ⟨hp0, hΨ⟩ := hk k
  obtain ⟨hbij, hrt, hcj, -⟩ := GlobalTheory.Relab.relab_good _ T.Q.H T.Q.l T.Q.c σ hσ
  replace hbij : Function.Bijective (relab T.Q.c σ) := hbij
  replace hrt : ∀ τ, relab T.Q.c σ τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 ↔ τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hrt
  replace hcj : ∀ τ, relab T.Q.c σ (conjEmb τ) = conjEmb (relab T.Q.c σ τ) := hcj
  rw [hp, hq] at hpq
  rw [hq] at hp0
  have hT : 0 < Tp D j Tn := by unfold Tp; omega
  have key : ∀ τ : ((T.U j σ).X k).Ψ, ∃ t, Function.invFun (relab T.Q.c σ) τ.1 = DV.tauEmb D t ∧
      Function.invFun (relab T.Q.c σ) (conjEmb τ.1) = conjEmb (DV.tauEmb D t) := by
    rintro ⟨τ, hτ⟩
    obtain ⟨ρ, rfl⟩ := hbij.2 τ
    obtain ⟨t, rfl⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q h.pins.1 ρ ((hrt ρ).1 ((hΨ _).1 hτ))
    refine ⟨t, Function.leftInverse_invFun hbij.1 _, ?_⟩
    show Function.invFun (relab T.Q.c σ) (conjEmb (relab T.Q.c σ (DV.tauEmb D t))) = _
    rw [← hcj]
    exact Function.leftInverse_invFun hbij.1 _
  have hu : ∀ τ : ((T.U j σ).X k).Ψ, ∀ x y, x < y → ((T.U j σ).X k).p0 + y < D.R.r →
      wtA wL (Function.invFun (relab T.Q.c σ) τ.1, y) < wtA wL (Function.invFun (relab T.Q.c σ) τ.1, x) := by
    intro τ x y hxy hy
    obtain ⟨t, ht, -⟩ := key τ
    rw [ht]
    refine wtA_lt_upper wL t hxy (extendByZero_strictAnti_of_positive_gaps _ (wL.aPlus_antitone t) (fun i hi => ?_) hxy (by omega))
    rw [hLP t i, if_pos hi]
    exact fdiv_pos hT (hgP t i hi)
  have hl : ∀ τ : ((T.U j σ).X k).Ψ, ∀ x y, x < y → y < ((T.U j σ).X k).p0 →
      wtA wL (Function.invFun (relab T.Q.c σ) (conjEmb τ.1), y) <
        wtA wL (Function.invFun (relab T.Q.c σ) (conjEmb τ.1), x) := by
    intro τ x y hxy hy
    obtain ⟨t, -, ht⟩ := key τ
    rw [ht]
    refine wtA_lt_lower wL t hxy (extendByZero_strictAnti_of_positive_gaps _ (wL.aM_anti t) (fun i hi => ?_) hxy (by omega))
    rw [hLM t i, if_pos hi]
    exact fdiv_pos hT (hgM t i hi)
  have h20 : 20 ≤ wL.n / 2 := by omega
  refine ⟨nd_eq _ hf hpq, ?_, fun i hi => ?_, fun hm => Or.inl ?_⟩
  · have h1 := strictDom_smul_sub (T.U j σ) (wtA wL) (fun _ => 0) (fun _ => rfl) wL.n 0 1 k one_pos (by omega) hu hl
    have h2 : laU (T.U j σ) (fun _ => 0) 0 k = 0 := by
      funext τ x
      simp [laU]
    rwa [h2, one_smul, sub_zero] at h1
  · have hg : 0 < i * g0 D := Nat.mul_pos hi (by unfold g0; omega)
    refine strictDom_smul_sub (T.U j σ) (wtA wL) _ (fun x => ?_) wL.n _ _ k hg ?_ hu hl
    · simp [wtA, etWt, wscalar, ext0]
    · show g0 D * i / 2 < i * g0 D * (wL.n / 2)
      have := Nat.mul_le_mul_left (i * g0 D) h20
      rw [mul_comm (g0 D) i]
      omega
  · rw [hp0, hm]
    simp [Ranks.sigW]

end GlobalTheory.RunWts
