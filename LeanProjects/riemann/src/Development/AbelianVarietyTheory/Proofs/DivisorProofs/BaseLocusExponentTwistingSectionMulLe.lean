import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentIntegralFramedPointLiesOnStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistingSectionMulLatticeValueLeStatement

set_option synthInstance.maxHeartbeats 400000

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.RefTwist

theorem vAdd_natCast_pos {K : Type} [Field K] [NumberField K] {q : ℕ} (hq : q ≠ 0) {w : HeightOneSpectrum (𝓞 K)}
    (hw : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : 0 < vAdd w (q : K) := by
  have h1 : w.valuation K (algebraMap (𝓞 K) K q) < 1 := (w.valuation_lt_one_iff_mem _).2 hw
  rw [map_natCast] at h1
  have h0 : w.valuation K (q : K) ≠ 0 := (w.valuation K).ne_zero_iff.2 (Nat.cast_ne_zero.2 hq)
  have h2 := (WithZero.log_lt_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vAdd
  omega

theorem nval_le_add_of_mul {T : CDVR} {e n : ℕ} {m s k : ℝ} (he : 0 < e) (hm : 0 < m) (hn : (n : ℝ) = e * m)
    (hs : s ≤ k * m) {a b : T.Fr} (h : nval T.V e b ≤ nval T.V e a + (s : EReal)) :
    nval T.V n b ≤ nval T.V n a + (k : EReal) := by
  by_cases ha : a = 0
  · rw [ha, nval_zero, EReal.top_add_coe]; exact le_top
  rw [nval_of_ne ha, ← EReal.coe_add] at h ⊢
  by_cases hb : b = 0
  · rw [hb, nval_zero] at h; exact absurd h (not_le.2 (EReal.coe_lt_top _))
  rw [nval_of_ne hb, EReal.coe_le_coe_iff] at h ⊢
  have he' : (0 : ℝ) < e := Nat.cast_pos.2 he
  rw [hn, ← div_div, ← div_div, div_le_iff₀ hm, add_mul, div_mul_cancel₀ _ hm.ne']
  linarith

theorem refExp_vp_add_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (G G₀ : WTZ E), Even G.2 → ∀ (cst k : ℝ) (q : ℕ), q.Prime → ∀ t : ∀ Z : Comp Xo c, TwSec U x Z G₀, (∀ Z (w : HeightOneSpectrum (𝓞 c.F)), ((q : ℕ) : 𝓞 c.F) ∈ w.asIdeal → (t Z).hi w - (⌊(t Z).lo w⌋ : ℝ) ≤ k * (vAdd w (q : c.F) : ℝ)) → refExp_vp U cst (G + G₀) q ≤ refExp_vp U cst G q + (k : EReal) := by
  intro E _ _ _ H Dw l Xo c r U hU x G G₀ hG cst k q hq t ht
  refine (refExp_vp_le_iff U).2 fun la T io e ho y hy φ hφ => ?_
  have h0 := (refExp_vp_le_iff U).1 (le_refl (refExp_vp U cst G q)) la T io e ho y hy φ hφ
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_component_integral_framedPoint_liesOn E H Dw l Xo c T io y
  have hv : (fun f => nval T.V e (evI y f)) ∈ valOn Z la.1 := ⟨PtV.mk la.1 ho y ⟨hy, hZ⟩ () trivial, rfl⟩
  have hm : 0 < vAdd la.1 (q : c.F) := vAdd_natCast_pos hq.ne_zero la.2
  have hq' : vV T.V (q : T.Fr) = (e : ℤ) * vAdd la.1 (q : c.F) := by
    rw [← map_natCast io q]; exact ho.2 _
  have hn : (((vV T.V (q : T.Fr)).toNat : ℕ) : ℝ) = e * (vAdd la.1 (q : c.F) : ℝ) := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg (hq' ▸ mul_nonneg (Int.natCast_nonneg e) hm.le), hq']
    push_cast; rfl
  have hd : depthAt_vp U (G + G₀) q y ≤ depthAt_vp U G q y + (k : EReal) := by
    rw [← EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    refine le_iInf₂ fun f hf => ?_
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]
    obtain ⟨g, hg, hle⟩ := GlobalTheory.T.exists_twistingSection_mul_lattice_value_le E H Dw l Xo c r U hU x G G₀ hG Z (t Z) la.1 _ hv f hf
    exact (iInf₂_le g hg).trans (nval_le_add_of_mul ho.1 (Int.cast_pos.2 hm) hn (ht Z la.1 la.2) hle)
  rw [add_right_comm]
  exact hd.trans (add_le_add h0 le_rfl)

end GlobalTheory.RefTwist

end
