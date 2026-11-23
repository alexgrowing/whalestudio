import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ProjKeepsLetter
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

theorem Lam_sub (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (Z W : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (Z - W) = D.abelian₂ p F Z - D.abelian₂ p F W := by
  unfold abelian₂; simp only [gaAct_eq_dg, map_sub, fock_sub_right]

theorem Lam_smul (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (a : K) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (a • Z) = a * D.abelian₂ p F Z := by
  unfold abelian₂; simp only [gaAct_eq_dg, map_smul, fock_smul_right]

theorem Lam_monomial (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) (c : K) :
    D.abelian₂ p F (monomial ζ c) =
      F.coeff (D.phE p ζ) * (D.ga (D.phE p ζ) * c) * (fact (D.phE p ζ) : K) := by
  unfold abelian₂; rw [ph_monomial, gaAct_eq_dg, dg_monomial, fock_monomial_right]

theorem ph_eq_sum (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.ph p Z = ∑ ζ ∈ Z.support, monomial (D.phE p ζ) (Z.coeff ζ) := by
  conv_lhs => rw [Z.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun ζ _ => D.ph_monomial p ζ _

theorem monomial_mem_PolK {L : Type} {r : ℕ} (d : L → ℕ) (α : L × Fin r →₀ ℕ) (c : K)
    (h : ∀ i, ldeg α i = d i) : monomial α c ∈ PolK K r d := by
  classical
  rw [mem_PolK_iff]
  intro β hβ
  have := support_monomial_subset hβ
  rw [Finset.mem_singleton] at this
  rw [this]; exact h

theorem ph_mem_PolK (p : ℕ) {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) :
    D.ph p Z ∈ PolK K D.r D.dO := by
  rw [ph_eq_sum]
  exact Submodule.sum_mem _ fun ζ hζ => monomial_mem_PolK _ _ _ (D.ldeg_phE p ζ (hZ ζ hζ))

theorem cge_ph (v : AddValuation K (WithTop ℚ)) (p : ℕ) {a : ℝ} {Z : MvPolynomial (D.ML × Fin D.r) K}
    (hZ : cge v a Z) : cge v a (D.ph p Z) := by
  rw [ph_eq_sum]
  exact cge_sum v _ _ fun ζ _ => cge_monomial v _ (hZ ζ)

theorem eC_nonneg {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.eC p C0 := by
  unfold eC
  have := lg_ge_one hp hr (2 * D.totDeg)
  positivity

theorem Dm_nonneg {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dm p C0 := by
  unfold Dm
  have := D.eC_nonneg hp hr h1
  exact Finset.sum_nonneg fun j _ => by positivity

theorem Dl_nonneg {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dl p C0 := by
  unfold Dl
  have := D.eC_nonneg hp hr h1
  have h2 : (0 : ℝ) ≤ (D.r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ D.r := by exact_mod_cast hr
    linarith
  positivity

theorem kapD_ge_one {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) (hJ : 1 ≤ D.J) : 1 ≤ D.kapD p := by
  unfold kapD
  refine le_trans ?_ (kap_ge_card hp hr D.dO)
  have h1 : 1 ≤ Fintype.card D.OL := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have : 1 ≤ D.J * D.r := Nat.mul_pos hJ hr
    omega
  have h2 : (1 : ℝ) ≤ (Fintype.card D.OL : ℝ) := by exact_mod_cast h1
  have h3 : (1 : ℝ) ≤ (D.r : ℝ) := by exact_mod_cast hr
  nlinarith

end TwistData

section Top

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

theorem stepBC_of (hB : StepB K v p C0) (hC : StepC K v p) : StepBC K v p C0 := by
  intro hD D hV hc F hF hF0
  obtain ⟨Gt, hGt, hval, hle⟩ := hB hD D hV hc F hF hF0
  obtain ⟨Z, hZi, hZg, hZph, hZv⟩ := hC hD D hV.1 hV.2.1 (fun j m => D.thl j m - 6 * D.c) Gt hGt hval
  refine ⟨Z, hZi, hZg, hZv, ?_⟩
  unfold TwistData.abelian₂
  rw [hZph]; exact hle

theorem plane_gram_theorem_of_combined_lemmas (h1 : 1 ≤ C0) (hBC : StepBC K v p C0) (hDEF : StepDEF K v p C0) :
    LiftBoundUniform K v p C0 := by
  intro hD D hV hH hc F hF hF0
  obtain ⟨Z, hZi, hZg, hZy, hZl⟩ := hBC hD D hV hc F hF hF0
  obtain ⟨Om, N2, hN2, hOi, hOg, hOc, hOy, hOl⟩ := hDEF hD D hV hH hc F hF hF0
  have hp : 2 ≤ p := two_le_p hD
  have hr : 1 ≤ D.r := hV.1
  have hJ : 1 ≤ D.J := hV.2.1
  have hkap := D.kapD_ge_one hp hr hJ
  have hDm := D.Dm_nonneg hp hr h1
  have hDl := D.Dl_nonneg hp hr h1
  have hcc : 4 * (D.Dm p C0 + D.Dl p C0 + 3 * D.kapD p) < D.c := hc
  have hG : D.Good p (((p : K) ^ N2) • Om Z) := TwistData.Good.smul D (hOg Z hZg) _
  have hGi : Integral v (((p : K) ^ N2) • Om Z) := hOi Z hZi hZg
  refine ⟨((p : K) ^ N2) • Om Z, 0, ⟨⟨hGi, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α hα j m hm a
    exact (hG α hα).2.1 j m hm a
  · intro j i
    exact vala_smul _ (hOc Z hZg j i)
  · intro j m hm
    have := vala_smul ((p : K) ^ N2) (hOy Z hZg j m _ hm (hZy j m hm))
    exact vala_mono (by linarith) this
  · intro α hα t a
    exact (hG α hα).1 t a
  · intro α hα; simp at hα
  · intro α hα; simp at hα
  · intro α; simp [vR]
  · intro α hα
    exact ⟨(hG α hα).2.2.1, fun t => by
      have := (hG α hα).2.2.2.1 t
      simp only [ldeg] at this
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      exact this⟩
  · intro α hα; simp at hα
  · rw [add_zero, ← bge_iff]
    have h2 := bge_of_cge hD (D.ph_mem_PolK p hG) (D.cge_ph v p ((cge_zero_iff_Integral v _).mpr hGi))
    refine bge_mono v ?_ h2
    have h3 := kapL_le_kap' hp hr D.dO
    have h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
    have h5 : D.kapD p = kap p D.r D.dO := rfl
    rw [h4, h5]; linarith
  · rw [add_zero]
    have e1 : fock F (D.gaAct (D.ph p (((p : K) ^ N2) • Om Z))) = (p : K) ^ N2 * D.abelian₂ p F (Om Z) :=
      D.Lam_smul p F _ _
    have e2 : D.abelian₂ p F (Om Z) = D.abelian₂ p F Z + (D.abelian₂ p F (Om Z) - D.abelian₂ p F Z) := by ring
    have h6 : vle v (D.n0 v + D.Dl p C0 + 1) (D.abelian₂ p F (Om Z)) := by
      rw [e2]
      exact vle_add_of_lt v hZl (hOl Z hZi hZg) (by linarith)
    have h7 := vle_pow_p hD N2 h6
    rw [e1]
    have h8 : vR v ((p : K) ^ N2 * D.abelian₂ p F (Om Z)) ≤ ((D.n0 v + D.Dl p C0 + 1 + N2 : ℝ) : WithTop ℝ) := h7
    calc vR v ((p : K) ^ N2 * D.abelian₂ p F (Om Z)) + ((-D.n0 v + D.kapD p : ℝ) : WithTop ℝ)
        ≤ ((D.n0 v + D.Dl p C0 + 1 + N2 : ℝ) : WithTop ℝ) + ((-D.n0 v + D.kapD p : ℝ) : WithTop ℝ) := by
          gcongr
      _ = ((D.n0 v + D.Dl p C0 + 1 + N2 + (-D.n0 v + D.kapD p) : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]
      _ ≤ ((D.E p C0 2 + 2 * D.kapD p : ℝ) : WithTop ℝ) := by
          rw [WithTop.coe_le_coe]
          unfold TwistData.E
          linarith

end Top

end Formalism.MainNotions.PlaneGram
