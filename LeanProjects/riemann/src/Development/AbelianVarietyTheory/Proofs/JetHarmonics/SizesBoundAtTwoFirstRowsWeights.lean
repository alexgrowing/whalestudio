import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulRowsScaledWeightLeKappaRowsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KappaRowsEntriesLeSizesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudSizesBetweenZeroAndTwiceBStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabelBijectiveCardEqFStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegreeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem vd2_nonneg_of_D7 (D : D7) : 0 ≤ vd2 D := by
  unfold vd2
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast D.host.QS_pos)

theorem sizes_two_arith (T f q m v A S C b Sc η : ℝ) (hf : 0 ≤ f) (hq : 0 ≤ q) (hqm : q ≤ m) (hv : 0 ≤ v)
    (hC : 1 ≤ C) (hb : 0 ≤ b) (hSc : 0 ≤ Sc) (hη : 0 ≤ η) (hA : T * A = 2 * b + Sc) (hS : T * S ≤ f * η) :
    T * (f * q * (1 + v / 2) * A + q * S) ≤ C * m * (2 + v) * (2 * f * b + f * (Sc + η)) := by
  have hm : 0 ≤ m := hq.trans hqm
  have e1 : T * (f * q * (1 + v / 2) * A + q * S) = q * (f * (1 + v / 2) * (2 * b + Sc) + T * S) := by
    rw [← hA]; ring
  have h1 : f * (1 + v / 2) * (2 * b + Sc) + T * S ≤ (2 + v) * (2 * f * b + f * (Sc + η)) := by
    have p1 : 0 ≤ f * (1 + v / 2) * (2 * b + Sc) := by positivity
    have p2 : 0 ≤ (1 + v) * (f * η) := by positivity
    nlinarith
  have h0 : 0 ≤ (2 + v) * (2 * f * b + f * (Sc + η)) := by positivity
  rw [e1]
  calc q * (f * (1 + v / 2) * (2 * b + Sc) + T * S) ≤ q * ((2 + v) * (2 * f * b + f * (Sc + η))) :=
        mul_le_mul_of_nonneg_left h1 hq
    _ ≤ m * ((2 + v) * (2 * f * b + f * (Sc + η))) := mul_le_mul_of_nonneg_right hqm h0
    _ ≤ C * (m * ((2 + v) * (2 * f * b + f * (Sc + η)))) := le_mul_of_one_le_left (mul_nonneg hm h0) hC
    _ = _ := by ring

theorem sizes_bound_two : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (Q : Par D), Q.Pins → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ C : ℝ, 1 ≤ C → ∀ j, InR D j → ∃ Ap : ℝ, 0 ≤ Ap ∧ (∀ τ, InPsi Q.H τ → (wtA (lR Tp hK j) (τ, 0) : ℝ) ≤ Ap) ∧ (open Classical in (Tp.TO : ℝ) * ((D.R.f : ℝ) * (Q.Dw j).q * (1 + vd2 D / 2) * Ap + (Q.Dw j).q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi Q.H τ), (wtA (lR Tp hK j) (τ, 0) : ℝ)) ≤ C * D.R.m * (2 + vd2 D) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz))) := by
  classical
  intro D L Pm Tp hK Q hQ hx hkb C hC j hj
  obtain ⟨hSe, hw⟩ := GlobalTheory.T.cloudSizes_between_zero_and_twice_b D L Pm hx hkb
  obtain ⟨hw1, -, -⟩ := hw j hj
  obtain ⟨-, -, hP, hN, hwt⟩ := GlobalTheory.T.weightExponents_embeddings_degree D Q hQ j hj (lR Tp hK j)
  have hT : (0 : ℝ) < (Tp.TO : ℝ) := by exact_mod_cast TO_pos Tp
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hSc := L.Sc_pos.le
  have hη := L.etaSz_pos.le
  have hplus : ∀ t, (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aP t) 0 : ℝ) ≤ 2 * L.sc.b + L.Sc := by
    intro t
    unfold Formalism.L2.Pj.ext0
    split_ifs with h
    · have h1 : (Tp.TO : ℝ) * ((lR Tp hK j).aP t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aP t ⟨0, h⟩ : ℝ) := by
        exact_mod_cast (GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK j t).1 ⟨0, h⟩
      obtain ⟨h2, h3, -⟩ := GlobalTheory.T.kappaRows_entries_le_sizes D L Pm Tp hK j hj t
      rcases Nat.lt_or_ge 0 (D.R.k - 1) with hk | hk
      · have := h2 ⟨0, h⟩ hk
        have := (hw1 t).2
        linarith
      · have := h3 ⟨0, h⟩ hk
        linarith
    · simp only [Nat.cast_zero, mul_zero]; linarith
  have hminus : ∀ t, (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aM t) 0 : ℝ) ≤ L.etaSz := by
    intro t
    unfold Formalism.L2.Pj.ext0
    split_ifs with h
    · have h1 : (Tp.TO : ℝ) * ((lR Tp hK j).aM t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aM t ⟨0, h⟩ : ℝ) := by
        exact_mod_cast (GlobalTheory.T.mul_rows_scaledWeight_le_kappaRows D L Pm Tp hK j t).2.1 ⟨0, h⟩
      exact h1.trans ((GlobalTheory.T.kappaRows_entries_le_sizes D L Pm Tp hK j hj t).2.2 _)
    · simpa using hη
  refine ⟨(2 * L.sc.b + L.Sc) / Tp.TO, by positivity, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨t, rfl⟩ := (hP τ).1 hτ
    rw [(hwt t 0).1, le_div_iff₀ hT, mul_comm]
    exact hplus t
  · have hq : (Q.Dw j).q ≤ D.R.m := by
      rw [(hQ.2.2.2 j hj).2.1]
      exact Nat.sub_le _ _
    refine sizes_two_arith _ _ _ _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hq)
      (vd2_nonneg_of_D7 D) hC hb hSc hη (by field_simp) ?_
    rw [Finset.mul_sum]
    have hcard : (Finset.univ.filter (fun τ => ¬ InPsi Q.H τ)).card ≤ D.R.f := by
      rw [← (GlobalTheory.T.realPlaceLabel_bijective_card_eq_f D).2, ← Finset.card_univ]
      refine le_trans (Finset.card_le_card ?_)
        (Finset.card_image_le (f := fun t => ComplexEmbedding.conjugate (DV.tauEmb D t)))
      intro τ hτ
      obtain ⟨t, rfl⟩ := (hN τ).1 (Finset.mem_filter.1 hτ).2
      exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩
    refine (Finset.sum_le_card_nsmul _ _ L.etaSz ?_).trans ?_
    · intro τ hτ
      obtain ⟨t, rfl⟩ := (hN τ).1 (Finset.mem_filter.1 hτ).2
      rw [(hwt t 0).2]
      exact hminus t
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hη

end GlobalTheory.RunDepth
