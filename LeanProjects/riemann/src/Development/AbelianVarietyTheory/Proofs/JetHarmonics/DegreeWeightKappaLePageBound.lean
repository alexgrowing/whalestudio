import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmQuadraticFormEqAlternatingForm
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KappaRowsEntriesLeSizesStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CloudSizesBetweenZeroAndTwiceBStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceLabelBijectiveCardEqFStatement

set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem sum_fin_le_two_blocks {n K j : ℕ} (hn : n = K + j) (a : Fin n → ℝ) (A B : ℝ)
    (h1 : ∀ i, i.1 < K → a i ≤ A) (h2 : ∀ i, K ≤ i.1 → a i ≤ B) : ∑ i, a i ≤ K * A + j * B := by
  subst hn
  rw [Fin.sum_univ_add]
  have e1 : ∑ i : Fin K, a (Fin.castAdd j i) ≤ ∑ _i : Fin K, A :=
    Finset.sum_le_sum fun i _ => h1 _ (by simp)
  have e2 : ∑ i : Fin j, a (Fin.natAdd K i) ≤ ∑ _i : Fin j, B :=
    Finset.sum_le_sum fun i _ => h2 _ (by simp)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e1 e2
  linarith

theorem four_sq_lt_of_eighth {k b g : ℝ} (hk : 5 ≤ k) (hb : 1 ≤ b) (hg : (k * b) ^ 8 ≤ g) :
    4 * k ^ 2 * b < (g - 2) / 2 := by
  have h5 : 5 ≤ k * b := by nlinarith
  have h0 : k ^ 2 * b ≤ (k * b) ^ 2 := by
    have : 0 ≤ k ^ 2 * b * (b - 1) := by
      have : 0 ≤ b - 1 := by linarith
      have : 0 ≤ b := by linarith
      positivity
    nlinarith
  set y := k * b
  have h2 : 25 ≤ y ^ 2 := by nlinarith
  have h6 : 25 ≤ y ^ 6 := h2.trans (pow_le_pow_right₀ (by linarith) (by norm_num))
  have h8 : y ^ 8 = y ^ 6 * y ^ 2 := by ring
  nlinarith

theorem DF_kaR_le : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D), 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ j, InR D j → (WeightAlgebra.DF (kaR Tp hK j) : ℝ) ≤ (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz)) ∧ ∀ i, (WeightAlgebra.DF (kaR Tp hK j) : ℝ) < ((D.host.g i : ℝ) - 2) / 2 := by
  intro D L Pm Tp hK hx hkb j hj
  obtain ⟨hSe, hw⟩ := GlobalTheory.T.cloudSizes_between_zero_and_twice_b D L Pm hx hkb
  have hw := (hw j hj).1
  have hrow := GlobalTheory.T.kappaRows_entries_le_sizes D L Pm Tp hK j hj
  have hcard := (GlobalTheory.T.realPlaceLabel_bijective_card_eq_f D).2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hmk : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hj1 := hj.1
  have hj2 := hj.2
  have hkR : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hmkR : (D.R.m : ℝ) ≤ D.R.k := by exact_mod_cast hmk
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast (D.R.f_le_k : D.R.f ≤ D.R.k)
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hb : 1 ≤ L.sc.b := by
    unfold Scale.b
    apply Real.one_le_exp
    unfold Scale.L
    exact Real.rpow_nonneg (by linarith) _
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hτ : ∀ τ : D.what₂.Tau, ((∑ i, ((kaR Tp hK j).aP τ i : ℝ)) + ∑ i, ((kaR Tp hK j).aM τ i : ℝ)) ≤
      (D.R.k : ℝ) * (2 * L.sc.b + (L.Sc + L.etaSz)) := by
    intro τ
    obtain ⟨r1, r2, r3⟩ := hrow τ
    have s1 := sum_fin_le_two_blocks (n := (D.R.sigW j).1) (K := D.R.k - 1) (j := j)
      (by show D.R.k + j - 1 = _; omega) (fun i => ((kaR Tp hK j).aP τ i : ℝ)) (2 * L.sc.b + L.Sc) L.etaSz
      (fun i hi => (r1 i hi).trans (by linarith [(hw τ).2])) r2
    have s2 := sum_fin_le_two_blocks (n := (D.R.sigW j).2) (K := 0) (j := D.R.m - j)
      (by show D.R.m - j = _; omega) (fun i => ((kaR Tp hK j).aM τ i : ℝ)) 0 L.etaSz
      (fun i hi => absurd hi (Nat.not_lt_zero _)) (fun i _ => r3 i)
    rw [Nat.cast_sub (by omega : 1 ≤ D.R.k)] at s1
    rw [Nat.cast_sub hj2] at s2
    have t1 : (D.R.m : ℝ) * L.etaSz ≤ D.R.k * L.etaSz := mul_le_mul_of_nonneg_right hmkR he.le
    push_cast at s1 s2
    nlinarith
  have hmain : (WeightAlgebra.DF (kaR Tp hK j) : ℝ) ≤
      (D.R.k : ℝ) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz)) := by
    unfold WeightAlgebra.DF WeightAlgebra.degP
    push_cast
    refine (Finset.sum_le_sum fun τ _ => hτ τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    apply le_of_eq
    ring
  refine ⟨hmain, fun i => ?_⟩
  obtain ⟨Y, hY, -, -, hg⟩ := Pm.g_Y
  refine lt_of_le_of_lt (hmain.trans ?_) (four_sq_lt_of_eighth hkR hb (hY.trans (hg i).1))
  have u1 : (D.R.f : ℝ) * (L.Sc + L.etaSz) ≤ D.R.f * (2 * L.sc.b) := mul_le_mul_of_nonneg_left hSe hf0
  have u2 : (D.R.f : ℝ) * L.sc.b ≤ D.R.k * L.sc.b := mul_le_mul_of_nonneg_right hfk (by linarith)
  calc _ ≤ (D.R.k : ℝ) * (4 * (D.R.k * L.sc.b)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ = _ := by ring

end GlobalTheory.RunDepth
