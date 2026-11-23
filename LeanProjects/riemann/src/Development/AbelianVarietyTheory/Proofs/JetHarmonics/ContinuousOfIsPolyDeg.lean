import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF Filter Topology

namespace GlobalTheory.HatNF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma norm_opApply_le_of_polynomial_coeffs_lemma {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ) (A : ℝ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp) (B : ℝ), _root_.Formalism.FourierDecayAlt.B.CCle A o G B →
      ∀ g ∈ _root_.Formalism.FourierDecayAlt.B.GV k r, ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ ≤ C * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
  induction Θ with
  | nil => exact ⟨0, le_rfl, fun G B hG g _ => by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply, _root_.Formalism.FourierDecayAlt.P.B4.gN_rpow_nonneg, mul_nonneg (mul_nonneg le_rfl (_root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hG))]⟩
  | cons T Θ ih =>
    obtain ⟨C₁, hC₁0, hC₁⟩ := ih (fun S hS => hΘ S (List.mem_cons_of_mem _ hS))
    obtain ⟨hlen, Q, hQ, hcoef⟩ := hΘ T List.mem_cons_self
    obtain ⟨CQ, hCQ0, hCQ⟩ := _root_.PI.UnitaryCorollaryDerivatives.pb_nonneg (_root_.PI.UnitaryCorollaryDerivatives.pb_poly hQ) 0
    have hunit : ∀ X ∈ List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word, _root_.Formalism.FourierDecayAlt.B.unitLie k r X := by
      intro X hX
      obtain ⟨Y, hY, rfl⟩ := List.mem_map.mp hX
      exact _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm_unit (T.word_lie Y hY)
    set ν : ℝ := ‖((List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nz T.word).prod : ℂ)‖ with hν
    refine ⟨CQ * ν + C₁, by positivity, fun G B hG g hg => ?_⟩
    have hgpos : 0 < _root_.Formalism.FourierDecayAlt.B.gN g := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg
    have hB : 0 ≤ B := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hG
    have hRw : _root_.Formalism.FourierDecayAlt.B.CCle A 0 (_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G) B :=
      _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_Rw hunit (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_m (by simpa using hlen) hG)
    have hRw' := hRw.2 [] [] (by simp) (by simp) (by simp) g hg
    simp only [_root_.Formalism.FourierDecayAlt.B.dLR, List.foldr_nil, _root_.Formalism.FourierDecayAlt.B.Rw] at hRw'
    have hword : ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖ ≤ B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A) := by
      rw [Real.rpow_neg hgpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hgpos _),
        mul_comm]
      simpa [_root_.Formalism.FourierDecayAlt.B.Rw] using hRw'
    have hQg : ‖Q g‖ ≤ CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) := by
      have := hCQ [] (by simp) (by simp) g hg
      simpa [_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw] using this
    have hterm : ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by
      rw [hcoef, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, norm_smul,
        congrFun (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.Rw_scale T.word G) g, norm_smul, ← hν, sub_eq_add_neg,
        Real.rpow_add hgpos]
      calc ‖Q g‖ * (ν * ‖_root_.Formalism.FourierDecayAlt.B.Rw (List.map _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.nrm T.word) G g‖)
          ≤ (CQ * _root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ)) * (ν * (B * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A))) := by
            gcongr
        _ = CQ * ν * B * (_root_.Formalism.FourierDecayAlt.B.gN g ^ (κ : ℝ) * _root_.Formalism.FourierDecayAlt.B.gN g ^ (-A)) := by ring
    have hrest := hC₁ G B hG g hg
    have hsplit : _root_.Formalism.FourierDecayAlt.B.opApply (T :: Θ) G g = (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g := by
      simp [_root_.Formalism.FourierDecayAlt.B.opApply]
    rw [hsplit]
    calc ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g) + _root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖
        ≤ ‖(T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)‖ + ‖_root_.Formalism.FourierDecayAlt.B.opApply Θ G g‖ := norm_add_le _ _
      _ ≤ CQ * ν * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) + C₁ * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) :=
          add_le_add hterm hrest
      _ = (CQ * ν + C₁) * B * _root_.Formalism.FourierDecayAlt.B.gN g ^ ((κ : ℝ) - A) := by ring

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
private lemma continuousOn_opApply_of_polynomial_coeffs_lemma_2 {k r : ℕ} {Wp Wq : Type}
    [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o κ : ℕ)
    (Θ : List (_root_.Formalism.FourierDecayAlt.B.DTerm k r Wp Wq))
    (hΘ : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat k r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp))
    {G : _root_.Formalism.FourierDecayAlt.B.Mat k r → Wq →L[ℂ] Wp} (hG : _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV k r) G) :
    ContinuousOn (_root_.Formalism.FourierDecayAlt.B.opApply Θ G) (_root_.Formalism.FourierDecayAlt.B.GV k r) := by
  apply _root_.Formalism.FourierDecayAlt.P.PBE.opApply_continuousOn
  intro T hT
  obtain ⟨-, Q, hQ, hcoef⟩ := hΘ T hT
  have hQc : Continuous Q := (_root_.Formalism.FourierDecayAlt.P.poly_adm (n := 0) hQ).1.continuous
  have hRw : ContinuousOn (_root_.Formalism.FourierDecayAlt.B.Rw T.word G) (_root_.Formalism.FourierDecayAlt.B.GV k r) :=
    _root_.Formalism.FourierDecayAlt.P.PBE.ckOn_continuousOn' subset_rfl (_root_.Formalism.FourierDecayAlt.P.MinorPolynomials.ckOn_Rw_top hG T.word_lie)
  have hfun : (fun g => (T.coef g) (_root_.Formalism.FourierDecayAlt.B.Rw T.word G g)) =
      fun g => Q g • _root_.Formalism.FourierDecayAlt.B.Rw T.word G g := by
    funext g
    rw [hcoef]
    simp
  rw [hfun]
  exact hQc.continuousOn.smul hRw

open MeasureTheory Filter Topology in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem _root_.GlobalTheory.HatNF.vecV_cut_polyOp : ∃ c₃ : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : _root_.Formalism.FourierDecayAlt.M.Par) (p : _root_.Formalism.FourierDecayAlt.KB.Pl P Wp Wq) (o κ : ℕ) (Θ : _root_.Formalism.FourierDecayAlt.B.DiffOp P.k P.r Wp Wq) (F : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp o κ Θ → _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) F → _root_.Formalism.FourierDecayAlt.B.InCC A o F → c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A - 1 - κ → ∀ cut : ℕ → _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, (∀ n g, cut n g = ((Real.smoothTransition ((4 - ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • g) i j)) / 3) : ℝ) : ℂ)) → ∀ γ : _root_.Formalism.FourierDecayAlt.C.LPt, Filter.Tendsto (fun n => p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) γ) Filter.atTop (nhds (p.V (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) γ)) := by
  obtain ⟨c₃, hc₃⟩ := _root_.Formalism.FourierDecayAlt.P.PBE.vecV_tendsto
  refine ⟨c₃, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p o κ Θ F A hΘ hF hCC hA cut hcut γ
  unfold _root_.Formalism.FourierDecayAlt.P.CutMP.PolyOp at hΘ
  have hΘ' : ∀ T ∈ Θ, T.word.length ≤ o ∧ ∃ Q : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℂ, _root_.Formalism.FourierDecayAlt.U.IsPolyDeg κ Q ∧
      ∀ g, T.coef g = Q g • ContinuousLinearMap.id ℂ (Wq →L[ℂ] Wp) := by
    intro T hT
    obtain ⟨hl, Q, hQ, hc, -⟩ := hΘ T hT
    exact ⟨hl, Q, hQ, hc⟩
  have hcutφ : ∀ n : ℕ, cut n = fun g => _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := by
    intro n
    funext g
    rw [hcut]
    rfl
  have hψ : ∀ (n : ℕ) g, cut n g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g := by
    intro n g
    have h : _root_.Formalism.FourierDecayAlt.P.JCx2.pdPsi ((n : ℝ) + 1) g = 1 - _root_.Formalism.FourierDecayAlt.P.JCx2.pdPhi (((n : ℝ) + 1)⁻¹ • g) := rfl
    rw [hcutφ, h]
    ring
  unfold _root_.Formalism.FourierDecayAlt.B.InCC at hCC
  obtain ⟨b, hb⟩ := hCC
  have hb0 : 0 ≤ b := _root_.Formalism.FourierDecayAlt.P.B4.cc_nonneg hb
  have hb1 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F b := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_mono_A (by linarith) hb
  obtain ⟨K, hK0, hK⟩ := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_ccle (k := P.k) (r := P.r) (E := Wq →L[ℂ] Wp) o
  have hGn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o (fun g => cut n g • F g) (b + K * b) := by
    intro n
    have hR : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h3 := _root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add hb1 (_root_.Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul (-1 : ℂ) (hK ((n : ℝ) + 1) hR A F b hb))
    refine _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c (_root_.Formalism.FourierDecayAlt.P.JCx2.mn_ccle_congr ?_ h3) ?_
    · intro g _
      rw [hψ n g, sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
    · rw [norm_neg, norm_one, one_mul]
      linarith [div_le_self (mul_nonneg hK0 hb0) (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1)]
  have hG0 : _root_.Formalism.FourierDecayAlt.B.CCle (A - 1) o F (b + K * b) := _root_.Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono_c hb1 (by nlinarith)
  obtain ⟨C, hC0, hC⟩ := norm_opApply_le_of_polynomial_coeffs_lemma o κ (A - 1) Θ hΘ'
  have hexp : (κ : ℝ) - (A - 1) = -(A - 1 - κ) := by ring
  have hckn : ∀ n : ℕ, _root_.Formalism.FourierDecayAlt.B.CkOn ⊤ (_root_.Formalism.FourierDecayAlt.B.GV P.k P.r) (fun g => cut n g • F g) := by
    intro n
    have h := (_root_.Formalism.FourierDecayAlt.P.JCx2.pd_cut_nice (R := (n : ℝ) + 1) (by positivity) hF).1
    rw [hcutφ n]
    exact h
  unfold _root_.Formalism.FourierDecayAlt.KB.Pl.V
  refine hc₃ P.k P.r Wp Wq p.T.base p.ν' p.m₀ γ (A - 1 - κ) hA
    (fun n => _root_.Formalism.FourierDecayAlt.B.opApply Θ (fun g => cut n g • F g)) (_root_.Formalism.FourierDecayAlt.B.opApply Θ F) (C * (b + K * b))
    (by positivity)
    (fun n => (continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' (hckn n)).mono
      (fun g hg => hg.1))
    ((continuousOn_opApply_of_polynomial_coeffs_lemma_2 o κ Θ hΘ' hF).mono (fun g hg => hg.1))
    (fun n g hg => by
      have := hC _ _ (hGn n) g hg.1
      rwa [hexp] at this)
    (fun g hg => by
      have := hC _ _ hG0 g hg.1
      rwa [hexp] at this) ?_
  intro g _
  set S : _root_.Formalism.FourierDecayAlt.B.Mat P.k P.r → ℝ := fun h => ∑ i, ∑ j, Complex.normSq (h i j) with hS
  have hScont : Continuous S :=
    continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
      Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i))
  have hO : IsOpen {h | S h < S g + 1} := isOpen_lt hScont continuous_const
  obtain ⟨N, hN⟩ := exists_nat_ge (S g + 1)
  apply tendsto_const_nhds.congr'
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  symm
  apply _root_.Formalism.FourierDecayAlt.P.JCTx6.Pos.opApply_congr_open Θ hO _ g (by simp)
  intro h hh
  have hSh : S h < S g + 1 := hh
  have hS0 : 0 ≤ S h := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Complex.normSq_nonneg _
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hscaled : ∑ i, ∑ j, Complex.normSq ((((n : ℝ) + 1)⁻¹ • h) i j) =
      ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h := by
    simp only [hS, Matrix.smul_apply, Complex.real_smul, Complex.normSq_mul,
      Complex.normSq_ofReal, Finset.mul_sum]
  have hle : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1)⁻¹ * S h ≤ 1 := by
    rw [← mul_inv, inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hone : cut n h = 1 := by
    rw [hcut, hscaled, Real.smoothTransition.one_of_one_le (by linarith)]
    simp
  simp only [hone, one_smul]

end GlobalTheory.HatNF
