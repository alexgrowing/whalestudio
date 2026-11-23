import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.AdmissibleLeHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdeleModuleDetDiagUnitsPosIdele

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CuspRep.CuspidalL2GL PositivityTheory.Rg.BcB.D1
open GroundTheory.Automorphic.Reduction
open scoped ENNReal Pointwise

namespace PositivityTheory.Rg.BcB.E1

theorem tor_val {E : Type} [Field E] [NumberField E] {n : ℕ} (x : Fin n → ℝ) : (An.tor E x : GA E n).val =
    diagonal fun i => ((posIdele (K := E) (Real.exp (x i)) (Real.exp_pos _) : (Ad E)ˣ) : Ad E) := coe_diagUnits _ _

theorem degCell_of (h1 : DegBasis) (h2 : DegAdelic) (h3 : DegBdd) (h4 : TorNorm) : DegCell := by
  intro E _ _ _ n Ω₀ hΩ
  have hb : ∀ W : Submodule E (Fin n → E), ∃ C : ℝ, ∀ o ∈ Ω₀, ‖deg o W‖ ≤ C := fun W =>
    hΩ.exists_bound_of_continuousOn ((h3 E n).2 W).continuousOn
  choose c hc using hb
  refine ⟨∑ i : Fin n, |c (Submodule.span E {Pi.single i 1})| + |c ⊤|, fun x o ho => ⟨fun i => ?_, ?_⟩⟩
  · set M : Matrix (Fin n) (Fin 1) E := Matrix.of fun j _ => (Pi.single i 1 : Fin n → E) j with hM
    have hr : Set.range Mᵀ = {Pi.single i 1} := by
      ext v; simp only [Set.mem_range, Set.mem_singleton_iff]
      exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
    have hl : LinearIndependent E Mᵀ := linearIndependent_unique_iff.2 (by
      change (Pi.single i 1 : Fin n → E) ≠ 0
      simp)
    have e := h2 E n 1 o (An.tor E x) (An.tor E fun _ : Fin 1 => x i) M hl (by
      ext j k
      rw [tor_val, tor_val, diagonal_mul, mul_diagonal]
      by_cases h : j = i
      · subst h; simp [hM]
      · simp [hM, h])
    rw [h1 E n 1 _ M hl, h1 E n 1 _ M hl, hr, ((h4 E).2 1 _).1] at e
    rw [e]
    have a1 := Finset.single_le_sum (f := fun i : Fin n => |c (Submodule.span E {Pi.single i 1})|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have a2 := (hc _ o ho).trans (le_abs_self (c (Submodule.span E {Pi.single i 1})))
    simp only [Finset.univ_unique, Finset.sum_singleton, add_sub_cancel_right]
    rw [Real.norm_eq_abs] at a2
    linarith [abs_nonneg (c ⊤)]
  · have hr : Submodule.span E (Set.range (1 : Matrix (Fin n) (Fin n) E)ᵀ) = ⊤ := by
      rw [transpose_one, ← (Pi.basisFun E (Fin n)).span_eq]
      congr 2
      funext i j
      simp [one_apply, Pi.single_apply, eq_comm]
    have hl : LinearIndependent E (1 : Matrix (Fin n) (Fin n) E)ᵀ :=
      Matrix.linearIndependent_cols_iff_isUnit.2 isUnit_one
    have e := h2 E n n o (An.tor E x) (An.tor E x) 1 hl (by
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one, Matrix.one_mul])
    rw [h1 E n n _ 1 hl, h1 E n n _ 1 hl, hr, ((h4 E).2 n _).1] at e
    rw [e, add_sub_cancel_right]
    have a2 := (hc ⊤ o ho).trans (le_abs_self _)
    rw [Real.norm_eq_abs] at a2
    have := Finset.sum_nonneg (s := Finset.univ) (f := fun i : Fin n => |c (Submodule.span E {Pi.single i 1})|)
      fun _ _ => abs_nonneg _
    linarith

theorem redCell_of (h1 : SizeBasic) (h2 : DegBdd) (h3 : DegRat) (h4 : DegRight) (h5 : TorNorm) (h6 : CutBox)
    (h7 : RedBasic) : RedCell := by
  intro E _ _ _ n Ω₀ hΩ
  obtain ⟨s1, s2, -, c, s4⟩ := h1 E n
  obtain ⟨r, hr⟩ := s1 Ω₀ hΩ
  obtain ⟨s, hs⟩ := (h2 E n).1 1
  obtain ⟨C, hC0, hC⟩ := h4 E n
  obtain ⟨C₁, hC₁0, hC₁⟩ := h6 E n Ω₀ hΩ
  set t : ℝ := |s| + |deg (1 : GA E n) ⊤| with ht
  have ht0 : 0 ≤ t := by positivity
  set d : ℝ := (Module.finrank ℚ E : ℝ) with hd
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  set C₂ : ℝ := 1 + C₁ * (1 + t + C) with hC₂
  have hC₂0 : 0 < C₂ := by positivity
  refine ⟨C₂ + (2 * d + |r| + |c|), by positivity, fun x o ho => ⟨?_, ?_⟩⟩
  · have key : ∀ γ, ‖x‖ / C₂ - 1 ≤ logSize (ratGL E n γ * (An.tor E x * o)) := fun γ => by
      set h : GA E n := ratGL E n γ * (An.tor E x * o) with hh
      have h0 := s2 h
      have a := hC₁ x o ho (t + C * (1 + logSize h)) (by positivity) (fun W _ => by
        have b1 := hC 1 h (img γ W)
        rw [one_mul, hh, h3, ← hh] at b1
        have b2 := hs ⟨img γ W, rfl⟩
        linarith [le_abs_self s, abs_nonneg (deg (1 : GA E n) ⊤)]) (by
        have b1 := hC h h⁻¹ ⊤
        have b2 : logSize h⁻¹ = logSize h := by rw [logSize, logSize, inv_inv, add_comm]
        have b3 : deg h ⊤ = deg (An.tor E x * o : GA E n) ⊤ := by rw [← h3 E n (An.tor E x * o) γ ⊤, img_top]
        rw [mul_inv_cancel, b2, b3] at b1
        linarith [neg_abs_le (deg (1 : GA E n) ⊤), abs_nonneg s])
      rw [sub_le_iff_le_add, div_le_iff₀ hC₂0]
      have : 0 ≤ C₁ * (1 + t) * logSize h := by positivity
      nlinarith
    have a : ‖x‖ / C₂ - 1 ≤ red (An.tor E x * o : GA E n) := le_ciInf key
    rw [sub_le_iff_le_add, div_le_iff₀ hC₂0] at a
    have a0 := ((h7 E n).2.1 (An.tor E x * o)).1
    have : 0 ≤ (2 * d + |r| + |c|) * (1 + red (An.tor E x * o : GA E n)) := by positivity
    nlinarith
  · have a1 := ((h7 E n).2.1 (An.tor E x * o)).2
    have a2 := s4 (An.tor E x) o
    have a3 := ((h5 E).2 n x).2
    have a4 := hr o ho
    have : 0 ≤ (C₂ + |r| + |c|) * ‖x‖ := by positivity
    nlinarith [le_abs_self r, le_abs_self c]

section Tor

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def pA (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (s : ℝ) : Ad E := 1 - sInf E 1 + sInf E fun _ => (s : ℂ)

theorem posIdele_val (t : ℝ) : ((posIdele (K := E) (Real.exp t) (Real.exp_pos t) : (Ad E)ˣ) : Ad E) = pA E (Real.exp t) := by
  rw [GlobalTheory.CuspBoundSiegel.posIdele_exp, pA, Complex.ofReal_exp]
  rfl

theorem cV_pA (v : InfinitePlace E) (s : ℝ) : cV v (pA E s) = s := by
  have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
  change pInf E (pA E s) v = s
  simp only [pA, map_add, map_sub, map_one, h, sub_self, zero_add]

theorem cW_pA (w : HeightOneSpectrum (𝓞 E)) (s : ℝ) : cW w (pA E s) = 1 := by
  have h : ∀ x, pFin E (sInf E x) = 0 := fun x => rfl
  change pLoc E w (pFin E (pA E s)) = 1
  simp only [pA, map_add, map_sub, map_one, h, sub_zero, add_zero]

theorem continuous_pA : Continuous (pA E) := by
  refine continuous_const.add ?_
  change Continuous fun s : ℝ => ((infEq E fun _ => (s : ℂ), 0) : InfiniteAdeleRing E × Af E)
  exact ((continuous_infEq E).comp (continuous_pi fun _ => Complex.continuous_ofReal)).prodMk continuous_const

theorem card_places : (2 : ℝ) * Fintype.card (InfinitePlace E) = Module.finrank ℚ E := by
  rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero]
  push_cast
  ring

theorem logAbs_pA (t : ℝ) : logAbs (pA E (Real.exp t)) = Module.finrank ℚ E * t := by
  simp only [logAbs, cV_pA, cW_pA, norm_one, Real.log_one, finsum_zero, add_zero, Complex.norm_real, Real.norm_eq_abs,
    Real.abs_exp, Real.log_pow, Real.log_exp, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← card_places]
  push_cast
  ring

theorem tor_inv {n : ℕ} (x : Fin n → ℝ) : (An.tor E x : GA E n)⁻¹ = An.tor E (-x) := by
  have h0 : (An.tor E (0 : Fin n → ℝ) : GA E n) = 1 := by
    have := JSqIntGlue.tor_add (K := E) (0 : Fin n → ℝ) 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  rw [inv_eq_iff_mul_eq_one, ← JSqIntGlue.tor_add, add_neg_cancel, h0]

theorem logSizeM_tor {n : ℕ} (x : Fin n → ℝ) : logSizeM (An.tor E x : GA E n).val ≤ Module.finrank ℚ E * ‖x‖ := by
  have a1 : ∀ v, Real.posLog (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ 2 * ‖x‖ := fun v => by
    have : (⨆ p : Fin n × Fin n, ‖cV v ((An.tor E x : GA E n).val p.1 p.2)‖ ^ 2) ≤ Real.exp (2 * ‖x‖) := by
      refine Real.iSup_le (fun p => ?_) (Real.exp_pos _).le
      rw [tor_val, diagonal_apply]
      split_ifs
      · rw [posIdele_val, cV_pA, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp, ← Real.exp_nat_mul]
        have := (le_abs_self _).trans (norm_le_pi_norm x p.1)
        exact Real.exp_le_exp.2 (by push_cast; linarith)
      · simp [(Real.exp_pos _).le]
    refine (Real.posLog_le_posLog (Real.iSup_nonneg fun _ => by positivity) this).trans ?_
    rw [Real.posLog_def]
    exact max_le (by positivity) (Real.log_exp _).le
  have a2 : ∀ w, Real.posLog (⨆ p : Fin n × Fin n, ‖cW w ((An.tor E x : GA E n).val p.1 p.2)‖) = 0 := fun w => by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (Real.iSup_nonneg fun _ => norm_nonneg _)]
    refine Real.iSup_le (fun p => ?_) zero_le_one
    rw [tor_val, diagonal_apply]
    split_ifs
    · rw [posIdele_val, cW_pA, norm_one]
    · simp
  simp only [logSizeM, a2, finsum_zero, add_zero]
  refine (Finset.sum_le_sum fun v _ => a1 v).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← card_places]
  ring

end Tor

theorem torNorm_holds : TorNorm := by
  intro E _ _ _
  refine ⟨fun t => by rw [posIdele_val, logAbs_pA], fun n x => ⟨?_, ?_⟩⟩
  · rw [← logAbs_pA, tor_val, det_diagonal]
    simp only [logAbs, map_prod, posIdele_val, cV_pA, cW_pA, Finset.prod_const_one, Real.exp_sum, Complex.ofReal_prod]
  · have := logSizeM_tor (E := E) (-x)
    rw [norm_neg] at this
    rw [logSize, tor_inv]
    linarith [logSizeM_tor (E := E) x]

theorem conjCpt_of (h : AdmLe) : ConjCpt := by
  intro E _ _ _ n ω t₀ hω ht
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  let f : Matrix (Fin n) (Fin n) (Ad E) × (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) (Ad E) :=
    fun p => Matrix.of fun i j => p.1 i j * pA E (p.2 i j)
  have hf : Continuous f := continuous_matrix fun i j =>
    (continuous_fst.matrix_elem i j).mul (continuous_pA.comp ((continuous_apply j).comp ((continuous_apply i).comp continuous_snd)))
  set B := Metric.closedBall (0 : Fin n → Fin n → ℝ) (Real.exp (n * t₀))
  have hB : IsCompact B := isCompact_closedBall _ _
  have k1 := ((hω.1.image Units.continuous_val).prod hB).image hf
  have k2 := (((hω.1.inv.image Units.continuous_val).prod hB).image hf).image MulOpposite.continuous_op
  have key : ∀ x, admitted t₀ x → ∀ c ∈ adelicBorel (K := E) (n := n), ∃ s ∈ B,
      f ((c : GA E n).val, s) = ((An.tor E x : GA E n)⁻¹ * c * An.tor E x).val := by
    intro x hx c hc
    refine ⟨fun i j => if i ≤ j then Real.exp (x j - x i) else 0, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Real.exp_pos _).le]
      intro i
      rw [pi_norm_le_iff_of_nonneg (Real.exp_pos _).le]
      intro j
      split_ifs with hij
      · rw [Real.norm_eq_abs, Real.abs_exp]
        exact Real.exp_le_exp.2 (by linarith [h n t₀ x ht hx i j hij])
      · simp [(Real.exp_pos _).le]
    · ext i j
      rw [tor_inv, Units.val_mul, Units.val_mul, tor_val, tor_val, mul_diagonal, diagonal_mul]
      simp only [f, of_apply]
      split_ifs with hij
      · rw [← posIdele_val, mul_right_comm, ← Units.val_mul, posIdele_mul, mul_comm]
        congr 2
        exact JSqIntGlue.posIdele_congr (by rw [← Real.exp_add, Pi.neg_apply]; ring_nf) _ _
      · have : (c : GA E n).val i j = 0 := hc (not_le.1 hij)
        simp [this]
  refine ⟨_, Units.isClosedEmbedding_embedProduct.isCompact_preimage (k1.prod k2), fun b hb x hx => ⟨?_, ?_⟩⟩
  · obtain ⟨s, hs, e⟩ := key x hx b (hω.2 hb)
    exact ⟨(_, s), ⟨⟨b, hb, rfl⟩, hs⟩, e⟩
  · obtain ⟨s, hs, e⟩ := key x hx b⁻¹ (inv_mem (hω.2 hb))
    refine ⟨_, ⟨(_, s), ⟨⟨b⁻¹, Set.inv_mem_inv.2 hb, rfl⟩, hs⟩, e⟩, ?_⟩
    simp [mul_assoc]

end PositivityTheory.Rg.BcB.E1

end
