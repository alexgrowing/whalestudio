import Formalism.HermitianCurvature.HermitianCurvatureProofs.PolynomialDegreeExpansion

namespace Formalism.FourierDecayAlt.P.WordNormLpLemmas

open Finset Polynomial Formalism.FourierDecayAlt.FormPairingAction Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.GramProductIdentities Formalism.FourierDecayAlt.P.DualKernelLemmas Formalism.FourierDecayAlt.P.RealWeightedForms
  Formalism.FourierDecayAlt.P.PolynomialDegreeExpansion
open scoped Matrix

theorem normW_append {S : Type} (nn : ℝ → ℝ) (L w : List (Letter ℂ S)) :
    normW nn (L ++ w) = normW nn L * normW nn w := by
  unfold normW; rw [List.map_append, List.prod_append]

theorem normW_Lp {S : Type} {K : ℕ} (nn : ℝ → ℝ) (sl : Fin K → S) (y : Fin K → ℝ) :
    normW nn (Lp sl y) = ∏ a, nn (y a) := by
  unfold normW Lp
  rw [List.map_ofFn, List.prod_ofFn]
  simp [Function.comp_def]

theorem normW_Lp_dl {S : Type} {K : ℕ} (nn : ℝ → ℝ) (sl : Fin K → S) (y : Fin K → ℝ) :
    normW nn ((Lp sl y).map dl) = ∏ a, nn (y a + 1) := by
  unfold normW Lp
  rw [List.map_ofFn, List.map_ofFn, List.prod_ofFn]
  simp [Function.comp_def, dl]

theorem key (a b Q W N N' T c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hQ : 0 < Q) (hW : 0 < W)
    (hN : 0 < N) (hN' : 0 < N') (hT : 0 ≤ T) (hc : 0 ≤ c) (hNT : N * N' / Q ≤ T ^ 2) :
    c * Real.sqrt (a * b / Q) / W ≤ c * T * ((a / (N * W) + b / (N' * W)) / 2) := by
  have hA : 0 ≤ a / (N * W) := by positivity
  have hB : 0 ≤ b / (N' * W) := by positivity
  have e : a * b / Q = W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * (N * N' / Q) := by
    field_simp
  have hAB : (a / (N * W)) * (b / (N' * W)) ≤ ((a / (N * W) + b / (N' * W)) / 2) ^ 2 := by
    nlinarith [sq_nonneg (a / (N * W) - b / (N' * W))]
  have h1 : a * b / Q ≤ (W * T * ((a / (N * W) + b / (N' * W)) / 2)) ^ 2 := by
    rw [e]
    calc W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * (N * N' / Q)
        ≤ W ^ 2 * ((a / (N * W)) * (b / (N' * W))) * T ^ 2 :=
          mul_le_mul_of_nonneg_left hNT (by positivity)
      _ ≤ W ^ 2 * ((a / (N * W) + b / (N' * W)) / 2) ^ 2 * T ^ 2 := by gcongr
      _ = (W * T * ((a / (N * W) + b / (N' * W)) / 2)) ^ 2 := by ring
  have h2 : Real.sqrt (a * b / Q) ≤ W * T * ((a / (N * W) + b / (N' * W)) / 2) :=
    (Real.sqrt_le_left (by positivity)).mpr h1
  calc c * Real.sqrt (a * b / Q) / W ≤ c * (W * T * ((a / (N * W) + b / (N' * W)) / 2)) / W := by
        gcongr
    _ = c * T * ((a / (N * W) + b / (N' * W)) / 2) := by field_simp

theorem lagCo_ne {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    F7.lagCo y j ≠ 0 := by
  unfold F7.lagCo
  refine Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  exact (Finset.ne_of_mem_erase hi) (hy h).symm

theorem cg_pos {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) : 0 < cg y := by
  unfold cg
  have h0 : 0 < |F7.lagCo y 0| := abs_pos.mpr (lagCo_ne y hy 0)
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun k => |F7.lagCo y k|)
    (fun k _ => abs_nonneg _) (Finset.mem_univ 0))

theorem p1c : NormaliserLowerBound := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid nn Qw BBs hData
    hG0 hImp hinj hadm hnn hQw hBB
  have hu := u72 A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid hData hG0 hImp hinj hadm
  obtain ⟨-, -, -, hK, -, -, -, -, -, -, -⟩ := id hData
  let a0 : Fin K := ⟨0, by omega⟩
  let j0 : Fin K → Fin (2 * n + 1) := fun _ => ⟨0, by omega⟩

  have hlet : ∀ (j : Fin K → Fin (2 * n + 1)) (a : Fin K),
      grid a (j a) ∈ Set.Ioo α β ∧ grid a (j a) + 1 ∈ Set.Ioo α β ∧
        0 < (q (grid a (j a))).re ∧ 0 < (qw q w (grid a (j a))).re := by
    intro j a
    have hm := mem_Lp sl (fun a => grid a (j a)) a
    obtain ⟨-, h2, h3⟩ := (hadm j).1.2.1 _ (List.mem_append_left _ hm)
    simp only [Complex.ofReal_re, if_true] at h2 h3
    refine ⟨h2, h3, (hG0 _ h2).2, ?_⟩
    exact ((admissible_dual_kernel_identity S α β q w _ (plus_Lp sl _) hG0 (hadm j).1 (hadm j).2).2 _ hm).2
  have hWpos : 0 < normW nn w := by
    refine normW_pos nn w fun l hl => hnn _ ?_
    exact ((hadm j0).1.2.1 l (List.mem_append_right _ hl)).2.1
  have hQw0 : 0 ≤ Qw := by
    have h := hQw a0 (j0 a0)
    obtain ⟨-, -, hq, hqw⟩ := hlet j0 a0
    exact le_trans (div_pos hq hqw).le h
  have hBB0 : 0 ≤ BBs := le_trans (Real.sqrt_nonneg _) (hBB a0 (j0 a0))
  set T := (Real.sqrt Qw * BBs) ^ K with hT
  have hT0 : 0 ≤ T := by positivity
  have hpowK : ∀ c : ℝ, c ^ K = ∏ _a : Fin K, c := fun c => by simp
  have hcg : ∀ a, 0 < cg (grid a) := fun a => cg_pos (grid a) (hinj a)

  have hid : ∀ j : Fin K → Fin (2 * n + 1), (∏ a, cg (grid a) * Real.sqrt Qw * BBs) * F7.thGrid grid j =
      (∏ a, |F7.lagCo (grid a) (j a)|) * T := by
    intro j
    unfold F7.thGrid
    rw [← Finset.prod_mul_distrib, hT, hpowK (Real.sqrt Qw * BBs), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    have := (hcg a).ne'
    unfold cg at this ⊢
    field_simp

  have hterm : ∀ j : Fin K → Fin (2 * n + 1),
      (∏ a, |F7.lagCo (grid a) (j a)|) *
        Real.sqrt ((frm ρ (RRw QQ (Lp sl (fun a => grid a (j a)) ++ w))
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)).re *
          (frm ρ (RRw QQ ((Lp sl (fun a => grid a (j a))).map dl ++ w))
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)).re /
          ∏ a, (qw q w (grid a (j a))).re) / normW nn w ≤
      (∏ a, cg (grid a) * Real.sqrt Qw * BBs) *
        (F7.thGrid grid j *
          (N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2) := by
    intro j
    have e : (∏ a, cg (grid a) * Real.sqrt Qw * BBs) *
        (F7.thGrid grid j * (N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2) =
        ((∏ a, cg (grid a) * Real.sqrt Qw * BBs) * F7.thGrid grid j) *
          ((N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2) := by ring
    rw [e, hid j]
    unfold N0
    rw [normW_append, normW_append, normW_Lp, normW_Lp_dl]
    refine key _ _ _ _ _ _ _ _ (hImp _ (hadm j).1 _).1 (hImp _ (hadm j).2 _).1
      (Finset.prod_pos fun a _ => (hlet j a).2.2.2) hWpos
      (Finset.prod_pos fun a _ => hnn _ (hlet j a).1) (Finset.prod_pos fun a _ => hnn _ (hlet j a).2.1)
      hT0 (Finset.prod_nonneg fun a _ => abs_nonneg _) ?_
    have hsq : ((Real.sqrt Qw * BBs) ^ K) ^ 2 = ∏ _a : Fin K, (Real.sqrt Qw * BBs) ^ 2 := by
      rw [← pow_mul, mul_comm K 2, pow_mul, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib, hT, hsq]
    refine Finset.prod_le_prod (fun a _ => ?_) fun a _ => ?_
    · obtain ⟨h1, h2, -, hqw⟩ := hlet j a
      have := hnn _ h1
      have := hnn _ h2
      positivity
    · obtain ⟨h1, h2, hq, hqw⟩ := hlet j a
      have hn1 := hnn _ h1
      have hn2 := hnn _ h2
      have hb := (Real.sqrt_le_left hBB0).mp (hBB a (j a))
      have hqq := hQw a (j a)
      have e2 : nn (grid a (j a)) * nn (grid a (j a) + 1) / (qw q w (grid a (j a))).re =
          (nn (grid a (j a)) * nn (grid a (j a) + 1) / (q (grid a (j a))).re) *
            ((q (grid a (j a))).re / (qw q w (grid a (j a))).re) := by
        field_simp
      rw [e2, mul_pow, Real.sq_sqrt hQw0, mul_comm Qw]
      exact mul_le_mul hb hqq (by positivity) (by positivity)

  have hW := hWpos
  calc ‖s‖ ^ K * (‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w)
      = ‖s‖ ^ K * ‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w := by ring
    _ ≤ (∑ j : Fin K → Fin (2 * n + 1), (∏ a, |F7.lagCo (grid a) (j a)|) *
          Real.sqrt ((frm ρ (RRw QQ (Lp sl (fun a => grid a (j a)) ++ w))
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)).re *
          (frm ρ (RRw QQ ((Lp sl (fun a => grid a (j a))).map dl ++ w))
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)).re /
          ∏ a, (qw q w (grid a (j a))).re)) / normW nn w := by gcongr
    _ = ∑ j : Fin K → Fin (2 * n + 1), (∏ a, |F7.lagCo (grid a) (j a)|) *
          Real.sqrt ((frm ρ (RRw QQ (Lp sl (fun a => grid a (j a)) ++ w))
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)
            (letters vA vB (Lp sl (fun a => grid a (j a))) x)).re *
          (frm ρ (RRw QQ ((Lp sl (fun a => grid a (j a))).map dl ++ w))
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)
            (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)).re /
          ∏ a, (qw q w (grid a (j a))).re) / normW nn w := Finset.sum_div _ _ _
    _ ≤ _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => hterm j

theorem first_polynomial_corollary_identity : SmallParameterNormBound := by
  intro A S V _ _ _ _ _ _ _ _ _ _ ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid nn Qw BBs X hData
    hG0 hImp hinj hAw hadm hnn hQw hBB hX
  obtain ⟨-, hW, hWQ, hK, -, -, hnd, -, -, -, -⟩ := id hData
  have hWpos : 0 < normW nn w := normW_pos nn w fun l hl => hnn _ (hAw.2.1 l hl).2.1
  refine ⟨fun _ => ?_, fun hXs => ?_⟩
  · exact p1a A S V ρ QQ f fi s nn w x hW hWQ hnd (hImp w hAw) fun l hl => hnn _ (hAw.2.1 l hl).2.1
  · have hc := p1c A S V ρ QQ q f fi s w n vA vB vAv vBv K sl x α β grid nn Qw BBs hData hG0 hImp hinj
      hadm hnn hQw hBB
    let a0 : Fin K := ⟨0, by omega⟩
    let j0 : Fin K → Fin (2 * n + 1) := fun _ => ⟨0, by omega⟩
    have hBB0 : 0 ≤ BBs := le_trans (Real.sqrt_nonneg _) (hBB a0 (j0 a0))
    have hfac0 : ∀ a, 0 ≤ cg (grid a) * Real.sqrt Qw * BBs := fun a => by
      have : 0 ≤ cg (grid a) := Finset.sum_nonneg fun k _ => abs_nonneg _
      positivity
    have hX0 : 0 ≤ X := le_trans (hfac0 a0) (hX a0)
    have hs : 0 < ‖s‖ := lt_of_le_of_lt hX0 hXs
    have hprod : ∏ a, cg (grid a) * Real.sqrt Qw * BBs ≤ X ^ K := by
      calc ∏ a, cg (grid a) * Real.sqrt Qw * BBs ≤ ∏ _a : Fin K, X :=
            Finset.prod_le_prod (fun a _ => hfac0 a) fun a _ => hX a
        _ = X ^ K := by simp
    have hsum : 0 ≤ ∑ j : Fin K → Fin (2 * n + 1), F7.thGrid grid j *
          (N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
              (letters vA vB (Lp sl (fun a => grid a (j a))) x) +
            N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
              (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x)) / 2 := by
      refine Finset.sum_nonneg fun j _ => ?_
      have ht : 0 ≤ F7.thGrid grid j := by
        unfold F7.thGrid
        exact Finset.prod_nonneg fun a _ =>
          div_nonneg (abs_nonneg _) (Finset.sum_nonneg fun k _ => abs_nonneg _)
      have hn1 : 0 ≤ N0 ρ QQ nn (Lp sl (fun a => grid a (j a)) ++ w)
          (letters vA vB (Lp sl (fun a => grid a (j a))) x) := by
        unfold N0
        exact div_nonneg (hImp _ (hadm j).1 _).1 (normW_pos nn _ fun l hl =>
          hnn _ ((hadm j).1.2.1 l hl).2.1).le
      have hn2 : 0 ≤ N0 ρ QQ nn ((Lp sl (fun a => grid a (j a))).map dl ++ w)
          (letters vAv vBv ((Lp sl (fun a => grid a (j a))).map dl) x) := by
        unfold N0
        exact div_nonneg (hImp _ (hadm j).2 _).1 (normW_pos nn _ fun l hl =>
          hnn _ ((hadm j).2.2.1 l hl).2.1).le
      positivity
    have h1 := le_trans hc (mul_le_mul_of_nonneg_right hprod hsum)
    rw [div_pow, div_mul_eq_mul_div, le_div_iff₀ (pow_pos hs K)]
    linarith [h1, mul_comm (‖s‖ ^ K)
      (‖frm ρ (RRw QQ w) (act (Vw f s w) x) x‖ / normW nn w)]

theorem first_polynomial_theorem_alt : PlaneWaveBoundAllPlaces := ⟨p1a, first_polynomial_degree, u72, p1c, first_polynomial_corollary_identity⟩

theorem p1cOfParts : NormaliserBoundOfParts := fun _ _ => p1c

theorem first_polynomial_corollary_of_parts : SmallParameterBoundOfParts := fun _ _ => first_polynomial_corollary_identity

theorem first_polynomial_theorem_of_parts : PlaneWaveTheoremOfParts := fun _ _ _ _ _ _ _ _ => first_polynomial_theorem_alt

end Formalism.FourierDecayAlt.P.WordNormLpLemmas

theorem Formalism.FourierDecayAlt.P.first_polynomial_third_clause : Formalism.FourierDecayAlt.FormPairingAction.NormaliserLowerBound := Formalism.FourierDecayAlt.P.WordNormLpLemmas.p1c
theorem Formalism.FourierDecayAlt.P.first_polynomial_corollary : Formalism.FourierDecayAlt.FormPairingAction.SmallParameterNormBound := Formalism.FourierDecayAlt.P.WordNormLpLemmas.first_polynomial_corollary_identity
theorem Formalism.FourierDecayAlt.P.first_polynomial_theorem : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveBoundAllPlaces := Formalism.FourierDecayAlt.P.WordNormLpLemmas.first_polynomial_theorem_alt
theorem Formalism.FourierDecayAlt.P.third_clause_of_parts : Formalism.FourierDecayAlt.FormPairingAction.NormaliserBoundOfParts := Formalism.FourierDecayAlt.P.WordNormLpLemmas.p1cOfParts
theorem Formalism.FourierDecayAlt.P.corollary_of_parts : Formalism.FourierDecayAlt.FormPairingAction.SmallParameterBoundOfParts := Formalism.FourierDecayAlt.P.WordNormLpLemmas.first_polynomial_corollary_of_parts
theorem Formalism.FourierDecayAlt.P.first_polynomial_theorem_of_components : Formalism.FourierDecayAlt.FormPairingAction.PlaneWaveTheoremOfParts :=
  Formalism.FourierDecayAlt.P.WordNormLpLemmas.first_polynomial_theorem_of_parts
