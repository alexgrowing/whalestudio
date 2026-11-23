import Formalism.HermitianCurvature.LevelRecursionCondNeeded
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChebyshevExtremalPolynomials
import Mathlib

namespace Formalism.FourierDecayAlt.P.LagrangeExtraction

open Finset Polynomial Formalism.FourierDecayAlt.F7

theorem lagrangeLead : LagrangeLead := by
  intro d y hy V _ _ a
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have : ∀ k : Fin (d + 1), (∑ j, lagCo y j * y j ^ (k : ℕ)) = if k = Fin.last d then 1 else 0 := by
    intro k
    rw [ChebyshevExtremalPolynomials.sum_lagCo_mul_pow y hy k (Nat.lt_succ_iff.mp k.2)]
    simp [Fin.ext_iff]
  simp [this]

theorem extractK : ExtractK := by
  intro V _ _ K
  induction K with
  | zero =>
    intro d s W grid _ _ y₀
    simp
    congr 1
    exact Subsingleton.elim _ _
  | succ K ih =>
    intro d s W grid hP hg y₀
    set c := y₀ (Fin.last K) with hc
    have hP' : PolyStep K d (fun a => s a.castSucc)
        (fun m (y' : Fin K → ℝ) => W m (Fin.snoc (α := fun _ => ℝ) y' c)) := by
      intro a y'
      obtain ⟨cc, h1, h2⟩ := hP a.castSucc (Fin.snoc (α := fun _ => ℝ) y' c)
      refine ⟨cc, by simpa using h1, fun t => ?_⟩
      have := h2 t
      rw [← Fin.snoc_update] at this
      simpa using this
    have ih' := ih d _ _ (fun a => grid a.castSucc) hP' (fun a => hg _) (Fin.init y₀)
    simp only [hc, Fin.snoc_init_self] at ih'
    have hl : ∀ y' : Fin K → ℝ, s (Fin.last K) • W K (Fin.snoc (α := fun _ => ℝ) y' c) =
        ∑ i, ((lagCo (grid (Fin.last K)) i : ℝ) : ℂ) •
          W (K + 1) (Fin.snoc (α := fun _ => ℝ) y' (grid (Fin.last K) i)) := by
      intro y'
      obtain ⟨cc, h1, h2⟩ := hP (Fin.last K) (Fin.snoc (α := fun _ => ℝ) y' c)
      rw [Fin.val_last] at h1 h2
      rw [← h1, ChebyshevExtremalPolynomials.lead_complex (grid (Fin.last K)) (hg _) cc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← h2, Fin.update_snoc_last]
    rw [Fin.prod_univ_castSucc, mul_comm, mul_smul, ih', Finset.smul_sum]
    rw [← (Fin.snocEquiv (fun _ : Fin (K + 1) => Fin (d + 1))).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [smul_comm, ← hc, hl, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : (fun a => grid a (Fin.snocEquiv (fun _ : Fin (K + 1) => Fin (d + 1)) (i, j') a)) =
        Fin.snoc (α := fun _ => ℝ) (fun a : Fin K => grid a.castSucc (j' a)) (grid (Fin.last K) i) := by
      funext a
      refine Fin.lastCases ?_ (fun a => ?_) a <;> simp [Fin.snocEquiv]
    rw [e, smul_smul, Fin.prod_univ_castSucc]
    congr 1
    simp [Fin.snocEquiv]

lemma sum_prod_abs {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ j : Fin K → Fin (d + 1), ∏ a, |lagCo (grid a) (j a)| = ∏ a, ∑ i, |lagCo (grid a) i| := by
  first
  | rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  | exact (Finset.prod_univ_sum (fun a i => |lagCo (grid a) i|)).symm
  | simp [Finset.prod_univ_sum]

lemma norm_le_sum {V : Type} [SeminormedAddCommGroup V] [NormedSpace ℂ V] {K d : ℕ} (s : Fin K → ℂ)
    (W : ℕ → (Fin K → ℝ) → V) (grid : Fin K → Fin (d + 1) → ℝ) (hP : PolyStep K d s W)
    (hg : ∀ a, Function.Injective (grid a)) (y₀ : Fin K → ℝ) :
    (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤
      ∑ j : Fin K → Fin (d + 1), (∏ a, |lagCo (grid a) (j a)|) * ‖W K fun a => grid a (j a)‖ := by
  have h := extractK V K d s W grid hP hg y₀
  calc (∏ a, ‖s a‖) * ‖W 0 y₀‖ = ‖(∏ a, s a) • W 0 y₀‖ := by rw [norm_smul, norm_prod]
    _ = ‖∑ j : Fin K → Fin (d + 1), ((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)‖ := by
        rw [h]
    _ ≤ ∑ j : Fin K → Fin (d + 1), ‖((∏ a, lagCo (grid a) (j a) : ℝ) : ℂ) • W K fun a => grid a (j a)‖ :=
        norm_sum_le _ _
    _ = _ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, Finset.abs_prod]

theorem extractBound : ExtractBound := by
  intro V _ _ K d s W grid hP hg y₀ B hB
  refine (norm_le_sum s W grid hP hg y₀).trans ?_
  rw [← sum_prod_abs, Finset.sum_mul]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_left (hB j) (Finset.prod_nonneg fun a _ => abs_nonneg _)

lemma lagCo_ne_zero {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) (j : Fin (d + 1)) :
    lagCo y j ≠ 0 := by
  unfold lagCo
  refine Finset.prod_ne_zero_iff.mpr fun i hi => inv_ne_zero (sub_ne_zero.mpr fun h => ?_)
  exact (Finset.mem_erase.mp hi).1 (hy h).symm

lemma sum_abs_pos {d : ℕ} (y : Fin (d + 1) → ℝ) (hy : Function.Injective y) :
    0 < ∑ i, |lagCo y i| := Finset.sum_pos' (fun i _ => abs_nonneg _)
    ⟨0, Finset.mem_univ _, abs_pos.mpr (lagCo_ne_zero y hy 0)⟩

theorem extractProb : ExtractProb := by
  intro V _ _ K d s W grid hP hg y₀
  set Pr : ℝ := ∏ a, ∑ i, |lagCo (grid a) i| with hPr
  have hPpos : 0 < Pr := Finset.prod_pos fun a _ => sum_abs_pos (grid a) (hg a)
  have hth : ∀ j, thGrid grid j = (∏ a, |lagCo (grid a) (j a)|) / Pr := by
    intro j; unfold thGrid; rw [Finset.prod_div_distrib]
  have h0 : ∀ j, 0 ≤ thGrid grid j := fun j => by
    rw [hth]; exact div_nonneg (Finset.prod_nonneg fun a _ => abs_nonneg _) hPpos.le
  have h1 : (∑ j, thGrid grid j) = 1 := by
    simp only [hth]
    rw [← Finset.sum_div, sum_prod_abs, div_self hPpos.ne']
  have h3 : (∏ a, ‖s a‖) * ‖W 0 y₀‖ ≤
      Pr * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) := by
    refine (norm_le_sum s W grid hP hg y₀).trans (le_of_eq ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hth]; field_simp
  refine ⟨h0, h1, h3, ?_⟩
  have hL : 0 ≤ (∏ a, ‖s a‖) * ‖W 0 y₀‖ :=
    mul_nonneg (Finset.prod_nonneg fun a _ => norm_nonneg _) (norm_nonneg _)
  have hcs : (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) ^ 2 ≤
      (∑ j, thGrid grid j) * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖ ^ 2) :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun j _ => h0 j)
      (fun j _ => mul_nonneg (h0 j) (sq_nonneg _)) (fun j _ => le_of_eq (by ring))
  rw [h1, one_mul] at hcs
  calc ((∏ a, ‖s a‖) * ‖W 0 y₀‖) ^ 2
      ≤ (Pr * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖)) ^ 2 :=
        pow_le_pow_left₀ hL h3 2
    _ = Pr ^ 2 * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖) ^ 2 := mul_pow _ _ _
    _ ≤ Pr ^ 2 * (∑ j, thGrid grid j * ‖W K fun a => grid a (j a)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)

theorem extractCheb : ExtractCheb := by
  intro V _ _ K d s W α β hd hαβ hP y₀ B hB
  have h := extractBound V K d s W (fun a => Formalism.SA.C.chebPt (α a) (β a) d) hP
    (fun a => (ChebyshevExtremalPolynomials.sharp (α a) (β a) d (hαβ a) hd).1) y₀ B hB
  have e : (∏ a, ∑ i, |lagCo (Formalism.SA.C.chebPt (α a) (β a) d) i|) =
      ∏ a, (1 / 2) * (4 / (β a - α a)) ^ d :=
    Finset.prod_congr rfl fun a _ => (ChebyshevExtremalPolynomials.sharp (α a) (β a) d (hαβ a) hd).2
  rw [← e]
  exact h

end Formalism.FourierDecayAlt.P.LagrangeExtraction

namespace Formalism.FourierDecayAlt.P

theorem lagrange_leading_coeff : Formalism.FourierDecayAlt.F7.LagrangeLead := LagrangeExtraction.lagrangeLead

theorem extract_K_bound : Formalism.FourierDecayAlt.F7.ExtractK := LagrangeExtraction.extractK

theorem extractBound_statement : Formalism.FourierDecayAlt.F7.ExtractBound := LagrangeExtraction.extractBound

theorem extract_probability_bound : Formalism.FourierDecayAlt.F7.ExtractProb := LagrangeExtraction.extractProb

theorem extract_chebyshev_bound : Formalism.FourierDecayAlt.F7.ExtractCheb := LagrangeExtraction.extractCheb

end Formalism.FourierDecayAlt.P
