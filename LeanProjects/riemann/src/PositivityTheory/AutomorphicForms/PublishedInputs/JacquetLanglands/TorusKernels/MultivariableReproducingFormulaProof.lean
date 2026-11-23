import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.MultivariableReproducingLemmas

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (by linarith) (sq_nonneg _)
  · exact le_rfl

theorem nrm_pos {I : Type} [Fintype I] (k : I → ℕ) (z : X I) : 0 < nrm k z :=
  Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.2 (z v).2) _

theorem Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w :=
  Finset.prod_nonneg fun _ _ => Real.rpow_nonneg (kap_nonneg _ _) _

theorem norm_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (hk : ∀ v, 1 ≤ k v) (z w : X I) :
    ‖qq k z w‖ * nrm k z = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * nrm k w := by
  simp only [qq, nrm, Kap, norm_prod, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun v _ => hb.2.2.2.2.2.1 (k v) (z v) (w v) (hk v)

theorem cont_qq {I : Type} [Fintype I] (hb : B1b) (k : I → ℕ) (z : X I) : Continuous (qq k z) := by
  unfold qq
  exact continuous_finsetProd _ fun v _ =>
    (hb.2.2.2.2.2.2.2.1 (k v)).comp (continuous_const.prodMk (continuous_apply v))

theorem integrable {I : Type} [Fintype I] (hb : B1b) (hK : KapInt) (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C)
    (z : X I) : Integrable (fun w => qq k z w * f w) := by
  obtain ⟨C1, A, h⟩ := hK I k hk
  obtain ⟨hm, hl, -⟩ := h z
  have hKi : Integrable (Kap k z) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    calc ∫⁻ w, ‖Kap k z w‖ₑ = ∫⁻ w, ENNReal.ofReal (Kap k z w) := by
          congr 1; funext w; exact Real.enorm_eq_ofReal (Kap_nonneg k z w)
      _ ≤ C1 := hl
      _ < ⊤ := ENNReal.coe_lt_top
  have hc : 0 ≤ ∏ v, (((k v : ℝ) - 1) / (4 * Real.pi)) := Finset.prod_nonneg fun v _ => by
    have h4 : (4 : ℝ) ≤ k v := by exact_mod_cast hk v
    exact div_nonneg (by linarith) (by positivity)
  refine (hKi.const_mul ((∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C / nrm k z)).mono'
    ((cont_qq hb k z).mul hf).aestronglyMeasurable (Filter.Eventually.of_forall fun w => ?_)
  have h1 := norm_qq hb k (fun v => le_trans (by norm_num) (hk v)) z w
  have hn := nrm_pos k z
  rw [norm_mul, div_mul_eq_mul_div, le_div_iff₀ hn]
  calc ‖qq k z w‖ * ‖f w‖ * nrm k z = (‖qq k z w‖ * nrm k z) * ‖f w‖ := by ring
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * (‖f w‖ * nrm k w) := by rw [h1]; ring
    _ ≤ (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * Kap k z w * C :=
        mul_le_mul_of_nonneg_left (hC w) (mul_nonneg hc (Kap_nonneg k z w))
    _ = (∏ v, (((k v : ℝ) - 1) / (4 * Real.pi))) * C * Kap k z w := by ring

theorem symm_eq (n : ℕ) (p : P × (Fin n → P)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p = Fin.cons p.1 p.2 := by
  funext j
  induction j using Fin.cases <;> simp [MeasurableEquiv.piFinSuccAbove_symm_apply]

theorem qq_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (z : X (Fin (n + 1))) (t : P) (w : Fin n → P) :
    qq k z (Fin.cons t w) = q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w := by
  simp only [qq, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem nrm_cons {n : ℕ} (k : Fin (n + 1) → ℕ) (t : P) (w : Fin n → P) :
    nrm k (Fin.cons t w : X (Fin (n + 1))) = |t.1.im| ^ ((k 0 : ℝ) / 2) * nrm (fun j => k j.succ) w := by
  simp only [nrm, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem fin_case (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) : ∀ (n : ℕ) (k : Fin n → ℕ), (∀ v, 4 ≤ k v) →
    ∀ f : X (Fin n) → ℂ, SepHol f → ∀ C, (∀ z, ‖f z‖ * nrm k z ≤ C) → ∀ z, ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  intro n
  induction n with
  | zero =>
    intro k hk f hf C hC z
    have hF : (fun w => qq k z w * f w) = fun _ => f z := funext fun w => by
      rw [Subsingleton.elim w z]; simp [qq]
    rw [hF, show (volume : Measure (X (Fin 0))) = Measure.dirac z from Measure.pi_of_empty _ z,
      integral_const]
    simp
  | succ n ih =>
    intro k hk f hf C hC z
    have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure P)) 0
    have hI := integrable hb hK k hk f hf.1 C hC z
    have hG : Integrable (fun p : P × (Fin n → P) =>
        q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 * f (Fin.cons p.1 p.2))
        ((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
      have := (hmp.symm.integrable_comp_emb
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm.measurableEmbedding).2 hI
      refine this.congr (Filter.Eventually.of_forall fun p => ?_)
      simp only [Function.comp_apply, symm_eq, qq_cons]
    have hin : ∀ w : Fin n → P, ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
        f (Fin.cons t w) = qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
      intro w
      have hol : Hol1 fun t => f (Fin.cons t w) := by
        have h := hf.2 (Fin.cons (z 0) w) 0
        convert h using 3 with t
        funext j
        induction j using Fin.cases <;> simp
      have hbd : ∃ C', ∀ t : P, ‖f (Fin.cons t w)‖ * |t.1.im| ^ ((k 0 : ℝ) / 2) ≤ C' := by
        refine ⟨C / nrm (fun j => k j.succ) w, fun t => ?_⟩
        rw [le_div_iff₀ (nrm_pos _ _), mul_assoc, ← nrm_cons]
        exact hC _
      have h := (h3 (k 0) (hk 0) (fun t => f (Fin.cons t w)) hol hbd (z 0)).2
      calc ∫ t, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons t w)
          = ∫ t, qq (fun j => k j.succ) (fun j => z j.succ) w * (q1 (k 0) (z 0) t * f (Fin.cons t w)) := by
            congr 1; funext t; ring
        _ = _ := by rw [integral_const_mul, h]
    have hsep : SepHol fun w : X (Fin n) => f (Fin.cons (z 0) w) := by
      refine ⟨hf.1.comp (continuous_pi fun j => ?_), fun w v => ?_⟩
      · induction j using Fin.cases
        · simpa using continuous_const
        · simpa using continuous_apply _
      · have h := hf.2 (Fin.cons (z 0) w) v.succ
        convert h using 3 with t
        funext j
        induction j using Fin.cases with
        | zero => simp [(Fin.succ_ne_zero v).symm]
        | succ j =>
          simp only [Fin.cons_succ, Function.update_apply, Fin.succ_inj]
          split_ifs <;> simp_all
    have hbd : ∀ w : X (Fin n), ‖f (Fin.cons (z 0) w)‖ * nrm (fun j => k j.succ) w ≤
        C / |(z 0).1.im| ^ ((k 0 : ℝ) / 2) := by
      intro w
      rw [le_div_iff₀ (Real.rpow_pos_of_pos (abs_pos.2 (z 0).2) _), mul_assoc, mul_comm (nrm _ _), ← nrm_cons]
      exact hC _
    calc ∫ w, qq k z w * f w
        = ∫ p, (fun w => qq k z w * f w)
            ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => P) 0).symm p)
            ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) :=
          (hmp.symm.integral_comp' _).symm
      _ = ∫ p : P × (Fin n → P), q1 (k 0) (z 0) p.1 * qq (fun j => k j.succ) (fun j => z j.succ) p.2 *
            f (Fin.cons p.1 p.2) ∂((volume : Measure P).prod (Measure.pi fun _ : Fin n => (volume : Measure P))) := by
          congr 1; funext p; simp only [symm_eq, qq_cons]
      _ = ∫ w : Fin n → P, (∫ t : P, q1 (k 0) (z 0) t * qq (fun j => k j.succ) (fun j => z j.succ) w *
            f (Fin.cons t w)) ∂(Measure.pi fun _ : Fin n => (volume : Measure P)) := integral_prod_symm _ hG
      _ = ∫ w : X (Fin n), qq (fun j => k j.succ) (fun j => z j.succ) w * f (Fin.cons (z 0) w) := by
          congr 1; funext w; exact hin w
      _ = f (Fin.cons (z 0) (fun j => z j.succ)) := ih _ (fun v => hk _) _ hsep _ hbd _
      _ = f z := congrArg f (Fin.cons_self_tail z)

theorem main (ha : B1a) (hb : B1b) (h3 : B3) (hK : KapInt) (I : Type) [Fintype I] (k : I → ℕ)
    (hk : ∀ v, 4 ≤ k v) (f : X I → ℂ) (hf : SepHol f) (C : ℝ) (hC : ∀ z, ‖f z‖ * nrm k z ≤ C) (z : X I) :
    ∫ w, qq k z w * f w = f z := by
  have : SigmaFinite (volume : Measure P) := ha.1
  let σ := Fintype.equivFin I
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin (Fintype.card I) => P) σ
  have hφ : ∀ (w : X I) j, φ w j = w (σ.symm j) := by
    intro w j
    have := Equiv.piCongrLeft_apply_apply (fun _ : Fin (Fintype.card I) => P) σ w (σ.symm j)
    rw [Equiv.apply_symm_apply] at this
    rw [MeasurableEquiv.coe_piCongrLeft]
    exact this
  have hmp : MeasurePreserving φ (volume : Measure (X I)) (volume : Measure (X (Fin (Fintype.card I)))) :=
    measurePreserving_piCongrLeft (fun _ : Fin (Fintype.card I) => (volume : Measure P)) σ
  have hsep : SepHol fun w' : X (Fin (Fintype.card I)) => f fun i => w' (σ i) := by
    refine ⟨hf.1.comp (continuous_pi fun i => continuous_apply _), fun w' j => ?_⟩
    have h := hf.2 (fun i => w' (σ i)) (σ.symm j)
    convert h using 3 with t
    funext i
    simp only [Function.update_apply, Equiv.eq_symm_apply]
    split_ifs <;> rfl
  have hnrm : ∀ w' : X (Fin (Fintype.card I)), nrm (fun j => k (σ.symm j)) w' = nrm k fun i => w' (σ i) := by
    intro w'
    exact Fintype.prod_equiv σ.symm _ _ fun j => by simp
  have hbd : ∀ w' : X (Fin (Fintype.card I)), ‖f fun i => w' (σ i)‖ * nrm (fun j => k (σ.symm j)) w' ≤ C := by
    intro w'; rw [hnrm]; exact hC _
  have hqq : ∀ w : X I, qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) (φ w) = qq k z w := by
    intro w
    simp only [qq, hφ]
    exact Fintype.prod_equiv σ.symm _ _ fun _ => rfl
  calc ∫ w, qq k z w * f w
      = ∫ w, (fun w' : X (Fin (Fintype.card I)) => qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' *
          f fun i => w' (σ i)) (φ w) := by
        congr 1; funext w; simp only [hqq, hφ, Equiv.symm_apply_apply]
    _ = ∫ w', qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i) :=
        hmp.integral_comp' (fun w' : X (Fin (Fintype.card I)) =>
          qq (fun j => k (σ.symm j)) (fun j => z (σ.symm j)) w' * f fun i => w' (σ i))
    _ = f fun i => z (σ.symm (σ i)) := fin_case ha hb h3 hK _ _ (fun v => hk _) _ hsep C hbd _
    _ = f z := by simp only [Equiv.symm_apply_apply]

end UpperTheory.Esk.MultivariableReproducingLemmas

open UpperTheory.Esk.MultivariableReproducingLemmas in
theorem UpperTheory.Esk.multivariable_reproducing_formula_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B3 → UpperTheory.Esk.KapInt → UpperTheory.Esk.MultivariableReproducingFormula := by
  intro ha hb h3 hK I _ k hk f hf hC z
  obtain ⟨C, hC⟩ := hC
  exact ⟨integrable hb hK k hk f hf.1 C hC z, main ha hb h3 hK I k hk f hf C hC z⟩
