import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.PSplit

theorem mp_merge {ι α : Type} [Fintype ι] [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    (p q : ι → Prop) [DecidablePred p] [Fintype {i // p i}] [Fintype {i // q i}]
    (hq : ∀ i, q i ↔ ¬ p i) :
    MeasurePreserving (fun x : ({i // p i} → α) × ({i // q i} → α) =>
      fun i => if h : p i then x.1 ⟨i, h⟩ else x.2 ⟨i, (hq i).2 h⟩) volume volume := by
  obtain rfl : q = fun i => ¬ p i := funext fun i => propext (hq i)
  have := (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => α) p).symm
  convert this using 1
  all_goals first | rfl | (congr <;> exact Subsingleton.elim _ _)

theorem mp_comm {A B C D : Type} [MeasureSpace A] [MeasureSpace B] [MeasureSpace C]
    [MeasureSpace D] [SFinite (volume : Measure A)] [SFinite (volume : Measure B)]
    [SFinite (volume : Measure C)] [SFinite (volume : Measure D)] :
    MeasurePreserving (fun x : (A × B) × (C × D) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      volume volume := by
  have h1 := measurePreserving_prodAssoc (volume : Measure A) (volume : Measure B)
    (volume : Measure (C × D))
  have h2 := (MeasurePreserving.id (volume : Measure A)).prod
    (measurePreserving_prodAssoc (volume : Measure B) (volume : Measure C)
      (volume : Measure D)).symm
  have h3 := (MeasurePreserving.id (volume : Measure A)).prod
    ((Measure.measurePreserving_swap (μ := (volume : Measure B)) (ν := (volume : Measure C))).prod
      (MeasurePreserving.id (volume : Measure D)))
  have h4 := (MeasurePreserving.id (volume : Measure A)).prod
    (measurePreserving_prodAssoc (volume : Measure C) (volume : Measure B)
      (volume : Measure D))
  have h5 := (measurePreserving_prodAssoc (volume : Measure A) (volume : Measure C)
    (volume : Measure (B × D))).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem lintegral_shift {A C T : Type} [MeasureSpace A] [MeasureSpace C] [MeasureSpace T]
    [SFinite (volume : Measure A)] [SFinite (volume : Measure C)] [SFinite (volume : Measure T)]
    [AddGroup C] [MeasurableAdd₂ C] [Measure.IsAddRightInvariant (volume : Measure C)]
    (F : (A × C) × T → ℝ≥0∞) (hF : Measurable F) (c : A × T → C) (hc : Measurable c) :
    ∫⁻ x, F x = ∫⁻ y : A × C, ∫⁻ t : T, F ((y.1, y.2 + c (y.1, t)), t) := by
  have hG : Measurable (fun x : (A × C) × T => F ((x.1.1, x.1.2 + c (x.1.1, x.2)), x.2)) := by
    apply hF.comp
    fun_prop
  rw [lintegral_lintegral_swap (f := fun (y : A × C) (t : T) => F ((y.1, y.2 + c (y.1, t)), t))
    hG.aemeasurable, Measure.volume_eq_prod, lintegral_prod_symm _ hF.aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [Measure.volume_eq_prod, lintegral_prod _ (Measurable.aemeasurable (by fun_prop)),
    lintegral_prod (fun y : A × C => F ((y.1, y.2 + c (y.1, t)), t))
      (Measurable.aemeasurable (hG.comp (f := fun y : A × C => (y, t)) (by fun_prop)))]
  refine lintegral_congr fun a => ?_
  exact (lintegral_add_right_eq_self (fun s => F ((a, s), t)) (c (a, t))).symm

theorem sf_pair (ι κ : Type) [Fintype ι] [Fintype κ] :
    SFinite (volume : Measure ((ι → ℂ) × (κ → ℝ))) := inferInstance

theorem sf_rows (ι κ : Type) [Fintype ι] [Fintype κ] :
    SFinite (volume : Measure (ι → κ → ℂ)) := inferInstance

theorem sf_triple (ι ι' κ κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] :
    SFinite (volume : Measure ((ι → ι' → ℂ) × (κ → ℂ) × (κ' → ℝ))) := by
  have := sf_pair κ κ'
  have := sf_rows ι ι'
  exact Measure.prod.instSFinite

theorem inv_pair (ι κ : Type) [Fintype ι] [Fintype κ] :
    Measure.IsAddRightInvariant (volume : Measure ((ι → ℂ) × (κ → ℝ))) :=
  Measure.prod.instIsAddRightInvariant

def merge (k r j : ℕ) (x : PSec k r j × PTop k r j) : PPar k r :=
  (fun a => if h : (a : ℕ) < j then x.1.1 ⟨a, h⟩ else x.2.1 ⟨a, not_lt.1 h⟩,
   fun p => if h : (p.1.1 : ℕ) < j then x.1.2.1 ⟨p, h⟩ else x.2.2.1 ⟨p, not_lt.1 h⟩,
   fun a => if h : (a : ℕ) < j then x.1.2.2 ⟨a, h⟩ else x.2.2.2 ⟨a, not_lt.1 h⟩)

theorem mp_mergeP (k r j : ℕ) : MeasurePreserving (merge k r j) volume volume := by
  have h1 := mp_merge (α := Fin (k + 1) → ℂ) (fun a : Fin r => (a : ℕ) < j)
    (fun a : Fin r => j ≤ (a : ℕ)) (fun _ => not_lt.symm)
  have h2 := mp_merge (α := ℂ) (fun p : UT r => (p.1.1 : ℕ) < j)
    (fun p : UT r => j ≤ (p.1.1 : ℕ)) (fun _ => not_lt.symm)
  have h3 := mp_merge (α := ℝ) (fun a : Fin r => (a : ℕ) < j)
    (fun a : Fin r => j ≤ (a : ℕ)) (fun _ => not_lt.symm)
  have := sf_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  have := sf_pair {p : UT r // j ≤ (p.1.1 : ℕ)} {a : Fin r // j ≤ (a : ℕ)}
  have := sf_pair (UT r) (Fin r)
  have h4 := (h2.prod h3).comp mp_comm
  have h5 := @MeasurePreserving.prod _ _ _ _ _ _ _ _ _ _ _ _ Measure.prod.instSFinite
    Measure.prod.instSFinite _ _ h1 h4
  exact h5.comp mp_comm

theorem cont_pOf (k r : ℕ) : Continuous (fun q : PPar k r => (fun a b => pOf k r q a b : Mt k r)) := by
  refine continuous_pi fun i => continuous_pi fun i' => ?_
  simp only [pOf, pEl, skewM, Rad.herm_Hb]
  split_ifs <;> fun_prop

noncomputable def shift (k r j : ℕ)
    (x : ({a : Fin r // (a : ℕ) < j} → Fin (k + 1) → ℂ) × PTop k r j) :
    ({p : UT r // (p.1.1 : ℕ) < j} → ℂ) × ({a : Fin r // (a : ℕ) < j} → ℝ) :=
  (fun p => if h : j ≤ (p.1.1.2 : ℕ) then
      herm (Hb k) (x.2.1 ⟨p.1.1.2, h⟩) (x.1 ⟨p.1.1.1, p.2⟩) / 2 else 0, 0)

theorem meas_shift (k r j : ℕ) : Measurable (shift k r j) := by
  refine Measurable.prodMk (measurable_pi_lambda _ fun p => ?_) measurable_const
  simp only [Rad.herm_Hb]
  split_ifs <;> fun_prop

theorem herm_zero_left {k : ℕ} (w : Fin (k + 1) → ℂ) : herm (Hb k) 0 w = 0 := by
  simp [Rad.herm_Hb]

theorem herm_zero_right {k : ℕ} (w : Fin (k + 1) → ℂ) : herm (Hb k) w 0 = 0 := by
  simp [Rad.herm_Hb]

theorem mul_eq (k r j : ℕ) (q' : PSec k r j) (q : PTop k r j) :
    pTop k r j q * pSec k r j q' =
      pOf k r (merge k r j ((q'.1, q'.2 + shift k r j (q'.1, q)), q)) := by
  simp only [pTop, pSec, pOf, Rad.pEl_mul, merge]
  congr 1
  · funext a
    by_cases h : (a : ℕ) < j
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  · ext a b
    simp only [Matrix.add_apply, Matrix.of_apply, skewM, shift]
    by_cases ha : (a : ℕ) < j <;> by_cases hb : (b : ℕ) < j
    · have ha' := not_le.2 ha
      have hb' := not_le.2 hb
      simp [ha, hb, ha', hb', herm_zero_left, herm_zero_right]
    · have ha' := not_le.2 ha
      have hb' := not_lt.1 hb
      have hab : a < b := by rw [Fin.lt_def]; omega
      simp [ha, hb, ha', hb', hab, herm_zero_left]
    · have ha' := not_lt.1 ha
      have hb' := not_le.2 hb
      have hab : b < a := by rw [Fin.lt_def]; omega
      simp [ha, hb, ha', hb', hab, hab.not_gt, herm_zero_left]
      rw [← Rad.herm_star]
      simp only [Complex.star_def]
      ring
    · have ha' := not_lt.1 ha
      have hb' := not_lt.1 hb
      simp [ha, hb, ha', hb', herm_zero_left, herm_zero_right]

theorem lintegral_split (k r j : ℕ) (f : Mat k r → ℝ≥0∞)
    (hf : Measurable (fun x : Mt k r => f (Matrix.of x))) :
    ∫⁻ q : PPar k r, f (pOf k r q) =
      ∫⁻ q' : PSec k r j, ∫⁻ q : PTop k r j, f (pTop k r j q * pSec k r j q') := by
  have hg : Measurable (fun q : PPar k r => f (pOf k r q)) :=
    hf.comp (f := fun q : PPar k r => (fun a b => pOf k r q a b : Mt k r))
      (cont_pOf k r).measurable
  have := sf_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  have := sf_triple {a : Fin r // j ≤ (a : ℕ)} (Fin (k + 1)) {p : UT r // j ≤ (p.1.1 : ℕ)}
    {a : Fin r // j ≤ (a : ℕ)}
  have := inv_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  rw [← (mp_mergeP k r j).lintegral_comp hg,
    lintegral_shift (fun x => f (pOf k r (merge k r j x))) (hg.comp (mp_mergeP k r j).measurable) _ (meas_shift k r j)]
  simp only [mul_eq]

end GlobalTheory.Amp.PSplit
