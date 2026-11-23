import Formalism.HermitianCurvature.CompositeFormulaOfDensities
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HsInnerAddSmulRight

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

section Split

variable {r : ℕ}

def coordinateRestEquiv (l : Fin r) :
    {j : {j : Fin r // l.castSucc.val ≤ j.val} // ¬ (j.1 = l)} ≃ {j : Fin r // l.succ.val ≤ j.val} where
  toFun j := ⟨j.1.1, by
    have h1 := j.1.2; have h2 := j.2
    simp only [Fin.coe_castSucc, Fin.val_succ] at h1 ⊢
    rcases Nat.lt_or_ge l.val j.1.1.val with h | h
    · omega
    · exact absurd (Fin.ext (by omega)) h2⟩
  invFun j := ⟨⟨j.1, by have := j.2; simp only [Fin.coe_castSucc, Fin.val_succ] at *; omega⟩, by
    intro h; have := j.2; rw [h] at this; simp at this⟩
  left_inv j := rfl
  right_inv j := rfl

instance uniqueCoordinateAtLevel (l : Fin r) : Unique {j : {j : Fin r // l.castSucc.val ≤ j.val} // j.1 = l} where
  default := ⟨⟨l, by simp⟩, rfl⟩
  uniq j := Subtype.ext (Subtype.ext j.2)

def coordinateSplit (l : Fin r) : Cf r l.castSucc ≃ᵐ ℂ × Cf r l.succ :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {j : Fin r // l.castSucc.val ≤ j.val} => ℂ)
      (fun j => j.1 = l)).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.piUnique _)
      (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (coordinateRestEquiv l)))

theorem coordinate_split_measurePreserving (l : Fin r) : MeasurePreserving (coordinateSplit l) volume volume := by
  unfold coordinateSplit
  refine MeasurePreserving.trans (volume_preserving_piEquivPiSubtypeProd _ _) ?_
  exact MeasurePreserving.prod (measurePreserving_piUnique _)
    (volume_measurePreserving_piCongrLeft (fun _ => ℂ) (coordinateRestEquiv l))

theorem coordinate_split_fst (l : Fin r) (a : Cf r l.castSucc) : (coordinateSplit l a).1 = a ⟨l, by simp⟩ := by
  rfl

theorem coordinate_split_snd (l : Fin r) (a : Cf r l.castSucc) (j : {j : Fin r // l.succ.val ≤ j.val}) :
    (coordinateSplit l a).2 j = a ⟨j.1, by have := j.2; simp only [Fin.coe_castSucc, Fin.val_succ] at *; omega⟩ := by
  rfl

theorem glue_coordinate_split (l : Fin r) (c : Fin r → ℂ) (a : Cf r l.castSucc) :
    glue l.castSucc c a = glue l.succ (Function.update c l (coordinateSplit l a).1) (coordinateSplit l a).2 := by
  funext j
  rw [coordinate_split_fst]
  unfold glue
  rcases lt_trichotomy j.val l.val with h | h | h
  · have h1 : ¬ (l.castSucc.val ≤ j.val) := by simp only [Fin.val_castSucc]; omega
    have h2 : ¬ (l.succ.val ≤ j.val) := by simp only [Fin.val_succ]; omega
    have h3 : j ≠ l := fun e => by rw [e] at h; omega
    rw [dif_neg h1, dif_neg h2, Function.update_of_ne h3]
  · have hj : j = l := Fin.ext h
    subst hj
    have h2 : ¬ (j.succ.val ≤ j.val) := by simp
    rw [dif_pos (by simp), dif_neg h2, Function.update_self]
  · have h1 : l.castSucc.val ≤ j.val := by simp only [Fin.val_castSucc]; omega
    have h2 : l.succ.val ≤ j.val := by simp only [Fin.val_succ]; omega
    rw [dif_pos h1, dif_pos h2, coordinate_split_snd]

theorem weight_coordinate_split (l : Fin r) (a : Cf r l.castSucc) :
    (∏ j, ‖a j‖ ^ (-2 : ℤ)) = ‖(coordinateSplit l a).1‖ ^ (-2 : ℤ) * ∏ j, ‖(coordinateSplit l a).2 j‖ ^ (-2 : ℤ) := by
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun j : {j : Fin r // l.castSucc.val ≤ j.val} => j.1 = l)]
  congr 1
  · rw [Fintype.prod_unique, coordinate_split_fst]; rfl
  · rw [← (coordinateRestEquiv l).prod_comp]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [coordinate_split_snd]; rfl

def coordinateExtension (i : Fin (r + 1)) (c : Fin r → ℂ) (a : Cf r i) : Cf r 0 := fun j => glue i c a j.1

theorem coordinate_extension_glue (i : Fin (r + 1)) (c : Fin r → ℂ) (a : Cf r i) : glue 0 c (coordinateExtension i c a) = glue i c a := by
  funext j
  simp [glue, coordinateExtension]

theorem coordinate_extension_measurable (i : Fin (r + 1)) (c : Fin r → ℂ) : Measurable (coordinateExtension i c) := by
  refine measurable_pi_lambda _ fun j => ?_
  by_cases h : i.val ≤ j.1.val
  · simp only [coordinateExtension, glue, dif_pos h]; exact measurable_pi_apply _
  · simp only [coordinateExtension, glue, dif_neg h]; exact measurable_const

theorem level_weight_measurable {β : Type} [MeasurableSpace β] (i : Fin (r + 1)) :
    Measurable (fun q : Cf r i × β => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ)) := by
  fun_prop

end Split

section Top

variable {r : ℕ}

instance isEmptyCoordinatesFromLastLevel : IsEmpty {l : Fin r // (Fin.last r).val ≤ l.val} :=
  ⟨fun j => by have h1 := j.2; have h2 := j.1.isLt; simp only [Fin.val_last] at h1; omega⟩

def lastLevelPoint (r : ℕ) : Cf r (Fin.last r) := isEmptyElim

theorem integral_top_level_point {β E : Type} [MeasurableSpace β] [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure β) [SFinite ν]
    (f : Cf r (Fin.last r) × β → E) :
    (Integrable f (volume.prod ν) ↔ Integrable (fun g => f (lastLevelPoint r, g)) ν) ∧
      ∫ q, f q ∂(volume.prod ν) = ∫ g, f (lastLevelPoint r, g) ∂ν := by
  have hv : (volume : Measure (Cf r (Fin.last r))) = Measure.dirac (lastLevelPoint r) := by
    rw [volume_pi]; exact Measure.pi_of_empty _ _
  rw [hv, Measure.dirac_prod]
  exact ⟨(measurableEmbedding_prodMk_left _).integrable_map_iff,
    (measurableEmbedding_prodMk_left _).integral_map _⟩

theorem glue_last_level (c : Fin r → ℂ) (a : Cf r (Fin.last r)) : glue (Fin.last r) c a = c := by
  funext j; have := j.isLt; simp only [glue, Fin.val_last]; rw [dif_neg (by omega)]

theorem weight_last_level (a : Cf r (Fin.last r)) : (∏ l, ‖a l‖ ^ (-2 : ℤ)) = 1 := Finset.prod_of_isEmpty _

end Top

section Dens

theorem sesquilinear_polarization {V : Type} [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ)
    (hl : ∀ (x x' y : V) (a : ℂ), β (x + a • x') y = β x y + a * β x' y)
    (hr : ∀ (x y y' : V) (a : ℂ), β x (y + a • y') = β x y + conj a * β x y') (x y : V) :
    4 * β x y = β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y) + Complex.I * β (x + Complex.I • y) (x + Complex.I • y)
      - β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y) - Complex.I * β (x + (-Complex.I) • y) (x + (-Complex.I) • y) := by
  simp only [hl, hr, map_one, map_neg, Complex.conj_I, neg_neg]
  linear_combination (2 * β x y - 2 * β y x) * Complex.I_mul_I

theorem sesquilinear_polarization_norm {V : Type} [AddCommGroup V] [Module ℂ V] (β : V → V → ℂ)
    (hl : ∀ (x x' y : V) (a : ℂ), β (x + a • x') y = β x y + a * β x' y)
    (hr : ∀ (x y y' : V) (a : ℂ), β x (y + a • y') = β x y + conj a * β x y') (x y : V) :
    ‖β x y‖ ≤ (‖β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y)‖ + ‖β (x + Complex.I • y) (x + Complex.I • y)‖
      + ‖β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y)‖ + ‖β (x + (-Complex.I) • y) (x + (-Complex.I) • y)‖) / 4 := by
  have h := sesquilinear_polarization β hl hr x y
  have h4 : ‖(4 : ℂ) * β x y‖ = 4 * ‖β x y‖ := by simp
  have : ‖(4 : ℂ) * β x y‖ ≤ ‖β (x + (1 : ℂ) • y) (x + (1 : ℂ) • y)‖ + ‖β (x + Complex.I • y) (x + Complex.I • y)‖
      + ‖β (x + (-1 : ℂ) • y) (x + (-1 : ℂ) • y)‖ + ‖β (x + (-Complex.I) • y) (x + (-Complex.I) • y)‖ := by
    rw [h]
    refine (norm_sub_le _ _).trans ?_
    refine add_le_add ((norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add le_rfl ?_)) le_rfl)) ?_
    · simp
    · simp
  linarith

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]
  (L : R.LevelData (Pr (RadSp k r z z' π π')) r) (st : Fr.Start (Pr (RadSp k r z z' π π')))
  (w : List (Letter ℂ S))

theorem top_density_add_left (x x' y : Ix S → RadSp k r z z' π π') (a : ℂ) (c : Fin r → ℂ) (g : Mx k r) :
    topDens L st w (x + a • x') y c g = topDens L st w x y c g + a * topDens L st w x' y c g := by
  simp only [topDens, act_add_smul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hsInner_add_smul_left, Finset.sum_add_distrib, Finset.mul_sum]

theorem top_density_add_right (x y y' : Ix S → RadSp k r z z' π π') (a : ℂ) (c : Fin r → ℂ) (g : Mx k r) :
    topDens L st w x (y + a • y') c g = topDens L st w x y c g + conj a * topDens L st w x y' c g := by
  simp only [topDens, act_add_smul, Pi.add_apply, Pi.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    hsInner_add_smul_right, Finset.sum_add_distrib, Finset.mul_sum]

theorem act_one_hermitian_curvature (x : Ix S → RadSp k r z z' π π') : act (1 : SlopeTestRemainingChoices S (Pr (RadSp k r z z' π π'))) x = x := by
  funext a
  simp only [act, Matrix.one_apply]
  rw [Finset.sum_eq_single a]
  · simp; rfl
  · intro b _ hb; rw [if_neg (Ne.symm hb)]; rfl
  · simp

end Dens

section Meas

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
  {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)} {μ : Measure (Mt P.k P.r)}
  {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r} {st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))}
  {K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')}

theorem level_integrand_aestronglyMeasurable (hM : TopDensMeas S P z z' π π' μ L st K) (w : List (Letter ℂ S))
    (x y : Ix S → RadSp P.k P.r z z' π π') (hx : InK (K (Fin.last P.r)) x) (hy : InK (K (Fin.last P.r)) y)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) :
    AEStronglyMeasurable (fun q : Cf P.r i × Mt P.k P.r => ((∏ l, ‖q.1 l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      topDens L st w x y (glue i c q.1) (Matrix.of q.2)) (volume.prod μ) := by
  have h0 := hM w x y hx hy c
  have e : (fun q : Cf P.r i × Mt P.k P.r => topDens L st w x y (glue i c q.1) (Matrix.of q.2)) =
      (fun q : Cf P.r 0 × Mt P.k P.r => topDens L st w x y (glue 0 c q.1) (Matrix.of q.2)) ∘
        Prod.map (coordinateExtension i c) id := by
    funext q; simp only [Function.comp, Prod.map, coordinate_extension_glue]; rfl
  have h1 : StronglyMeasurable (fun q : Cf P.r i × Mt P.k P.r => topDens L st w x y (glue i c q.1) (Matrix.of q.2)) := by
    rw [e]; exact h0.comp_measurable ((coordinate_extension_measurable i c).prodMap measurable_id)
  exact (level_weight_measurable i).aestronglyMeasurable.mul h1.aestronglyMeasurable

end Meas

end Formalism.FourierDecayAlt.P5
