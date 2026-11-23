import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.PRVComponents.TensorActionLieRelations

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount

namespace GlobalTheory.CompanionTheory.RealCount.Extremal

variable {n : ℕ}

def permM (w : Equiv.Perm (Fin n)) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => if i = w j then 1 else 0

theorem permM_conjTranspose (w : Equiv.Perm (Fin n)) : (permM w)ᴴ = permM w⁻¹ := by
  ext i j
  simp only [permM, Matrix.conjTranspose_apply, Matrix.of_apply]
  by_cases h : j = w i
  · have h2 : i = w⁻¹ j := by subst h; simp
    rw [if_pos h, if_pos h2]; simp
  · have h2 : ¬ i = w⁻¹ j := fun e => h (by rw [e]; simp)
    rw [if_neg h, if_neg h2]; simp

theorem permM_mul_single (w : Equiv.Perm (Fin n)) (c d : Fin n) :
    permM w * Matrix.single c d (1 : ℂ) = Matrix.single (w c) d 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single c]
  · by_cases h1 : i = w c <;> by_cases h2 : d = j
    · simp [h1, h2]
    · simp [h1, h2]
    · simp [h2, h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1]
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem single_mul_permM (v : Equiv.Perm (Fin n)) (c d : Fin n) :
    Matrix.single c d (1 : ℂ) * permM v = Matrix.single c (v⁻¹ d) 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.single_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single d]
  · by_cases h1 : c = i
    · by_cases h2 : d = v j
      · subst h1 h2; simp
      · subst h1
        have h3 : ¬ v.symm d = j := fun e => h2 (by rw [← e]; simp)
        simp [h2, h3]
    · simp [h1]
  · intro b _ hb
    rw [if_neg (fun q => hb q.2.symm)]; simp
  · simp

theorem permM_single (w : Equiv.Perm (Fin n)) (c d : Fin n) :
    permM w * Matrix.single c d (1 : ℂ) * (permM w)ᴴ = Matrix.single (w c) (w d) 1 := by
  rw [permM_conjTranspose, permM_mul_single, single_mul_permM, inv_inv]

theorem permM_mul (w v : Equiv.Perm (Fin n)) : permM w * permM v = permM (w * v) := by
  ext i j
  simp only [Matrix.mul_apply, permM, Matrix.of_apply]
  rw [Finset.sum_eq_single (v j)]
  · have e : (w * v) j = w (v j) := rfl
    by_cases h : i = w (v j)
    · rw [if_pos h, if_pos rfl, if_pos (h.trans e.symm)]; simp
    · rw [if_neg h, zero_mul, if_neg (fun q => h (q.trans e))]
  · intro b _ hb
    rw [if_neg hb]; simp
  · simp

theorem permM_one : permM (1 : Equiv.Perm (Fin n)) = 1 := by
  ext i j
  simp only [permM, Matrix.of_apply, Matrix.one_apply]
  have e : (1 : Equiv.Perm (Fin n)) j = j := rfl
  by_cases h : i = j
  · rw [if_pos (h.trans e.symm), if_pos h]
  · rw [if_neg (fun q => h (q.trans e)), if_neg h]

theorem Jm_true : ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin n => true) = 1 := by
  simp [ReciprocityTheory.ChartRestriction.DS.Jm]

def permU (w : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := permM w
  inv := permM w⁻¹
  val_inv := by rw [permM_mul, mul_inv_cancel, permM_one]
  inv_val := by rw [permM_mul, inv_mul_cancel, permM_one]

theorem permM_unitary (w : Equiv.Perm (Fin n)) : permM w ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, permM_conjTranspose, permM_mul,
    mul_inv_cancel, permM_one]

def permK (w : Equiv.Perm (Fin n)) : ReciprocityTheory.ChartRestriction.DS.S7.KG (fun _ : Fin n => true) :=
  ⟨⟨permU w, by
      show (permM w)ᴴ * ReciprocityTheory.ChartRestriction.DS.Jm (fun _ : Fin n => true) * permM w = _
      rw [Jm_true, Matrix.mul_one, permM_conjTranspose, permM_mul, inv_mul_cancel, permM_one]⟩,
    by
      show permM w ∈ ReciprocityTheory.ChartRestriction.DS.Kset (fun _ : Fin n => true)
      refine ⟨permM_unitary w, ?_⟩
      rw [Jm_true, Matrix.mul_one, Matrix.one_mul]⟩

theorem toMK_permK (w : Equiv.Perm (Fin n)) : ReciprocityTheory.ChartRestriction.DS.S7.toMK (permK w) = permM w := rfl

theorem conj_single {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : ReciprocityTheory.ChartRestriction.DS.S7.KType ε Λ)
    (k : ReciprocityTheory.ChartRestriction.DS.S7.KG ε) {c d : Fin n} (h : ε c = ε d) :
    T.op k * T.dτ (Matrix.single c d 1) * star (T.op k) =
      T.dτ (ReciprocityTheory.ChartRestriction.DS.S7.toMK k * Matrix.single c d 1 * star (ReciprocityTheory.ChartRestriction.DS.S7.toMK k)) := by
  have h1 := ReciprocityTheory.ChartRestriction.DS.HW.KType.conj_dτ T k (ReciprocityTheory.ChartRestriction.DS.HW.inK_hermitian_unit h)
  have h2 := ReciprocityTheory.ChartRestriction.DS.HW.KType.conj_dτ T k (ReciprocityTheory.ChartRestriction.DS.HW.inK_skew_hermitian_unit h)
  rw [ReciprocityTheory.ChartRestriction.DS.HW.single_eq_kp c d, map_add, map_smul, mul_add, add_mul, mul_smul_comm, smul_mul_assoc,
    h1, h2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul]

theorem unit_translate {Λ : Fin n → ℝ} (T : ReciprocityTheory.ChartRestriction.DS.S7.KType (fun _ : Fin n => true) Λ)
    (w : Equiv.Perm (Fin n)) (c d : Fin n) (v : T.V) :
    T.dτ (Matrix.single (w c) (w d) 1) (T.op (permK w) v) = T.op (permK w) (T.dτ (Matrix.single c d 1) v) := by
  have h := conj_single T (permK w) (c := c) (d := d) rfl
  rw [toMK_permK, Matrix.star_eq_conjTranspose, permM_single] at h
  rw [← h]
  have hu : star (T.op (permK w)) * T.op (permK w) = 1 := Unitary.coe_star_mul_self _
  have e : T.op (permK w) * T.dτ (Matrix.single c d 1) * star (T.op (permK w)) * T.op (permK w) =
      T.op (permK w) * T.dτ (Matrix.single c d 1) := by
    rw [mul_assoc _ (star _), hu, mul_one]
  exact congrArg (fun F : T.V →L[ℂ] T.V => F v) e

theorem extremal_module : ∀ {n : ℕ} (κ : Fin n → ℝ), Antitone κ → ∀ s : ℝ, (∀ a, ∃ m : ℤ, κ a - s = m) →
    ∀ w : Equiv.Perm (Fin n),
    ∃ (Z : Type) (_ : NormedAddCommGroup Z) (_ : InnerProductSpace ℂ Z) (_ : FiniteDimensional ℂ Z)
      (E : Fin n → Fin n → Module.End ℂ Z) (u a : Z),
      Formalism.REAL.GlRel E ∧ (∀ x y (f g : Z), ⟪E x y f, g⟫_ℂ = ⟪f, E y x g⟫_ℂ) ∧ u ≠ 0 ∧
      Formalism.REAL.KHighest (fun _ => true) E κ u ∧
      (∀ W : Submodule ℂ Z, (∀ x y, ∀ f ∈ W, E x y f ∈ W) → u ∈ W → W = ⊤) ∧ a ≠ 0 ∧
      (∀ x, E (w x) (w x) a = ((κ x : ℝ) : ℂ) • a) ∧ ∀ x y, x < y → E (w x) (w y) a = 0 := by
  intro n κ hκ s hs w
  obtain ⟨T⟩ := ReciprocityTheory.ChartRestriction.DS.HW.kType_exists_of_dom (fun _ : Fin n => true) (fun a => κ a - s) hs
    (fun a b hab _ => sub_le_sub_right (hκ hab.le) s)
  set F := ReciprocityTheory.ChartRestriction.DS.HW.kunits T with hF
  set E := ReciprocityTheory.ChartRestriction.DS.HW.endomorphismFamilyShift F (fun _ => s) with hE
  have hEval : ∀ x y (f : T.V), E x y f = T.dτ (Matrix.single x y 1) f + (if x = y then ((s : ℝ) : ℂ) else 0) • f := by
    intro x y f
    simp only [hE, hF, ReciprocityTheory.ChartRestriction.DS.HW.endomorphismFamilyShift, ReciprocityTheory.ChartRestriction.DS.HW.kunits, LinearMap.add_apply,
      LinearMap.smul_apply, Module.End.one_apply, ContinuousLinearMap.coe_coe]
  have hrel : Formalism.REAL.KRel (fun _ : Fin n => true) E :=
    ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kRel (ReciprocityTheory.ChartRestriction.DS.HW.KType.kRel T) (fun _ _ _ => rfl)
  have huni : Formalism.REAL.KUnit (fun _ : Fin n => true) E :=
    ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kUnit (ReciprocityTheory.ChartRestriction.DS.HW.KType.kUnit T) _
  have hhigh : Formalism.REAL.KHighest (fun _ => true) E κ T.w := by
    have h := ReciprocityTheory.ChartRestriction.DS.HW.ext1Shift_kHighest (t := fun _ => s) (ReciprocityTheory.ChartRestriction.DS.HW.KType.kHighest_w T)
    have e : (fun a => κ a - s) + (fun _ => s) = κ := by
      funext a
      simp
    rwa [e] at h
  have hw0 := ReciprocityTheory.ChartRestriction.DS.HW.KType.w_ne_zero T
  set k := permK w with hk
  refine ⟨T.V, inferInstance, inferInstance, inferInstance, E, T.w, T.op k T.w, fun a b c d => hrel a b c d rfl rfl,
    fun x y => huni x y rfl, hw0, hhigh, ?_, ?_, ?_, ?_⟩
  · intro W hW hu
    have hW' : ∀ a b, (fun _ : Fin n => true) a = (fun _ : Fin n => true) b → ∀ v ∈ W,
        T.dτ (Matrix.single a b 1) v ∈ W := by
      intro a b _ v hv
      have h1 := hW a b v hv
      rw [hEval] at h1
      exact (W.add_mem_iff_left (W.smul_mem _ hv)).1 h1
    rcases ReciprocityTheory.ChartRestriction.DS.HW.KType.dτ_irred T W hW' with h | h
    · rw [h, Submodule.mem_bot] at hu
      exact absurd hu hw0
    · exact h
  · intro h0
    have hu : star (T.op k) * T.op k = 1 := Unitary.coe_star_mul_self _
    have := congrArg (fun G : T.V →L[ℂ] T.V => G T.w) hu
    simp only [ContinuousLinearMap.mul_apply, h0, map_zero] at this
    exact hw0 this.symm
  · intro x
    rw [hEval, unit_translate, T.w_wt x, if_pos rfl, map_smul, ← add_smul]
    congr 1
    push_cast
    ring
  · intro x y hxy
    have hne : w x ≠ w y := fun e => (ne_of_lt hxy) (w.injective e)
    rw [hEval, unit_translate, T.w_hw x y hxy rfl, if_neg hne]
    simp

end GlobalTheory.CompanionTheory.RealCount.Extremal
