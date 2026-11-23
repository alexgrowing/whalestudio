import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.ColOfLeftInv

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace WlocSk.UnitaryRepLocal

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

theorem uh_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) :=
  WlocSk.UnitaryGroupBasics.uh_mul ha hb

theorem uh_inv {a : Mx k r} (ha : a ∈ UH (Hpk k r)) :
    a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r) := by
  have hu := WlocSk.UnitaryGroupBasics.isUnit_of_uh ha
  exact ⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, WlocSk.UnitaryGroupBasics.uh_inv ha⟩

theorem hpk_sq : Hpk k r * Hpk k r = 1 := WlocSk.UnitaryGroupBasics.hpk_sq

theorem col_eq (g : Mx k r) (j : Fin (2 * r + k + 1)) : g *ᵥ bvec j = fun i => g i j := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def inB (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance (i : Fin (2 * r + k + 1)) : Decidable (inB k r i) := by unfold inB; infer_instance

def eB (k r : ℕ) (m : Fin k) : Fin (2 * r + k + 1) := ⟨r + m.val, by omega⟩

theorem eB_inj : Function.Injective (eB k r) := by
  intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp [eB] at this; omega

theorem eB_inB (m : Fin k) : inB k r (eB k r m) := by unfold inB eB; simp

theorem eq_eB_of_inB {i : Fin (2 * r + k + 1)} (hi : inB k r i) : i = eB k r ⟨i.val - r, by unfold inB at hi; omega⟩ := by
  apply Fin.ext; unfold inB at hi; simp [eB]; omega

def ub (c : Mx k r) : Matrix (Fin k) (Fin k) ℂ := fun m m' => c (eB k r m) (eB k r m')

theorem blockW_in {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : inB k r i) (hj : inB k r j) :
    blockW k r h i j = h ⟨i.val - r, by unfold inB at hi; omega⟩ ⟨j.val - r, by unfold inB at hj; omega⟩ := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  unfold blockW; rw [dif_pos hi', dif_pos hj']

theorem blockW_in_out {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : inB k r i) (hj : ¬ inB k r j) :
    blockW k r h i j = 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
  unfold blockW; rw [dif_pos hi', dif_neg hj']

theorem blockW_out {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : ¬ inB k r i) :
    blockW k r h i j = if i = j then 1 else 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  unfold blockW; rw [dif_neg hi']

theorem blockW_eB (h : Matrix (Fin k) (Fin k) ℂ) (m m' : Fin k) : blockW k r h (eB k r m) (eB k r m') = h m m' := by
  rw [blockW_in (eB_inB m) (eB_inB m')]
  congr 1 <;> apply Fin.ext <;> simp [eB]

theorem sum_block (F : Fin (2 * r + k + 1) → ℂ) (hF : ∀ l, ¬ inB k r l → F l = 0) :
    ∑ l, F l = ∑ m : Fin k, F (eB k r m) := by
  symm
  refine Finset.sum_of_injOn (eB k r) eB_inj.injOn (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    (fun i _ hi => hF i ?_) (fun _ _ => rfl)
  intro hb
  exact hi ⟨_, by simp, (eq_eB_of_inB hb).symm⟩

theorem blockW_mul (h₁ h₂ : Matrix (Fin k) (Fin k) ℂ) :
    blockW k r (h₁ * h₂) = blockW k r h₁ * blockW k r h₂ := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : inB k r i
  · rw [sum_block _ (fun l hl => by rw [blockW_in_out hi hl, zero_mul])]
    by_cases hj : inB k r j
    · rw [eq_eB_of_inB hi, eq_eB_of_inB hj, blockW_eB, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => by rw [blockW_eB, blockW_eB]
    · rw [blockW_in_out hi hj]
      exact (Finset.sum_eq_zero fun m _ => by rw [blockW_in_out (eB_inB m) hj, mul_zero]).symm
  · rw [blockW_out hi, Finset.sum_eq_single i (fun l _ hl => by rw [blockW_out hi, if_neg (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), blockW_out hi, if_pos rfl, one_mul, blockW_out hi]

theorem hpk_in_col {i m : Fin (2 * r + k + 1)} (hm : inB k r m) : Hpk k r i m = if i = m then 1 else 0 := by
  unfold inB at hm
  unfold Hpk
  by_cases him : i = m
  · subst him; rw [if_pos rfl]
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_neg (by omega)]
  · rw [if_neg him]
    have : i.val ≠ m.val := fun h => him (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by tauto)]

theorem eq_blockW {c : Mx k r} (hc : c ∈ UH (Hpk k r))
    (hfix : ∀ l, ¬ inB k r l → c *ᵥ bvec l = bvec l) : c = blockW k r (ub c) := by
  have hcol : ∀ i l, ¬ inB k r l → c i l = if i = l then 1 else 0 := by
    intro i l hl
    have := congrFun (hfix l hl) i
    simp only [col_eq] at this
    rw [this]; simp [bvec, Pi.single_apply]

  have hHc : ∀ l j, ¬ inB k r l → inB k r j → (Hpk k r * c) l j = 0 := by
    intro l j hl hj
    have hU : cᴴ * Hpk k r * c = Hpk k r := hc
    have e1 := congrFun (congrFun hU l) j
    have e2 : (cᴴ * Hpk k r * c) l j = (Hpk k r * c) l j := by
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single l]
      · rw [Matrix.conjTranspose_apply, hcol l l hl, if_pos rfl, star_one, one_mul]
      · intro m _ hm
        rw [Matrix.conjTranspose_apply, hcol m l hl, if_neg hm, star_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ l) h
    have hne : l ≠ j := fun h => hl (h ▸ hj)
    rw [← e2, e1, hpk_in_col hj, if_neg hne]
  have hoff : ∀ i j, ¬ inB k r i → inB k r j → c i j = 0 := by
    intro i j hi hj
    have hsq : Hpk k r * (Hpk k r * c) = c := by rw [← Matrix.mul_assoc, hpk_sq, Matrix.one_mul]
    rw [← hsq, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : inB k r m
    · have hne : i ≠ m := fun h => hi (h ▸ hm)
      rw [hpk_in_col hm, if_neg hne, zero_mul]
    · rw [hHc m j hm hj, mul_zero]
  ext i j
  by_cases hi : inB k r i
  · by_cases hj : inB k r j
    · rw [eq_eB_of_inB hi, eq_eB_of_inB hj, blockW_eB]; rfl
    · have hne : i ≠ j := fun h => hj (h ▸ hi)
      rw [blockW_in_out hi hj, hcol i j hj, if_neg hne]
  · rw [blockW_out hi]
    by_cases hj : inB k r j
    · have hne : i ≠ j := fun h => hi (h ▸ hj)
      rw [hoff i j hi hj, if_neg hne]
    · exact hcol i j hj

theorem ub_unitary {c : Mx k r} (hc : c ∈ UH (Hpk k r)) (hb : c = blockW k r (ub c)) :
    ub c ∈ UJset (allPos k) := by
  show (ub c)ᴴ * Formalism.REAL.Jm (allPos k) * ub c = Formalism.REAL.Jm (allPos k)
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    unfold Formalism.REAL.Jm allPos; simp
  rw [hJ, Matrix.mul_one]
  have hU : cᴴ * Hpk k r * c = Hpk k r := hc
  ext m m'
  have e := congrFun (congrFun hU (eB k r m)) (eB k r m')
  rw [hpk_in_col (eB_inB m')] at e
  rw [Matrix.one_apply]
  have hin : (eB k r m = eB k r m') ↔ (m = m') := eB_inj.eq_iff
  rw [Matrix.mul_apply] at e
  rw [sum_block _ (fun l hl => by
    have hne : l ≠ eB k r m' := fun h => hl (h ▸ eB_inB m')
    rw [hb, blockW_out hl, if_neg hne, mul_zero])] at e
  rw [Matrix.mul_apply]
  have hterm : ∀ t : Fin k, (cᴴ * Hpk k r) (eB k r m) (eB k r t) * c (eB k r t) (eB k r m') =
      (ub c)ᴴ m t * ub c t m' := by
    intro t
    rw [Matrix.mul_apply, Finset.sum_eq_single (eB k r t)]
    · rw [hpk_in_col (eB_inB t), if_pos rfl, mul_one]; rfl
    · intro l _ hl; rw [hpk_in_col (eB_inB t), if_neg hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hterm] at e
  rw [e]
  by_cases h : m = m'
  · rw [if_pos (hin.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hin.mp h')), if_neg h]

theorem piAll_loc (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) :
    π 1 = 1 ∧ (∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, π (a * b) = (π a).comp (π b)) ∧
      ∀ a ∈ UWset k r z, ∀ x : Wp, ‖π a x‖ = ‖x‖ := by
  obtain ⟨g, hg, hπU⟩ := hπ
  obtain ⟨hgU, hgfix, hgz⟩ := hg
  obtain ⟨-, -, ⟨⟨hπ1, hπmul⟩, hπiso, -⟩, -⟩ := hπU
  have hgi := uh_inv hgU

  have hfixg : ∀ a ∈ UWset k r z, ∀ l, ¬ inB k r l → a *ᵥ (g *ᵥ bvec l) = g *ᵥ bvec l := by
    intro a ha l hl
    unfold inB at hl
    by_cases h1 : l.val < r
    · have hl' : l = eI k r ⟨l.val, h1⟩ := Fin.ext rfl
      rw [hl', (hgfix ⟨l.val, h1⟩).1, (ha.2.1 ⟨l.val, h1⟩).1]
    · by_cases h2 : r + k < l.val
      · have hl' : l = esI k r ⟨2 * r + k - l.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
        rw [hl', (hgfix _).2, (ha.2.1 _).2]
      · have hl' : l = wI k r (Fin.last k) := by apply Fin.ext; simp [wI]; omega
        have hs : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by
          have := Real.sqrt_pos.mpr hT; exact_mod_cast this.ne'
        obtain ⟨t, ht⟩ : ∃ t : ℂ, t = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) := ⟨_, rfl⟩
        rw [← ht] at hgz hs
        have hgw : g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • z := by
          calc g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • (t • g *ᵥ bvec (wI k r (Fin.last k))) := by
                rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
            _ = t⁻¹ • z := by rw [← Matrix.mulVec_smul, hgz]
        rw [hl', hgw, Matrix.mulVec_smul, ha.2.2]
  let hOf : Mx k r → Matrix (Fin k) (Fin k) ℂ := fun a => ub (g⁻¹ * a * g)
  have hstruct : ∀ a ∈ UWset k r z, g⁻¹ * a * g ∈ UH (Hpk k r) ∧
      g⁻¹ * a * g = blockW k r (hOf a) ∧ hOf a ∈ UJset (allPos k) ∧ a = g * blockW k r (hOf a) * g⁻¹ := by
    intro a ha
    have hc : g⁻¹ * a * g ∈ UH (Hpk k r) := uh_mul (uh_mul hgi.2.2 ha.1) hgU
    have hb : g⁻¹ * a * g = blockW k r (hOf a) := by
      refine eq_blockW hc fun l hl => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfixg a ha l hl, Matrix.mulVec_mulVec, hgi.2.1,
        Matrix.one_mulVec]
    refine ⟨hc, hb, ub_unitary hc hb, ?_⟩
    rw [← hb]
    calc a = (g * g⁻¹) * a * (g * g⁻¹) := by rw [hgi.1, Matrix.one_mul, Matrix.mul_one]
      _ = g * (g⁻¹ * a * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
  have hB1 : blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
    ext i j
    by_cases hi : inB k r i
    · by_cases hj : inB k r j
      · rw [blockW_in hi hj, Matrix.one_apply, Matrix.one_apply]
        by_cases h : i = j
        · subst h; simp
        · rw [if_neg h, if_neg]; intro h'; apply h; apply Fin.ext
          have := congrArg Fin.val h'; unfold inB at hi hj; simp at this; omega
      · have hne : i ≠ j := fun h => hj (h ▸ hi)
        rw [blockW_in_out hi hj, Matrix.one_apply, if_neg hne]
    · rw [blockW_out hi, Matrix.one_apply]
  refine ⟨?_, ?_, ?_⟩
  · have := hπ1
    simp only [hB1, Matrix.mul_one, hgi.1] at this
    exact this
  · intro a ha b hb
    obtain ⟨-, hba, hua, ea⟩ := hstruct a ha
    obtain ⟨-, hbb, hub, eb⟩ := hstruct b hb
    have hab : a * b = g * blockW k r (hOf a * hOf b) * g⁻¹ := by
      calc a * b = (g * blockW k r (hOf a) * g⁻¹) * (g * blockW k r (hOf b) * g⁻¹) := by rw [← ea, ← eb]
        _ = g * (blockW k r (hOf a) * blockW k r (hOf b)) * g⁻¹ := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g⁻¹ g, hgi.2.1, Matrix.one_mul]
        _ = g * blockW k r (hOf a * hOf b) * g⁻¹ := by rw [blockW_mul]
    have hm := hπmul _ hua _ hub
    simp only at hm
    rw [hab, hm, ← ea, ← eb]
  · intro a ha x
    obtain ⟨-, -, hua, ea⟩ := hstruct a ha
    rw [ea]
    exact hπiso _ hua x

end WlocSk.UnitaryRepLocal

open WlocSk.UnitaryRepLocal in
theorem representation_unitary : WlocSk.PiUnit := by
  intro k r z u Vp _ _ π hz hT hπ
  obtain ⟨h1, h2, h3⟩ := piAll_loc z u Vp π hz hT hπ
  exact ⟨⟨h1, h2⟩, h3⟩
