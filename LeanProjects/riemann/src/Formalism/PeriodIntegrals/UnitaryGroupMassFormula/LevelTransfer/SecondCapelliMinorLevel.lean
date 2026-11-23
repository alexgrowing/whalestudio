import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.FormalDegreeBessel.FinalG
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelTransfer.LzConjTranspose

open Matrix

noncomputable section

namespace PIQnLT

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k i r' : ℕ}

theorem mulVec_liftVec (M : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (v : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k i r' M *ᵥ liftVec k i r' v = liftVec k i r' (M *ᵥ v) := by
  funext p
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · obtain ⟨a, rfl⟩ : ∃ a, levPos k i r' a = p :=
      ⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩
    rw [liftVec_lev]
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_lev]
    · simp only [ιLev_lev, liftVec_lev]
    · intro q hq
      rw [liftVec_out _ _ hq, mul_zero]
  · rw [liftVec_out _ _ hp]
    simp only [Matrix.mulVec, dotProduct, ιLev_out M p _ hp, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    exact liftVec_out _ _ hp

theorem hpk_mulVec_liftVec (v : Fin (2 * r' + k + 1) → ℂ) :
    Hpk k (i + r') *ᵥ liftVec k i r' v = liftVec k i r' (Hpk k r' *ᵥ v) := by
  funext p
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · obtain ⟨a, rfl⟩ : ∃ a, levPos k i r' a = p :=
      ⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩
    rw [liftVec_lev]
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_lev]
    · simp only [hpk_lev, liftVec_lev]
    · intro q hq
      rw [liftVec_out _ _ hq, mul_zero]
  · rw [liftVec_out _ _ hp]
    simp only [Matrix.mulVec, dotProduct]
    rw [sum_lev]
    · refine Finset.sum_eq_zero fun j _ => ?_
      have hj := j.isLt
      have hjin : i ≤ (levPos k i r' j).val ∧ (levPos k i r' j).val < 2 * r' + k + 1 + i := by rw [lev_val]; omega
      rw [hpk_out_in p (levPos k i r' j) hp hjin, zero_mul]
    · intro q hq
      rw [liftVec_out _ _ hq, mul_zero]

theorem dot_liftVec (w u : Fin (2 * r' + k + 1) → ℂ) :
    star (liftVec k i r' w) ⬝ᵥ liftVec k i r' u = star w ⬝ᵥ u := by
  simp only [dotProduct, Pi.star_apply]
  rw [sum_lev]
  · simp only [liftVec_lev]
  · intro q hq
    rw [liftVec_out _ _ hq, star_zero, zero_mul]

theorem herm_liftVec (v w : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (i + r')) (liftVec k i r' v) (liftVec k i r' w) = herm (Hpk k r') v w := by
  unfold herm
  rw [hpk_mulVec_liftVec, dot_liftVec]

theorem bvec_lev (q : Fin (2 * r' + k + 1)) : bvec (levPos k i r' q) = liftVec k i r' (bvec q) := by
  funext p
  by_cases hp : i ≤ p.val ∧ p.val < 2 * r' + k + 1 + i
  · obtain ⟨a, rfl⟩ : ∃ a, levPos k i r' a = p :=
      ⟨⟨p.val - i, by omega⟩, Fin.ext (by show p.val - i + i = p.val; omega)⟩
    rw [liftVec_lev]
    simp only [bvec, Pi.single_apply, lev_inj.eq_iff]
  · rw [liftVec_out _ _ hp]
    simp only [bvec, Pi.single_apply]
    rw [if_neg]
    rintro rfl
    apply hp
    rw [lev_val]
    have := q.isLt
    omega

theorem fvec_lift (z : Fin (2 * r' + k + 1) → ℂ) :
    fvec k (i + r') (liftVec k i r' z) ⟨i, by omega⟩ = liftVec k i r' (fvec k r' z 0) := by
  simp only [fvec]
  split_ifs with h1 h2 h2
  · rw [← bvec_lev]
    congr 1
    apply Fin.ext
    simp [eI, lev_val]
  · exfalso
    simp only [Fin.val_zero, Fin.val_mk] at h1 h2
    omega
  · exfalso
    simp only [Fin.val_zero, Fin.val_mk] at h1 h2
    omega
  · rfl

theorem ιLev_inv (hL : LevHom) (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (hg : IsUnit g.det) :
    (ιLev k i r' g)⁻¹ = ιLev k i r' g⁻¹ :=
  Matrix.inv_eq_left_inv (by rw [← (hL k i r').2, Matrix.nonsing_inv_mul _ hg, (hL k i r').1])

theorem isUnit_det_of_UH (g : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) (hg : g ∈ UH (Hpk k r')) :
    IsUnit g.det := by
  obtain ⟨_, hI, -⟩ := hpkFacts k r'
  have hU : gᴴ * Hpk k r' * g = Hpk k r' := hg
  exact Matrix.isUnit_det_of_left_inverse (B := Hpk k r' * gᴴ * Hpk k r') (by
    rw [Matrix.mul_assoc (Hpk k r' * gᴴ), Matrix.mul_assoc (Hpk k r'), ← Matrix.mul_assoc gᴴ, hU, hI])

section Ops

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (hL : LevHom)
include hL

theorem chatL_lev {t : ℕ} (pos : Fin t → Fin (2 * r' + k + 1)) (u : ℂ)
    (a β : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → Fin t → ℂ)
    (a' β' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ → Fin t → ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (ha : a (ιLev k i r' x) = a' x) (hb : β (ιLev k i r' x) = β' x) :
    chatL (Formalism.FourierDecayAlt.Q.EH k (i + r')) (levPos k i r' ∘ pos) u a β F (ιLev k i r' x) =
      chatL (Formalism.FourierDecayAlt.Q.EH k r') pos u a' β' (fun y => F (ιLev k i r' y)) x := by
  simp only [chatL]
  rw [ha, hb]
  refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
  rw [Function.comp_assoc, Function.comp_assoc, qminorOp_lev]
  all_goals try exact hL

theorem second_capelli_minor_level {t : ℕ} (pos : Fin t → Fin (2 * r' + k + 1)) (u : ℂ)
    (a a₁ β β₁ : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → Fin t → ℂ)
    (a' a₁' β' β₁' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ → Fin t → ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (ha : a (ιLev k i r' x) = a' x) (ha₁ : a₁ (ιLev k i r' x) = a₁' x)
    (hb : β (ιLev k i r' x) = β' x) (hb₁ : β₁ (ιLev k i r' x) = β₁' x) :
    chat2L (Formalism.FourierDecayAlt.Q.EH k (i + r')) (levPos k i r' ∘ pos) u a a₁ β β₁ F (ιLev k i r' x) =
      chat2L (Formalism.FourierDecayAlt.Q.EH k r') pos u a' a₁' β' β₁' (fun y => F (ιLev k i r' y)) x := by
  simp only [chat2L]
  rw [ha, ha₁, hb, hb₁]
  refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ =>
    Finset.sum_congr rfl fun j₃ _ => Finset.sum_congr rfl fun j₄ _ => ?_
  split_ifs
  · rw [Function.comp_assoc, Function.comp_assoc, qminorOp_lev]
    all_goals try exact hL
  · rfl

omit hL in
theorem pos_comp {t : ℕ} (pos₁ : Fin t → Fin (2 * (i + r') + k + 1)) (pos₂ : Fin t → Fin (2 * r' + k + 1))
    (hpos : ∀ j, pos₁ j = levPos k i r' (pos₂ (Fin.cast rfl j))) : pos₁ = levPos k i r' ∘ pos₂ := by
  funext j
  exact hpos j

theorem capL_cast {t₁ t₂ : ℕ} (h : t₁ = t₂) (pos₁ : Fin t₁ → Fin (2 * (i + r') + k + 1))
    (pos₂ : Fin t₂ → Fin (2 * r' + k + 1)) (hpos : ∀ j, pos₁ j = levPos k i r' (pos₂ (Fin.cast h j))) (u : ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ) :
    qminorOp (Formalism.FourierDecayAlt.Q.EH k (i + r')) pos₁ pos₁ u F (ιLev k i r' x) =
      qminorOp (Formalism.FourierDecayAlt.Q.EH k r') pos₂ pos₂ u (fun y => F (ιLev k i r' y)) x := by
  subst h
  have hp : pos₁ = levPos k i r' ∘ pos₂ := pos_comp pos₁ pos₂ hpos
  subst hp
  rw [qminorOp_lev]
  all_goals try exact hL

theorem chatL_cast {t₁ t₂ : ℕ} (h : t₁ = t₂) (pos₁ : Fin t₁ → Fin (2 * (i + r') + k + 1))
    (pos₂ : Fin t₂ → Fin (2 * r' + k + 1)) (hpos : ∀ j, pos₁ j = levPos k i r' (pos₂ (Fin.cast h j))) (u : ℂ)
    (a β : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → Fin t₁ → ℂ)
    (a' β' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ → Fin t₂ → ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (ha : ∀ j, a (ιLev k i r' x) j = a' x (Fin.cast h j)) (hb : ∀ j, β (ιLev k i r' x) j = β' x (Fin.cast h j)) :
    chatL (Formalism.FourierDecayAlt.Q.EH k (i + r')) pos₁ u a β F (ιLev k i r' x) =
      chatL (Formalism.FourierDecayAlt.Q.EH k r') pos₂ u a' β' (fun y => F (ιLev k i r' y)) x := by
  subst h
  have hp : pos₁ = levPos k i r' ∘ pos₂ := pos_comp pos₁ pos₂ hpos
  subst hp
  exact chatL_lev hL pos₂ u a β a' β' F x (funext fun j => ha j) (funext fun j => hb j)

theorem second_capelli_minor_cast {t₁ t₂ : ℕ} (h : t₁ = t₂) (pos₁ : Fin t₁ → Fin (2 * (i + r') + k + 1))
    (pos₂ : Fin t₂ → Fin (2 * r' + k + 1)) (hpos : ∀ j, pos₁ j = levPos k i r' (pos₂ (Fin.cast h j))) (u : ℂ)
    (a a₁ β β₁ : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → Fin t₁ → ℂ)
    (a' a₁' β' β₁' : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ → Fin t₂ → ℂ)
    (F : Matrix (Fin (2 * (i + r') + k + 1)) (Fin (2 * (i + r') + k + 1)) ℂ → E)
    (x : Matrix (Fin (2 * r' + k + 1)) (Fin (2 * r' + k + 1)) ℂ)
    (ha : ∀ j, a (ιLev k i r' x) j = a' x (Fin.cast h j)) (ha₁ : ∀ j, a₁ (ιLev k i r' x) j = a₁' x (Fin.cast h j))
    (hb : ∀ j, β (ιLev k i r' x) j = β' x (Fin.cast h j)) (hb₁ : ∀ j, β₁ (ιLev k i r' x) j = β₁' x (Fin.cast h j)) :
    chat2L (Formalism.FourierDecayAlt.Q.EH k (i + r')) pos₁ u a a₁ β β₁ F (ιLev k i r' x) =
      chat2L (Formalism.FourierDecayAlt.Q.EH k r') pos₂ u a' a₁' β' β₁' (fun y => F (ιLev k i r' y)) x := by
  subst h
  have hp : pos₁ = levPos k i r' ∘ pos₂ := pos_comp pos₁ pos₂ hpos
  subst hp
  exact second_capelli_minor_level hL pos₂ u a a₁ β β₁ a' a₁' β' β₁' F x (funext fun j => ha j) (funext fun j => ha₁ j)
    (funext fun j => hb j) (funext fun j => hb₁ j)

end Ops

theorem mdim_lev (k i r' : ℕ) : mdim k (i + r') ⟨i, by omega⟩ = mdim k r' 0 := by
  simp only [mdim, Fin.val_zero, Fin.val_mk]
  omega

theorem posL_lev (k i r' : ℕ) (j : Fin (mdim k (i + r') ⟨i, by omega⟩)) :
    posL k (i + r') ⟨i, by omega⟩ j = levPos k i r' (posL k r' 0 (Fin.cast (mdim_lev k i r') j)) := by
  apply Fin.ext
  simp only [posL, lev_val, Fin.coe_cast, Fin.val_zero, Fin.val_mk]
  omega

theorem uC_lev (k i r' : ℕ) (Y : ℂ) : uC k (i + r') ⟨i, by omega⟩ Y = uC k r' 0 Y := by
  unfold uC
  rw [mdim_lev]

end PIQnLT
