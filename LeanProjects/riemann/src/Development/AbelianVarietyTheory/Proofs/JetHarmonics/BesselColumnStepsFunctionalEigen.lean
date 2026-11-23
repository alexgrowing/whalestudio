import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorColumnExpansionUnderLinearMapStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem quantumMinor_columnSteps_partial (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp]
    [Module ℂ Wp] (k r : ℕ)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp)
    (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ) (hE : Formalism.REAL.GlRel E)
    (hp : ∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) →
      (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ =
        (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ)
          else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ
          else 0))
    (w : Fin k → Fin (2 * r + k + 1)) (hw : ∀ i, (w i).val = r + i.val) (j : ℕ) :
    j ≤ r → ∀ (t : ℕ) (a b : Fin t → Fin (2 * r + k + 1)), t = k + j →
      (∀ i, (a i).val = r + i.val) →
      (∀ i, (b i).val = if i.val < k then r + i.val else r + i.val + 1) →
      ∃ c : ℂ, ‖c‖ = (if j = 0 then 1 else τ) ∧ ∀ u v,
        l (Formalism.REAL.qminor E a b u v) = c • l (Formalism.REAL.qminor E w w (u - (j : ℂ)) v) := by
  induction j with
  | zero =>
    intro _ t a b ht ha hb
    obtain rfl : t = k := ht
    have h1 : a = w := funext fun i => Fin.ext (by rw [ha, hw])
    have h2 : b = w := funext fun i => Fin.ext (by rw [hb, hw, if_pos i.isLt])
    refine ⟨1, by simp, fun u v => ?_⟩
    simp [h1, h2]
  | succ j ih =>
    intro hj t a b ht ha hb
    obtain rfl : t = (k + j) + 1 := ht
    obtain ⟨c, hc, hcu⟩ := ih (by omega) (k + j) (fun i => a i.castSucc) (fun i => b i.castSucc) rfl
      (fun i => by simpa using ha i.castSucc) (fun i => by simpa using hb i.castSucc)
    have hai : Function.Injective a := fun x y h => by
      have h' := congrArg Fin.val h
      rw [ha, ha] at h'
      exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y h => by
      have h' := congrArg Fin.val h
      rw [hb, hb] at h'
      exact Fin.ext (by split_ifs at h' <;> omega)
    have hr : ∀ f : Fin (k + j + 1) → Fin (2 * r + k + 1),
        Set.range f = insert (f (Fin.last _)) (Set.range fun i : Fin (k + j) => f i.castSucc) := by
      intro f
      ext x
      simp only [Set.mem_range, Set.mem_insert_iff, Fin.exists_fin_succ', eq_comm, or_comm]
    have hn : ∀ f : Fin (k + j + 1) → Fin (2 * r + k + 1), Function.Injective f →
        f (Fin.last _) ∉ Set.range fun i : Fin (k + j) => f i.castSucc := by
      rintro f hf ⟨i, hi⟩
      exact (Fin.castSucc_lt_last i).ne (hf hi)
    have hal : (a (Fin.last _)).val = r + (k + j) := by rw [ha]; simp
    have hbl : (b (Fin.last _)).val = r + (k + j) + 1 := by rw [hb]; simp
    have hlt : ∀ i, a i < b (Fin.last _) := fun i => by
      have := i.isLt
      rw [Fin.lt_def, ha, hbl]; omega
    have hq := fun i => hp (a i) (b (Fin.last _)) (hlt i) (by rw [hbl]; omega)
    obtain ⟨e, he, heu⟩ := GlobalTheory.T.quantumMinor_column_expansion_under_linearMap M Wp _ (k + j) E l a b (fun i => a i.castSucc)
      (fun i => b i.castSucc) (a (Fin.last _)) (b (Fin.last _))
      (p (a (Fin.last _)) (b (Fin.last _))) hE hai hbi
      (hai.comp (Fin.castSucc_injective _)) (hbi.comp (Fin.castSucc_injective _))
      (hr a) (hn a hai) (hr b) (hn b hbi)
      (by rintro ⟨i, hi⟩; exact (hlt i).ne hi)
      (by
        intro i v
        rw [(hq i).1 v]
        split_ifs with h
        · rw [h]
        · have h0 := (hq i).2
          have hi : (a i).val ≠ r + (k + j) := fun h' => h (Fin.ext (by rw [h', hal]))
          have hi2 := ha i
          rw [hbl, if_neg (by omega), if_neg (by omega)] at h0
          rw [norm_eq_zero.1 h0])
    refine ⟨e * p (a (Fin.last _)) (b (Fin.last _)) * c, ?_, fun u v => ?_⟩
    · have h0 := (hq (Fin.last _)).2
      rw [hal, hbl] at h0
      rw [norm_mul, norm_mul, he, hc, h0]
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simp
        intro h; omega
      · rw [if_pos (by omega), if_neg (by omega), if_neg (by omega)]
        simp
    · rw [heu, hcu, smul_smul]
      congr 4
      push_cast
      ring

theorem qminor_column_chain : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) = c • l (Formalism.REAL.qminor E (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (u - (r : ℂ)) v) := by
  intro M Wp _ _ _ _ k r E l p τ _ hE hp hr
  have h := quantumMinor_columnSteps_partial M Wp k r E l p τ hE hp
    (fun i : Fin k => (⟨r + i.val, by omega⟩ : Fin (2 * r + k + 1))) (fun _ => rfl) r le_rfl (r + k)
    (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
    (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
      by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) (Nat.add_comm _ _) (fun _ => rfl) (fun _ => rfl)
  rw [if_neg (by omega)] at h
  exact h

end GlobalTheory
