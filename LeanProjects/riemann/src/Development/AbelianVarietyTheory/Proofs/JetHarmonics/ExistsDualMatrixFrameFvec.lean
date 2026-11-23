import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.BasicLiftAll

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.DualFrame

theorem exists_linearIndependent_extend {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (v : Fin n → V)
    (hv : LinearIndependent ℂ v) (m : ℕ) (hm : n + m ≤ Module.finrank ℂ V) :
    ∃ w : Fin (n + m) → V, LinearIndependent ℂ w ∧ ∀ j, w (Fin.castAdd m j) = v j := by
  induction m with
  | zero => exact ⟨v, hv, fun j => rfl⟩
  | succ m ih =>
    obtain ⟨w, hw, hwv⟩ := ih (by omega)
    have hx : ∃ x, x ∉ Submodule.span ℂ (Set.range w) := by
      by_contra h
      have htop : Submodule.span ℂ (Set.range w) = ⊤ :=
        eq_top_iff.mpr (fun x _ => by_contra (fun hx => h ⟨x, hx⟩))
      have h1 := finrank_range_le_card (R := ℂ) (b := w)
      rw [Set.finrank, htop, finrank_top, Fintype.card_fin] at h1
      omega
    obtain ⟨x, hx⟩ := hx
    refine ⟨Fin.snoc (α := fun _ => V) w x, linearIndependent_finSnoc.mpr ⟨hw, hx⟩, fun j => ?_⟩
    have hj : (Fin.castAdd (m + 1) j : Fin (n + (m + 1))) = Fin.castSucc (Fin.castAdd m j) := Fin.ext rfl
    rw [hj, Fin.snoc_castSucc, hwv]

theorem linearIndependent_fvec (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z') (h0 : z' ≠ 0) :
    LinearIndependent ℂ (fvec k r z') := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hs : ∀ d, ∑ i : Fin r, g (Fin.castSucc i) * bvec (eI k r i) d + g (Fin.last r) * z' d = 0 := by
    intro d
    have := congrFun hg d
    rw [Fin.sum_univ_castSucc] at this
    simpa [fvec] using this
  have hlast : g (Fin.last r) = 0 := by
    obtain ⟨d, hd⟩ := Function.ne_iff.mp h0
    have hd' : r ≤ d.val := by
      by_contra hlt
      exact hd (hz d (Or.inl (by omega)))
    have := hs d
    have hb : ∀ i : Fin r, bvec (eI k r i) d = 0 := by
      intro i
      have hne : d ≠ eI k r i := by
        intro h
        have := congrArg Fin.val h
        simp [eI] at this
        omega
      simp [bvec, hne]
    simp only [hb, mul_zero, Finset.sum_const_zero, zero_add] at this
    exact (mul_eq_zero.mp this).resolve_right hd
  intro i
  refine Fin.lastCases hlast (fun a => ?_) i
  have := hs (eI k r a)
  rw [hlast, zero_mul, add_zero] at this
  rw [Finset.sum_eq_single a] at this
  · simpa [bvec] using this
  · intro b _ hb
    have hne : eI k r a ≠ eI k r b := by
      intro h
      apply hb
      have := congrArg Fin.val h
      simp [eI] at this
      exact Fin.ext this.symm
    simp [bvec, hne]
  · simp

theorem exists_dual_matrix (k r : ℕ) (z' : Fin (2 * r + k + 1) → ℂ)
    (e : Fin (r + 1 + (r + k)) ≃ Fin (2 * r + k + 1)) (hz : inWb k r z') (hT : 0 < Tz k r z') :
    ∃ Q : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ, Q.det ≠ 0 ∧
      (∀ (i j : Fin (r + 1)), ∑ d, Q (Fin.castAdd (r + k) i) d * fvec k r z' j (e d) = if i = j then 1 else 0) ∧
      ∀ (i : Fin (r + k)) (j : Fin (r + 1)), ∑ d, Q (Fin.natAdd (r + 1) i) d * fvec k r z' j (e d) = 0 := by
  have hz0 : z' ≠ 0 := by
    rintro rfl
    simp [Tz, herm] at hT
  have hli := linearIndependent_fvec k r z' hz hz0
  set u : Fin (r + 1) → Fin (r + 1 + (r + k)) → ℂ := fun j d => fvec k r z' j (e d) with hu
  have hul : LinearIndependent ℂ u :=
    hli.map' (LinearEquiv.funCongrLeft ℂ ℂ e).toLinearMap (LinearEquiv.ker _)
  obtain ⟨w, hw, hwu⟩ := exists_linearIndependent_extend u hul (r + k)
    (by rw [Module.finrank_fin_fun])
  set A : Matrix (Fin (r + 1 + (r + k))) (Fin (r + 1 + (r + k))) ℂ := Matrix.of w with hA
  have hAu : IsUnit A := Matrix.linearIndependent_rows_iff_isUnit.mp hw
  have hdet : IsUnit A.transpose.det := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det A).mp hAu
  have hQ : (A.transpose)⁻¹ * A.transpose = 1 := Matrix.nonsing_inv_mul _ hdet
  have hcol : ∀ (i : Fin (r + 1 + (r + k))) (j : Fin (r + 1)),
      ∑ d, (A.transpose)⁻¹ i d * fvec k r z' j (e d) = if i = Fin.castAdd (r + k) j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hQ i) (Fin.castAdd (r + k) j)
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp [hA, hwu, hu]
  refine ⟨(A.transpose)⁻¹, ?_, fun i j => ?_, fun i j => ?_⟩
  · intro h
    have := congrArg Matrix.det hQ
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  · rw [hcol]
    simp [Fin.castAdd_inj]
  · rw [hcol]
    have : Fin.natAdd (r + 1) i ≠ Fin.castAdd (r + k) j := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [this]

end GlobalTheory.HatNF.DualFrame
