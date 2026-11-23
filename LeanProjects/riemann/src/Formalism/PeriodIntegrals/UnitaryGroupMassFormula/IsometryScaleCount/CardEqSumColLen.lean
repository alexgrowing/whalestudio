import Mathlib
import Formalism.PeriodIntegrals.IsoScaleA

noncomputable section

namespace PI.IsoScaleA.UnitaryGroupMassFormula

open PI.IsoScaleA

theorem card_eq_sum_colLen (μ : YoungDiagram) :
    μ.card = ∑ c : Fin (μ.rowLen 0), μ.colLen c := by
  classical
  rw [← Finset.sum_range (fun j => μ.colLen j)]
  have hmaps : ((μ.cells : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).MapsTo Prod.snd
      (Finset.range (μ.rowLen 0)) := by
    intro x hx
    have hx' : (x.1, x.2) ∈ μ := hx
    have h0 : (0, x.2) ∈ μ := μ.up_left_mem (Nat.zero_le _) le_rfl hx'
    simpa [Finset.mem_range] using YoungDiagram.mem_iff_lt_rowLen.mp h0
  rw [YoungDiagram.card, Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (μ.cells.filter fun x => x.2 = j) =
      (Finset.range (μ.colLen j)).map ⟨fun i => (i, j), fun a b h => by simpa using h⟩ := by
    ext ⟨i, k⟩
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_range]
    constructor
    · rintro ⟨h1, rfl⟩
      exact ⟨i, YoungDiagram.mem_iff_lt_colLen.mp h1, rfl⟩
    · rintro ⟨a, ha, h⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (show (a, j) = (i, k) from h)
      exact ⟨YoungDiagram.mem_iff_lt_colLen.mpr ha, rfl⟩
  rw [this, Finset.card_map, Finset.card_range]

theorem PIJ_scale {Lt T : Type} [Fintype Lt] (tp : Lt → T) {N N' : ℕ} (nu : Lt → YoungDiagram)
    (c s : T → ℂ) (I : ColChoice N' nu) (J : ColChoice N nu) :
    PIJ tp nu (fun τ => c τ * s τ) I J =
      MvPolynomial.C (∏ z : Lt, c (tp z) ^ (nu z).card) * PIJ tp nu s I J := by
  unfold PIJ
  have hdet : ∀ z (cc : Fin ((nu z).rowLen 0)),
      Matrix.det (Matrix.of fun i k : Fin ((nu z).colLen cc) =>
        MvPolynomial.C (c (tp z) * s (tp z)) * MvPolynomial.X ((tp z, I z cc i, J z cc k) : Idx T N N')) =
      MvPolynomial.C (c (tp z)) ^ (nu z).colLen cc *
        Matrix.det (Matrix.of fun i k : Fin ((nu z).colLen cc) =>
          MvPolynomial.C (s (tp z)) * MvPolynomial.X ((tp z, I z cc i, J z cc k) : Idx T N N')) := by
    intro z cc
    have : (Matrix.of fun i k : Fin ((nu z).colLen cc) =>
        MvPolynomial.C (c (tp z) * s (tp z)) * MvPolynomial.X ((tp z, I z cc i, J z cc k) : Idx T N N')) =
        (MvPolynomial.C (c (tp z)) : MvPolynomial (Idx T N N') ℂ) • (Matrix.of fun i k : Fin ((nu z).colLen cc) =>
          MvPolynomial.C (s (tp z)) * MvPolynomial.X ((tp z, I z cc i, J z cc k) : Idx T N N')) := by
      ext i k
      simp [MvPolynomial.C_mul, mul_assoc]
    rw [this, Matrix.det_smul, Fintype.card_fin]
  simp_rw [hdet, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← card_eq_sum_colLen,
    map_prod, map_pow]

theorem applyAt0_C_mul {T : Type} [Fintype T] {N N' : ℕ} (a : ℂ) (P : MvPolynomial (Idx T N N') ℂ)
    (G : VC T N N' → ℂ) : applyAt0 (MvPolynomial.C a * P) G = a * applyAt0 P G := by
  unfold applyAt0
  rw [MvPolynomial.C_mul', Finset.mul_sum]
  rw [Finset.sum_subset MvPolynomial.support_smul]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    ring
  · intro α _ hα
    rw [MvPolynomial.notMem_support_iff.mp hα]
    ring

theorem isoScaleA : IsoScaleA := by
  intro Lt T _ _ _ tp N N' nu c s Θ φ
  funext I
  simp only [AOp, Pi.smul_apply, smul_eq_mul, PIJ_scale, applyAt0_C_mul, mul_assoc]
  rw [mul_finsum]

end PI.IsoScaleA.UnitaryGroupMassFormula
