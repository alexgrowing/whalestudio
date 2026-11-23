import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemConjSub
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemIntegralGLIffIntegralUnitDet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocalFieldUniformizerNormProperties
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.QIndex
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.QIndex.ConjLe

section Field

variable {F : Type} [Field F]

theorem det_eq_one_add (O : Subring F) {c : F} (hc : c ∈ O) {n : ℕ}
    {g : Matrix (Fin n) (Fin n) F} (h : Lvl O c (g - 1)) : ∃ o ∈ O, g.det = 1 + c * o := by
  classical
  have hint : IsInt O g := fun i j => by
    obtain ⟨o, ho, e⟩ := h i j
    have e' : g i j = (1 : Matrix (Fin n) (Fin n) F) i j + c * o := by
      rw [← e]; simp
    rw [e']
    refine O.add_mem ?_ (O.mul_mem hc ho)
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact O.one_mem
    · rw [Matrix.one_apply_ne hij]; exact O.zero_mem
  let M : Matrix (Fin n) (Fin n) O := fun i j => ⟨g i j, hint i j⟩
  have hM : O.subtype.mapMatrix M = g := by
    ext i j; rfl
  let c' : O := ⟨c, hc⟩
  let π := Ideal.Quotient.mk (Ideal.span {c'})
  have hc0 : π c' = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self c')
  have hπ : π.mapMatrix M = 1 := by
    ext i j
    obtain ⟨o, ho, e⟩ := h i j
    have e' : M i j = (1 : Matrix (Fin n) (Fin n) O) i j + c' * ⟨o, ho⟩ := by
      apply Subtype.ext
      have e2 : g i j = (1 : Matrix (Fin n) (Fin n) F) i j + c * o := by
        rw [← e]; simp
      by_cases hij : i = j
      · subst hij; rw [Matrix.one_apply_eq] at e2 ⊢; simpa [M, c'] using e2
      · simpa [M, c', hij] using e2
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, e', map_add, map_mul, hc0, zero_mul, add_zero]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · simp [hij]
  have hdet : π (M.det - 1) = 0 := by
    rw [map_sub, RingHom.map_det, hπ, Matrix.det_one, map_one, sub_self]
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hdet)
  refine ⟨a, a.2, ?_⟩
  have h1 : (O.subtype M.det) = g.det := by
    rw [RingHom.map_det, hM]
  have h2 : (a : F) * c = (M.det : F) - 1 := by
    simpa [c'] using congrArg Subtype.val ha
  have h3 : (M.det : F) = g.det := h1
  rw [← h3]
  linear_combination -h2

theorem diag_inv {n : ℕ} (g : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) :
    (∀ a, dd a ≠ 0) ∧
      ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = diagonal fun a => (dd a)⁻¹ := by
  have hmul : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul]; simp
  have hne : ∀ a, dd a ≠ 0 := fun a => by
    have h1 := congrFun (congrFun hmul a) a
    rw [hD, diagonal_mul, one_apply_eq] at h1
    exact left_ne_zero_of_mul_eq_one h1
  refine ⟨hne, ?_⟩
  have h2 : (diagonal fun a => (dd a)⁻¹) * (g : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [hD, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext a
    exact inv_mul_cancel₀ (hne a)
  calc ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
      = ((diagonal fun a => (dd a)⁻¹) * (g : Matrix (Fin n) (Fin n) F)) *
          ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by rw [h2, Matrix.one_mul]
    _ = diagonal fun a => (dd a)⁻¹ := by rw [Matrix.mul_assoc, hmul, Matrix.mul_one]

theorem conj_entry {n : ℕ} (g p : GL (Fin n) F) {dd : Fin n → F}
    (hD : (g : Matrix (Fin n) (Fin n) F) = diagonal dd) (a b : Fin n) :
    (((g * p * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1) a b =
      dd a * ((p : Matrix (Fin n) (Fin n) F) - 1) a b * (dd b)⁻¹ := by
  obtain ⟨-, hE⟩ := diag_inv g hD
  have hmul : (g : Matrix (Fin n) (Fin n) F) * ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 := by
    rw [← Units.val_mul]; simp
  have h1 : ((g * p * g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 =
      (g : Matrix (Fin n) (Fin n) F) * ((p : Matrix (Fin n) (Fin n) F) - 1) *
        ((g⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    rw [Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hmul]
  rw [h1, hE, Matrix.mul_diagonal, hD, diagonal_mul]

end Field

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}

theorem mem_congGL_of_lvl (hLF : LF O ϖ nrm q) {n T : ℕ} (hT : 1 ≤ T) (g : GL (Fin n) F)
    (h : Lvl O (ϖ ^ T) ((g : Matrix (Fin n) (Fin n) F) - 1)) : g ∈ congGL O (ϖ ^ T) n := by
  obtain ⟨-, hpi, hle, hlt, -, hult, -⟩ := GlobalTheory.T.localField_uniformizer_norm_properties hLF
  have hc : ϖ ^ T ∈ O := O.pow_mem hpi T
  refine ⟨(GlobalTheory.CompanionTheory.QLDet.mem_GLint_iff hLF n g).2 ⟨fun i j => ?_, ?_⟩, h⟩
  · obtain ⟨o, ho, e⟩ := h i j
    have e' : (g : Matrix (Fin n) (Fin n) F) i j = (1 : Matrix (Fin n) (Fin n) F) i j + ϖ ^ T * o := by
      rw [← e]; simp
    rw [e']
    refine O.add_mem ?_ (O.mul_mem hc ho)
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq]; exact O.one_mem
    · rw [Matrix.one_apply_ne hij]; exact O.zero_mem
  · obtain ⟨o, ho, e⟩ := det_eq_one_add O hc h
    rw [e]
    have hy : nrm (ϖ ^ T * o) < 1 := by
      refine (hlt _).2 ⟨ϖ ^ (T - 1) * o, O.mul_mem (O.pow_mem hpi _) ho, ?_⟩
      obtain ⟨k, rfl⟩ : ∃ k, T = k + 1 := ⟨T - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    apply le_antisymm
    · refine (hult _ _).trans (max_le ?_ hy.le)
      simp
    · by_contra hcon
      have hcon' : nrm (1 + ϖ ^ T * o) < 1 := not_le.1 hcon
      have h1 := hult (1 + ϖ ^ T * o) (-(ϖ ^ T * o))
      rw [add_neg_cancel_right, map_one, map_neg_eq_map] at h1
      exact absurd h1 (not_le.2 (max_lt hcon' hy))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ (n : ℕ) (β : Fin n → ℕ) (Q : Subgroup (GL (Fin n) F)), (∀ g, g ∈ Q ↔ (g : Matrix (Fin n) (Fin n) F).BlockTriangular β) → ∀ T : ℕ, 1 ≤ T → ∀ d : Q, ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).IsDiag → (∀ a b, ϖ ^ T * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) b b)⁻¹) ∈ O) → conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ≤ (congGL O (ϖ ^ T) n).subgroupOf Q ∧ ∀ p ∈ (congGL O (ϖ ^ T) n).subgroupOf Q, (p ∈ conjSub ((congGL O (ϖ ^ (2 * T)) n).subgroupOf Q) d ↔ ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) - 1 ∈ boxAdd O β (lev ϖ T fun a => ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a)) := by
  intro F _ _ _ _ O ϖ nrm q hLF n β Q hQ T hT d hdiag hd
  have hD : ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      diagonal fun a => ((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a :=
    hdiag.diagonal_diag.symm
  obtain ⟨hne, -⟩ := diag_inv (d : GL (Fin n) F) hD
  have hent := fun (p : GL (Fin n) F) => conj_entry (d : GL (Fin n) F) p hD
  have hconj : ∀ p : Q, ((d * p * d⁻¹ : Q) : GL (Fin n) F) =
      (d : GL (Fin n) F) * (p : GL (Fin n) F) * (d : GL (Fin n) F)⁻¹ := fun p => rfl
  have h2T : 1 ≤ 2 * T := by omega
  refine ⟨fun p hp => ?_, fun p _ => ?_⟩
  · rw [mem_conjSub, Subgroup.mem_subgroupOf, hconj] at hp
    rw [Subgroup.mem_subgroupOf]
    refine mem_congGL_of_lvl hLF hT _ fun a b => ?_
    obtain ⟨o, ho, e⟩ := hp.2 a b
    rw [hent] at e
    refine ⟨o * (ϖ ^ T * (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) b b *
      (((d : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a a)⁻¹)), O.mul_mem ho (hd b a), ?_⟩
    have hna := hne a
    have hnb := hne b
    field_simp at e ⊢
    linear_combination e
  · rw [mem_conjSub, Subgroup.mem_subgroupOf, hconj]
    constructor
    · intro hp
      refine ⟨((hQ _).1 p.2).sub (blockTriangular_one), fun a b => ?_⟩
      obtain ⟨o, ho, e⟩ := hp.2 a b
      rw [hent] at e
      refine ⟨o, ho, ?_⟩
      have hna := hne a
      have hnb := hne b
      simp only [lev]
      field_simp at e ⊢
      linear_combination e
    · rintro ⟨-, hx⟩
      refine mem_congGL_of_lvl hLF h2T _ fun a b => ?_
      obtain ⟨o, ho, e⟩ := hx a b
      refine ⟨o, ho, ?_⟩
      rw [hent, e]
      have hna := hne a
      have hnb := hne b
      simp only [lev]
      field_simp

end GlobalTheory.CompanionTheory.QL.QIndex.ConjLe
