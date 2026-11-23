import Mathlib

set_option autoImplicit false

namespace GlobalTheory.SatMinor

variable {p : ℕ} [Fact p.Prime]

theorem mem_int_iff (x : ℂ_[p]) : x ∈ PadicComplexInt p ↔ ‖x‖ ≤ 1 := by
  rw [PadicComplex.norm_eq_norm]
  unfold PadicComplexInt
  rw [Valuation.mem_valuationSubring_iff]
  simp [Valuation.norm_def]

theorem isUnit_int_iff (x : PadicComplexInt p) : IsUnit x ↔ ‖(x : ℂ_[p])‖ = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have h1 : ‖((u : PadicComplexInt p) : ℂ_[p])‖ ≤ 1 := (mem_int_iff _).1 (u : PadicComplexInt p).2
    have h2 : ‖((u⁻¹ : (PadicComplexInt p)ˣ) : PadicComplexInt p).1‖ ≤ 1 :=
      (mem_int_iff _).1 ((u⁻¹ : (PadicComplexInt p)ˣ) : PadicComplexInt p).2
    have h3 : ((u : PadicComplexInt p) : ℂ_[p]) * ((u⁻¹ : (PadicComplexInt p)ˣ) : PadicComplexInt p).1 = 1 := by
      exact congrArg Subtype.val u.mul_inv
    have h4 := congrArg norm h3
    rw [norm_mul, norm_one] at h4
    nlinarith [norm_nonneg ((u : PadicComplexInt p) : ℂ_[p]),
      norm_nonneg (((u⁻¹ : (PadicComplexInt p)ˣ) : PadicComplexInt p).1)]
  · intro h
    have h0 : (x : ℂ_[p]) ≠ 0 := by
      intro h0; rw [h0, norm_zero] at h; exact zero_ne_one h
    have hm : (x : ℂ_[p])⁻¹ ∈ PadicComplexInt p := by
      rw [mem_int_iff, norm_inv, h, inv_one]
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hm⟩, Subtype.ext (by simp [h0])⟩

theorem exists_minor_ne_zero' {K : Type} [Field K] {κ J : Type} [Fintype κ] [DecidableEq κ] [Fintype J]
    (M : Matrix κ J K) (hM : LinearIndependent K M.row) :
    ∃ f : κ → J, Function.Injective f ∧ (M.submatrix id f).det ≠ 0 := by
  classical
  obtain ⟨ι, b, hb, hsp, hli⟩ := exists_linearIndependent' K M.col
  have : Finite ι := Finite.of_injective b hb
  let : Fintype ι := Fintype.ofFinite ι
  have hι : Fintype.card ι = Fintype.card κ := by
    rw [← finrank_span_eq_card hli, hsp, ← Matrix.rank_eq_finrank_span_cols, hM.rank_matrix]
  let e : κ ≃ ι := (Fintype.equivOfCardEq hι).symm
  have h1 : LinearIndependent K (M.submatrix id (b ∘ e)).col := hli.comp e e.injective
  exact ⟨b ∘ e, hb.comp e.injective,
    ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 h1)).ne_zero⟩

theorem exists_minor_norm_one : ∀ (p : ℕ) [Fact p.Prime] {κ J : Type} [Fintype κ] [DecidableEq κ] [Fintype J]
    (c : Matrix κ J ℂ_[p]),
    (∀ k i, ‖c k i‖ ≤ 1) →
    (∀ a : κ → ℂ_[p], (∀ i, ‖∑ k, a k * c k i‖ ≤ 1) → ∀ k, ‖a k‖ ≤ 1) →
    ∃ f : κ → J, Function.Injective f ∧ ‖(c.submatrix id f).det‖ = 1 := by
  intro p _ κ J _ _ _ c hc hsat
  classical
  let c' : Matrix κ J (PadicComplexInt p) := fun k i => ⟨c k i, (mem_int_iff _).2 (hc k i)⟩
  let R := IsLocalRing.residue (PadicComplexInt p)
  let cb : Matrix κ J (IsLocalRing.ResidueField (PadicComplexInt p)) := c'.map R
  have hli : LinearIndependent (IsLocalRing.ResidueField (PadicComplexInt p)) cb.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg k0
    by_contra hk0
    obtain ⟨a, ha⟩ : ∃ a : κ → PadicComplexInt p, ∀ k, R (a k) = g k :=
      ⟨fun k => (IsLocalRing.residue_surjective (g k)).choose,
        fun k => (IsLocalRing.residue_surjective (g k)).choose_spec⟩
    have hx : ∀ i, ‖∑ k, (a k : ℂ_[p]) * c k i‖ < 1 := by
      intro i
      have h1 : R (∑ k, a k * c' k i) = 0 := by
        have := congrFun hg i
        simpa [map_sum, map_mul, ← ha, cb, Matrix.row, Finset.sum_apply] using this
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        isUnit_int_iff] at h1
      have h2 : ‖((∑ k, a k * c' k i : PadicComplexInt p) : ℂ_[p])‖ ≤ 1 :=
        (mem_int_iff _).1 (∑ k, a k * c' k i).2
      have h3 : ((∑ k, a k * c' k i : PadicComplexInt p) : ℂ_[p]) = ∑ k, (a k : ℂ_[p]) * c k i := by
        push_cast; rfl
      rw [h3] at h1 h2
      exact lt_of_le_of_ne h2 h1
    have hu : ‖(a k0 : ℂ_[p])‖ = 1 := by
      rw [← isUnit_int_iff, ← IsLocalRing.residue_ne_zero_iff_isUnit]
      exact (ha k0).symm ▸ hk0
    obtain ⟨ε, hε0, hε1⟩ := NormedField.exists_norm_lt_one ℂ_[p]
    let v : Option J → ℂ_[p] := fun o => o.elim ε (fun i => ∑ k, (a k : ℂ_[p]) * c k i)
    obtain ⟨o, -, ho⟩ := Finset.exists_max_image Finset.univ (fun o => ‖v o‖) ⟨none, Finset.mem_univ _⟩
    have hm0 : 0 < ‖v o‖ := lt_of_lt_of_le hε0 (ho none (Finset.mem_univ _))
    have hm1 : ‖v o‖ < 1 := by
      cases o with
      | none => exact hε1
      | some i => exact hx i
    have := hsat (fun k => (a k : ℂ_[p]) / v o) (fun i => by
      have e : ∑ k, (a k : ℂ_[p]) / v o * c k i = (∑ k, (a k : ℂ_[p]) * c k i) / v o := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun k _ => by ring
      rw [e, norm_div, div_le_one hm0]
      exact ho (some i) (Finset.mem_univ _)) k0
    rw [norm_div, div_le_one hm0, hu] at this
    linarith
  obtain ⟨f, hf, hdet⟩ := exists_minor_ne_zero' cb hli
  refine ⟨f, hf, ?_⟩
  have e1 : R (c'.submatrix id f).det = (cb.submatrix id f).det := by rw [RingHom.map_det]; rfl
  have e2 : (((c'.submatrix id f).det : PadicComplexInt p) : ℂ_[p]) = (c.submatrix id f).det := by
    show (PadicComplexInt p).subtype _ = _
    rw [RingHom.map_det]; rfl
  rw [← e2, ← isUnit_int_iff, ← IsLocalRing.residue_ne_zero_iff_isUnit]
  exact e1 ▸ hdet

end GlobalTheory.SatMinor
