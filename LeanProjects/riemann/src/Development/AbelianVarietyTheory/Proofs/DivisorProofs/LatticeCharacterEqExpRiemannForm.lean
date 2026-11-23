import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff

namespace GlobalTheory

theorem unitary_char_eq_exp_riem : ∀ {g : ℕ} {M : Submodule ℤ (Fl g)}, IsLat M → ∀ χ : Fl g → ℂ,
    (∀ l ∈ M, ‖χ l‖ = 1) → (∀ l ∈ M, ∀ l' ∈ M, χ (l + l') = χ l * χ l') →
    ∃ x : Fl g, ∀ l ∈ M, χ l = Complex.exp (2 * π * Complex.I * riem x l) := by
  intro g M hM χ hn hmul
  obtain ⟨hd, hz⟩ := hM
  haveI : Module.Free ℤ M := ZLattice.module_free ℝ M
  haveI : Module.Finite ℤ M := ZLattice.module_finite ℝ M
  set b := Module.Free.chooseBasis ℤ M
  set bR := Module.Basis.ofZLatticeBasis ℝ M b
  set a : Module.Free.ChooseBasisIndex ℤ M → ℝ := fun k => Complex.arg (χ (b k)) / (2 * π) with ha_def
  have ha : ∀ k, χ (b k) = Complex.exp (2 * π * Complex.I * (a k : ℂ)) := by
    intro k
    have h := Complex.norm_mul_exp_arg_mul_I (χ (b k))
    rw [hn _ (b k).2] at h
    have e : 2 * π * Complex.I * (a k : ℂ) = (Complex.arg (χ (b k)) : ℂ) * Complex.I := by
      simp only [ha_def]
      push_cast
      field_simp
    rw [e]
    simpa using h.symm
  set f : Fl g →ₗ[ℝ] ℝ := bR.constr ℝ a
  set w : Fl g := fun i => f (fun j => if i = j then 1 else 0) with hw
  set x : Fl g := Sum.elim (fun i => - w (Sum.inr i)) (fun i => w (Sum.inl i)) with hx_def
  have hx : ∀ y, riem x y = f y := by
    intro y
    rw [LinearMap.pi_apply_eq_sum_univ f y, Fintype.sum_sum_type]
    simp only [riem, hx_def, Sum.elim_inl, Sum.elim_inr, smul_eq_mul, ← Finset.sum_add_distrib, hw]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hxb : ∀ k, riem x (b k) = a k := by
    intro k
    rw [hx, ← Module.Basis.ofZLatticeBasis_apply ℝ M b k]
    exact bR.constr_basis ℝ a k
  have h0 : χ 0 = 1 := by
    have e := hmul 0 M.zero_mem 0 M.zero_mem
    rw [add_zero] at e
    have hne : χ 0 ≠ 0 := by
      intro h
      have := hn 0 M.zero_mem
      rw [h, norm_zero] at this
      exact zero_ne_one this
    exact mul_left_cancel₀ hne (by rw [mul_one]; exact e.symm)
  let T : AddSubgroup (Fl g) :=
    { carrier := {l | l ∈ M ∧ χ l = Complex.exp (2 * π * Complex.I * riem x l)}
      add_mem' := by
        rintro l l' ⟨hl, el⟩ ⟨hl', el'⟩
        refine ⟨M.add_mem hl hl', ?_⟩
        rw [hmul l hl l' hl', el, el', ← Complex.exp_add]
        congr 1
        have : riem x (l + l') = riem x l + riem x l' := by
          simp only [riem, Pi.add_apply, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [this]
        push_cast
        ring
      zero_mem' := ⟨M.zero_mem, by simp [h0, riem]⟩
      neg_mem' := by
        rintro l ⟨hl, el⟩
        refine ⟨M.neg_mem hl, ?_⟩
        have e1 := hmul (-l) (M.neg_mem hl) l hl
        rw [neg_add_cancel, h0, el] at e1
        have : riem x (-l) = - riem x l := by
          simp only [riem, Pi.neg_apply, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun _ _ => by ring
        have e2 : Complex.exp (2 * π * Complex.I * ((riem x (-l) : ℝ) : ℂ)) =
            (Complex.exp (2 * π * Complex.I * ((riem x l : ℝ) : ℂ)))⁻¹ := by
          rw [← Complex.exp_neg, this]
          push_cast
          ring_nf
        rw [e2]
        exact eq_inv_of_mul_eq_one_left e1.symm }
  have hMT : M ≤ AddSubgroup.toIntSubmodule T := by
    rw [← Module.Basis.ofZLatticeBasis_span ℝ M b, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [Module.Basis.ofZLatticeBasis_apply]
    refine ⟨(b k).2, ?_⟩
    rw [ha k, hxb k]
  exact ⟨x, fun l hl => (show l ∈ T from hMT hl).2⟩

end GlobalTheory
