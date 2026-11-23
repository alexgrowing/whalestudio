import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory

theorem relIndex_mul_periodLattice (L : PeriodPair) {α : ℂ} (h0 : α ≠ 0)
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice) :
    (((AddSubgroup.map (AddMonoidHom.mulLeft α) L.lattice.toAddSubgroup).relIndex
      L.lattice.toAddSubgroup : ℕ) : ℝ) = ‖α‖ ^ 2 := by
  classical
  let f : L.lattice →ₗ[ℤ] L.lattice := (LinearMap.mulLeft ℤ α).restrict (fun l hl => hα l hl)
  have hf : ∀ x : L.lattice, (f x : ℂ) = α * x := fun x => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun t : L.lattice => (t : ℂ)) hxy
    simp only [hf] at this
    exact Subtype.ext (mul_left_cancel₀ h0 this)
  have hsub : (AddSubgroup.map (AddMonoidHom.mulLeft α) L.lattice.toAddSubgroup).addSubgroupOf
      L.lattice.toAddSubgroup = (LinearMap.range f).toAddSubgroup := by
    ext x
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, y.2, congrArg Subtype.val hy⟩
  have hidx := AddSubgroup.index_eq_natAbs_det L.latticeBasis (LinearMap.range f).toAddSubgroup
    (L.latticeBasis.map (LinearEquiv.ofInjective f hinj))
  have hdet : (L.latticeBasis.det fun i =>
      ((L.latticeBasis.map (LinearEquiv.ofInjective f hinj)) i : L.lattice)) =
      L.latticeBasis.repr (f (L.latticeBasis 0)) 0 * L.latticeBasis.repr (f (L.latticeBasis 1)) 1 -
      L.latticeBasis.repr (f (L.latticeBasis 1)) 0 * L.latticeBasis.repr (f (L.latticeBasis 0)) 1 := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    rfl
  have hrep : ∀ x : L.lattice, α * x = (L.latticeBasis.repr (f x) 0 : ℤ) * L.ω₁ +
      (L.latticeBasis.repr (f x) 1 : ℤ) * L.ω₂ := by
    intro x
    have := congrArg (fun t : L.lattice => (t : ℂ)) (L.latticeBasis.sum_repr (f x))
    simp only [Fin.sum_univ_two, hf] at this
    rw [← this]
    simp
  have h1 := hrep (L.latticeBasis 0)
  have h2 := hrep (L.latticeBasis 1)
  rw [AddSubgroup.relIndex, hsub]
  refine (congrArg Nat.cast (hidx.trans (congrArg Int.natAbs hdet))).trans ?_
  generalize L.latticeBasis.repr (f (L.latticeBasis 0)) 0 = a at h1 h2 ⊢
  generalize L.latticeBasis.repr (f (L.latticeBasis 0)) 1 = c at h1 h2 ⊢
  generalize L.latticeBasis.repr (f (L.latticeBasis 1)) 0 = b at h1 h2 ⊢
  generalize L.latticeBasis.repr (f (L.latticeBasis 1)) 1 = d at h1 h2 ⊢
  simp only [PeriodPair.latticeBasis_zero, PeriodPair.latticeBasis_one] at h1 h2
  have hD : L.ω₁.re * L.ω₂.im - L.ω₂.re * L.ω₁.im ≠ 0 := by
    intro hD
    have hind := LinearIndependent.pair_iff.mp L.indep
    have e1 := hind L.ω₂.im (-L.ω₁.im) (by
      apply Complex.ext <;> simp <;> linarith)
    have e2 := hind L.ω₂.re (-L.ω₁.re) (by
      apply Complex.ext <;> simp <;> linarith)
    have e3 : L.ω₂ = 0 := Complex.ext e2.1 e1.1
    have := hind 0 1 (by simp [e3])
    exact one_ne_zero this.2
  have r1 := congrArg Complex.re h1
  have i1 := congrArg Complex.im h1
  have r2 := congrArg Complex.re h2
  have i2 := congrArg Complex.im h2
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.intCast_re,
    Complex.intCast_im, zero_mul, sub_zero, add_zero] at r1 i1 r2 i2
  have key : ((a * d - b * c : ℤ) : ℝ) = ‖α‖ ^ 2 := by
    apply mul_right_cancel₀ hD
    rw [Complex.sq_norm, Complex.normSq_apply]
    push_cast
    have : (α.re * L.ω₁.re - α.im * L.ω₁.im) * (α.re * L.ω₂.im + α.im * L.ω₂.re) -
        (α.re * L.ω₂.re - α.im * L.ω₂.im) * (α.re * L.ω₁.im + α.im * L.ω₁.re) =
        (a * L.ω₁.re + c * L.ω₂.re) * (b * L.ω₁.im + d * L.ω₂.im) -
        (b * L.ω₁.re + d * L.ω₂.re) * (a * L.ω₁.im + c * L.ω₂.im) := by
      rw [r1, i1, r2, i2]
    linear_combination -this
  rw [Nat.cast_natAbs, Int.cast_abs, key]
  exact abs_of_nonneg (by positivity)

theorem exists_weierstrassP_mul_ode : ∀ (L : PeriodPair) (α : ℂ) (N : ℕ), α ≠ 0 → (∀ l ∈ L.lattice, α * l ∈ L.lattice) → ‖α‖ ^ 2 = N → ∃ A D : ℂ[X], D ≠ 0 ∧ A.natDegree = N ∧ D.natDegree + 1 = N ∧ (∀ z, α * z ∉ L.lattice → D.eval (L.weierstrassP z) ≠ 0 ∧ L.weierstrassP (α * z) = A.eval (L.weierstrassP z) / D.eval (L.weierstrassP z)) ∧ C (α ^ 2) * D * (4 * A ^ 3 - C L.g₂ * A * D ^ 2 - C L.g₃ * D ^ 3) = (derivative A * D - A * derivative D) ^ 2 * (4 * X ^ 3 - C L.g₂ * X - C L.g₃) := by
  intro L α N h0 hα hN
  obtain ⟨A, D, -, -, hmon, -, -, hA, hD, hz, hdiv⟩ :=
    exists_weierstrassP_mul_eq_div h0 hα ⊤ trivial trivial trivial (fun _ _ _ => trivial)
  have hAN : A.natDegree = N := by
    have := relIndex_mul_periodLattice L h0 hα
    rw [← hA, hN] at this
    exact_mod_cast this
  refine ⟨A, D, hmon.ne_zero, hAN, hD.trans hAN, fun z hz' => ⟨?_, hdiv z hz'⟩, ?_⟩
  · intro h
    exact hz' ((hz z (fun hl => hz' (hα z hl))).mp h)
  · apply Polynomial.eq_of_infinite_eval_eq
    have hfin : {x : ℂ | D.IsRoot x}.Finite := Polynomial.finite_setOfPred_isRoot hmon.ne_zero
    refine hfin.infinite_compl.mono ?_
    intro x hx
    obtain ⟨z, hzL, rfl⟩ := exists_weierstrassP_eq L x
    have hx' : D.eval (L.weierstrassP z) ≠ 0 := hx
    have hαz : α * z ∉ L.lattice := fun h => hx' ((hz z hzL).mpr h)
    have e1 := derivWeierstrassP_mul_eq hα hdiv hαz hx'
    have e2 := L.derivWeierstrassP_sq z hzL
    have e3 := L.derivWeierstrassP_sq _ hαz
    rw [hdiv z hαz] at e3
    simp only [Set.mem_ofPred_eq, eval_mul, eval_sub, eval_pow, eval_C, eval_X, eval_ofNat] at e1 ⊢
    rw [← e2]
    have e4 := congrArg (· ^ 2) e1
    simp only [mul_pow] at e4
    rw [e3] at e4
    field_simp at e4
    linear_combination e4

end GlobalTheory
