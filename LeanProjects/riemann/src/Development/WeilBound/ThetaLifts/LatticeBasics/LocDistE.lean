import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.LocDistB
import Development.WeilBound.ThetaLifts.LatticeBasics.LocDistD

open Filter Topology GlobalTheory.WeilM Matrix

namespace GlobalTheory.ThK.Dbl.LD

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}

def invT : GL (Fin d) k →* GL (Fin d) k where
  toFun x := ⟨x.invᵀ, x.valᵀ, by rw [← transpose_mul, x.val_inv, transpose_one], by rw [← transpose_mul, x.inv_val, transpose_one]⟩
  map_one' := Units.ext transpose_one
  map_mul' x y := Units.ext (transpose_mul _ _)

theorem cont_invT : Continuous (invT (k := k) (d := d)) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

open Classical in

noncomputable def toGL (X : Matrix (Fin d) (Fin d) k) : GL (Fin d) k := if h : IsUnit X then h.unit else 1

theorem toGL_val {X : Matrix (Fin d) (Fin d) k} (h : X.det ≠ 0) : (toGL X).1 = X := by
  rw [toGL, dif_pos ((isUnit_iff_isUnit_det X).2 h.isUnit)]; rfl

theorem toGL_coe (x : GL (Fin d) k) : toGL x.1 = x := Units.ext (toGL_val x.det_ne_zero)

theorem cont_toGL : ContinuousOn (toGL (k := k) (d := d)) {X | X.det ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict, Units.continuous_iff]
  refine ⟨continuous_subtype_val.congr fun X => (toGL_val X.2).symm, ?_⟩
  have : ContinuousOn (fun X : Matrix (Fin d) (Fin d) k => X⁻¹) {X | X.det ≠ 0} := fun X hX =>
    (continuousAt_matrix_inv X (by rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hX)).continuousWithinAt
  refine this.restrict.congr fun X => ?_
  rw [coe_units_inv]
  exact congrArg _ (toGL_val X.2).symm

theorem top_cell (ξ : kˣ →* ℂˣ) (l : (Matrix (Fin d) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ)
    {g : GL (Fin d) k} (hg : g.1ᵀ = g.1) {φ : Matrix (Fin d) (Fin d) k → ℂ} (hφ : φ ∈ SB _) (h0 : ∀ X, X.det = 0 → φ X = 0) :
    l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ := by
  classical
  have hU : IsOpen {X : Matrix (Fin d) (Fin d) k | X.det ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  let m : (GL (Fin d) k → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun ψ => l fun X => if X.det ≠ 0 then ψ (toGL X) else 0
      map_add' := fun F F' => by rw [← map_add]; congr 1; ext z; by_cases h : z.det = 0 <;> simp [h]
      map_smul' := fun a F => by rw [← map_smul]; congr 1; ext z; by_cases h : z.det = 0 <;> simp [h] }
  have hm : ∀ ψ, m ψ = l fun X => if X.det ≠ 0 then ψ (toGL X) else 0 := fun _ => rfl
  have a := left_of_right ((Units.coeHom ℂ).comp (ξ.comp GeneralLinearGroup.det)) invT cont_invT
    (fun x => Units.ext (transpose_transpose _)) (g := g)
    (inv_injective (Units.ext hg)) m (fun ψ hψ h => ?_) (φ := fun x => φ x.1)
    (sb_chart (U := Set.univ) (T := {X : Matrix (Fin d) (Fin d) k | X.det ≠ 0}) isOpen_univ Units.continuous_val.continuousOn cont_toGL
      (fun x _ => toGL_coe x) (fun _ _ => trivial) hφ (fun X hX => h0 X (not_not.1 hX)) (fun _ _ => rfl)
      fun _ h => absurd trivial h)
  · rw [hm, hm] at a
    convert a using 3 with X
    · split_ifs with h
      · rw [Units.val_mul, toGL_val h]
      · exact h0 _ (by rw [det_mul, not_not.1 h, mul_zero])
    · rfl
    · ext X
      split_ifs with h
      · rw [toGL_val h]
      · exact h0 _ (not_not.1 h)
  · rw [hm, hm]
    refine Eq.trans ?_ (hl (fun X => if X.det ≠ 0 then ψ (toGL X) else 0) (sb_chart (T := Set.univ) hU cont_toGL Units.continuous_val.continuousOn (fun X hX => toGL_val hX)
      (fun x _ => x.det_ne_zero) hψ (fun _ h => absurd trivial h) (fun X hX => if_pos hX) fun X hX => if_neg hX) h)
    congr 1; ext X
    by_cases hX : X.det = 0
    · simp [hX]
    · have : (X * h.1).det ≠ 0 := by rw [det_mul]; exact mul_ne_zero hX h.det_ne_zero
      rw [if_pos hX, if_pos this]
      congr 1; apply Units.ext
      rw [Units.val_mul, toGL_val hX, toGL_val this]

variable [NonarchimedeanAddGroup k] [LocallyCompactSpace k]

theorem vanish (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t) {n : ℕ}
    (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ)
    (hd : ∀ φ ∈ SB _, (∀ X, Deg X → φ X = 0) → l φ = 0) : ∀ φ ∈ SB _, l φ = 0 := by
  classical
  let c : k → ℂ := fun a => if h : a = 0 then 0 else ξ (Units.mk0 a h)
  have hc : ∀ a : kˣ, c a = ξ a := fun a => by simp [c]
  refine claim (c := c) (ϖ := ϖ) (fun a ha => ?_) ϖ.ne_zero (fun h => hξ 1 one_pos ?_) (fun t ht h => hξ t⁻¹ (inv_pos.2 ht) ?_)
    n d l (fun h hh => ⟨1, one_pos, fun φ hφ => ?_⟩) hd
  · simp [c, ha]
  · rw [Units.val_eq_one.1 h]; simp
  · rw [← hc, Complex.ofReal_inv]; exact eq_inv_of_mul_eq_one_left h
  · have := hl φ hφ (toGL h)
    rw [← hc, GeneralLinearGroup.val_det_apply, toGL_val hh] at this
    simpa using this

theorem lt_case (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t) {n : ℕ} (hn : n < d)
    (l : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ) :
    ∀ φ ∈ SB _, l φ = 0 := by
  refine vanish ξ ϖ hξ l hl fun φ _ h => ?_
  rw [show φ = 0 from funext fun X => h X ?_, map_zero]
  obtain ⟨v, hv, h0⟩ := (Submodule.ne_bot_iff _).1 (LinearMap.ker_ne_bot_of_finrank_lt (f := X.mulVecLin) (by simpa using hn))
  exact ⟨v, h0, hv⟩

theorem sb_left {φ : Matrix (Fin d) (Fin d) k → ℂ} (hφ : φ ∈ SB _) (g : GL (Fin d) k) :
    (fun y => φ (g.1 * y)) ∈ SB (Matrix (Fin d) (Fin d) k) :=
  sb_comp (g.1 * ·) ((g⁻¹).1 * ·) (by fun_prop) (by fun_prop) (fun x => g.inv_mul_cancel_left x) hφ

theorem eq_case (ξ : kˣ →* ℂˣ) (ϖ : kˣ) (hξ : ∀ t : ℝ, 0 < t → (ξ ϖ : ℂ) ≠ t)
    (l : (Matrix (Fin d) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hl : ∀ φ ∈ SB _, ∀ h : GL (Fin d) k, l (fun y => φ (y * h.1)) = ξ (GeneralLinearGroup.det h) * l φ) (g : GL (Fin d) k) :
    ∀ φ ∈ SB _, l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ := by
  let P : Matrix (Fin d) (Fin d) k → Prop := fun M => ∀ g : GL (Fin d) k, g.1 = M →
    ∀ φ ∈ SB _, l (fun y => φ (g.1 * y)) = ξ (GeneralLinearGroup.det g) * l φ
  have sym : ∀ M, Mᵀ = M → P M := by
    rintro _ hg g rfl φ hφ
    refine sub_eq_zero.1 (vanish ξ ϖ hξ (l ∘ₗ LinearMap.funLeft ℂ ℂ (g.1 * ·) - (ξ (GeneralLinearGroup.det g) : ℂ) • l)
      (fun ψ hψ h => ?_) (fun ψ hψ h0 => sub_eq_zero.2 (top_cell ξ l hl hg hψ fun X hX => h0 X ?_)) φ hφ)
    · have a := hl _ (sb_left hψ g) h
      simp only [← Matrix.mul_assoc] at a
      show (l fun y => ψ (g.1 * y * h.1)) - _ * (l fun y => ψ (y * h.1)) = _ * ((l fun y => ψ (g.1 * y)) - _ * l ψ)
      rw [a, hl ψ hψ h]; ring
    · exact exists_mulVec_eq_zero_iff.2 hX
  have mul : ∀ A B : Matrix (Fin d) (Fin d) k, A.det ≠ 0 → B.det ≠ 0 → P A → P B → P (A * B) := by
    intro A B hA hB pA pB g hg φ hφ
    have e : g = toGL A * toGL B := Units.ext (by rw [hg, Units.val_mul, toGL_val hA, toGL_val hB])
    have a := pB _ (toGL_val hB) _ (sb_left hφ (toGL A))
    rw [pA _ (toGL_val hA) _ hφ] at a
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
    rw [a]; ring
  refine diagonal_transvection_induction_of_det_ne_zero P g.1 g.det_ne_zero (fun D _ => sym _ (diagonal_transpose D))
    (fun t => ?_) mul g rfl
  have hs : (swap k t.i t.j).det ≠ 0 := (isUnit_det_of_left_inverse (swap_mul_self _ _)).ne_zero
  have := mul _ (swap k t.i t.j * t.toMatrix) hs (by rw [det_mul, t.det, mul_one]; exact hs) (sym _ (transpose_swap _ _))
    (sym _ ?_)
  · rwa [← Matrix.mul_assoc, swap_mul_self, Matrix.one_mul] at this
  have e : swap k t.i t.j * single t.i t.j t.c = single t.j t.j t.c := by
    ext a b
    by_cases h1 : a = t.i
    · rw [h1, swap_mul_apply_left]; simp [single_apply, t.hij, t.hij.symm]
    by_cases h2 : a = t.j
    · rw [h2, swap_mul_apply_right]; simp [single_apply]
    · rw [swap_mul_of_ne h1 h2]; simp [single_apply, Ne.symm h1, Ne.symm h2]
  rw [TransvectionStruct.toMatrix, transvection, Matrix.mul_add, Matrix.mul_one, e, transpose_add, transpose_swap,
    transpose_single]

end GlobalTheory.ThK.Dbl.LD
