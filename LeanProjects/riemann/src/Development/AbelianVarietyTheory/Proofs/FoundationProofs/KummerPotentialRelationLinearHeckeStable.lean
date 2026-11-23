import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerPotentialIncrementLinearLawsStatement
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3.RelOp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem kmap_eq_self (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (φ : X.K ≃+* X.K) (hφ : ∀ f, φ f = f)
    (x : X.Khat l) : X.kmap l φ x = x := by
  have h1 : Units.map φ.toMonoidHom = MonoidHom.id X.Kˣ := by
    ext u; simp [hφ]
  have h2 : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom)) :
      Additive X.Kˣ →ₗ[ℤ] Additive X.Kˣ) = LinearMap.id := by
    rw [h1]; ext u; rfl
  unfold Tower.kmap
  rw [h2, LinearMap.baseChange_id, AdicCompletion.map_id]
  rfl

theorem mob_one' (z : ℂ) : mob 1 z = z := by
  simp [mob, ent]

section Main

variable (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]

theorem rel_add {b b' : X.Fn l} {F F' : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) (h' : Rel X l b' F') :
    Rel X l (b + b') (F + F') := by
  intro u
  have := (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).1 _ _ _ _ (h u) (h' u)
  convert this using 1 <;> first | rfl | (funext z; simp)

theorem rel_zero : Rel X l 0 0 := by
  intro u
  convert (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).2.1 using 1 <;> first | rfl | (funext z; simp)

theorem rel_smul (c : ℤ_[l]) {b : X.Fn l} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) :
    Rel X l (c • b) (c • F) := by
  intro u
  have := (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).2.2.1 c _ _ (h u)
  convert this using 1 <;> first | rfl | (funext z; simp)

theorem rel_act (m : Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l} {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) :
    Rel X l (X.act l m b) (opP ℤ_[l] m F) := by
  intro u
  have e : (fun z => MvPolynomial.eval u (opP ℤ_[l] m F z)) =
      fun z => (fun z => MvPolynomial.eval (mZl l m *ᵥ u) (F z)) (mob (toGQ m) z) := by
    funext z
    simp only [opP, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Betti.eval_slP]; rfl
  show R1 X l (X.kmap l (X.sl (toGQ m)).toRingEquiv (b (mZl l m *ᵥ u))) _
  rw [e]
  by_cases hm : 0 < m.det
  · exact (GlobalTheory.T.r1_smul_and_kmap_of_r1_linear_laws Ω ε X l).2.2.2 m _ _ hm (h _)
  · have h1 : toGQ m = 1 := by unfold toGQ; rw [dif_neg hm]
    rw [h1, kmap_eq_self X l _ (fun f => X.sl_one f)]
    simp only [mob_one']
    exact h _

theorem rel_sum {ι : Type} (s : Finset ι) (m : ι → Matrix (Fin 2) (Fin 2) ℤ) {b : X.Fn l}
    {F : ℂ → MvPolynomial (Fin 2) ℤ_[l]} (h : Rel X l b F) :
    Rel X l ((∑ j ∈ s, X.act l (m j)) b) ((∑ j ∈ s, opP ℤ_[l] (m j)) F) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using rel_zero X l
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, LinearMap.add_apply, LinearMap.add_apply]
    exact rel_add X l (rel_act X l _ h) ih

end Main

end GlobalTheory.KZ.H3.RelOp

open GlobalTheory.KZ.H3.RelOp in

theorem GlobalTheory.KZ.H3.rel_ops : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    (∀ b b' F F', Rel X l b F → Rel X l b' F' → Rel X l (b + b') (F + F')) ∧ Rel X l 0 0 ∧
    (∀ (c : ℤ_[l]) b F, Rel X l b F → Rel X l (c • b) (c • F)) ∧
    (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) b F, Rel X l b F → Rel X l (X.act l m b) (opP ℤ_[l] m F)) ∧
    (∀ (N : ℕ) (T : Letter) b F, Rel X l b F → Rel X l (X.op N l T b) (opL ℤ_[l] N l T F)) := by
  intro Ω _ _ ε X l _
  refine ⟨fun b b' F F' h h' => rel_add X l h h', rel_zero X l, fun c b F h => rel_smul X l c h,
    fun m b F h => rel_act X l m h, fun N T b F h => ?_⟩
  cases T with
  | T q =>
    simp only [Tower.op, Tower.heckeT, opL, LinearMap.add_apply]
    exact rel_add X l (rel_sum X l _ _ h) (rel_act X l _ h)
  | U =>
    simp only [Tower.op, Tower.heckeU, opL]
    exact rel_sum X l _ _ h
  | D d =>
    simp only [Tower.op, Tower.diam, opL]
    exact rel_act X l _ h
