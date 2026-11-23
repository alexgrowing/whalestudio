import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VecZero
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SumTransportAlt
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NatCastQb

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private theorem pull_tri {R : Type} [CommRing R] {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C']
    [Category.{0} C''] {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} {F'' : C'' ⥤ ModuleCat.{0} R}
    (a : CH.Mor F F' (RingHom.id R)) (b : CH.Mor F' F'' (RingHom.id R)) (c : CH.Mor F F'' (RingHom.id R)) (j : ℕ)
    (h : ∀ z : CH.Cn F j, c.pullC j z = b.pullC j (a.pullC j z)) (x : CH.H F j) :
    c.pull j x = b.pull j (a.pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((CH.cx F'').B j).submoduleOf ((CH.cx F'').Z j))) (Subtype.ext (h z.1))

private theorem pull_self {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ ModuleCat.{0} R}
    (c : CH.Mor F F (RingHom.id R)) (j : ℕ) (h : ∀ z : CH.Cn F j, c.pullC j z = z) (x : CH.H F j) :
    c.pull j x = x := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((CH.cx F).B j).submoduleOf ((CH.cx F).Z j))) (Subtype.ext (h z.1))

private theorem pullH_comp {P P' P'' : PAlg l ⥤ Type} (u : P ⟶ P') (v : P' ⟶ P'') (n j : ℕ) (x : MH P'' n j) :
    pullH (u ≫ v) n j x = pullH u n j (pullH v n j x) :=
  pull_tri (pullMor v n) (pullMor u n) (pullMor (u ≫ v) n) j (fun _ => funext fun _ => rfl) x

private theorem pullH_id (P : PAlg l ⥤ Type) (n j : ℕ) (x : MH P n j) : pullH (𝟙 P) n j x = x :=
  pull_self (pullMor (𝟙 P) n) j (fun _ => funext fun _ => rfl) x

private theorem phi_pull' {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (n j : ℕ) (x : MH P' n j) :
    phiH P n j (pullH u n j x) = pullH u n j (phiH P' n j x) :=
  (frEx l ℤ (Spec (CommRingCat.of ℤ)) (𝟙 _) (Int.castRingHom _) (Int.castRingHom _) 0 0 (fun _ => by simp)).2.2 P P' u n j x

private theorem iter_semi {A B : Type*} (p : B → B) (r : A → A) (h : A → B) (e : ∀ x, p (h x) = h (r x))
    (m : ℕ) (x : A) : p^[m] (h x) = h (r^[m] x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, e]

private theorem iter_step {A : Type*} (p : A → A) (f k : ℕ) (x : A) : p^[f * (k + 1)] x = p^[f * k] (p^[f] x) := by
  rw [Nat.mul_succ, Function.iterate_add_apply]

private theorem phi_iter_pull {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (n j m : ℕ) (x : MH P' n j) :
    (phiH P n j)^[m] (pullH u n j x) = pullH u n j ((phiH P' n j)^[m] x) :=
  iter_semi _ _ (pullH u n j) (phi_pull' u n j) m x

private theorem itE_succ {P : PAlg l ⥤ Type} (F : P ⟶ P) (k : ℕ) : itE F (k + 1) = F ≫ itE F k := by
  unfold itE
  rw [pow_succ]
  rfl

private theorem phi_iter_itE {P : PAlg l ⥤ Type} (F : P ⟶ P) (f n j : ℕ) (x : MH P n j)
    (hx : (phiH P n j)^[f] x = pullH F n j x) (k : ℕ) :
    (phiH P n j)^[f * k] x = pullH (itE F k) n j x := by
  induction k with
  | zero => exact (pullH_id P n j x).symm
  | succ k ih =>
    refine (iter_step (phiH P n j) f k x).trans ((congrArg _ hx).trans ((phi_iter_pull F n j (f * k) x).trans
      ((congrArg (pullH F n j) ih).trans ?_)))
    exact (pullH_comp F (itE F k) n j x).symm.trans (congrArg (fun w : P ⟶ P => pullH w n j x) (itE_succ F k).symm)

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.siteAnn :
    UpperTheory.Ru.crystallineComparison.SiteAnn := by
  intro l _ O _ Y q g Q P ρ F f I _ a t k hT n j x hx
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (sumMH l Q (PQ q g) I a (fun i => t i ≫ ρ ≫ itE F (k i)) hT n j x)
  refine congrArg (a i • ·) ?_
  refine (congrArg (pullH (t i) n j) ((phi_iter_pull ρ n j (f * k i) x).trans
    (congrArg (pullH ρ n j) (phi_iter_itE F f n j x hx (k i))))).trans ?_
  exact ((congrArg (pullH (t i) n j) (pullH_comp ρ (itE F (k i)) n j x).symm).trans
    (pullH_comp (t i) (ρ ≫ itE F (k i)) n j x).symm)
