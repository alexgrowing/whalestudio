import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitValue
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueSecEqMulGen

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.ZH
noncomputable section
namespace GlobalTheory.ZH.SecComb
open GlobalTheory.ZH.SecValue

theorem pull_liftFun {S : Scheme.{0}} {A T : Over S} [GrpObj A] (ψ : T ⊗ A ⟶ T ⊗ A) (hψ : ψ ≫ fst T A = fst T A)
    {U W : (T ⊗ A).left.Opens} (h : W ≤ ψ.left ⁻¹ᵁ U) (r : Γ(T.left, ⊤)) :
    ((T ⊗ A).left.presheaf.map (homOfLE h).op).hom ((ψ.left.app U).hom (liftFun A U r)) = liftFun A W r := by
  have e : ψ.left ≫ (fst T A).left = (fst T A).left := by rw [← Over.comp_left, hψ]
  have e₁ : ∀ V : (T ⊗ A).left.Opens, liftFun A V r = ((fst T A).left.appLE ⊤ V le_top).hom r := fun _ => rfl
  rw [e₁, e₁]
  refine (congrArg (fun q => q.hom r) (Scheme.Hom.appLE_comp_appLE ψ.left (fst T A).left ⊤ U W le_top h)).trans ?_
  simp only [e]

theorem ring_sum {B B' C I : Type} [CommRing B] [CommRing B'] [CommRing C] [Fintype I] (f' : B' →+* C) (f : B →+* C)
    (u : C) {c s : I → B} {c' s' : I → B'} {t : B} {t' : B'} (ht : t = ∑ l, c l * s l) (ht' : t' = ∑ l, c' l * s' l)
    (hc : ∀ l, f' (c' l) = f (c l)) (h : ∀ l, f' (s' l) = u * f (s l)) : f' t' = u * f t := by
  rw [ht, ht', map_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [map_mul, map_mul, h, hc, mul_left_comm]

theorem isTwistPull_sum {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left} (ψ : T ⊗ A ⟶ T ⊗ A)
    (hψ : ψ ≫ fst T A = fst T A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (a b : ℤ) (α) {I : Type} [Fintype I]
    (c : I → Γ(T.left, ⊤)) {s : I → LB.Sec (LPow A L b T)} {s' : I → LB.Sec (LPow A L a T)}
    {t : LB.Sec (LPow A L b T)} {t' : LB.Sec (LPow A L a T)}
    (ht : ∀ j, t.f j = ∑ l, liftFun A _ (c l) * (s l).f j) (ht' : ∀ j, t'.f j = ∑ l, liftFun A _ (c l) * (s' l).f j)
    (h : ∀ l, IsTwistPull A L ψ m hm a b α (s l) (s' l)) : IsTwistPull A L ψ m hm a b α t t' := fun j =>
  ring_sum _ (RingHom.comp _ _) _ (ht _) (ht' _)
    (fun l => (res_liftHom A _ (c l)).trans (pull_liftFun ψ hψ (chart_le_pull A L ψ m hm j) (c l)).symm) fun l => h l j

section
variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

theorem valM_zero (x) (e : FrAt x) : ValM (0 : SecM A.A A.L k (TFK (R := R) F)) x e 0 := fun z J hJ => by
  have h := ThetaAct.sv_add (0 : SecM A.A A.L k (TFK (R := R) F)) 0 (ptSecT A.A x).left z hJ
  rw [add_zero, left_eq_add] at h
  refine h.trans ?_
  simp only [id, CoefBasic.cst_eq, map_zero]
  exact (zero_mul (M₀ := (TFK (R := R) F).left.presheaf.stalk z) _).symm

theorem valM_sum {x} {e : FrAt x} {J : Type} (s : Finset J)
    {σ : J → SecM A.A A.L k (TFK (R := R) F)} {c : J → F} (h : ∀ l, ValM (σ l) x e (c l)) :
    ValM (∑ l ∈ s, σ l) x e (∑ l ∈ s, c l) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valM_zero x e
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a).add ih

theorem exists_valAt (t : SecA A F k) {x} {e : FrAt x} (he : e.IsGen) : ∃ c, ValAt t x e c := by
  obtain ⟨w, hw⟩ := ThetaPtExist.exists_isValueAt A.isLB t x (powFrame A.A A.L x e k) (EvVal.powFrame_isGen A.A A.L x e he k)
  obtain ⟨c, rfl⟩ := kon_surj w
  refine ⟨c, fun z J hJ => ?_⟩
  have := ThetaPtMove.sv_of_isValueAt hw (𝟙 _) z hJ
  rw [Category.id_comp] at this
  exact this

end

theorem lin_comb_value_act : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), (∀ (t : SecA A F k) x (e : FrAt x), e.IsGen → ∃! a : F, ValAt t x e a) ∧ ∀ (I : Type) [Fintype I] (c : I → F) (s : I → SecA A F k), (∃ t, IsComb s c t) ∧ ∀ t, IsComb s c t → (∀ x (e : FrAt x) (a : I → F), (∀ i, ValAt (s i) x e (a i)) → ValAt t x e (∑ i, c i * a i)) ∧ ∀ (θ : ThetaGrp A.A A.L k (TFK (R := R) F)) (s' : I → SecA A F k) t', (∀ i, IsActOf A.A A.L k θ (s i) (s' i)) → IsComb s' c t' → IsActOf A.A A.L k θ t t' := by
  intro R _ _ A F _ _ k
  refine ⟨fun t x e he => ?_, fun I _ c s => ⟨?_, fun t ht => ⟨fun x e a ha => ?_, fun θ s' t' hs ht' => ?_⟩⟩⟩
  · obtain ⟨a, ha⟩ := exists_valAt t he
    exact ⟨a, ha, fun b hb => ValM.unique (σ := SecM.ofSec A.A t) hb ha⟩
  · exact ⟨SecM.toSec A.A (∑ l, kon R F (c l) • SecM.ofSec A.A (s l)), (isComb_iff _ _ _).2 rfl⟩
  · have h := valM_sum (Finset.univ : Finset I) fun l => ValM.smul (σ := SecM.ofSec A.A (s l)) (ha l) (c l)
    rw [← (isComb_iff _ _ _).1 ht] at h
    exact h
  · exact isTwistPull_sum _ (lift_fst _ _) _ _ _ _ _ (fun l => kon R F (c l)) ht ht' hs

end GlobalTheory.ZH.SecComb
end
