import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ConstGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProdPairing

open GlobalTheory.CechPic GlobalTheory.DiagPairing

section Theta

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {P : LB (A ⊗ A).left} (hP : P.IsLB)
  (hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y)
  (hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y')

include hB in
theorem pc_one_left {T : Over S} (y : T ⟶ A) : pc hP (1 : T ⟶ A) y = 0 := by
  have := hB T 1 1 y
  rwa [_root_.mul_one, left_eq_add] at this

include hB' in
theorem pc_one_right {T : Over S} (x : T ⟶ A) : pc hP x (1 : T ⟶ A) = 0 := by
  have := hB' T x 1 1
  rwa [_root_.mul_one, left_eq_add] at this

include hB hB' in

theorem exists_theta_prod {k : ℕ} {T : Over S} (X : T ⟶ G2 A) (hX : X ^ k = 1) :
    ∃ θ : Out.ThetaGrp (G2 A) P k T, θ.pt = X := by
  have e : ∀ g : T ⊗ G2 A ⟶ G2 A, pull g.left (cls P hP) = pc hP (g ≫ fst A A) (g ≫ snd A A) := fun g => by
    unfold pc
    rw [← comp_lift, lift_fst_snd, Category.comp_id]
  have tr : Out.translPt (G2 A) X = (fst T (G2 A) ≫ X) * snd T (G2 A) := rfl
  have h₁ : (fst T (G2 A) ≫ X ≫ fst A A) ^ k = 1 := by
    rw [← Category.assoc, ← pow_comp, ← comp_pow, hX, MonObj.comp_one, MonObj.one_comp]
  have h₂ : (fst T (G2 A) ≫ X ≫ snd A A) ^ k = 1 := by
    rw [← Category.assoc, ← pow_comp, ← comp_pow, hX, MonObj.comp_one, MonObj.one_comp]
  have z₁ : ∀ y, k • pc hP (fst T (G2 A) ≫ X ≫ fst A A) y = 0 := fun y => by
    rw [← pc_pow_left hP hB, h₁, pc_one_left hP hB]
  have z₂ : ∀ x, k • pc hP x (fst T (G2 A) ≫ X ≫ snd A A) = 0 := fun x => by
    rw [← pc_pow_right hP hB', h₂, pc_one_right hP hB']
  obtain ⟨t, ht⟩ : ∃ t : LB.Gen (Out.thetaLB (G2 A) P k X), t.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
    rw [cls_linComb hP, Fin.sum_univ_two]
    show (k : ℤ) • pull (snd T (G2 A)).left _ + (-(k : ℤ)) • pull (Out.translPt (G2 A) X).left _ = 0
    rw [e, e, tr, mul_comp, mul_comp, Category.assoc, Category.assoc, hB, hB', hB']
    simp only [natCast_zsmul, neg_smul, smul_add, z₁, z₂]
    abel
  exact ⟨⟨X, t, ht⟩, rfl⟩

end Theta

theorem exists_weilIs_prod_root : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    ∀ (k : ℕ), 0 < k → ∀ (T : Over S) (X Y : T ⟶ G2 A), X ^ k = 1 → Y ^ k = 1 →
    ∃ c : Γ(T.left, ⊤)ˣ, c ^ k = 1 ∧ Out.WeilIs (G2 A) P k X Y c := by
  intro S A _ _ hA P hP rig₁ rig₂ hamp k hk T X Y hX hY
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP rig₁ rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP rig₁ rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have lifts : ∀ Z : T ⟶ G2 A, Z ^ k = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp (G2 A) P k (Out.overRes V), θ.pt = Out.overResι V ≫ Z := fun Z hZ p => by
    obtain ⟨θ, hθ⟩ := exists_theta_prod hP hB hB' (k := k) (Out.overResι ⊤ ≫ Z)
      (by rw [← MonObj.comp_pow, hZ, MonObj.comp_one])
    exact ⟨⊤, trivial, θ, hθ⟩
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_weilIs hG hAA hP (lifts X hX) (lifts Y hY)
  obtain ⟨c₁, hc₁⟩ := CommutatorPairing.exists_weilIs hG hAA hP (lifts 1 (one_pow k)) (lifts Y hY)
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP hc₁ hc₁
  rw [_root_.mul_one] at h11
  have e₁ : c₁ * c₁ = c₁ := CommutatorPairing.weilIs_unique hG hAA hP h11 hc₁
  have e₁' : c₁ = 1 := mul_eq_left.1 e₁
  have pw : ∀ m : ℕ, Out.WeilIs (G2 A) P k (X ^ (m + 1)) Y (c₀ ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hc₀
    | succ m ih =>
      rw [pow_succ X (m + 1), pow_succ c₀ (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP ih hc₀
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hX] at hp
  exact ⟨c₀, CommutatorPairing.weilIs_unique hG hAA hP hp (e₁' ▸ hc₁), hc₀⟩

end GlobalTheory.ProdPairing
