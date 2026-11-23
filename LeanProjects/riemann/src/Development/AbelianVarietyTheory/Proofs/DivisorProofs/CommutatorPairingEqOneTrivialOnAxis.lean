import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSiegAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeOfExistsRelAmple
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilIsDiagRoot
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.WeilSqKer

open GlobalTheory.CechPic GlobalTheory.DiagPairing

theorem weilIs_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (k : Type) [Field k] [IsAlgClosed k] (x₀ : Sp k ⟶ S) (m : ℕ), (m : k) ≠ 0 → ∀ (a b : Over.mk x₀ ⟶ A), a ^ m = 1 → b ^ m = 1 → (∃ t : (P.pull (lift (snd A (Over.mk x₀) ≫ a ^ 2) (fst A (Over.mk x₀))).left).Gen, t.IsGen) → ∀ c : Γ((Over.mk x₀).left, ⊤)ˣ, Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) (m : ℤ) a b c → c = 1 := by
  intro S A _ _ hA P hP h₁ h₂ hsym hamp k _ _ x₀ m hm a b ha hb ha2 c hc
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple hA hD hamp hD
  have hB : ∀ (T : Over S) (x x' y : T ⟶ A), pc hP (x * x') y = pc hP x y + pc hP x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂
        T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ A), pc hP x (y * y') = pc hP x y + pc hP x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD hamp P hP h₁ h₂
        T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
      rw [cls_linComb hP, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hS : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
    (cls_eq_iff hP (pull_isLB hP _)).2 hsym
  have hsw : ∀ (T : Over S) (x y : T ⟶ A), pc hP x y = pc hP y x := fun T x y => by
    have h := congrArg (pull (lift x y).left) hS
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst] at h
    exact h
  let T : Over S := Over.mk x₀
  have e : ∀ g : T ⊗ A ⟶ A, pull g.left (cls _ hD) = pc hP g g := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
    rfl

  have hpt : ∀ {N : LB T.left} (hN : N.IsLB), cls N hN = 0 := fun {N} hN => by
    haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum k))
    obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum k))
    obtain ⟨i, hi⟩ := exists_chart hN p
    exact (cls_eq_zero_iff hN).2
      (DescendedPrincipal.exists_gen_of_chart hN i fun y => Subsingleton.elim p y ▸ hi)
  have haa : pc hP (fst T A ≫ a) (fst T A ≫ a) = 0 := by
    unfold pc
    rw [← comp_lift, Over.comp_left, pull_comp, ← cls_pull hP _ (pull_isLB hP _),
      hpt (pull_isLB hP _), map_zero]
  have ha2' : pc hP (fst T A ≫ a) (snd T A) + pc hP (fst T A ≫ a) (snd T A) = 0 := by
    rw [← hB]
    obtain ⟨u, hu⟩ := ha2
    have z := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨u, hu⟩
    rw [cls_pull hP] at z
    have z' := congrArg (pull (β_ T A).hom.left) z
    rw [← pull_comp, ← Over.comp_left, comp_lift, braiding_hom_snd_assoc, braiding_hom_fst, map_zero] at z'
    unfold pc
    rw [← MonObj.comp_mul, ← pow_two]
    exact z'
  obtain ⟨φ, hφ⟩ : ∃ φ : LB.Gen (Out.thetaLB A (P.pull (lift (𝟙 A) (𝟙 A)).left) 1 a), φ.IsGen := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hD _ _)).1 ?_
    rw [cls_linComb hD, Fin.sum_univ_two]
    show (1 : ℤ) • pull (snd T A).left _ + (-1 : ℤ) • pull ((fst T A ≫ a) * snd T A).left _ = 0
    rw [e, e, hB, hB', hB', hsw _ (snd T A) (fst T A ≫ a), haa]
    calc _ = -(pc hP (fst T A ≫ a) (snd T A) + pc hP (fst T A ≫ a) (snd T A)) := by abel
      _ = 0 := by rw [ha2', neg_zero]
  have h1 : Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) 1 a 1 1 :=
    DescendedPrincipal.weilIs_one_right hG hA hD fun p => by
      obtain ⟨θ, hθ⟩ := CommutatorPairing.exists_pull hD (⟨a, φ, hφ⟩ : Out.ThetaGrp A _ 1 T)
        (Out.overResι (⊤ : T.left.Opens))
      exact ⟨⊤, trivial, θ, hθ⟩
  have h1' := CommPairing.weilIs_symm hD h1
  have hc' := CommPairing.weilIs_symm hD hc
  rw [inv_one, ← hb] at h1'
  have hc'' : Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) ((1 : ℤ) * (m : ℕ)) b a c⁻¹ := by
    rw [_root_.one_mul]; exact hc'
  have key := PairingLevels.weilIs_value_eq hG hA hD ht hc'' h1'
  exact inv_eq_one.1 key

end GlobalTheory.WeilSqKer
