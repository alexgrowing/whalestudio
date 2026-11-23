import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisConnectingExistsUniqueAdditiveExact
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfTwoElementCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupHypercohomologyPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductAssocStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow
namespace UpperTheory.ChaseS

variable {q : ℕ}

private theorem c_cc {E : Spc} {n i n' i' n'' i'' : ℤ} (a : n = n') (b : i = i') (c : n' = n'') (d : i' = i'')
    (x : Ht q E n i) : (x.cast a b).cast c d = x.cast (a.trans c) (b.trans d) := by
  subst a b c d
  rfl

private theorem c_zero {E : Spc} {n i n' i' : ℤ} (a : n = n') (b : i = i') :
    (0 : Ht q E n i).cast a b = 0 := by
  subst a b
  rfl

private theorem c_sum {E : Spc} {n i n' i' : ℤ} (a : n = n') (b : i = i') {ι : Type} (s : Finset ι)
    (f : ι → Ht q E n i) : (∑ j ∈ s, f j).cast a b = ∑ j ∈ s, (f j).cast a b := by
  subst a b
  rfl

private theorem pull_c {X Y : Spc} (f : X ⟶ Y) {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q Y n i) :
    pull _ f _ _ (x.cast hn hi) = Ht.cast hn hi (pull _ f _ _ x : Ht q X n i) := by
  subst hn hi
  rfl

private theorem pull_u {X Y : Spc} (f : X ⟶ Y) {n m i j : ℤ} (a : Ht q Y n i) (b : Ht q Y m j) :
    pull _ f _ _ (cup q a b) = cup q (pull _ f _ _ a : Ht q X n i) (pull _ f _ _ b : Ht q X m j) :=
  GlobalTheory.T.cup_hypercohomologyPullback (ZMod q) (twPair q i j) f rfl a b

private theorem cup_cl {E : Spc} {n m i j n' i' : ℤ} (hn : n = n') (hi : i = i') (a : Ht q E n i) (b : Ht q E m j) :
    cup q (a.cast hn hi) b = (cup q a b).cast (by rw [hn]) (by rw [hi]) := by
  subst hn hi
  rfl

private theorem cup_cr {E : Spc} {n m i j m' j' : ℤ} (hm : m = m') (hj : j = j') (a : Ht q E n i) (b : Ht q E m j) :
    cup q a (b.cast hm hj) = (cup q a b).cast (by rw [hm]) (by rw [hj]) := by
  subst hm hj
  rfl

variable [NeZero q]

private theorem cup_one_r {E : Spc} (hE : Inv q E) {n i : ℤ} (a : Ht q E n i) :
    cup q a (one q E) = a.cast (by ring) (by ring) := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q E a (one q E)]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  rw [(GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE a, c_cc]

private theorem cup_pow_zero {E : Spc} (hE : Inv q E) (ξ : Ht q E 2 1) {k : ℕ} (hk : k = 0) {n i : ℤ} (a : Ht q E n i) :
    cup q a (cpow q ξ k) = a.cast (by subst hk; simp) (by subst hk; simp) := by
  subst hk
  rw [cpow_zero, cup_cr, cup_one_r hE, c_cc]

private theorem cpow_one' {E : Spc} (hE : Inv q E) (ξ : Ht q E 2 1) :
    cpow q ξ 1 = ξ.cast (by simp) (by simp) := by
  refine (cpow_succ q ξ 0).trans ?_
  rw [cpow_zero, cup_cl, (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 E hE ξ, c_cc, c_cc]

private theorem cpow_zero_one {E : Spc} : cpow q (0 : Ht q E 2 1) 1 = 0 := by
  refine (cpow_succ q (0 : Ht q E 2 1) 0).trans ?_
  rw [map_zero, c_zero]

private theorem two_terms {X B : Spc} (p : B ⟶ X) (ξ : Ht q B 2 1) (hB : Inv q B) (n i : ℤ)
    (y : ∀ j : Fin 2, Ht q X (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ))) :
    ∑ j, ((cup q (pull _ p _ _ (y j)) (cpow q ξ j)).cast (by ring) (by ring) : Ht q B n i) =
      pull _ p _ _ ((y 0).cast (by simp) (by simp) : Ht q X n i) +
      (cup q (pull _ p _ _ ((y 1).cast (by simp) (by simp) : Ht q X (n - 2) (i - 1))) (cpow q ξ 1)).cast
        (by push_cast; ring) (by push_cast; ring) := by
  rw [Fin.sum_univ_two]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [cup_pow_zero hB ξ (k := ((0 : Fin 2) : ℕ)) rfl, c_cc, pull_c]
  · rw [pull_c, cup_cl, c_cc]
    rfl

private theorem succ_terms {E Y : Spc} (πY : Y ⟶ E) (ξ : Ht q Y 2 1) (hY : Inv q Y) (N : ℕ) (n i : ℤ)
    (a : Ht q E n i) (b : ∀ j : Fin N, Ht q E (n - 2 - 2 * (((j : ℕ) : ℤ))) (i - 1 - ((j : ℕ) : ℤ))) :
    ∑ j : Fin (N + 1), ((cup q (pull _ πY _ _ ((Fin.cases (motive := fun j : Fin (N + 1) =>
        Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ))) (a.cast (by simp) (by simp))
        (fun j => (b j).cast (by rw [Fin.val_succ]; push_cast; ring) (by rw [Fin.val_succ]; push_cast; ring)) j))) (cpow q ξ j)).cast
        (by ring) (by ring) : Ht q Y n i) =
      pull _ πY _ _ a + ∑ j : Fin N, ((cup q (pull _ πY _ _ (b j)) (cpow q ξ ((j : ℕ) + 1))).cast
        (by push_cast; ring) (by push_cast; ring) : Ht q Y n i) := by
  rw [Fin.sum_univ_succ]
  refine congrArg₂ (· + ·) ?_ (Finset.sum_congr rfl fun j _ => ?_)
  · rw [cup_pow_zero hY ξ (k := ((0 : Fin (N + 1)) : ℕ)) rfl, c_cc]
    simp only [Fin.cases_zero]
    rw [pull_c, c_cc]
    rfl
  · simp only [Fin.cases_succ]
    rw [pull_c, cup_cl, c_cc]
    rfl

private theorem rel_term {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y) (hp : p ≫ πX = β ≫ πY)
    (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1) (iX : Inv q X) (iY : Inv q Y) (iB : Inv q B)
    (hrel : ∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) =
      (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring))
    {m e n i : ℤ} (k : ℕ) (hn : m + 2 * (k : ℤ) = n - 2) (hi : e + (k : ℤ) = i - 1) (b : Ht q E m e) :
    ((cup q (pull _ p _ _ ((cup q (pull _ πX _ _ b) (cpow q ξX k)).cast hn hi)) (cpow q (pull _ β _ _ ξY) 1)).cast
        (by push_cast; ring) (by push_cast; ring) : Ht q B n i) =
      pull _ β _ _ ((cup q (pull _ πY _ _ b) (cpow q ξY (k + 1))).cast (by push_cast; omega) (by push_cast; omega) : Ht q Y n i) := by
  have e1 : (pull _ p _ _ (pull _ πX _ _ b) : Ht q B m e) = pull _ β _ _ (pull _ πY _ _ b) := by
    rw [← pull_comp, ← pull_comp, hp]
  rw [pull_c, pull_u, pull_c, pull_u, UpperTheory.pull_cupPow_eq_cupPow_pull q p ξX k iX, UpperTheory.pull_cupPow_eq_cupPow_pull q β ξY (k + 1) iY, e1, hrel k,
    cpow_one' iB, cup_cl, cup_cr, c_cc, GlobalTheory.T.tateTwistCupProduct_assoc, cup_cr, c_cc, c_cc, c_cc]

private theorem rel_sum {E X Y B : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y) (hp : p ≫ πX = β ≫ πY)
    (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1) (iX : Inv q X) (iY : Inv q Y) (iB : Inv q B)
    (hrel : ∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) =
      (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring))
    (N : ℕ) (n i : ℤ) (b : ∀ j : Fin N, Ht q E (n - 2 - 2 * (((j : ℕ) : ℤ))) (i - 1 - ((j : ℕ) : ℤ))) :
    ((cup q (pull _ p _ _ (∑ j : Fin N, ((cup q (pull _ πX _ _ (b j)) (cpow q ξX j)).cast (by ring) (by ring) : Ht q X (n - 2) (i - 1))))
        (cpow q (pull _ β _ _ ξY) 1)).cast (by push_cast; ring) (by push_cast; ring) : Ht q B n i) =
      pull _ β _ _ (∑ j : Fin N, ((cup q (pull _ πY _ _ (b j)) (cpow q ξY ((j : ℕ) + 1))).cast
        (by push_cast; ring) (by push_cast; ring) : Ht q Y n i)) := by
  rw [map_sum, map_sum, map_sum, AddMonoidHom.finset_sum_apply, c_sum]
  exact Finset.sum_congr rfl fun j _ => rel_term πX πY p β hp ξX ξY iX iY iB hrel _ (by ring) (by ring) (b j)

private theorem gysin_chase_identity {E X Y B W₁ B₁ : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y)
    (f₁ : W₁ ⟶ Y) (g₁ : B₁ ⟶ B) (b₁ : B₁ ⟶ W₁) (h₁ : g₁ ≫ β = b₁ ≫ f₁) (hp : p ≫ πX = β ≫ πY) (ξ : Ht q B 2 1)
    (iB : Inv q B) (hg : pull _ g₁ _ _ ξ = 0) {n i : ℤ} (hinj : Function.Injective (pull _ (g₁ ≫ p) (tw q i) n))
    (x : Ht q Y n i) (y0 : Ht q X n i) (y1 : Ht q X (n - 2) (i - 1)) (a0 : Ht q E n i)
    (hy : pull _ β _ _ x = pull _ p _ _ y0 + ((cup q (pull _ p _ _ y1) (cpow q ξ 1)).cast
      (by push_cast; ring) (by push_cast; ring) : Ht q B n i))
    (ha : pull _ (f₁ ≫ πY) _ _ a0 = pull _ f₁ _ _ x) : y0 = pull _ πX _ _ a0 := by
  apply hinj
  have e1 : pull _ g₁ _ _ ((cup q (pull _ p _ _ y1) (cpow q ξ 1)).cast
      (by push_cast; ring) (by push_cast; ring) : Ht q B n i) = 0 := by
    rw [pull_c, pull_u, UpperTheory.pull_cupPow_eq_cupPow_pull q g₁ ξ 1 iB, hg, cpow_zero_one, map_zero, c_zero]
  calc pull _ (g₁ ≫ p) _ _ y0 = pull _ g₁ _ _ (pull _ β _ _ x) := by
        rw [hy, map_add, e1, add_zero, pull_comp]
    _ = pull _ b₁ _ _ (pull _ f₁ _ _ x) := by rw [← pull_comp, h₁, pull_comp]
    _ = pull _ ((b₁ ≫ f₁) ≫ πY) _ _ a0 := by rw [← ha, ← pull_comp, Category.assoc]
    _ = pull _ (g₁ ≫ p) _ _ (pull _ πX _ _ a0) := by
        rw [← h₁, ← pull_comp, Category.assoc, Category.assoc, hp]

end UpperTheory.ChaseS

open UpperTheory.ChaseS in
theorem UpperTheory.leray_hirsch_of_two_covers_pullback_square :
    ∀ (q : ℕ) [NeZero q] (N : ℕ), 1 ≤ N → ∀ {E X Y B W₁ W₂ B₁ B₂ : Spc} (πX : X ⟶ E) (πY : Y ⟶ E) (p : B ⟶ X) (β : B ⟶ Y)
        (f₁ : W₁ ⟶ Y) (f₂ : W₂ ⟶ Y) (g₁ : B₁ ⟶ B) (g₂ : B₂ ⟶ B) (b₁ : B₁ ⟶ W₁) (b₂ : B₂ ⟶ W₂)
        (h₁ : g₁ ≫ β = b₁ ≫ f₁) (h₂ : g₂ ≫ β = b₂ ≫ f₂) (_ : p ≫ πX = β ≫ πY) (ξX : Ht q X 2 1) (ξY : Ht q Y 2 1),
        Inv q X → Inv q Y → Inv q B → Cover2 (ZMod q) f₁ f₂ → Cover2 (ZMod q) g₁ g₂ →
        LH q πX (fun j : Fin N => 2 * (((j : ℕ) : ℤ))) (fun j : Fin N => ((j : ℕ) : ℤ)) (fun j => cpow q ξX j) →
        LH q p (fun j : Fin 2 => 2 * (((j : ℕ) : ℤ))) (fun j : Fin 2 => ((j : ℕ) : ℤ)) (fun j => cpow q (pull _ β _ _ ξY) j) →
        (∀ i, Eqv _ (f₁ ≫ πY) (tw q i)) → (∀ i, Eqv _ (g₁ ≫ p) (tw q i)) → (∀ i, Eqv _ b₂ (tw q i)) →
        (∀ i, Eqv _ (pullback.map g₁ g₂ f₁ f₂ b₁ b₂ β h₁ h₂) (tw q i)) →
        pull _ g₁ _ _ (pull _ β _ _ ξY) = 0 →
        (∀ j : ℕ, cpow q (pull _ β _ _ ξY) (j + 1) = (cup q (cpow q (pull _ p _ _ ξX) j) (pull _ β _ _ ξY)).cast (by push_cast; ring) (by push_cast; ring)) →
        ∀ n i : ℤ, Function.Surjective fun a : ∀ j : Fin (N + 1), Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)) =>
          ∑ j, ((cup q (pull _ πY _ _ (a j)) (cpow q ξY j)).cast (by ring) (by ring) : Ht q Y n i) := by
  intro q _ N hN E X Y B W₁ W₂ B₁ B₂ πX πY p β f₁ f₂ g₁ g₂ b₁ b₂ h₁ h₂ hp ξX ξY iX iY iB c1 c2 lX lp ef eg eb eM hg hrel n i x
  obtain ⟨y, hy⟩ := (lp n i).2 (pull _ β _ _ x)
  have hy2 := (two_terms p (pull _ β _ _ ξY) iB n i y).symm.trans hy
  obtain ⟨y0, y1, hy3⟩ : ∃ (y0 : Ht q X n i) (y1 : Ht q X (n - 2) (i - 1)), pull _ β _ _ x = pull _ p _ _ y0 +
      ((cup q (pull _ p _ _ y1) (cpow q (pull _ β _ _ ξY) 1)).cast (by push_cast; ring) (by push_cast; ring) : Ht q B n i) :=
    ⟨_, _, hy2.symm⟩
  obtain ⟨a0, ha0⟩ := (ef i n).2 (pull _ f₁ _ _ x)
  have hy0 := gysin_chase_identity πX πY p β f₁ g₁ b₁ h₁ hp _ iB hg ((eg i n).1) x y0 y1 a0 hy3 ha0
  obtain ⟨b, hb⟩ := (lX (n - 2) (i - 1)).2 y1
  have hb' : ∑ j : Fin N, ((cup q (pull _ πX _ _ (b j)) (cpow q ξX j)).cast (by ring) (by ring) : Ht q X (n - 2) (i - 1)) = y1 := hb
  have hR := rel_sum πX πY p β hp ξX ξY iX iY iB hrel N n i b
  rw [hb'] at hR
  have hv := UpperTheory.leray_hirsch_of_two_element_cover q N hN πX πY p β f₁ f₂ g₁ g₂ b₁ b₂ h₁ h₂ hp ξX iX c1 c2 lX ef eg eb eM n i
    (x - pull _ πY _ _ a0 - ∑ j : Fin N, ((cup q (pull _ πY _ _ (b j)) (cpow q ξY ((j : ℕ) + 1))).cast
        (by push_cast; ring) (by push_cast; ring) : Ht q Y n i))
    (by
      rw [map_sub, map_sub, ← hR, hy3, hy0, ← pull_comp, ← pull_comp, hp]
      abel)
  refine ⟨Fin.cases (motive := fun j : Fin (N + 1) => Ht q E (n - 2 * (((j : ℕ) : ℤ))) (i - ((j : ℕ) : ℤ)))
    (Ht.cast (by simp) (by simp) a0)
    (fun j => Ht.cast (by rw [Fin.val_succ]; push_cast; ring) (by rw [Fin.val_succ]; push_cast; ring) (b j)), ?_⟩
  refine (succ_terms πY ξY iY N n i a0 b).trans ?_
  rw [sub_sub, sub_eq_zero] at hv
  exact hv.symm
