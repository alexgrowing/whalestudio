import Formalism.SharpRestriction.Divisibility.GeneratorPowers.JetSubstPSTrunc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l}

theorem act_zero : Xo.univ.t.act.act 0 = 1 := by
  have h := Xo.univ.t.act.add 0 0
  rw [add_zero] at h
  first
    | exact mul_eq_left.mp h.symm
    | exact mul_right_eq_self.mp h.symm
    | exact self_eq_mul_right.mp h
    | simpa using h

private theorem comp_psum_lemma {T T' : Over Xo.X} (f : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G))
    (S : Finset (Fin n)) :
    f ≫ psum Xo.univ.t.G xs S = psum Xo.univ.t.G (fun i => f ≫ xs i) S := by
  unfold psum
  generalize (List.finRange n).filter (· ∈ S) = L
  induction L with
  | nil =>
    simp only [List.foldr_nil, pzero]
    first
      | simp
      | rw [← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
  | cons k L ih =>
    simp only [List.foldr_cons]
    rw [← ih]
    simp only [padd]
    first
      | rw [CartesianMonoidalCategory.comp_lift_assoc]
      | simp

theorem comp_cφ {T T' : Over Xo.X} (f : T' ⟶ T) {n : ℕ} (xs : Fin n → (T ⟶ Xo.univ.t.G)) (I : ULift (Finset (Fin n))) :
    f.left ≫ cφ xs I = cφ (fun i => f ≫ xs i) I := by
  simp only [cφ]
  rw [← Over.comp_left, comp_psum_lemma]

theorem comp_thφ {T T' : Over Xo.X} (f : T' ⟶ T) (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) (I : thK) :
    f.left ≫ thφ Xo.univ.t.G xs I = thφ Xo.univ.t.G (fun i => f ≫ xs i) I := by
  simp only [thφ]
  rw [← Over.comp_left, comp_psum_lemma]

private theorem padd_eq_lemma_2 {T : Over Xo.X} (a b : T ⟶ Xo.univ.t.G) :
    padd Xo.univ.t.G a b = a * b := rfl

private theorem pzero_eq_lemma_3 (T : Over Xo.X) : pzero Xo.univ.t.G T = 1 := rfl

set_option maxHeartbeats 800000 in

theorem prod_cφ2 {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 2 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : ULift (Finset (Fin 2)), h (cφ xs I) ^ cε 2 I =
      h (1 : T ⟶ Xo.univ.t.G).left * (h (xs 0 * 1).left)⁻¹ * (h (xs 1 * 1).left)⁻¹ * h (xs 0 * (xs 1 * 1)).left := by
  have hsum : ∀ F : ULift (Finset (Fin 2)) → U,
      ∏ I : ULift (Finset (Fin 2)), F I = ∏ s : Finset (Fin 2), F (ULift.up s) :=
    fun F => Fintype.prod_equiv Equiv.ulift _ _ (fun _ => rfl)
  have hU : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  have f0 : (List.finRange 2).filter (· ∈ (∅ : Finset (Fin 2))) = [] := by decide
  have f1 : (List.finRange 2).filter (· ∈ ({0} : Finset (Fin 2))) = [0] := by decide
  have f2 : (List.finRange 2).filter (· ∈ ({1} : Finset (Fin 2))) = [1] := by decide
  have f3 : (List.finRange 2).filter (· ∈ ({0, 1} : Finset (Fin 2))) = [0, 1] := by decide
  have c3 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
  rw [hsum, hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [cφ, cε, psum, f0, f1, f2, f3, c3, List.foldr_cons, List.foldr_nil, padd_eq_lemma_2,
    pzero_eq_lemma_3, Finset.card_empty, Finset.card_singleton]
  clear hsum hU f0 f1 f2 f3 c3
  try norm_num only
  try simp only [zpow_one, zpow_neg, zpow_neg_one]
  rw [mul_assoc (h (Over.Hom.left (1 : T ⟶ Xo.univ.t.G))),
    mul_assoc (h (Over.Hom.left (1 : T ⟶ Xo.univ.t.G))), mul_assoc (h (xs 0 * 1).left)⁻¹]

set_option maxHeartbeats 800000 in

theorem cocycle_product_three {T : Over Xo.X} {U : Type} [CommGroup U] (h : (T.left ⟶ Xo.univ.t.G.left) → U)
    (xs : Fin 3 → (T ⟶ Xo.univ.t.G)) :
    ∏ I : thK, h (thφ Xo.univ.t.G xs I) ^ thε I =
      (h (1 : T ⟶ Xo.univ.t.G).left)⁻¹ * h (xs 0 * 1).left * h (xs 1 * 1).left * h (xs 2 * 1).left *
        (h (xs 0 * (xs 1 * 1)).left)⁻¹ * (h (xs 0 * (xs 2 * 1)).left)⁻¹ * (h (xs 1 * (xs 2 * 1)).left)⁻¹ *
          h (xs 0 * (xs 1 * (xs 2 * 1))).left := by
  have hsum : ∀ F : thK → U, ∏ I : thK, F I = ∏ s : Finset (Fin 3), F (ULift.up s) :=
    fun F => Fintype.prod_equiv (Equiv.ulift : thK ≃ Finset (Fin 3)) _ _ (fun _ => rfl)
  have hU : (Finset.univ : Finset (Finset (Fin 3))) =
      {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by decide
  have f0 : (List.finRange 3).filter (· ∈ (∅ : Finset (Fin 3))) = [] := by decide
  have f1 : (List.finRange 3).filter (· ∈ ({0} : Finset (Fin 3))) = [0] := by decide
  have f2 : (List.finRange 3).filter (· ∈ ({1} : Finset (Fin 3))) = [1] := by decide
  have f3 : (List.finRange 3).filter (· ∈ ({2} : Finset (Fin 3))) = [2] := by decide
  have f4 : (List.finRange 3).filter (· ∈ ({0, 1} : Finset (Fin 3))) = [0, 1] := by decide
  have f5 : (List.finRange 3).filter (· ∈ ({0, 2} : Finset (Fin 3))) = [0, 2] := by decide
  have f6 : (List.finRange 3).filter (· ∈ ({1, 2} : Finset (Fin 3))) = [1, 2] := by decide
  have f7 : (List.finRange 3).filter (· ∈ ({0, 1, 2} : Finset (Fin 3))) = [0, 1, 2] := by decide
  have c4 : ({0, 1} : Finset (Fin 3)).card = 2 := by decide
  have c5 : ({0, 2} : Finset (Fin 3)).card = 2 := by decide
  have c6 : ({1, 2} : Finset (Fin 3)).card = 2 := by decide
  have c7 : ({0, 1, 2} : Finset (Fin 3)).card = 3 := by decide
  rw [hsum, hU, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  simp only [thφ, thε, psum, f0, f1, f2, f3, f4, f5, f6, f7, c4, c5, c6, c7, List.foldr_cons,
    List.foldr_nil, padd_eq_lemma_2, pzero_eq_lemma_3, Finset.card_empty, Finset.card_singleton]
  clear hsum hU f0 f1 f2 f3 f4 f5 f6 f7 c4 c5 c6 c7
  try norm_num only
  try simp only [zpow_one, zpow_neg, zpow_neg_one]
  repeat rw [mul_assoc (h (1 : T ⟶ Xo.univ.t.G).left)⁻¹]
  repeat rw [mul_assoc (h (xs 0 * 1).left)]
  repeat rw [mul_assoc (h (xs 1 * 1).left)]
  repeat rw [mul_assoc (h (xs 2 * 1).left)]
  repeat rw [mul_assoc (h (xs 0 * (xs 1 * 1)).left)⁻¹]
  repeat rw [mul_assoc (h (xs 0 * (xs 2 * 1)).left)⁻¹]
  all_goals exact (rfl : (0 : ℕ) = 0)

abbrev AdTy (Xo : Moduli Dw l) (a : 𝓞 E) : Type :=
  LB.Gen (LB.LinComb Xo.univ.t.PP.L
    (Sum.elim (cφ ![fst Xo.univ.t.G Xo.univ.t.G, snd Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act (H.bar a)])
      (cφ ![fst Xo.univ.t.G Xo.univ.t.G ≫ Xo.univ.t.act.act a, snd Xo.univ.t.G Xo.univ.t.G]))
    (Sum.elim (cε 2) fun I => -cε 2 I))

abbrev wPc (wP : PrimTy H Xo) (c : 𝓞 E) :=
  LB.pullGen Xo.univ.t.PP.L _ _ wP (Xo.univ.t.act.act c).left

abbrev cubAt (p q r : Xo.univ.t.G ⟶ Xo.univ.t.G) :=
  LB.pullGen Xo.univ.t.PP.L (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) thε Xo.univ.t.cub.t (lift p (lift q r)).left

def Bq (wP : PrimTy H Xo) (a : 𝓞 E) (wLa : AdTy Xo a) (wLb : AdTy Xo (H.bar a)) :=
  let A := Xo.univ.t.act.act
  let b := a * H.bar a
  LB.mulGen Xo.univ.t.PP.L _ _ _ _
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (wPc wP (1 + b))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP a))
          (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP a))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.invGen Xo.univ.t.PP.L _ _ wP)
        (LB.invGen Xo.univ.t.PP.L _ _ (wPc wP b))))
    (LB.mulGen Xo.univ.t.PP.L _ _ _ _
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (cubAt (A 1) (A b) (A ((1 + b) * H.w0)))
        (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (cubAt (A H.w0) (A (b * H.w0)) (A 1))
          (cubAt (A H.w0) (A (b * H.w0)) (A b))))
      (LB.mulGen Xo.univ.t.PP.L _ _ _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wLa (lift (A 1) (A (a * H.w0))).left)
        (LB.invGen Xo.univ.t.PP.L _ _ (LB.pullGen Xo.univ.t.PP.L _ _ wLb (lift (A a) (A H.w0)).left))))

theorem Bq_isGen (wP : PrimTy H Xo) (hwP : wP.IsGen) (a : 𝓞 E) (wLa : AdTy Xo a) (hwa : wLa.IsGen)
    (wLb : AdTy Xo (H.bar a)) (hwb : wLb.IsGen) : (Bq wP a wLa wLb).IsGen := by
  have hP := fun c => ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ wP hwP (Xo.univ.t.act.act c).left
  have hC := fun (p q r : Xo.univ.t.G ⟶ Xo.univ.t.G) =>
    ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen Xo.univ.t.PP.L _ _ _ Xo.univ.t.cub.isGen (lift p (lift q r)).left
  unfold Bq
  refine ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hP _)
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))
          (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))))
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ hwP)
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (hP _))))
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hC _ _ _)
        (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _ (hC _ _ _) (hC _ _ _)))
      (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen _ _ _ _ _ _ _
        (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwa _)
        (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen _ _ _ _ hwb _))))

theorem exists_betaRaw (wP : PrimTy H Xo) (hwP : wP.IsGen) (a : 𝓞 E) (hbb : H.bar (H.bar a) = a)
    (wLa : AdTy Xo a) (hwa : wLa.IsGen) (wLb : AdTy Xo (H.bar a)) (hwb : wLb.IsGen) :
    ∃ β : LB.Gen (LB.LinComb Xo.univ.t.PP.L (betaφ (Xo := Xo) a) betaε), β.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Xo.univ.t.G.left) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι),
        Good Xo.univ.t.PP.L z J → val β r z J = val (Bq wP a wLa wLb) r z J := by
  have hL := Xo.univ.t.PP.isLB
  refine exists_gen hL ?_ _ (Bq_isGen wP hwP a wLa hwa wLb hwb)
  intro U _ hU
  unfold betaφ betaε
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Fin.prod_univ_four,
    comp_cφ, comp_thφ, Category.comp_id, zpow_neg, zpow_one, neg_neg, Finset.prod_inv_distrib, prod_cφ2, cocycle_product_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons, x3, lift_fst, lift_snd_assoc, lift_snd, lift_fst_assoc, Category.id_comp]
  have h1 : ∀ p q : 𝓞 E, Xo.univ.t.act.act p * Xo.univ.t.act.act q = Xo.univ.t.act.act (p + q) :=
    fun p q => (Xo.univ.t.act.add p q).symm
  have h2 : ∀ p q : 𝓞 E, Xo.univ.t.act.act p ≫ Xo.univ.t.act.act q = Xo.univ.t.act.act (p * q) :=
    fun p q => (Xo.univ.t.act.mul p q).symm
  have h3 : (1 : Xo.univ.t.G ⟶ Xo.univ.t.G) = Xo.univ.t.act.act 0 := act_zero.symm
  have h4 : 𝟙 Xo.univ.t.G = Xo.univ.t.act.act 1 := Xo.univ.t.act.one.symm
  have h5 : 𝟙 Xo.univ.t.G.left = (Xo.univ.t.act.act 1).left := by rw [Xo.univ.t.act.one]; rfl
  simp only [h3, h1, h2, hbb, h4, h5]
  ring_nf
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
  abel

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpGC
