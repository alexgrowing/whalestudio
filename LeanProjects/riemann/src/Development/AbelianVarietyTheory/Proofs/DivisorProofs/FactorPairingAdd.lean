import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FactorAdd

open GlobalTheory.CechPic

variable {S S' : Scheme.{0}}

theorem comp_psum {G T T' : Over S} [GrpObj G] [IsCommMonObj G] (u : T' ⟶ T) {n : ℕ} (x : Fin n → (T ⟶ G))
    (x' : Fin n → (T' ⟶ G)) (h : ∀ i, u ≫ x i = x' i) (I : Finset (Fin n)) :
    u.left ≫ (psum G x I).left = (psum G x' I).left :=
  congrArg (fun q => q.left) ((psum_hom (preHom u) x I).trans (congrArg (fun q => psum G q I) (funext h)))

theorem pull_lam {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (h : (abelian₂ G L).IsLB)
    (x y : T ⟶ G) :
    pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L) h) =
      pull (x * y).left (cls L hL) - pull x.left (cls L hL) - pull y.left (cls L hL) +
        pull (1 : T ⟶ G).left (cls L hL) := by
  have e := cls_linComb hL (K := ULift.{0} (Finset (Fin 2))) (fun I => (psum G (x2 G) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) h
  refine (congrArg (pull (lift x y : T ⟶ G2 G).left) e).trans ?_
  rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (2 - I.card)) • pull (psum G ![x, y] I).left (cls L hL)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x y : T ⟶ G2 G) (x2 G) ![x, y] (fun i => by fin_cases i <;> simp [x2])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, y] ∅ = 1 := rfl
  have p₁ : psum G ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum G ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [neg_smul, one_smul]
  abel

theorem cube {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (x x' y : T ⟶ G) :
    pull (x * x' * y).left (cls L.L L.isLB) - pull (x * x').left (cls L.L L.isLB) - pull (x * y).left (cls L.L L.isLB)
      - pull (x' * y).left (cls L.L L.isLB) + pull x.left (cls L.L L.isLB) + pull x'.left (cls L.L L.isLB)
      + pull y.left (cls L.L L.isLB) - pull (1 : T ⟶ G).left (cls L.L L.isLB) = 0 := by
  have h : (Theta G L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have z : cls (Theta G L.L) h = 0 := (cls_eq_zero_iff h).2 ⟨c.t, c.isGen⟩
  have e := cls_linComb L.isLB (K := ULift.{0} (Finset (Fin 3))) (fun I => (psum G (x3 G) I.down).left)
    (fun I => (-1) ^ (3 - I.down.card)) h
  have e' := (congrArg (pull (lift x (lift x' y) : T ⟶ G3 G).left) (e.symm.trans z)).trans (map_zero _)
  refine Eq.trans (Eq.symm ?_) e'
  rw [map_sum]
  refine (Fintype.sum_equiv Equiv.ulift _
    (fun I => ((-1 : ℤ) ^ (3 - I.card)) • pull (psum G ![x, x', y] I).left (cls L.L L.isLB)) fun I => ?_).trans ?_
  · rw [map_zsmul, ← pull_comp, comp_psum (lift x (lift x' y) : T ⟶ G3 G) (x3 G) ![x, x', y]
      (fun i => by fin_cases i <;> simp [x3])]
    rfl
  rw [show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have p₀ : psum G ![x, x', y] ∅ = 1 := rfl
  have p₁ : psum G ![x, x', y] {0} = x := _root_.mul_one x
  have p₂ : psum G ![x, x', y] {1} = x' := _root_.mul_one x'
  have p₃ : psum G ![x, x', y] {2} = y := _root_.mul_one y
  have p₄ : psum G ![x, x', y] {0, 1} = x * x' := congrArg (x * ·) (_root_.mul_one x')
  have p₅ : psum G ![x, x', y] {0, 2} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have p₆ : psum G ![x, x', y] {1, 2} = x' * y := congrArg (x' * ·) (_root_.mul_one y)
  have p₇ : psum G ![x, x', y] {0, 1, 2} = x * x' * y :=
    (congrArg (fun q => x * (x' * q)) (_root_.mul_one y)).trans (_root_.mul_assoc _ _ _).symm
  have q₀ : (-1 : ℤ) ^ (3 - (∅ : Finset (Fin 3)).card) = -1 := by decide
  have q₁ : ∀ i : Fin 3, (-1 : ℤ) ^ (3 - ({i} : Finset (Fin 3)).card) = 1 := by decide
  have q₄ : (-1 : ℤ) ^ (3 - ({0, 1} : Finset (Fin 3)).card) = -1 := by decide
  have q₅ : (-1 : ℤ) ^ (3 - ({0, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₆ : (-1 : ℤ) ^ (3 - ({1, 2} : Finset (Fin 3)).card) = -1 := by decide
  have q₇ : (-1 : ℤ) ^ (3 - ({0, 1, 2} : Finset (Fin 3)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, p₄, p₅, p₆, p₇, q₀, q₁, q₁, q₁, q₄, q₅, q₆, q₇]
  simp only [neg_smul, one_smul]
  abel

theorem lam_add {G T : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L) (h : (abelian₂ G L.L).IsLB)
    (x x' y : T ⟶ G) :
    pull (lift (x * x') y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) - pull (lift x y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h)
      - pull (lift x' y : T ⟶ G2 G).left (cls (abelian₂ G L.L) h) = 0 := by
  rw [pull_lam L.isLB, pull_lam L.isLB, pull_lam L.isLB, ← cube c x x' y]
  abel

theorem lift_square {G : Over S} {H : Over S'} [GrpObj G] [GrpObj H] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x y : T ⟶ H) :
    (lift x y : T ⟶ G2 H).left ≫ κ = (lift (pushHom hp T x) (pushHom hp T y) : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
  have A : ∀ (p q : Over.mk (T.hom ≫ f) ⟶ G), p.left = x.left ≫ φ → q.left = y.left ≫ φ →
      (lift x y : T ⟶ G2 H).left ≫ κ = (lift p q : Over.mk (T.hom ≫ f) ⟶ G2 G).left := by
    intro p q hp' hq'
    apply pullback.hom_ext
    · show (_ ≫ κ) ≫ (fst G G).left = (lift p q ≫ fst G G).left
      rw [lift_fst, hp', Category.assoc, hκ.1, ← Category.assoc, ← Over.comp_left, lift_fst]
    · show (_ ≫ κ) ≫ (snd G G).left = (lift p q ≫ snd G G).left
      rw [lift_snd, hq', Category.assoc, hκ.2, ← Category.assoc, ← Over.comp_left, lift_snd]
  exact A _ _ rfl rfl

theorem exists_gen {G G' : Over S} {H : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] [GrpObj H]
    {L : RigLB G'} (c : CubicalStr G' L) (a b : G ⟶ G') [IsMonHom a] {f : S' ⟶ S} {φ : H.left ⟶ G.left}
    (hp : IsGrpPullback H G f φ) {κ : (G2 H).left ⟶ (G2 G).left} (hκ : Geo.Tor.IsSquare (G' := H) (G := G) φ κ)
    {T : Over S'} (x x' y : T ⟶ H) (ψ : Fin 3 → (T.left ⟶ (G2 H).left))
    (h₀ : ψ 0 = (lift (x * x') y : T ⟶ G2 H).left) (h₁ : ψ 1 = (lift x y : T ⟶ G2 H).left)
    (h₂ : ψ 2 = (lift x' y : T ⟶ G2 H).left) :
    ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' L.L).pull (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left).pull κ)
      (K := Fin 3) ψ ![1, -1, -1]), u.IsGen := by
  have hΛ : (abelian₂ G' L.L).IsLB := LB.isLB_linComb L.isLB _ _
  have hP := pull_isLB (pull_isLB hΛ (lift (fst G G ≫ a) (snd G G ≫ b) : G2 G ⟶ G2 G').left) κ
  have key : ∀ p q : T ⟶ H, pull (lift p q : T ⟶ G2 H).left (cls _ hP) =
      pull (lift (pushHom hp T p ≫ a) (pushHom hp T q ≫ b) : Over.mk (T.hom ≫ f) ⟶ G2 G').left (cls _ hΛ) := by
    intro p q
    rw [cls_pull (pull_isLB hΛ _), cls_pull hΛ, ← pull_comp, ← pull_comp, lift_square hp hκ]
    refine congrArg (fun m => pull m (cls _ hΛ)) ?_
    refine congrArg (fun m : Over.mk (T.hom ≫ f) ⟶ G2 G' => m.left)
      (show lift (pushHom hp T p) (pushHom hp T q) ≫ lift (fst G G ≫ a) (snd G G ≫ b) = _ from ?_)
    simp
  refine (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).1 ?_
  rw [cls_linComb hP, Fin.sum_univ_three, h₀, h₁, h₂, key, key, key, map_mul, MonObj.mul_comp]
  have e := lam_add c hΛ (pushHom hp T x ≫ a) (pushHom hp T x' ≫ a) (pushHom hp T y ≫ b)
  refine Eq.trans ?_ e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    one_smul, neg_smul, sub_eq_add_neg]

end GlobalTheory.Mum.FactorAdd

theorem GlobalTheory.Mum.factorPairing_add : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen := by
  intro R _ _ _ _ D D' F A' G' _ _ _ U' oA oG _ G _ _ _ inc pr hinc _ _ _ κ₀ hκ
  exact GlobalTheory.Mum.FactorAdd.exists_gen U'.cubG inc (inc ≫ oG.act F.f) (isGrpPullback_pullback G (jK R)) hκ
    (fst _ _) (snd _ _ ≫ fst _ _) (snd _ _ ≫ snd _ _) _ rfl rfl
    (by rw [lift_comp_fst_snd]; rfl)
