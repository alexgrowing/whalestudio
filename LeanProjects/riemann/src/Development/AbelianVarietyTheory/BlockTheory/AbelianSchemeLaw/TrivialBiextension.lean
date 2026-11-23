import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

universe u

attribute [local instance] Over.cartesianMonoidalCategory

def flatGen {X Y Z : Scheme.{u}} (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']
    (ψ : K' → (Y ⟶ X)) (δ : K' → ℤ) (φ : K → (Z ⟶ Y)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb (LB.LinComb L ψ δ) φ ε)) :
    LB.Gen (LB.LinComb L (K := K × K') (fun p => φ p.1 ≫ ψ p.2) (fun p => ε p.1 * δ p.2)) where
  s := fun j => res
    ((fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun l => Set.mem_iInter.1 hy (k, l)) :
      LB.wchart L (fun p : K × K' => φ p.1 ≫ ψ p.2) j ≤
        LB.wchart (LB.LinComb L ψ δ) φ (fun k l => j (k, l)))
    (t.s (fun k l => j (k, l)))

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

def pt {T : Over S} (a b : T ⟶ G) : T.left ⟶ (G2 G).left := (lift a b).left

def lawε : ULift.{u} (Fin 3) → ℤ := fun k => ![1, -1, -1] k.down

def law₁φ {T : Over S} (a a' b : T ⟶ G) : ULift.{u} (Fin 3) → (T.left ⟶ (G2 G).left) :=
  fun k => ![pt G (padd G a a') b, pt G a b, pt G a' b] k.down

def law₂φ {T : Over S} (a b b' : T ⟶ G) : ULift.{u} (Fin 3) → (T.left ⟶ (G2 G).left) :=
  fun k => ![pt G a (padd G b b'), pt G a b, pt G a b'] k.down

abbrev Law₁LB (P : LB (G2 G).left) : LB (G3 G).left :=
  LB.LinComb P (law₁φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε

abbrev Law₂LB (P : LB (G2 G).left) : LB (G3 G).left :=
  LB.LinComb P (law₂φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε

def pt₃ {T : Over S} (a b c : T ⟶ G) : T.left ⟶ (G3 G).left := (lift a (lift b c)).left

abbrev law₁At {P : LB (G2 G).left} (t : LB.Gen (Law₁LB G P)) {T : Over S} (a a' b : T ⟶ G) :=
  LB.pullGen P (law₁φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε t (pt₃ G a a' b)

abbrev law₂At {P : LB (G2 G).left} (t : LB.Gen (Law₂LB G P)) {T : Over S} (a b b' : T ⟶ G) :=
  LB.pullGen P (law₂φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε t (pt₃ G a b b')

structure Biext [IsCommMonObj G] (P : LB (G2 G).left) where

  isLB : P.IsLB

  law₁ : LB.Gen (Law₁LB G P)
  law₁_isGen : law₁.IsGen

  law₂ : LB.Gen (Law₂LB G P)
  law₂_isGen : law₂.IsGen

  comm₁ : LB.Gen.Corr P _ _ _ _ law₁ (law₁At G law₁ (x3 G 1) (x3 G 0) (x3 G 2))

  comm₂ : LB.Gen.Corr P _ _ _ _ law₂ (law₂At G law₂ (x3 G 0) (x3 G 2) (x3 G 1))

  assoc₁ : LB.Gen.Corr P _ _ _ _
    (LB.mulGen P _ _ _ _
      (law₁At G law₁ (padd G (x4 G 0) (x4 G 1)) (x4 G 2) (x4 G 3))
      (law₁At G law₁ (x4 G 0) (x4 G 1) (x4 G 3)))
    (LB.mulGen P _ _ _ _
      (law₁At G law₁ (x4 G 0) (padd G (x4 G 1) (x4 G 2)) (x4 G 3))
      (law₁At G law₁ (x4 G 1) (x4 G 2) (x4 G 3)))

  assoc₂ : LB.Gen.Corr P _ _ _ _
    (LB.mulGen P _ _ _ _
      (law₂At G law₂ (x4 G 0) (padd G (x4 G 1) (x4 G 2)) (x4 G 3))
      (law₂At G law₂ (x4 G 0) (x4 G 1) (x4 G 2)))
    (LB.mulGen P _ _ _ _
      (law₂At G law₂ (x4 G 0) (x4 G 1) (padd G (x4 G 2) (x4 G 3)))
      (law₂At G law₂ (x4 G 0) (x4 G 2) (x4 G 3)))

  compat : LB.Gen.Corr P _ _ _ _
    (LB.mulGen P _ _ _ _
      (law₂At G law₂ (padd G (x4 G 0) (x4 G 1)) (x4 G 2) (x4 G 3))
      (LB.mulGen P _ _ _ _
        (law₁At G law₁ (x4 G 0) (x4 G 1) (x4 G 2))
        (law₁At G law₁ (x4 G 0) (x4 G 1) (x4 G 3))))
    (LB.mulGen P _ _ _ _
      (law₁At G law₁ (x4 G 0) (x4 G 1) (padd G (x4 G 2) (x4 G 3)))
      (LB.mulGen P _ _ _ _
        (law₂At G law₂ (x4 G 0) (x4 G 2) (x4 G 3))
        (law₂At G law₂ (x4 G 1) (x4 G 2) (x4 G 3))))

def lamφ : ULift.{u} (Finset (Fin 2)) → ((G2 G).left ⟶ G.left) :=
  fun I => (psum G (x2 G) I.down).left

def lamε : ULift.{u} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

example (L : LB G.left) : abelian₂ G L = LB.LinComb L (lamφ G) lamε := rfl

def Biext.IsCube [IsCommMonObj G] {L : RigLB G} (B : Biext G (abelian₂ G L.L)) (c : CubicalStr G L) : Prop :=
  LB.Gen.Corr L.L _ _ (thφ G (x3 G)) thε
      (flatGen L.L (lamφ G) lamε (law₁φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε B.law₁) c.t ∧
  LB.Gen.Corr L.L _ _ (thφ G (x3 G)) thε
      (flatGen L.L (lamφ G) lamε (law₂φ G (x3 G 0) (x3 G 1) (x3 G 2)) lawε B.law₂) c.t

def LamBiext : Prop :=
  ∀ (S : Scheme.{u}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L),
    ∃ B : Biext G (abelian₂ G L.L), B.IsCube G c

def LamBiextNonempty : Prop :=
  ∀ (S : Scheme.{u}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G),
    Nonempty (CubicalStr G L) → Nonempty (Biext G (abelian₂ G L.L))

theorem LamBiext.nonempty (h : LamBiext.{u}) : LamBiextNonempty.{u} :=
  fun S G _ _ L ⟨c⟩ => let ⟨B, _⟩ := h S G L c; ⟨B⟩

lemma pt₃_pt {T : Over S} (a b c : T ⟶ G) (p q : G3 G ⟶ G) :
    pt₃ G a b c ≫ pt G p q = pt G (lift a (lift b c) ≫ p) (lift a (lift b c) ≫ q) := by
  rw [pt, pt, pt₃, ← Over.comp_left, comp_lift]

lemma pt₃_law₁φ {T : Over S} (a a' b : T ⟶ G) :
    (fun k => pt₃ G a a' b ≫ law₁φ G (x3 G 0) (x3 G 1) (x3 G 2) k) = law₁φ G a a' b := by
  funext ⟨k⟩
  fin_cases k <;> refine (pt₃_pt G _ _ _ _ _).trans ?_ <;>
    simp [law₁φ, padd, x3, comp_lift_assoc]

lemma pt₃_law₂φ {T : Over S} (a b b' : T ⟶ G) :
    (fun k => pt₃ G a b b' ≫ law₂φ G (x3 G 0) (x3 G 1) (x3 G 2) k) = law₂φ G a b b' := by
  funext ⟨k⟩
  fin_cases k <;> refine (pt₃_pt G _ _ _ _ _).trans ?_ <;>
    simp [law₂φ, padd, x3, comp_lift_assoc]

lemma sum_ulift_three (f : ULift.{u} (Fin 3) → ℤ) : ∑ k, f k = f ⟨0⟩ + f ⟨1⟩ + f ⟨2⟩ := by
  rw [← Equiv.ulift.symm.sum_comp, Fin.sum_univ_three]; rfl

lemma compat_sameSum {T : Over S} (a a' b b' : T ⟶ G) :
    LB.SameSum
      (Sum.elim (law₂φ G (padd G a a') b b') (Sum.elim (law₁φ G a a' b) (law₁φ G a a' b')))
      (Sum.elim lawε (Sum.elim lawε lawε))
      (Sum.elim (law₁φ G a a' (padd G b b')) (Sum.elim (law₂φ G a b b') (law₂φ G a' b b')))
      (Sum.elim lawε (Sum.elim lawε lawε)) := by
  intro ψ
  classical
  obtain ⟨c, hc⟩ : ∃ c : (T.left ⟶ (G2 G).left) → ℤ, ∀ (χ) (n : ℤ) (d : Decidable (χ = ψ)),
      (@ite _ (χ = ψ) d n 0) = n * c χ :=
    ⟨fun χ => if χ = ψ then 1 else 0, fun χ n d => by split_ifs <;> simp [*]⟩
  simp only [hc]
  simp only [Fintype.sum_sum_type, sum_ulift_three, Sum.elim_inl, Sum.elim_inr, law₁φ, law₂φ, lawε,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

def trivLB (X : Scheme.{u}) : LB X := ⟨PUnit, fun _ => ⊤, fun _ _ => 1⟩

section
variable {X Y Z : Scheme.{u}} (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']

lemma pull_one (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (h : Z ⟶ Y)
    (ht : ∀ j, t.s j = 1) (j) : (LB.pullGen L φ ε t h).s j = 1 := by
  unfold LB.pullGen
  dsimp only
  erw [ht]
  exact (congrArg _ (map_one _)).trans (map_one _)

lemma mul_one' (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht : ∀ j, t.s j = 1) (ht' : ∀ j, t'.s j = 1) (j) : (LB.mulGen L φ ε φ' ε' t t').s j = 1 := by
  unfold LB.mulGen
  dsimp only
  erw [ht, ht']
  exact (congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)

lemma corr_one (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε'))
    (ht : ∀ j, t.s j = 1) (ht' : ∀ j, t'.s j = 1) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' _ _ _
  erw [ht, ht']
  exact (map_one _).trans (map_one _).symm

lemma isGen_one (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Gen.IsGen (L := LB.LinComb (trivLB X) φ ε) ⟨fun _ => 1⟩ := by
  intro i j
  have hg : (LB.LinComb (trivLB X) φ ε).g i j = 1 :=
    Finset.prod_eq_one fun k _ =>
      (congrArg (· ^ ε k) ((congrArg _ (map_one _)).trans (map_one _))).trans (one_zpow _)
  rw [hg]
  exact (map_one _).trans ((_root_.one_mul _).trans (map_one _)).symm
end

def trivBiext [IsCommMonObj G] : Biext G (trivLB (G2 G).left) where
  isLB := ⟨@iSup_const _ PUnit _ _ _, fun _ => map_one _, fun _ _ _ =>
    ((congrArg₂ (· * ·) (map_one _) (map_one _)).trans (_root_.mul_one _)).trans (map_one _).symm⟩
  law₁ := ⟨fun _ => 1⟩
  law₁_isGen := isGen_one _ _
  law₂ := ⟨fun _ => 1⟩
  law₂_isGen := isGen_one _ _
  comm₁ := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  comm₂ := corr_one _ _ _ _ _ _ _ (fun _ => rfl) (pull_one _ _ _ _ _ fun _ => rfl)
  assoc₁ := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl)
      (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl)
      (pull_one _ _ _ _ _ fun _ => rfl))
  assoc₂ := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl)
      (pull_one _ _ _ _ _ fun _ => rfl))
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl)
      (pull_one _ _ _ _ _ fun _ => rfl))
  compat := corr_one _ _ _ _ _ _ _
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl)
      (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl)
      (pull_one _ _ _ _ _ fun _ => rfl)))
    (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl)
      (mul_one' _ _ _ _ _ _ _ (pull_one _ _ _ _ _ fun _ => rfl)
      (pull_one _ _ _ _ _ fun _ => rfl)))

end

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
