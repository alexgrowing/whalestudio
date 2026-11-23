import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

variable {S : Scheme.{0}}

theorem prod_alt_const {U : Type} [CommGroup U] (m : U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), m ^ ((-1 : ℤ) ^ (2 - I.down.card)) = 1 := by
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => m ^ ((-1 : ℤ) ^ (2 - I.card))) (fun I => rfl)).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp

theorem lift_one_psum {G : Over S} [GrpObj G] [IsCommMonObj G] {T : Over S} (I : Finset (Fin 2)) :
    lift (1 : T ⟶ G) (1 : T ⟶ G) ≫ psum G (x2 G) I = 1 := by
  rw [comp_psum]
  have e : (fun k => lift (1 : T ⟶ G) (1 : T ⟶ G) ≫ x2 G k) = fun _ => (1 : T ⟶ G) := by
    funext k
    fin_cases k <;> simp [x2]
  rw [e]
  unfold psum
  induction ((List.finRange 2).filter (· ∈ I)) with
  | nil => simp only [List.foldr_nil, pzero]; rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    show (1 : T ⟶ G) * 1 = 1
    exact _root_.mul_one _

variable {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]

theorem kappa_comp_mφ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b] (k : MK) :
    (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left ≫ mφ H₁ H₂ a b k =
      Sum.elim (fun _ => (1 : H₁ ⊗ H₁ ⟶ H₂).left ≫ coprod.inr) (fun _ => (1 : H₁ ⊗ H₁ ⟶ H₁).left ≫ coprod.inl) k := by
  rcases k with I | I
  · simp only [mφ, Sum.elim_inl]
    rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, comp_lift, lift_fst_assoc,
      lift_snd_assoc, MonObj.one_comp, MonObj.one_comp, lift_one_psum]
  · simp only [mφ, Sum.elim_inr]
    rw [← Category.assoc, ← Over.comp_left, lift_one_psum]

theorem exists_isNrm : ∀ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    {L₁ : LB H₁.left} {L₂ : LB H₂.left}, (join L₁ L₂).IsLB → ∀ (a b : H₁ ⟶ H₂) [IsMonHom a] [IsMonHom b]
    (t : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)), t.IsGen →
    ∃ u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε), IsNrm u := by
  intro S H₁ H₂ _ _ _ _ L₁ L₂ hL a b _ _ t ht
  have p : ∀ (V : Type) [CommGroup V] (k : ((H₁ ⊗ H₁).left ⟶ H₁.left ⨿ H₂.left) → V),
      ∏ i : MK, k ((lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left ≫ mφ H₁ H₂ a b i) ^ mε i = 1 := by
    intro V _ k
    rw [Fintype.prod_sum_type]
    simp only [kappa_comp_mφ, Sum.elim_inl, Sum.elim_inr, mε, zpow_neg, Finset.prod_inv_distrib]
    rw [prod_alt_const, prod_alt_const, inv_one, _root_.mul_one]
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := mφ H₁ H₂ a b) (ε' := mε)
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := MK) (K' := MK) (U := V) _
        (c := ∏ i, k (mφ H₁ H₂ a b i) ^ mε i) rfl (DVR.prod_neg _ _ (p V k))) ?_
      simp)
    (LB.mulGen _ _ _ _ _ t (LB.invGen _ _ _ (LB.pullGen _ _ _ t (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, fun y J hJ => ?_⟩
  have e : (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left ≫ (lift (1 : H₁ ⊗ H₁ ⟶ H₁) (1 : H₁ ⊗ H₁ ⟶ H₁)).left =
      (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
  rw [hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

end GlobalTheory.HomMum
