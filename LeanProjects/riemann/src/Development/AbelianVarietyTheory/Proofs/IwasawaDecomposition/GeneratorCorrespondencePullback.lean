import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.LN GlobalTheory.TorRef GlobalTheory.IntegralCombination GlobalTheory.UU Formalism.L2.Pj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.IntFam
noncomputable section
namespace GlobalTheory.IntFam.TermLift

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

abbrev gB : D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (toUnit _) (𝟙 _)

abbrev trB (mu : D.X) : D.P.A ⟶ D.P.A := padd D.P.A (𝟙 _) (toUnit _ ≫ D.c mu)

omit [IsDomain R] in
theorem comp_padd {T T' : Over (Spec (CommRingCat.of R))} (A : Over (Spec (CommRingCat.of R))) [GrpObj A]
    (x : T' ⟶ T) (a b : T ⟶ A) : x ≫ padd A a b = padd A (x ≫ a) (x ≫ b) := by
  rw [padd, padd, ← Category.assoc, comp_lift]

omit [IsDomain R] in
theorem comp_toUnit {Y T W : Over (Spec (CommRingCat.of R))} (f : 𝟙_ _ ⟶ W) (x : T ⟶ Y) :
    x ≫ toUnit Y ≫ f = toUnit T ≫ f := by
  rw [← Category.assoc, toUnit_unique (x ≫ toUnit Y) (toUnit T)]

theorem gB_famφT (β : D.X) (i : Fin 4) : (gB D).left ≫ famφT D (𝟙_ _) β i = D.famφB β i := by
  fin_cases i
  · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (lift_snd (toUnit D.P.A) (𝟙 D.P.A))
  · refine congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (?_ : gB D ≫ padd D.P.A (snd _ _) (toUnit _ ≫ D.c β) = _)
    rw [comp_padd, lift_snd, comp_toUnit]
  · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (comp_toUnit (D.c β) (gB D))
  · exact congrArg (fun q : D.P.A ⟶ D.P.A => q.left) (comp_toUnit (MonObj.one : 𝟙_ _ ⟶ D.P.A) (gB D))

theorem gB_trT (mu : D.X) : gB D ≫ trT D (toUnit (𝟙_ _) ≫ D.c mu) = trB D mu ≫ gB D := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, Category.assoc, trT, lift_fst, lift_fst]
    exact toUnit_unique _ _
  · rw [Category.assoc, Category.assoc, trT, lift_snd, lift_snd, Category.comp_id, comp_padd, lift_snd,
      ← Category.assoc, lift_fst, comp_toUnit]

theorem gB_trT_famφT (mu α : D.X) (i : Fin 4) :
    (gB D).left ≫ (trT D (toUnit (𝟙_ _) ≫ D.c mu)).left ≫ famφT D (𝟙_ _) α i = (trB D mu).left ≫ D.famφB α i := by
  rw [← Category.assoc, ← Over.comp_left, gB_trT, Over.comp_left, Category.assoc, gB_famφT]

theorem formEq (k : ℕ) (α mu : D.X) :
    FormEq (Sum.elim (fun i => (trB D mu).left ≫ D.famφB α i)
        (fun i => (gB D).left ≫ deltaφT D (α + k • mu) α (toUnit (𝟙_ _) ≫ D.c mu) i))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.famφB (α + k • mu)) (DegPre.famε k) := by
  intro U _ h
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, deltaφT, DegPre.deltaε, gB_famφT, gB_trT_famφT,
    zpow_neg, Finset.prod_inv_distrib]
  rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem prB_gB : DegPre.prB D F ≫ gB D = toUnit (TF (R := R) F) ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, lift_fst, whiskerRight_fst]
    exact toUnit_unique _ _
  · rw [Category.assoc, lift_snd, whiskerRight_snd, Category.comp_id]

theorem trF_prB (mu : D.X) : DegPre.trF D F mu ≫ DegPre.prB D F = DegPre.prB D F ≫ trB D mu := by
  rw [DegPre.trF, lift_snd, comp_padd, Category.comp_id, comp_toUnit]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (k : ℕ) (α mu : D.X)
    (u₀ : LB.Gen (LB.LinComb D.P.L (deltaφT D (α + k • mu) α (toUnit (𝟙_ _) ≫ D.c mu)) (DegPre.deltaε k))) (a : R),
    u₀.IsGen → (∀ (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen →
        LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D (FractionRing R)).left)
          (DegPre.famMult D (FractionRing R) k mu α) →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D (FractionRing R)).left) (z : Z) (J), Good D.P.L z J →
          (val u r z J).val = gs r z ⊤ (scal (DegPre.BF D (FractionRing R)).hom a) *
            (val u₀ (r ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left) z J).val) →
    ∀ (σ : SecAb D k α) (Φ : Fam D (FractionRing R) k), Φ.s α = pullAb D (FractionRing R) k α σ →
      ∃ f : SecAb D k (α + k • mu), pullAb D (FractionRing R) k (α + k • mu) f = Φ.s (α + k • mu) := by
  intro R _ _ D k α mu u₀ a hu₀ hrel σ Φ hΦ
  have hL := D.P.isLB
  have hG : GlobalFnsSt := GlobalTheory.allSixLaws.1.globalFns
  obtain ⟨t, ht⟩ := exists_sec hL (formEq D k α mu)
    (pullMulSec σ (trB D mu).left (LB.pullGen D.P.L _ _ u₀ (gB D).left) (pullGen_isGen _ _ _ _ hu₀ _))
  refine ⟨a • (show SecAb D k (α + k • mu) from t), GlobalTheory.FieldBaseChange.sec_ext' hL fun y J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D) (F := FractionRing R) hG k mu α
  have e₁ := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (Φ.fe mu α u hu hc) _ (𝟙 _) y J hJ
  have e₂ := hrel u hu hc _ (𝟙 _) y J hJ
  rw [e₁, e₂, hΦ, sval_pullAb _ _ _ _ hJ, sval_pullAb _ _ _ _ hJ, GlobalTheory.FieldBaseChange.sval_smul' hJ,
    ht _ _ y J hJ]
  erw [sval_pullMulSec σ (trB D mu).left (LB.pullGen D.P.L _ _ u₀ (gB D).left) (pullGen_isGen _ _ _ _ hu₀ _)
    (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) y hJ]
  rw [val_pull hJ, GlobalTheory.FieldBaseChange.gs_scal]
  have m₁ : (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) ≫ (trB D mu).left =
      (𝟙 _ ≫ (DegPre.trF D (FractionRing R) mu).left) ≫ (DegPre.prB D (FractionRing R)).left := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, ← Over.comp_left, trF_prB]
  have m₂ : (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) ≫ (gB D).left =
      𝟙 _ ≫ (toUnit (TF (R := R) (FractionRing R)) ▷ D.P.A).left := by
    rw [Category.id_comp, Category.id_comp, ← Over.comp_left, prB_gB]
  have m₃ : (𝟙 _ ≫ (DegPre.prB D (FractionRing R)).left) ≫ D.P.A.hom = 𝟙 _ ≫ (DegPre.BF D (FractionRing R)).hom := by
    rw [Category.assoc, Over.w]
  rw [m₁, m₂, m₃]
  ring

end GlobalTheory.IntFam.TermLift
