import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GtTorsionPoints

section Values

variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']

theorem corr_of_val_pull (hL : L.IsLB) (ρ : Z ⟶ Y) (hinj : ∀ U, Function.Injective (ρ.app U).hom)
    (hρ : ∀ a b : Y ⟶ X, ρ ≫ a = ρ ≫ b → a = b)
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro j j' c₁ c₂ c₃
  refine Units.ext (hinj _ (fn_ext fun z hz => ?_))
  have hz' : ρ z ∈ LB.wchart L φ j ⊓ LB.wchart L φ' j' := hz
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun k => ρ ≫ Sum.elim φ φ' k) (Sum.elim j j') (by
    rintro (a | a) (b | b) e <;> replace e := hρ _ _ e
    exacts [c₁ a b e, c₃ a b e, (c₃ b a e.symm).symm, c₂ a b e]) (by
    rintro (a | a)
    exacts [Set.mem_iInter.1 hz'.1 a, Set.mem_iInter.1 hz'.2 a])
  have := h z J hJ
  rw [val_of t _ z J j (fun k => e (.inl k)), val_of t' _ z J j' (fun k => e (.inr k))] at this
  rw [gs_pull (𝟙 Z) ρ z _ hz', gs_pull (𝟙 Z) ρ z _ hz', Category.id_comp, gs_unit ρ z _ hz', gs_unit ρ z _ hz']
  exact congrArg Units.val ((gm_res ρ z _ hz' _).trans (this.trans (gm_res ρ z _ hz' _).symm))

end Values

section Valuation

variable {S F : Type} [CommRing S] [IsDomain S] [ValuationRing S] [Field F] [Algebra S F] [IsFractionRing S F]

end Valuation

section Main

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F]
  {T : Over (Spec (CommRingCat.of R))} (ρ : TF (R := R) F ⟶ T)

def cubVal {Z : Scheme.{0}} (r : Z ⟶ (G3 D.P.A).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι) :
    (Z.presheaf.stalk z)ˣ :=
  val (L := D.P.L) (φ := thφ D.P.A (x3 D.P.A)) (ε := thε) D.cub.t r z J

theorem cF_eq (χ : D.X) : DegPre.cF D F χ = ρ ≫ DegPre.cT D T χ := by
  rw [← Category.assoc, comp_toUnit]

theorem zeroF_eq : DegPre.zeroF D F = ρ ≫ DegPre.zeroT D T := by
  rw [← Category.assoc, comp_toUnit]

theorem padd_comp (x y : T ⟶ D.P.A) : padd D.P.A (ρ ≫ x) (ρ ≫ y) = ρ ≫ padd D.P.A x y := by
  simp only [padd]
  rw [← Category.assoc, comp_lift]

theorem gtφ_eq (b : T ⟶ D.P.A) {b' : TF (R := R) F ⟶ D.P.A} (hb : b' = ρ ≫ b) (χ : D.X) (k : Fin 4) :
    DegPre.gtφ D F b' χ k = ρ.left ≫ DegPre.gtφT D T b χ k := by
  subst hb
  fin_cases k
  · change (padd D.P.A (DegPre.cF D F χ) (ρ ≫ b)).left = (ρ ≫ padd D.P.A (DegPre.cT D T χ) b).left
    rw [cF_eq D ρ, padd_comp]
  · change (DegPre.cF D F χ).left = (ρ ≫ DegPre.cT D T χ).left
    rw [cF_eq D ρ]
  · rfl
  · change (DegPre.zeroF D F).left = (ρ ≫ DegPre.zeroT D T).left
    rw [zeroF_eq D ρ]

variable {z : (TF (R := R) F).left} {J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι}

end Main

end GlobalTheory.GtTorsionPoints
