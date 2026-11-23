import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTraitImports
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

namespace GlobalTheory.ThetaMove

theorem exists_down_three {XA XP XG XT Y Y' : Scheme.{0}} {LA : LB XA} {LP : LB XP} {LG : LB XG} {LT : LB XT}
    (hA : LA.IsLB) (hP : LP.IsLB) (hG : LG.IsLB) (hT : LT.IsLB) {α : XA ⟶ XP} {β : XG ⟶ XP} {c : XT ⟶ XG}
    (wA : LB.Iso LA (LP.pull α)) (hwA : wA.IsGen) (ℓ : LB.Iso LG (LP.pull β)) (hℓ : ℓ.IsGen)
    (w : LB.Iso LT (LG.pull c)) (hw : w.IsGen) (f : Y' ⟶ Y) (sA mA : Y ⟶ XA) (sT mT : Y' ⟶ XT) (e' : Y' ⟶ Y')
    (h₁ : f ≫ sA ≫ α = sT ≫ c ≫ β) (h₂ : e' ≫ sT = mT) (h₃ : e' ≫ f ≫ sA = f ≫ mA) (k : ℤ)
    (u : LB.Gen (LB.LinComb LA ![sA, mA] ![k, -k])) (hu : u.IsGen) :
    ∃ u' : LB.Gen (LB.LinComb LT ![sT, mT] ![k, -k]), u'.IsGen ∧ ∀ (Z : Scheme.{0}) (q : Z ⟶ Y') (z : Z) JP JA JG Jt,
      Good LP z JP → Good LA z JA → Good LG z JG → Good LT z Jt →
      val u (q ≫ f) z JA = tf wA ℓ w f sA sT q z JP JA JG Jt ^ k * val u' q z Jt *
        (tf wA ℓ w f sA sT (q ≫ e') z JP JA JG Jt ^ k)⁻¹ := by
  have hm : f ≫ mA ≫ α = mT ≫ c ≫ β := by
    rw [← h₂, Category.assoc, ← h₁, ← Category.assoc f mA, ← h₃]
    simp only [Category.assoc]
  obtain ⟨t₁, ht₁, v₁⟩ := exists_up ((isGen_iff wA).1 hwA) hP hA (φ' := ![sA, mA]) (ε := ![k, -k]) u hu
  obtain ⟨t₂, ht₂, v₂⟩ := GlobalTheory.ArcPull.exists_down_om hℓ hP hG (φ' := ![sT ≫ c, mT ≫ c]) f (fun i => by
      fin_cases i
      · simpa using h₁.symm
      · simpa using hm.symm) t₁ ht₁
  obtain ⟨u', hu', v₃⟩ := GlobalTheory.ArcPull.exists_down_om hw hG hT (φ' := ![sT, mT]) (φ := ![sT ≫ c, mT ≫ c]) (𝟙 Y')
    (fun i => by fin_cases i <;> simp) t₂ ht₂
  refine ⟨u', hu', fun Z q z JP JA JG Jt hP' hA' hG' hT' => ?_⟩
  have e₁ : val t₁ (q ≫ f) z JP = pw wA ![sA, mA] ![k, -k] (q ≫ f) z (fun i => JP ((q ≫ f) ≫ ![sA, mA] i ≫ α))
      (fun i => JA ((q ≫ f) ≫ ![sA, mA] i)) * val u (q ≫ f) z JA :=
    v₁ Z (q ≫ f) z _ _ (hP'.mem _ _) (hA'.mem _ _)
  have e₂ := v₂ Z q z JP JG hP' hG'
  have e₃ := v₃ Z q z JG Jt hG' hT'
  rw [Category.comp_id] at e₃
  rw [e₂, e₃] at e₁
  simp only [pw, GlobalTheory.ArcPull.om, tf, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Category.assoc] at e₁ ⊢
  simp only [reassoc_of% h₁, reassoc_of% hm, reassoc_of% h₂, reassoc_of% h₃, h₁, hm, h₂, h₃] at e₁ ⊢
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul e₁
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
  linear_combination (norm := module) -e'

end GlobalTheory.ThetaMove
