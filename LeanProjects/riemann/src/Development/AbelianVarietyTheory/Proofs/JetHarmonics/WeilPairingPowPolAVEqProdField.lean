import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGenOfSection
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSec
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilPower

open GlobalTheory.CommutatorPairing GlobalTheory.BoxPhi

variable {S : Scheme.{0}} {j : ℕ} {A A' : PolAV S} (pA : IsPowPolAV A' A j) {k : ℤ} {T : Over S}

theorem exists_box_theta (x : T ⟶ A'.A) (θ : Fin j → ThetaGrp A.A A.L k T) (hθ : ∀ i, (θ i).pt = x ≫ pA.pr i) :
    ∃ θ' : ThetaGrp A'.A A'.L k T, θ'.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A'.A) (z : Z.left) (J J'),
      Good A.L z J → Good A'.L z J' →
      om pA.w z J J' a.left ^ k * om pA.w z J J' ((t ≫ x) * a).left ^ (-k) * thetaVal θ' t a z J' =
        ∏ i, thetaVal (θ i) t (a ≫ pA.pr i) z J := by
  have hP : ∀ i, translPt A'.A x ≫ pA.pr i = T ◁ pA.pr i ≫ translPt A.A (θ i).pt := fun i => by
    have := pA.hom i
    rw [hθ, BoxTheta.translPt_hom]
  obtain ⟨u, hu, hv⟩ := exists_box_gen (pr := fun i => (pA.pr i).left) A.isLB A'.isLB pA.w pA.w_gen (K := Fin 2)
    (φ' := ![(snd T A'.A).left, (translPt A'.A x).left])
    (φ := fun i => ![(snd T A.A).left, (translPt A.A (θ i).pt).left]) (ε := ![k, -k])
    (p := fun i => (T ◁ pA.pr i).left) (fun i a => by
      fin_cases a
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T (pA.pr i)).symm
      · exact congrArg (fun q => q.left) (hP i)) (fun i => (θ i).φ) (fun i => (θ i).isGen)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J J' hJ hJ' => ?_⟩
  have e := hv _ (lift t a).left z J J' hJ hJ'
  rw [prod_theta x t a (om pA.w z J J')] at e
  refine e.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← Over.comp_left, lift_whiskerLeft]
  rfl

theorem commVal_pow (hG : GlobalFnsSt) (θx' θy' : ThetaGrp A'.A A'.L k T) (θx θy : Fin j → ThetaGrp A.A A.L k T)
    (hx : ∀ i, (θx i).pt = θx'.pt ≫ pA.pr i) (hy : ∀ i, (θy i).pt = θy'.pt ≫ pA.pr i)
    {Z : Over S} (t : Z ⟶ T) (a : Z ⟶ A'.A) (z : Z.left) {J J'} (hJ : Good A.L z J) (hJ' : Good A'.L z J') :
    commVal θx' θy' t a z J' = ∏ i, commVal (θx i) (θy i) t (a ≫ pA.pr i) z J := by
  have := A'.isAb.comm
  obtain ⟨bx, ex, vx⟩ := exists_box_theta pA θx'.pt θx hx
  obtain ⟨by', ey, vy⟩ := exists_box_theta pA θy'.pt θy hy
  rw [commVal_indep hG A'.isAb A'.isLB θx' θy' bx by' t t (by rw [ex]) (by rw [ey]) a z J' hJ']
  have m : ∀ (x : T ⟶ A'.A) (i), ((t ≫ x) * a) ≫ pA.pr i = (t ≫ x ≫ pA.pr i) * (a ≫ pA.pr i) := fun x i => by
    have := pA.hom i
    rw [MonObj.mul_comp, Category.assoc]
  have e₁ := vx Z t a z J J' hJ hJ'
  have e₂ := vy Z t ((t ≫ θx'.pt) * a) z J J' hJ hJ'
  have e₃ := vy Z t a z J J' hJ hJ'
  have e₄ := vx Z t ((t ≫ θy'.pt) * a) z J J' hJ hJ'
  rw [mul_left_comm (t ≫ θy'.pt)] at e₂
  simp only [m, ← hx, ← hy] at e₂ e₄
  simp only [commVal, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← e₁, ← e₂, ← e₃, ← e₄, ex, ey, zpow_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem weilIs_pow (hG : GlobalFnsSt) [Subsingleton T.left] (x y : T ⟶ A'.A) (c : Fin j → Γ(T.left, ⊤)ˣ)
    (h : ∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (y ≫ pA.pr i) (c i)) : WeilIs A'.A A'.L k x y (∏ i, c i) := by
  intro p
  have h' : ∀ i, (∃ θx θy : ThetaGrp A.A A.L k (overRes ⊤), θx.pt = overResι ⊤ ≫ x ≫ pA.pr i ∧
      θy.pt = overResι ⊤ ≫ y ≫ pA.pr i) ∧ ∀ θx θy : ThetaGrp A.A A.L k (overRes ⊤),
      θx.pt = overResι ⊤ ≫ x ≫ pA.pr i → θy.pt = overResι ⊤ ≫ y ≫ pA.pr i →
      CommIsOf A.A A.L k θx θy (unitRes ⊤ (c i)) := fun i => by
    obtain ⟨V, hV, H⟩ := h i p
    obtain rfl : V = ⊤ := top_le_iff.1 fun q _ => by rw [Subsingleton.elim q p]; exact hV
    exact H
  choose θx θy hx hy using fun i => (h' i).1
  obtain ⟨bx, ex, -⟩ := exists_box_theta pA (overResι ⊤ ≫ x) θx (fun i => by rw [hx, Category.assoc])
  obtain ⟨by', ey, -⟩ := exists_box_theta pA (overResι ⊤ ≫ y) θy (fun i => by rw [hy, Category.assoc])
  refine ⟨⊤, trivial, ⟨bx, by', ex, ey⟩, fun θx' θy' ex' ey' => (commIsOf_iff A'.isLB _ _ _).2 fun Z t a z J' hJ' => ?_⟩
  choose J hJ using fun χ : Z.left ⟶ A.A.left => exists_chart A.isLB (χ z)
  rw [commVal_pow pA hG θx' θy' θx θy (fun i => by rw [hx, ex', Category.assoc])
    (fun i => by rw [hy, ey', Category.assoc]) t a z hJ hJ']
  refine (Finset.prod_congr rfl fun i _ => (commIsOf_iff A.isLB _ _ _).1 ((h' i).2 _ _ (hx i) (hy i)) Z t _ z J hJ).trans ?_
  exact (map_prod _ _ _).symm.trans (congrArg _ (map_prod (Units.map (⊤ : T.left.Opens).ι.appTop.hom.toMonoidHom) c _).symm)

theorem weilIs_pow_field : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (x x' : TFK (R := R) F ⟶ A'.A) (c : Fin j → Fˣ), (∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (x' ≫ pA.pr i) (unitOn (c i))) → WeilIs A'.A A'.L k x x' (unitOn (∏ i, c i)) := by
  intro hL _ _ _ R _ _ j A A' pA F _ _ k _ x x' c h
  have : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  have e : unitOn (∏ i, c i) = ∏ i, unitOn (c i) := map_prod (Units.map _) _ _
  rw [e]
  exact weilIs_pow pA hL.globalFns x x' (fun i => unitOn (c i)) h

end GlobalTheory.WeilPower
