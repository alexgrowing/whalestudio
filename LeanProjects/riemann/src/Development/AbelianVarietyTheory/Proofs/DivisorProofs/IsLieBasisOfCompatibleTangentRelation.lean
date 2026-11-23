import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TanRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationPointsAddPullTangent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorLiftsToDegenerationPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationTangentPointUniqueLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentRelationAdditiveScaling
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPointOfIffThick
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsEigenvectorIffLieBasisCoordinates
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LieTransfer

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent

variable {R : Type} [CommRing R] {G H : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]

theorem rel_comb (Rel : (epsR R ⟶ G) → (epsR R ⟶ H) → Prop) (h1 : Rel 1 1)
    (hmul : ∀ y y' x x', Rel y x → Rel y' x' → Rel (y * y') (x * x'))
    (hsc : ∀ (c : R) (y : epsR R ⟶ G) (x : epsR R ⟶ H) (y' : epsR R ⟶ G) (x' : epsR R ⟶ H),
      y'.left = spMap (epsScaleR c) ≫ y.left → x'.left = spMap (epsScaleR c) ≫ x.left → Rel y x → Rel y' x')
    {n : ℕ} (x : Fin n → (epsR R ⟶ H)) (y : Fin n → (epsR R ⟶ G)) (hr : ∀ j, Rel (y j) (x j))
    (c : Fin n → R) : Rel (comb y c) (comb x c) := by
  classical
  unfold comb
  suffices h : ∀ s : Finset (Fin n), Rel (∏ i ∈ s, epsScale (c i) ≫ y i) (∏ i ∈ s, epsScale (c i) ≫ x i) from h _
  intro s
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using h1
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact hmul _ _ _ _ (hsc (c a) (y a) (x a) _ _ rfl rfl (hr a)) ih

end GlobalTheory.LieTransfer

open GlobalTheory.Reg.VecEig GlobalTheory.LieTransfer in

theorem GlobalTheory.LieTransfer.isLieBasis_of_rel : ∀ (R : Type) [CommRing R] (G H : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (Rel : (epsR R ⟶ G) → (epsR R ⟶ H) → Prop), Rel 1 1 → (∀ y y' x x', Rel y x → Rel y' x' → Rel (y * y') (x * x')) → (∀ (c : R) (y : epsR R ⟶ G) (x : epsR R ⟶ H) (y' : epsR R ⟶ G) (x' : epsR R ⟶ H), y'.left = spMap (epsScaleR c) ≫ y.left → x'.left = spMap (epsScaleR c) ≫ x.left → Rel y x → Rel y' x') → (∀ y, IsTangent y → ∃ x, IsTangent x ∧ Rel y x) → (∀ y y' x, IsTangent y → IsTangent y' → Rel y x → Rel y' x → y = y') → (∀ y x x', Rel y x → Rel y x' → x = x') → ∀ (n : ℕ) (x : Fin n → (epsR R ⟶ H)) (y : Fin n → (epsR R ⟶ G)), IsLieBasis x → (∀ j, IsTangent (y j) ∧ Rel (y j) (x j)) → IsLieBasis y := by
  intro R _ G H _ _ _ _ Rel h1 hmul hsc hex hinj hfun n x y hx hy
  have hyt : ∀ j, IsTangent (y j) := fun j => (hy j).1
  have hrc := rel_comb Rel h1 hmul hsc x y (fun j => (hy j).2)
  refine ⟨hyt, fun w hw => ?_⟩
  obtain ⟨xw, hxw, hrw⟩ := hex w hw
  obtain ⟨c, hc, -⟩ := hx.2 xw hxw
  rw [isLieComb_iff_comb] at hc
  subst hc
  refine ⟨c, (isLieComb_iff_comb _ _ _).2 (hinj w _ _ hw (isTangent_comb hyt c) hrw (hrc c)), ?_⟩
  intro c' hc'
  rw [isLieComb_iff_comb] at hc'
  subst hc'
  have e2 : comb x c = comb x c' := hfun _ _ _ (hrc c') hrw |>.symm
  exact (comb_injective hx e2).symm
