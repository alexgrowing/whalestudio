import Development.EtaleCohomology.EtaleSheaves.CupUnitChernKummerLaws

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E8

def RatModel {k : Type} [Field k] {P : Scheme.{0}} (r : P ⟶ Spec (CommRingCat.of k)) (d : ℕ) : Prop :=
  ∃ (V : P.Opens) (e : V.toScheme ⟶ 𝔸(Fin d; Spec (CommRingCat.of k))), IsOpenImmersion e ∧ Nonempty V ∧
    e ≫ (𝔸(Fin d; Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k)) = V.ι ≫ r

def LeafPointModel : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ d : ℕ,
  ∃ (P : Scheme.{0}) (_ : IsIntegral P) (r : P ⟶ Spec (CommRingCat.of k)) (_ : IsProper r)
    (_ : SmoothOfRelativeDimension d r), RatModel r d ∧
    ∀ (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens), (W : Set P) = (Set.range y)ᶜ →
      ∃ c : Ht q (sch.obj P) (2 * d) d, pull _ (sch.map W.ι) _ _ c = 0 ∧ addOrderOf c = q

def LeafPointTransfer : Prop := Base → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of k)) [IsProper p] (d : ℕ) [SmoothOfRelativeDimension d p]
    {P : Scheme.{0}} [IsIntegral P] (r : P ⟶ Spec (CommRingCat.of k)) [IsProper r] [SmoothOfRelativeDimension d r],
  RatModel r d →
  ∃ (x : Spec (CommRingCat.of k) ⟶ X) (_ : x ≫ p = 𝟙 _) (U : X.Opens) (_ : (U : Set X) = (Set.range x)ᶜ)
    (y : Spec (CommRingCat.of k) ⟶ P) (_ : y ≫ r = 𝟙 _) (W : P.Opens) (_ : (W : Set P) = (Set.range y)ᶜ)
    (T : Ht q (sch.obj X) (2 * d) d →+ Ht q (sch.obj P) (2 * d) d),
    ∀ c' : Ht q (sch.obj P) (2 * d) d, pull _ (sch.map W.ι) _ _ c' = 0 →
      ∃ c : Ht q (sch.obj X) (2 * d) d, pull _ (sch.map U.ι) _ _ c = 0 ∧ T c = c'

end LateralTheory.E.E8

end
