import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ClosedPointWeilPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ConjugateKernelCount
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValPowGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionFactsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateKernelCount

section Operators

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

def cUnit (ζ : F) (hζ : ζ ≠ 0) : Γ((TF (R := R) F).left, ⊤)ˣ :=
  ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit

end Operators

section Data

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]

def FinOrdConcl (k : ℕ) : Prop :=
  ∀ (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
    w.IsGen → ∃ ζ : F, ζ ≠ 0 ∧ FinOrd D F k p w ζ

def FrameConcl (Q : D.toPre.X → ℤ) (v : AddValuation F (WithTop ℚ)) (N : ℕ) (s₀ : Fam D.toPre F (1 * N)) : Prop :=
  ∀ r : ℚ, NuGe D Q F v (1 * N) s₀ r → ((r + (Q 0 : ℚ) / (1 : ℕ) : ℚ) : WithTop ℚ) ≤ v 1

open QForm in

theorem bOf_balance {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] (ιD : D.toPre.OAct O) (hQ : IsQ D.toPre ϖ Q) (a : O) (χ χ' : D.toPre.X) :
    bOf D.toPre Q (a • χ) χ' = bOf D.toPre Q χ (star a • χ') := by
  have hL := D.toPre.P.isLB
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  obtain ⟨u, hu, hnorm⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB _ _ (ιD.onB.rosati a)
  have hc := ιD.tau_bal a u hu hnorm χ χ'
  obtain ⟨_, _, hsA, hA⟩ := tau_val hϖ D hQ (a • χ) χ'
  obtain ⟨_, _, hsB, hB⟩ := tau_val hϖ D hQ χ (star a • χ')
  have hu0 := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ u hu (lift (D.toPre.c χ) (D.toPre.c χ')).left
    (D.toPre.pt2 χ χ') (by simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hA hu0
  have := genHasVal_unique hϖ D.toPre.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _
      (sumElim_sec hsA (fun k => by
        obtain ⟨q, hq⟩ := rosatiφ_over D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k
        show (_ ≫ rosatiφ D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k) ≫ _ = _
        rw [hq]; exact over_sec _ _)) hsB _ _
      (genHasVal_isGen D.toPre.P.L _ _ _ _ _ hB) hc h1) hB
  linarith

end Data

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
  (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [Algebra (FractionRing V) F]

def EnumConcl (α : 𝓞 E) (N : ℕ) : Prop :=
  letI := H.starRing
  ∃ (p : Fin (N ^ P.A.g) → QkPt P.D.toPre F (1 * N)) (x : Fin (N ^ P.A.g) → (TFK (R := V) F ⟶ P.A.A)),
    (∀ b, P.ToA F (1 * N) (p b) (x b)) ∧ (∀ b, x b ≫ P.oA.act (star α) = 1) ∧ Function.Injective x ∧
    ∀ y : TFK (R := V) F ⟶ P.A.A, y ≫ P.oA.act (star α) = 1 → ∃ b, x b = y

def CanonConcl (α : 𝓞 E) (N : ℕ) (s₀ : Fam P.D.toPre F (1 * N)) : Prop :=
  letI := H.starRing
  ∀ (p : QkPt P.D.toPre F (1 * N)) (x : TFK (R := V) F ⟶ P.A.A), P.ToA F (1 * N) p x →
    x ≫ P.oA.act α = 1 →
    ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * N))),
      w.IsGen ∧ FinOrd P.D F (1 * N) p w 1 ∧ PhiRel P.D.toPre F (1 * N) p w s₀ s₀

def PairConcl (α : 𝓞 E) (N : ℕ) : Prop :=
  letI := H.starRing
  ∀ (x x' : TFK (R := V) F ⟶ P.A.A), x ≫ P.oA.act (star α) = 1 → x' ≫ P.oA.act (star α) = 1 → x ≠ x' →
    ∃ z : TFK (R := V) F ⟶ P.A.A, z ≫ P.oA.act α = 1 ∧
      ∃ c c' : Γ((TFK (R := V) F).left, ⊤)ˣ,
        WeilIs P.A.A P.A.L N z x c ∧ WeilIs P.A.A P.A.L N z x' c' ∧ c ≠ c'

end Unif

end GlobalTheory.TorsionFactsCompare
