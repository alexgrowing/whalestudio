import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UT.Cl
section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def Torsion (U : Unif I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (k : ℕ), 1 ≤ k → ∃ f, Tors U.toUnifPre F k f ∧ ∀ p, f p ^ k = 1

def Galois (U : Unif I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (F' : Type) [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (k : ℕ), 1 ≤ k →
    ∀ p : QkPt D.toPre F k, (∃ p' : QkPt D.toPre F' k, QkExt σ.toRingHom p p') ∧
      (∀ x : TFK (R := R) F ⟶ A.A, ∃ x' : TFK (R := R) F' ⟶ A.A, x'.left = spMap σ.toRingHom ≫ x.left) ∧
      ∀ (p' : QkPt D.toPre F' k) (x : TFK (R := R) F ⟶ A.A) (x' : TFK (R := R) F' ⟶ A.A), QkExt σ.toRingHom p p' →
        x'.left = spMap σ.toRingHom ≫ x.left → (QkToAkU U.toUnifPre F k p x ↔ QkToAkU U.toUnifPre F' k p' x')

def SymFrame (U : Unif I D A G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (N : ℕ), Odd N → ∀ p : QkPt D.toPre F N,
    ((∃ w, TXFrame N p w) ∧ ∀ w w', TXFrame N p w → TXFrame N p w' →
      ∀ z J, Good D.toPre.P.L z J → val w (𝟙 _) z J = val w' (𝟙 _) z J) ∧
    ∀ x, QkToAkU U.toUnifPre F N p x → (∃ θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F), SymLift A.A A.L N N x θ) ∧
      ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) F)), SymLift A.A A.L N N x θ → ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen →
        ∀ w, TXFrame N p w → ∀ t t' s s', U.ExpandsF F N w₀ t s → U.ExpandsF F N w₀ t' s' → IsActOf A.A A.L N θ t t' →
          PhiRel D.toPre F N p w s s'

def SeriesFrame {D₀ : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] (m : ℕ) (p : QkPt D₀ F (m ^ 2))
    (g' : GtPtF D₀ F) (w' : Frm D₀ F 1 g'.b) : Prop :=
  GtPtF.IsNsmul m p.g g' ∧ w'.IsGen ∧ ∃ (w : Frm D₀ F (m ^ 2) p.g.b) (κ : LB.Gen (kapLB D₀ (𝟙 D₀.P.A ^ m) (m ^ 2) 1)),
    TXFrame (m ^ 2) p w ∧ Normd κ ∧ ∀ z J, Good D₀.P.L z J → val w (𝟙 _) z J * val κ p.g.b.left z J = val w' (𝟙 _) z J

def Series (U : Unif I D A G) : Prop :=
  (∃ w₀ ρ, NormW U.toUnifPre w₀ ρ) ∧
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ th : SecA A F 1, (∃! ϑ : Fam D.toPre F 1, U.ExpandsF F 1 w₀ th ϑ) ∧
    ∀ ϑ : Fam D.toPre F 1, U.ExpandsF F 1 w₀ th ϑ → ∀ (m : ℕ), Odd m → ∀ x : TFK (R := R) F ⟶ A.A, x ^ (m ^ 2) = 1 →
      (∃ p : QkPt D.toPre F (m ^ 2), QkToAkU U.toUnifPre F (m ^ 2) p x) ∧
      (∃! q : SecA A F (m ^ 2) × F, ThC A ρ m th x q.1 q.2) ∧
      ∀ p : QkPt D.toPre F (m ^ 2), QkToAkU U.toUnifPre F (m ^ 2) p x →
        (∃ (g' : GtPtF D.toPre F) (w' : Frm D.toPre F 1 g'.b), SeriesFrame m p g' w') ∧
        ∀ (g' : GtPtF D.toPre F) (w' : Frm D.toPre F 1 g'.b), SeriesFrame m p g' w' →
          ∀ t c, ThC A ρ m th x t c → SumF I F (coef ϑ g' w') c ∧
            ∀ s, U.ExpandsF F (m ^ 2) w₀ t s → ∀ (o : GtPtF D.toPre F) (w₁ : Frm D.toPre F (m ^ 2) o.b), o.IsZero → FrmOne w₁ →
              (∀ χ, coef s o w₁ (m • χ + p.y) = coef ϑ g' w' χ) ∧ ∀ β, (∀ χ, β ≠ m • χ + p.y) → coef s o w₁ β = 0

def Functorial (U : Unif I D A G) : Prop :=
  (∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA) ∧
  ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) →
    (RosatiAdj A.A A.L E.aA E'.aA ∧ RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB ∧
      (∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB) ∧ ∀ χ, D.toPre.c (E'.h χ) = D.toPre.c χ ≫ E.aB) ∧
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], (∀ g : GtPtF D.toPre F, ∃! g', E.Act g g') ∧
      (∀ y (g g' : GtPtF D.toPre F), GtPtF.IsIota y g → E.Act g g' → GtPtF.IsIota (E'.h y) g') ∧
      ∀ (k : ℕ), 1 ≤ k → ∀ (p p' : QkPt D.toPre F k) x, p'.y = E'.h p.y → E.Act p.g p'.g → QkToAkU U.toUnifPre F k p x →
        QkToAkU U.toUnifPre F k p' (x ≫ E.aA)

def FamilyRing (U : Unif I D A G) : Prop :=
  ExpBijF U.toUnifPre ∧ ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k k' k'' : ℕ), 1 ≤ k → 1 ≤ k' → k'' = k + k' → ∀ (t : SecA A F k) (t' : SecA A F k') (t'' : SecA A F k'') s s' s'', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → U.ExpandsF F k'' w₀ t'' s'' → (∀ z J, Good A.L z J → sA t'' (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J) → ∀ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b) (w' : Frm D.toPre F k' g.b) (w'' : Frm D.toPre F k'' g.b), w.IsGen → w'.IsGen → w''.IsGen → (∀ z J, Good D.toPre.P.L z J → val w'' (𝟙 _) z J = val w (𝟙 _) z J * val w' (𝟙 _) z J) → ∀ α, SumF I F (fun χ => coef s g w χ * coef s' g w' (α - χ)) (coef s'' g w'' α)

def Determined (U : Unif I D A G) : Prop :=
  ∀ (D' : DegData R I) (A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G' : Over (Spec (CommRingCat.of R))) [GrpObj G']
    [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre),
    ∃ (ψ : G' ≅ G) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (φ : A'.A ≅ A.A), IsMonHom ψ.hom ∧ IsMonHom bc.hom ∧
      bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left ∧ IsPullUnif (RingHom.id R) hD bc U U' ∧
      IsMonHom φ.hom ∧ (Over.pullback (jK R)).map ψ.hom ≫ U.gen.hom = U'.gen.hom ≫ φ.hom ∧ LBIso A'.L (A.L.pull φ.hom.left)

def Balanced (U : Unif I D A G) : Prop :=
  (∀ (O : Type) [CommRing O] [StarRing O] (ιA : A.OAct O) (ιG : RingAct G O), (∀ a, (Over.pullback (jK R)).map (ιG.act a) ≫ U.gen.hom = U.gen.hom ≫ ιA.act a) → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∃ (_ : Module O D.toPre.X) (ιD : D.toPre.OAct O), U.toUnifPre.OLinear O ιD ιA ιG) ∧
  ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (ιD : D.toPre.OAct O) (ιA : A.OAct O) (ιG : RingAct G O), U.toUnifPre.OLinear O ιD ιA ιG → (∀ a, LBIso (cubeLB G ![fst G G ≫ ιG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ ιG.act (star a)] U.LG.L)) → ∀ (w₀ : O) (ν : ℕ), w₀ + star w₀ = 1 → w₀ * star w₀ = (ν : O) → 1 ≤ ν → Even ν → LBIso U.LG.L (cubeLB G ![𝟙 G, ιG.act w₀] U.LG.L) → TraceFormTwistIso D.toPre ιD w₀
end

def SeriesVal {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) : Prop :=
  ∀ (ϖ : V) (hϖ : Irreducible ϖ), (∃ Q : D.toPre.X → ℤ, QForm.IsQ D.toPre ϖ Q) ∧ ∀ Q : D.toPre.X → ℤ, QForm.IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v),
      (∀ (N : ℕ), 1 ≤ N → ∀ (p : QkPt D.toPre F N) w, TXFrame N p w → GenV hϖ hv w ((Q p.y : ℚ) / N)) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ (p : QkPt D.toPre F (m ^ 2)) (g' : GtPtF D.toPre F) (w' : Frm D.toPre F 1 g'.b),
        SeriesFrame m p g' w' → ∀ ϑ : Fam D.toPre F 1, NuGe D Q F v 1 ϑ 0 →
          ∀ χ, (((Q (m • χ + p.y) : ℚ) / (m ^ 2 : ℕ) : ℚ) : WithTop ℚ) ≤ v (coef ϑ g' w' χ)
end GlobalTheory.UT.Cl
end
