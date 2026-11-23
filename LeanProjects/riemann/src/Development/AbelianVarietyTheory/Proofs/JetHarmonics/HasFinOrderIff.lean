import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.RigidNormaliserGenerators
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.DiagonalActionLiftPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GeneratorsCompare

open GlobalTheory.IndefiniteRowSideFullHecke

def ThFin {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) : Prop :=
  ∃ M : ℕ, 0 < M ∧ θ.pt ^ M = 1 ∧ LB.Gen.Corr L _ _ _ _ (ReciprocityTheory.ChartRestriction.G.Out.powGen A L k θ M) (LB.oneGen L)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]

def PtSame (b : TF (R := R) F ⟶ G) (x : TFK (R := R) F ⟶ A.A) : Prop :=
  b.left = (x ≫ U.gen.inv).left ≫ pullback.fst G.hom (jK R)

variable (k : ℕ) (W : LB.Iso (A.L.pull U.gen.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R))))

def SecOnA (t : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))) (σ' : U.SecGF F k) : Prop :=
  GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) W
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
    (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ'

def wAt {Z : Scheme.{0}} (m : Z ⟶ pullback G.hom (jK R)) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι)
    (JA : (Z ⟶ A.A.left) → A.L.ι) : (Z.presheaf.stalk z)ˣ :=
  BoxExpansion.pw W m z (JA (m ≫ U.gen.hom.left)) (J (m ≫ pullback.fst G.hom (jK R)))

def ThetaValRel (ga : ThetaGrp G U.LG.L (k : ℤ) (TF (R := R) F)) (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) :
    Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (UnifPre.GF (R := R) (G := G) F).left) (z : Z) (J : (Z ⟶ G.left) → U.LG.L.ι)
    (JA : (Z ⟶ A.A.left) → A.L.ι), Good U.LG.L z J → Good A.L z JA →
    val (L := U.LG.L) (φ := ![(snd (TF (R := R) F) G).left, (translPt G ga.pt).left]) (ε := ![(k : ℤ), -(k : ℤ)])
        ga.φ (r ≫ RigidNormaliserGenerators.cmp G F) z J *
      wAt U W (r ≫ (U.genF F ≫ translPt A.A θ.pt ≫ U.gen.inv).left) z J JA ^ k =
    wAt U W (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) z J JA ^ k *
      val (L := A.L) (φ := ![(snd (TFK (R := R) F) A.A).left, (translPt A.A θ.pt).left]) (ε := ![(k : ℤ), -(k : ℤ)])
        θ.φ (r ≫ (U.genF F).left) z JA

def ThetaSame (ga : ThetaGrp G U.LG.L (k : ℤ) (TF (R := R) F)) (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F)) :
    Prop :=
  PtSame U F ga.pt θ.pt ∧ (ThFin G U.LG.L ga ↔ ThFin A.A A.L θ) ∧
    ∀ (σ₁ σ₂ : LB.Sec (LPow G U.LG.L (k : ℤ) (TF (R := R) F))) (σ₁' σ₂' : U.SecGF F k)
      (t₁ t₂ : LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F))),
      RigidNormaliserGenerators.SameSec F U k σ₁ σ₁' → RigidNormaliserGenerators.SameSec F U k σ₂ σ₂' → SecOnA U F k W t₁ σ₁' → SecOnA U F k W t₂ σ₂' →
      (IsActOf G U.LG.L (k : ℤ) ga σ₁ σ₂ ↔ IsActOf A.A A.L (k : ℤ) θ t₁ t₂)

end GlobalTheory.GeneratorsCompare
