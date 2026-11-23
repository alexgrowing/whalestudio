import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl GlobalTheory.Ex
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def KeyAtMap {R R' : Type} [CommRing R] [CommRing R'] (x' : KeyIn R') (x : KeyIn R) (f : R →+* R')
    (φ : x'.P.A.left ⟶ x.P.A.left) : Prop :=
  ∃ (he : eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A)
    (w : LB.Iso x'.P.L (x.P.L.pull φ)) (hg : x'.P.g = x.P.g) (F : DualNumber R →+* DualNumber R'),
    IsGrpPullback x'.P.A x.P.A (spMap f) φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x'.P.A) (fun _ => 1)) x'.rig
      (rigPullOf φ (spMap f) he x.P.L x.rig) ∧
    (∀ (j : (x.P.L.pull φ).ι) (i : x'.P.L.ι)
      (h : (x.P.L.pull φ).U j ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U (j PUnit.unit)),
      (φ.appLE _ _ h).hom (x.th.f (j PUnit.unit)) =
        (show Γ(x'.P.A.left, (x.P.L.pull φ).U j ⊓ x'.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x'.th.f i)) ∧
    (∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) ∧ F DualNumber.eps = DualNumber.eps ∧
    ∀ i, (x'.v i).left ≫ φ = spMap F ≫ (x.v (i.cast hg)).left

def LocSet {R K : Type} [CommRing R] [Field K] (f : R →+* K) (x : KeyIn K) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {φ : x.P.A.left ⟶ G.left} {M : RigLB G} {m : ℕ} (w : LB.Iso (M.L.pull φ) (lbPow x.P.L (m ^ 2)))
    (y : Fin x.P.g → (epsR R ⟶ G)) : Prop :=
  IsSemiAbelian G ∧ IsGrpPullback x.P.A G (spMap f) φ ∧ Nonempty (CubicalStr G M) ∧ w.IsGen ∧ RigPow f w x.rig ∧
    IsLieBasis y ∧ ∀ i, IsVecOver f φ (y i) (x.v i)

def SecAgree {X Y Z W : Scheme.{0}} {N : LB Z} {a : X ⟶ Z} {b : Y ⟶ Z} (s : (N.pull a).Sec) (t : (N.pull b).Sec)
    (p : W ⟶ X) (q : W ⟶ Y) : Prop :=
  ∀ (i : N.ι) (O : W.Opens) (h₁ : O ≤ p ⁻¹ᵁ (N.pull a).U fun _ => i) (h₂ : O ≤ q ⁻¹ᵁ (N.pull b).U fun _ => i),
    (p.appLE _ _ h₁).hom (s.f fun _ => i) = (q.appLE _ _ h₂).hom (t.f fun _ => i)

def IntU {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F]
    (k : ℕ) (w₀ : GlobalTheory.UT.W0 U) (t : GlobalTheory.UT.SecA A F k) : Prop :=
  ∃ (σ' : U.SecGF F k) (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))),
    GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w₀
      (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
      (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ' ∧
    GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) σ'
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F) 1

def AllUQ (P : ∀ {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (IsLocalRing.maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G]
    (_ : Unif (IsLocalRing.maximalIdeal V) D A G) (_ : D.toPre.X → ℤ) {F : Type} [Field F] [Algebra (FractionRing V) F],
    AddValuation F (WithTop ℚ) → Prop) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (IsLocalRing.maximalIdeal V))
    (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), DVR.QForm.IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)),
      DVR.ValOver ϖ F v → P U Q v

end GlobalTheory.MBLow

end
