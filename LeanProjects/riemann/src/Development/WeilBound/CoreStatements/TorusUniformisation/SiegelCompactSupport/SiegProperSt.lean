import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SiegelAtOfKnownTheorem
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN
open scoped CategoryTheory.Obj

namespace PositivityTheory.Member.SiegelModularCharts

def SiegPt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X Y : Scheme.{0}} (t : SAB H X)
    {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {s : Y ⟶ Sp B} (u : SiegPre g n ζ s) (y : X ⟶ Y)
    (α : t.G.left ⟶ u.A.left) : Prop :=
  IsGrpPullback t.G u.A y α ∧ ∃ α₂ : (G2 t.G).left ⟶ (G2 u.A).left, IsSquare α α₂ ∧ LBIso (abelian₂ t.G t.PP.L) (u.P.pull α₂)

def GenLam {Y S : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {s : Y ⟶ Sp B} (u : SiegPre g n ζ s) {G : Over S}
    (e : u.A.left ⟶ G.left) {R : Type} [CommRing R] [IsDomain R] (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁]
    (φ₁ : G₁.left ⟶ G.left) (L : LB G₁.left) : Prop :=
  ∃ α₂ : pullback (G2 G₁).hom (jK R) ⟶ (G2 u.A).left,
    α₂ ≫ (fst u.A u.A).left ≫ e = pullback.fst _ _ ≫ (fst G₁ G₁).left ≫ φ₁ ∧
    α₂ ≫ (snd u.A u.A).left ≫ e = pullback.fst _ _ ≫ (snd G₁ G₁).left ≫ φ₁ ∧
    LBIso ((abelian₂ G₁ L).pull (pullback.fst (G2 G₁).hom (jK R))) (u.P.pull α₂)

def SiegObjSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B F B' : Type) [CommRing B]
    [Field F] [CommRing B'] (b : Base l B) (X : Scheme.{0}) (s : X ⟶ Sp B) (sF : X ⟶ Sp F) (o : Obj D l b s) (z : F) (n : ℕ)
    (ζ : B') (κ : B' →+* F), 1 ≤ D.p + D.q → IsReduced X → IsLocallyNoetherian X → IsPrimitiveRoot z l.M → n ∣ l.M →
    κ ζ = z ^ (l.M / n) →
    ∃ (u : SiegPre (Module.finrank ℚ E / 2 * (D.p + D.q)) n ζ (sF ≫ spMap κ)) (α : o.t.G.left ⟶ u.A.left),
      u.Principal ∧ SiegPt o.t u (𝟙 X) α

def SiegProperSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l)
    (oF : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))
    (_ : ObjMap oF Xo.univ (pullback.fst _ _)) (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (F : SFam g n ζ) (κ : B →+* c.F)
    (y : Xo.XF c ⟶ F.X) (hy : y ≫ F.s = pullback.snd _ _ ≫ spMap κ) (α : oF.t.G.left ⟶ F.univ.A.left),
    1 ≤ D.p + D.q → SiegPt oF.t F.univ y α → IsProper (pullback.lift y (pullback.snd _ _) hy)

def SiegQFinSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l)
    (oF : Obj D l (baseKA l) (pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s))
    (_ : ObjMap oF Xo.univ (pullback.fst _ _)) (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (F : SFam g n ζ) (κ : B →+* c.F)
    (y : Xo.XF c ⟶ F.X) (hy : y ≫ F.s = pullback.snd _ _ ≫ spMap κ) (α : oF.t.G.left ⟶ F.univ.A.left),
    1 ≤ D.p + D.q → SiegPt oF.t F.univ y α → LocallyQuasiFinite (pullback.lift y (pullback.snd _ _) hy)

def LBExtSt : Prop :=
  ∀ (n : ℕ), n ≠ 0 → ∀ (X Y : Scheme.{0}) (s : X ⟶ Sp (cycAway n)) (j : Y ⟶ X), Smooth s → QuasiCompact s →
    IsOpenImmersion j → ∀ L : LB Y, L.IsLB → ∃ L' : LB X, L'.IsLB ∧ LBIso L (L'.pull j)

def TripleExtSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X U : Scheme.{0}) (j : U ⟶ X) (z : X ⟶ Sp ℤ),
    Geo.Tor.IsNormalScheme X → LocallyOfFiniteType z → Flat z → QuasiCompact z → IsPreimmersion j → Flat j → IsDominant j →
    QuasiCompact j → IsLocallyNoetherian U → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G →
    ∀ (t₀ : SAB H U) (a : t₀.G.left ⟶ G.left) (a₂ : (G2 t₀.G).left ⟶ (G2 G).left) (P : LB (G2 G).left),
      IsProper t₀.G.hom → IsGrpPullback t₀.G G j a → IsSquare a a₂ → P.IsLB → LBIso (abelian₂ t₀.G t₀.PP.L) (P.pull a₂) →
      ∃ (t : SAB H X) (ψ : t.G.left ⟶ G.left) (m : SABMap t₀ t j), IsGrpPullback t.G G (𝟙 X) ψ ∧ m.φ ≫ ψ = a

def SepSplitSt : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Sp k)) [GrpObj G], IsSemiAbelian G →
    ∃ (k' : Type) (_ : Field k') (_ : Algebra k k'), FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧
      Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap k k'))).obj G))

def ThetaLocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (t : SAB H (Sp R)), IsCN R → PolAt t (jK R) → SplitOver t.G (maximalIdeal R) → ThetaNZ t.G t.PP.L

def ThetaDescSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X)
    (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X) (t' : SAB H (Sp R)) (_ : SABMap t' t ξ),
    Geo.Tor.IsNormalScheme X → IsCN R → (Scheme.stalkClosedPointTo ξ).hom.Flat → PolAt t' (jK R) → ThetaNZ t'.G t'.PP.L →
    ∃ V : X.Opens, ξ (closedPoint R) ∈ V ∧ ∃ θ ∈ secOn t.PP.L (t.G.hom ⁻¹ᵁ V),
      ∀ y ∈ V, ∃ (g : t.G.left) (i : t.PP.L.ι), t.G.hom g = y ∧ g ∈ t.G.left.basicOpen (θ i)

def PeriodCmpSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R →
    ∀ (D D' : DegData R (maximalIdeal R)) (A A' : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G),
    LBIso ((abelian₂ G U.LG.L).pull (pullback.fst (G2 G).hom (jK R))) ((abelian₂ G U'.LG.L).pull (pullback.fst (G2 G).hom (jK R))) →
    ∃ ε : D.toPre.X ≃+ D'.toPre.X, ∀ y r r', PsiCoord D.toPre y r → PsiCoord D'.toPre (ε y) r' → Associated r r'

def ChartCmpSt : Prop :=
  ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (F : SFam g n ζ) (S : Scheme.{0}) (j : F.X ⟶ S) (G : Over S) [GrpObj G]
    (e : F.univ.A.left ⟶ G.left), IsOpenImmersion j → IsSemiAbelian G → IsGrpPullback F.univ.A G j e →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ S) (m : ℕ) (t : Fin m → R)
      (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (r : Fin m → R')
      (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (D : DegData R' (maximalIdeal R'))
      (A : PolAV (Sp (FractionRing R'))) (U : Unif (maximalIdeal R') D A G') (γ : Fin m → LinearMap.BilinForm ℤ D.toPre.X),
      IsCN R → IsCN R' → (∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ i, t i ∉ p.asIdeal) → Function.Injective ρ → ρ.Finite →
      IsLocalHom ρ → (∀ i, r i ^ 2 = ρ (t i)) → IsUnifOf F j e (spMap ρ ≫ ξ) π U →
      (IsMonomial D.toPre r fun i => (2 * n : ℤ) • γ i) →
    ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (f : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁]
      [IsCommMonObj G₁] (φ₁ : G₁.left ⟶ G.left) (D₁ : DegData R₁ (maximalIdeal R₁)) (A₁ : PolAV (Sp (FractionRing R₁)))
      (U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁), IsCN R₁ → IsLocalHom f → IsGrpPullback G₁ G (spMap f ≫ ξ) φ₁ →
      Set.range (jK R₁ ≫ spMap f ≫ ξ) ⊆ Set.range j → GenLam F.univ e G₁ φ₁ U₁.LG.L →
      ∃ ε : D₁.toPre.X ≃+ D.toPre.X, ∀ y r₁, PsiCoord D₁.toPre y r₁ →
        ∃ k : Fin m → ℕ, (∀ i, (k i : ℤ) = n * γ i (ε y) (ε y)) ∧ Associated (r₁ ^ 2) (∏ i, f (t i) ^ k i)

def EtCplSt : Prop :=
  ∀ (X S : Scheme.{0}) [IsLocallyNoetherian S] (π : X ⟶ S) (w : X ⟶ Sp ℤ) (z : X), Geo.Tor.IsNormalScheme X →
    LocallyOfFiniteType w → Flat w → ∀ (R : Type) [CommRing R] [IsLocalRing R] (ξ : Sp R ⟶ S), IsNoetherianRing R →
    IsAdicComplete (maximalIdeal R) R → ξ (closedPoint R) = π z → IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom →
    ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified →
    ∀ (k : Type) [Field k] [Algebra (X.residueField z) k], FiniteDimensional (X.residueField z) k →
      Algebra.IsSeparable (X.residueField z) k →
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ξ₁ : Sp R₁ ⟶ X) (f : R →+* R₁)
      (ι : k →+* R₁ ⧸ maximalIdeal R₁), IsCN R₁ ∧ ξ₁ (closedPoint R₁) = z ∧
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ₁).hom ∧
      ((residue R₁).comp (Scheme.stalkClosedPointTo ξ₁).hom).FormallyUnramified ∧ IsLocalHom f ∧
      ξ₁ ≫ π = spMap f ≫ ξ ∧
      spMap (Ideal.Quotient.mk (maximalIdeal R₁)) ≫ ξ₁ =
        spMap ι ≫ Spec.map (CommRingCat.ofHom (algebraMap (X.residueField z) k)) ≫ X.fromSpecResidueField z

def HodgeSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l)
    (O : Type) [CommRing O] (β : O →+* c.F) (C : Model Xo c β) (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ)
    (π : C.X ⟶ S) (φ : C.t.G.left ⟶ G.left), IsSemiAbelian G → SmoothOfRelativeDimension g G.hom →
    IsGrpPullback C.t.G G π φ → (GlobalTheory.FlagMod.detOm C).IsLB → LBIso (GlobalTheory.FlagMod.detOm C) ((hodge G g).pull π)

def SiegOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
    {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (C : Model Xo c β) {g n : ℕ} {B : Type} [CommRing B] {ζ : B}
    (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) {G : Over S} [GrpObj G] (e : F.univ.A.left ⟶ G.left) (π : C.X ⟶ S)
    (φ : C.t.G.left ⟶ G.left) : Prop :=
  IsAffineHom π ∧ IsGrpPullback C.t.G G π φ ∧
    ∃ (y : Xo.XF c ⟶ F.X) (α : C.oF.t.G.left ⟶ F.univ.A.left), y ≫ j = C.j ≫ π ∧ α ≫ e = C.m.φ ≫ φ ∧
      SiegPt C.oF.t F.univ y α

end PositivityTheory.Member.SiegelModularCharts
