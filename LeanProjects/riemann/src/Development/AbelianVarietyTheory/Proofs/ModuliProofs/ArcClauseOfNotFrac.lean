import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FractionLevelCorrespondence
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsoIffAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.InjectiveOfIsAlgebraic
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenRelNeZero
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDescOfPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsShiftGen
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ArcClauseCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.TorusExt GlobalTheory.ArcInputCompare GlobalTheory.ArcDataDescent GlobalTheory.LN
open scoped CategoryTheory.Obj

section Bundles

variable {X X' T : Scheme.{0}} {K : Type} [Fintype K] {L' : LB X'} {L : LB X} {φ : X' ⟶ X}
  {w : LB.Iso L' (L.pull φ)} {a : K → (T ⟶ X')} {b : K → (T ⟶ X)} {ε : K → ℤ}
  {t' : LB.Gen (LB.LinComb L' a ε)} {t : LB.Gen (LB.LinComb L b ε)} {z : Γ(T, ⊤)ˣ}

end Bundles

theorem qkToAkU_of_equiv {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (hk : 1 ≤ k)
    {p q : QkPt D.toPre F k} (e : QkPt.Equiv D.toPre F p q) {x : TFK (R := R) F ⟶ A.A} (h : QkToAkU U F k p x) :
    QkToAkU U F k q x := by
  obtain ⟨z, hy, g, hι, hadd⟩ := e
  refine fun w₀ hw₀ => ⟨(h w₀ hw₀).1, fun θ hθ => ?_⟩
  obtain ⟨w, hw, H⟩ := (h w₀ hw₀).2 θ hθ
  obtain ⟨w₂, hw₂, H₂⟩ := QkShift.qk_shift globalFns_holds R D.toPre D.tau_bimult F k hk p q z g hy hι hadd w hw
  exact ⟨w₂, hw₂, fun t t' s s' a b c => H₂ s s' (H t t' s s' a b c)⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}
  {R : Type} [CommRing R] [IsDomain R] {f : O' →+* R} {u : R}

section Transport

open ArcTransport

variable {a : ArcIn D l β O' b} {P : DegPre R} [Module (𝓞 E) P.X] {φ : P.P.A.left ⟶ a.D₀.P.A.left}
  {w : LB.Iso P.P.L (a.D₀.P.L.pull φ)} {e : a.D₀.X ≃ₗ[𝓞 E] P.X}
  {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F]
  [Field F'] [Algebra (FractionRing R) F'] [Algebra (FractionRing O') F'] (σ : F →+* F')
  (h₁ : σ.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F')
  (h₂ : σ.comp (algebraMap (FractionRing O') F) = algebraMap (FractionRing O') F')

variable {oP : letI := H.starRing; P.OAct (𝓞 E)} {he : eSec P.P.A ≫ φ = spMap f ≫ eSec a.D₀.P.A}
  (hW : Match a f u P oP φ he w e)
  (hF : ∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x)))

end Transport

section Twist

variable (x : TateUniformizationInput.ArcInput D c β O' b) (hf : Function.Injective f) (hu : u ≠ 0) {I : Ideal R}
  (Δ : UniformTorsionIsomorphism.OData H I) (φ : Δ.D.toPre.P.A.left ⟶ x.P.P.A.left) (w : LB.Iso Δ.D.toPre.P.L (x.P.P.L.pull φ))
  (e : x.P.X ≃ₗ[𝓞 E] Δ.D.toPre.X)

@[reducible] def fracAlg (hf : Function.Injective f) : Algebra (FractionRing O') (FractionRing R) :=
  (FractionLevelCorrespondence.fracMap f hf).toAlgebra

end Twist

variable {Xo : Moduli D l} (Y : Model Xo c β)

section Level

variable {I : Ideal R} {χ : Sp R ⟶ Y.X} {t : SAB H (Sp R)} (m : SABMap t Y.t χ) (P : PELUnif I t)

def LevelAt (a : ArcIn D l β O' b) (f : O' →+* R) (u : R) {φ : P.D.toPre.P.A.left ⟶ a.D₀.P.A.left}
    (w : LB.Iso P.D.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.D.toPre.X) (k : ℕ)
    (p₀ : QkPt a.D₀ (FractionRing O') k) (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing O') F] (uF : F),
    (∀ x, algebraMap (FractionRing O') F (algebraMap O' _ x) = algebraMap (FractionRing R) F (algebraMap R _ (f x))) →
    uF = algebraMap (FractionRing R) F (algebraMap R _ u) →
    ∀ yF : Sp F ⟶ Xo.XF c, yF ≫ Y.j = jFK (R := R) F ≫ jK R ≫ χ →
      ∀ (q₀ : QkPt a.D₀ F k) (q : QkPt P.D.toPre F k) (x : TFK (R := R) F ⟶ P.A.A),
        QkExt (algebraMap _ F) p₀ q₀ → MatchRigid.IsTransport a w e uF q₀ q →
        x.left ≫ PelUnifCompare.genMap P ≫ m.φ = yF ≫ σ.left ≫ Y.m.φ → P.ToA F k q x

variable {Y m P}

end Level

def ArcCond (a : ArcIn D l β O' b) (π : O') (χ : Sp (PowerSeries O') ⟶ Y.X) : Prop :=
  χ ≫ Y.s = spMap (PowerSeries.C (R := O')) ≫ spMap b ∧
  (∀ x : Sp (PowerSeries O'), χ x ∈ abLocus Y.t.G ↔ PowerSeries.X ∉ x.asIdeal) ∧
  (∀ x : Sp (PowerSeries O'), PowerSeries.C π * PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) ∧
  Y.HasArcData a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := O')) PowerSeries.X χ

def ValueCond (a : ArcIn D l β O' b) (π : O') (χ : Sp (PowerSeries O') ⟶ Y.X) : Prop :=
  ∀ (y' : Sp O' ⟶ Y.X) (ev : PowerSeries O' →+* O'), y' ≫ Y.s = spMap b →
    Set.range (jK O' ≫ y') ⊆ Set.range Y.j → Y.HasArcData a (Ideal.span {π}) (RingHom.id O') π y' →
    (∀ x, ev (PowerSeries.C x) = x) → ev PowerSeries.X = π → spMap ev ≫ χ = y'

end GlobalTheory.ArcClauseCompare
