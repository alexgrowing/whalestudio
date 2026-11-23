import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

abbrev XQ (X : Scheme.{0}) : Scheme.{0} := pullback (toZ X) (toZ (Sp ℚ))

abbrev XQ.fst (X : Scheme.{0}) : XQ X ⟶ X := pullback.fst _ _

abbrev XQ.snd (X : Scheme.{0}) : XQ X ⟶ Sp ℚ := pullback.snd _ _

def toXQ {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) : Sp F ⟶ XQ X :=
  pullback.lift x (spMap (algebraMap ℚ F)) (specULiftZIsTerminal.hom_ext _ _)

@[simp] theorem toXQ_fst {X : Scheme.{0}} {F : Type} [Field F] [CharZero F] (x : Sp F ⟶ X) :
    toXQ x ≫ XQ.fst X = x := pullback.lift_fst _ _ _

def evalAt {S : Scheme.{0}} (U : S.Opens) (f : Γ(S, U)) (z : Sp ℂ ⟶ S) (hz : centre z ∈ U) : ℂ :=
  (Scheme.stalkClosedPointTo z).hom (S.presheaf.germ U (centre z) hz f)

def anTop (S : Scheme.{0}) : TopologicalSpace (Sp ℂ ⟶ S) :=
  TopologicalSpace.generateFrom
    {A | ∃ (U : S.Opens) (f : Γ(S, U)) (V : Set ℂ), IsOpen V ∧ A = {z | ∃ hz : centre z ∈ U, evalAt U f z hz ∈ V}}

section Good

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  {M : LieModel G ξ Li}

def GoodAt (h : LieMetric M y) (C : ℝ) {L : Type} [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) {GK : Over (Sp L)}
    [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) : Prop :=
  letI := τ.addCommGroup
  ∃ (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)),
    ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT →
    ∀ (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier),
      IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∀ ε : Fin r → B.carrier,
      (∀ a, MB.Lifts (algebraMap (𝓞 L) L) φ (ε a) (MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i)) →
      ∀ (σ : L →+* ℂ) (w : Fin r → ℂ),
        C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ∧
        sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2

end Good

end GlobalTheory.CompanionTheory.Ar.TorusUnif
