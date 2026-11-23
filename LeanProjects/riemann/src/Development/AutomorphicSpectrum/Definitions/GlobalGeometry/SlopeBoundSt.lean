import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

section Metric

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

structure LieMetric (M : LieModel G ξ Li) {K : Type} {J : K → Type} (y : (Σ k, J k) → Ω) where

  ip : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ
  herm : ∀ (z : Sp ℂ ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V),
    ∃ core : InnerProductSpace.Core ℂ V, ∀ a b, core.inner a b = ip z (Mz.pt a) (Mz.pt b)
  conj : ∀ (z : Sp ℂ ⟶ X) (v w : epsAt z ⟶ G) (v' w' : epsAt (spMap (starRingEnd ℂ) ≫ z) ⟶ G),
    v'.left = spMap (dualMap (starRingEnd ℂ)) ≫ v.left → w'.left = spMap (dualMap (starRingEnd ℂ)) ≫ w.left →
      ip _ v' w' = starRingEnd ℂ (ip z v w)
  cont : ∀ a b : Li, ∃ F : ((Σ k, J k) → ℂ) → ℂ,
    ContinuousOn F {w | ∃ (z : Sp ℂ ⟶ X) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w ∧ M.ValAt z a va ∧ M.ValAt z b vb} ∧
      ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ) (va vb : epsAt z ⟶ G), CoordsAt ξ y z w → M.ValAt z a va →
        M.ValAt z b vb → F w = ip z va vb

def LieMetric.Orth {M : LieModel G ξ Li} {K : Type} {J : K → Type} {y : (Σ k, J k) → Ω} (h : LieMetric M y)
    {O : Type} [CommRing O] (act : OAct O G) : Prop :=
  ∀ (z : Sp ℂ ⟶ X) (τ τ' : O →+* ℂ) (v w : epsAt z ⟶ G), τ ≠ τ' → IsLieEigen act z τ v → IsLieEigen act z τ' w →
    h.ip z v w = 0

variable {L : Type} [Field L] [NumberField L]

def IsFibre (rel : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ → Prop) (z : Sp (𝓞 L) ⟶ X)
    (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier) : Prop :=
  ∀ (σ : L →+* ℂ) (x x' : B.carrier) (v v' : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ z) ⟶ G),
    MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) x v → MB.Lifts (σ.comp (algebraMap (𝓞 L) L)) (𝟙 G.left) x' v' →
      rel _ v v' ((B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x'))

def IsSubFibre (M : LieModel G ξ Li) (U : Submodule Ω Li) (z : Sp (𝓞 L) ⟶ X) {V : Type} [AddCommGroup V]
    [Module (𝓞 L) V] (MB : LieModel G z V) (F : Submodule (𝓞 L) V) : Prop :=
  ∀ x, x ∈ F ↔ ∃ a : 𝓞 L, a ≠ 0 ∧ a • x ∈ Submodule.span (𝓞 L)
    {x' | ∃ e ∈ U, ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
      M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v}

end Metric

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure AbPart {S : Scheme.{0}} (t : SAB H S) {K : Type} [Field K] (z : Sp K ⟶ S) where

  tK : SAB H (Sp K)
  m : SABMap tK t z

  τ : TorusExtension tK.G

  tB : SAB H (Sp K)

  e : τ.B ≅ tB.G
  e_hom : letI := τ.grpB; IsMonHom e.hom
  act : ∀ a, tK.act.act a ≫ τ.q ≫ e.hom = τ.q ≫ e.hom ≫ tB.act.act a
  pp : LBIso tK.PP.L (tB.PP.L.pull (τ.q ≫ e.hom).left)

def IsPrincipal {K : Type} [Field K] (t : SAB H (Sp K)) : Prop :=
  IsProper t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L

def SlopeBoundSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L]
    (t : SAB H (Sp (𝓞 L))) (tK : SAB H (Sp L)) (_ : SABMap tK t (spMap (algebraMap (𝓞 L) L))), IsPrincipal tK →
    ∀ (B : HermitianBundle.{0} L) (MB : LieModel t.G (𝟙 _) B.carrier), IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB →
      B.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 L) B.carrier + max (-B.normDegree ⊤) 0) : ℝ) : EReal)

end GlobalTheory.CompanionTheory.Ar
