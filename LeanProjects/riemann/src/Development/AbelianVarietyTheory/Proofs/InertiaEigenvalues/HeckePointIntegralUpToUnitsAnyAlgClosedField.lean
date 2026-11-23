import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFrameIntAnyField

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt GlobalTheory.FlagTan GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

namespace GlobalTheory.HkAnyFieldOf

theorem heckeFrameInt_anyField_of : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l 𝔓 p → (p : 𝓞 c.F) ∉ la.asIdeal → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, algCls Xo c T io y → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω], letI := io.toAlgebra; ∀ k : T.Fr →ₐ[c.F] Ω, ∀ yΩ : FrPt Xo c Ω, FrMap k y.1 yΩ → ∀ (C : hkKer (Xo := Xo) 𝔓 p i Ω yΩ) (z : FrPt Xo c Ω), hkRelFr 𝔓 p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω yΩ C z → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsIntegralUpToUnits (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) T io k.toRingHom z := by
  intro hHI E _ _ _ H Dw l Xo c la 𝔓 p i hP hpla T io e hla y hy Ω _ _ _ k yΩ hyΩ C z hz
  letI : Algebra c.F T.Fr := io.toAlgebra

  letI : Algebra T.Fr Ω := k.toRingHom.toAlgebra
  haveI : IsScalarTower c.F T.Fr Ω := IsScalarTower.of_algebraMap_eq fun a => (k.commutes a).symm
  let k₀ : T.Fr →ₐ[c.F] AlgebraicClosure T.Fr := IsScalarTower.toAlgHom c.F T.Fr (AlgebraicClosure T.Fr)
  let φ₀ : AlgebraicClosure T.Fr →ₐ[T.Fr] Ω := IsAlgClosed.lift
  let φ : AlgebraicClosure T.Fr →ₐ[c.F] Ω := φ₀.restrictScalars c.F
  have hφk : ∀ a, φ (k₀ a) = k a := fun a => φ₀.commutes a

  obtain ⟨yK, hyK⟩ := exists_frMap k₀ y.1
  have hKΩ : FrMap φ yK yΩ := frMap_of_comp hyK hyΩ hφk

  obtain ⟨C₀, z₀, hz₀, hz₀z⟩ := GlobalTheory.HkAnyField.exists_hkRelFr_down hP φ hKΩ C hz
  have halg : (letI := k₀.toRingHom.toAlgebra; Algebra.IsAlgebraic T.Fr (AlgebraicClosure T.Fr)) := by
    have hA : k₀.toRingHom.toAlgebra = AlgebraicClosure.instAlgebra T.Fr :=
      Algebra.algebra_ext _ _ fun _ => rfl
    exact hA ▸ AlgebraicClosure.isAlgebraic T.Fr
  have h₀ := (hHI E H Dw l Xo c).2.1 la 𝔓 p i hP hpla T io e hla y hy trivial (AlgebraicClosure T.Fr) k₀ halg
    yK hyK C₀ z₀ hz₀

  have h₁ := GlobalTheory.HkAnyField.isIntegralUpToUnits_up φ hz₀z h₀
  have hcomp : φ.toRingHom.comp k₀.toRingHom = k.toRingHom := RingHom.ext hφk
  rwa [hcomp] at h₁

end GlobalTheory.HkAnyFieldOf
