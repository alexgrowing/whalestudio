import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckePointIntegralUpToUnitsAnyAlgClosedField
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
open NumberField IsDedekindDomain Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePoint_integral_upToUnits_anyAlgClosedField : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsHeckePrime H l 𝔓 p → (p : 𝓞 c.F) ∉ la.asIdeal → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ y : IntFr Xo c T io, algCls Xo c T io y → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra c.F Ω], letI := io.toAlgebra; ∀ k : T.Fr →ₐ[c.F] Ω, ∀ yΩ : FrPt Xo c Ω, FrMap k y.1 yΩ → ∀ (C : hkKer (Xo := Xo) 𝔓 p i Ω yΩ) (z : FrPt Xo c Ω), hkRelFr 𝔓 p i (GlobalTheory.ThetaTrace.hkTr Xo c p) Ω yΩ C z → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.IsIntegralUpToUnits (GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.trivialClassCondition Xo c) T io k.toRingHom z := by
  first | exact @GlobalTheory.HkAnyFieldOf.heckeFrameInt_anyField_of | exact GlobalTheory.HkAnyFieldOf.heckeFrameInt_anyField_of | (intros; apply GlobalTheory.HkAnyFieldOf.heckeFrameInt_anyField_of <;> assumption)
