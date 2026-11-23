import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicExtensionSectionReading
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OffZero
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_extension_section_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (r : ℕ) (σ : c.F →+* ℂ) (V : Unf Xo c σ r) (T : GlobalTheory.CompHS.TorFlag Xo c) (e : Ix D → ℤ) (k : V.Comp) (P : Frame (V.X k).Ψ r → ℂ) (h : (T.X.LL e).ι → GlobalTheory.CxPts (GlobalTheory.CompHS.flagStr T.X) σ → ℂ), GlobalTheory.CompanionTheory.Ar.HolExt.Reads V T e k P h → ∀ (m : ℕ) (as : Fin m → ℂ) (ss : Fin m → (T.X.LL e).Sec), h = ∑ j, as j • GlobalTheory.CxPts.secVal (GlobalTheory.CompHS.flagStr T.X) σ (ss j) → ∀ x ∈ (V.X k).dom, P x = ∑ j, as j * rdU V (GlobalTheory.CompanionTheory.Ar.OntoDef.ruleTop T.X e (GlobalTheory.Vanishing.H0.ofSec (GlobalTheory.CompHS.flagStr T.X) ⊤ (ss j))) k x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb | exact GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb | (intros; apply GlobalTheory.CompanionTheory.Ar.HolExt.reads_comb <;> assumption)
