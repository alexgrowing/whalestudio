import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionUnitsGenericOpen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowOfFramesTriv
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_section_units_generic_open : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (A : Adl C Y) (p : ℕ), p.Prime →
  ∀ (V : Cover Y) (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens)
    (c : ι → V.G.functionFieldˣ) (c' : ι → V.X.functionFieldˣ), genericPoint Y.X ∈ W →
    (∀ a, GlobalTheory.TrueGeo.SmallSec.fnMap V.j hη (c' a) = c a) →
    (∀ a (z : V.G), V.j z ∈ U a → UnitAt z (V.φ (genAt A.D (V.π z)) * c a)) →
    (∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a → A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) * (c a : V.G.functionField))))) →
    ∀ (V' : Cover Y) (π : V'.X ⟶ V.X) (hπ : π (genericPoint V'.X) ⤳ genericPoint V.X), Lies V' V π →
    ∀ (L : LB V'.X) (m : ℕ), NormsAt V' L p ⊤ (fun x => genAt A.D x ^ m) (fun v e y => m * A.lg v e y) →
      GlobalTheory.FrameGlue.PowOfFrames p (fun a => π ⁻¹ᵁ U a) (fun a => Units.map (GlobalTheory.TrueGeo.SmallSec.fnMap π hπ).toMonoidHom (c' a)) m L := by
  first | exact @GlobalTheory.FrameGlue.powOfFrames_of_normsAt | exact GlobalTheory.FrameGlue.powOfFrames_of_normsAt | (intros; apply GlobalTheory.FrameGlue.powOfFrames_of_normsAt <;> assumption)
