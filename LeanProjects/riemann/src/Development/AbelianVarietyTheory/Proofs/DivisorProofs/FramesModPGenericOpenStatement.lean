import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesModPGenericOpen
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
theorem _root_.GlobalTheory.T.frames_mod_p_generic_open : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (C : CxSt F) (N : ℕ) (A : Fin N → Adl C Y) (p : ℕ), p.Prime →
  ∀ (V : Cover Y) (hη : V.j (genericPoint V.G) ⤳ genericPoint V.X) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens)
    (M : ι → Matrix (Fin N) (Fin N) V.X.functionField) (c : ι → Fin N → V.G.functionFieldˣ), genericPoint Y.X ∈ W →
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) →
    (∀ a, ∀ x ∈ U a, ¬ IsUnit (p : V.X.presheaf.stalk x) → (∀ i k, RegAt x (M a i k)) ∧ UnitAt x (M a).det) →
    (∀ a i (z : V.G), V.j z ∈ U a → UnitAt z (V.φ (genAt (A i).D (V.π z)) * c a i)) →
    (∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
        (∀ i, (A i).lg v e y =
          Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1)) * (c a i : V.G.functionField))))) ∧
        ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ i, (∀ k, k < i → e.w (valAt (z ≫ V.j) (((M a)⁻¹ * M b) i k)) < 1) ∧
          e.w (valAt (z ≫ V.j) (((M a)⁻¹ * M b) i i) - valAt z ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField)) < 1) →
    ∃ c' : ι → Fin N → V.X.functionFieldˣ, (∀ a i, GlobalTheory.TrueGeo.SmallSec.fnMap V.j hη (c' a i) = c a i) ∧ GlobalTheory.FrameGlue.ModPFrames p U M c' := by
  first | exact @GlobalTheory.FrameGlue.exists_modPFrames_of_bounds | exact GlobalTheory.FrameGlue.exists_modPFrames_of_bounds | (intros; apply GlobalTheory.FrameGlue.exists_modPFrames_of_bounds <;> assumption)
