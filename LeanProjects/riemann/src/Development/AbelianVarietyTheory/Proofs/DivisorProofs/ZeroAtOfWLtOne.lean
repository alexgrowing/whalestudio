import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodReductionExtendsRegular
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAlgebraicPointSpecializing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtPointsOverPrimeBound
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.WholeFlag GlobalTheory.ShFam.Pad

set_option autoImplicit false

namespace GlobalTheory.Cover.ZeroAtFibre

theorem zeroAt_of_w_lt_one : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p.Prime → ∀ (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens) (f : V.X.functionField), (∀ v : HeightOneSpectrum (𝓞 F), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (z ≫ V.j) f) < 1) → ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → RegAt x f → ZeroAt x f := by
  intro F _ _ Y V p hp W hW U f hf x hxU hpx hreg
  rw [zeroAt_iff]
  refine ⟨hreg, fun hu => ?_⟩
  obtain ⟨N, hxN, hN⟩ := hu.exists_nhds
  obtain ⟨v, e, y, z, yt, hv, hyW, hz, hyt, hU, -⟩ :=
    GlobalTheory.Mean4O.Cover.ThroughFibre.exists_algPt_through F Y V p hp W hW (U ⊓ N) x ⟨hxU, hxN⟩ hpx
  have hc : yt (IsLocalRing.closedPoint e.O) ∈ U ⊓ N := hU (Set.mem_univ _)
  have h1 := GlobalTheory.NormExt.w_valAt_eq_one e yt (hN _ hc.2)
  rw [hyt] at h1
  have h2 := hf v hv e y hyW z yt hz hyt (fun q _ => (hU (Set.mem_univ q)).1)
  rw [h1] at h2
  exact lt_irrefl _ h2

end GlobalTheory.Cover.ZeroAtFibre
