import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsValuationSubringComplexPrimeMemNonunits
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnfFamily
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsVanBdOfMemExtVanZ
import Development.AbelianVarietyTheory.Definitions.Divisors.SecondCountableTopologyOfIsProjOver

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HolExt

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompHS

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

def Reads (V : Unf Xo c σ r) (T : TorFlag Xo c) (e : Ix D → ℤ) (k : V.Comp) (P : Frame (V.X k).Ψ r → ℂ)
    (h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ) : Prop :=
  ∀ (x : Frame (V.X k).Ψ r) (hx : x ∈ (V.X k).dom) (i : T.X.F.J) (y : GlobalTheory.CxPts (flagStr T.X) σ)
    (hz : ⊤ ≤ (y.1 : Sp (Formalism.L2.Pj.CAt σ) ⟶ T.X.YY) ⁻¹ᵁ T.X.F.U i) (Q : FrPt Xo c (Formalism.L2.Pj.CAt σ)) (t : Ix D → (Formalism.L2.Pj.CAt σ)ˣ),
    T.X.ptY (V.un k ⟨x, hx⟩) = y.1 → @GlobalTheory.FlagMod.Frames.ChartFr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T.X.F (Formalism.L2.Pj.CAt σ) _ (instAlgebraCAt σ) i y.1 hz Q → FrBor t Q (V.un k ⟨x, hx⟩) →
    P x = toC (∏ ix, t ix ^ e ix).val * h i y

def OffZero (V : Unf Xo c σ r) (T : TorFlag Xo c) {e : Ix D → ℤ} (k : V.Comp)
    (h : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ) : Prop :=
  ∀ i (y : GlobalTheory.CxPts (flagStr T.X) σ), (∀ (x : Frame (V.X k).Ψ r) (hx : x ∈ (V.X k).dom),
    T.X.ptY (V.un k ⟨x, hx⟩) ≠ y.1) → h i y = 0

example (V : Unf Xo c σ r) (T : TorFlag Xo c) (e : Ix D → ℤ) (k : V.Comp) :
    Reads V T e k 0 (0 : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ) ∧ OffZero V T k
      (0 : (T.X.LL e).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ) :=
  ⟨fun _ _ _ _ _ _ _ _ _ _ => (mul_zero _).symm, fun _ _ _ => rfl⟩

end GlobalTheory.CompanionTheory.Ar.HolExt
