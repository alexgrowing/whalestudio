import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.RootOfUnityFn

theorem evR_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) {S : Type} [CommRing S]
    [Algebra c.F S] (y : FrPt Xo c S)
    (h : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y) (m : ℕ) :
    evR Xo c (f ^ m) y = evR Xo c f y ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero]; exact evalAt_one _ _ y h
  | succ k ih =>
    rw [pow_succ, pow_succ, ← ih]
    exact evalAt_mul _ _ _ _ y

theorem exists_character : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (n : ℕ) (d : DeltaDat Xo c n) (m : ℕ), 0 < m → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → d.cδ ^ m = 1 → (∀ y : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom), ∃ a : d.c₂.F, evR d.Xo₂ d.c₂ d.cδ y = algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom) a) → ∃ (Cls : Type) (_ : CommGroup Cls) (_ : Finite Cls) (δ : Cls →* d.c₂.Fˣ) (gdet : FrPt d.Xo₂ d.c₂ (CAt d.c₂.F.val.toRingHom) → Cls), CMP Xo c d _ Cls δ gdet false := by
  intro E _ _ _ H Dw l Xo c n d m hm hsec hpow hval
  choose a ha using hval
  haveI : NeZero m := ⟨hm.ne'⟩
  haveI : IsReduced (CAt d.c₂.F.val.toRingHom) := (inferInstance : IsReduced ℂ)
  have hinj : Function.Injective (algebraMap d.c₂.F (CAt d.c₂.F.val.toRingHom)) :=
    (d.c₂.F.val.toRingHom).injective
  have hroot : ∀ y, a y ^ m = 1 := by
    intro y
    have hT := GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.firstFiveLaws.1.secBaseChange E H Dw d.l₂ d.Xo₂ d.c₂ _ y
    have h1 := evR_pow d.Xo₂ d.c₂ d.cδ y hT m
    have h0 := evR_pow d.Xo₂ d.c₂ d.cδ y hT 0
    rw [pow_zero, pow_zero] at h0
    rw [hpow, h0, ha, ← map_pow] at h1
    exact hinj (by rw [map_one]; exact h1.symm)
  refine ⟨rootsOfUnity m d.c₂.F, inferInstance, inferInstance, (rootsOfUnity m d.c₂.F).subtype,
    fun y => rootsOfUnity.mkOfPowEq (a y) (hroot y), hsec, fun y => ?_⟩
  rw [ha]
  rfl

end GlobalTheory.RootOfUnityFn
