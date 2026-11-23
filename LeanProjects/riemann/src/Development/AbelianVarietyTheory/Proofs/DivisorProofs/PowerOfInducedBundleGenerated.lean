import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleNsmul
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo

set_option autoImplicit false

namespace GlobalTheory.TrueGeo.InducedGen

theorem exists_isGenerated_pow : ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y)
    (M : TrueGeo.Model Y) (L : HermLB M.p) (q : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
    A.Induced M L q cf → Y.ample A.D → ∃ m : ℕ, 1 ≤ m ∧ GlobalTheory.IsGenerated ((L.pow m).B.pull M.j) := by
  intro F _ _ C Y A M L q cf hI hA
  obtain ⟨_, r, hr, _, _⟩ := hI
  have hq : Y.ample ((q : ℕ) • A.D) := Var.ample_nsmul F Y A.D q q.pos hA
  have hiso : LBIso (L.B.pull M.j) (toLB ((q : ℕ) • A.D)) := hr.lbIso (presents_toLB _)
  have hamp : IsAmpleLB (L.B.pull M.j) := IsAmpleLB.of_lbIso hq hr.isLB hiso
  obtain ⟨n, hn, hg⟩ := hamp.exists_isGenerated_pow
  refine ⟨n, hn, ?_⟩
  exact hg.of_lbIso (LB.isLB_pull (isLB_lbPow L.isLB n) M.j)
    (LBIso.symm (lbIso_lbPow_pull L.isLB M.j n))

end GlobalTheory.TrueGeo.InducedGen
