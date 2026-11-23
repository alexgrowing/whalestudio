import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsGlobal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsEquivOfGivenStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SplitComponentsOfAlgClosedStatement
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ModelSmall
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.OverLaUnique
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
open NumberField IsDedekindDomain Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec GlobalTheory.CompanionTheory.Ar.Plug
attribute [-instance] GlobalTheory.CompHt.fintypePsi
namespace GlobalTheory.CompanionTheory.Ar.Plug

theorem vs_tower : Top.Given → Top.GoodTowerExistsX → Top.VolumeTheoremX → ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (II : IntersectionSystem), IsFullIntersectionSystem II → FnAlgClosed Xo c → (∀ p : ℕ, p.Prime → l.GoodAt p) → l.A = 1 → 1 ≤ Dw.q → 3 * Dw.q + 1 ≤ Dw.p + Dw.q → (2 * discr E * l.M').natAbs.primeFactors.card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 → ∃ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (κ : Comp Xo c ≃ T.Comp), o.Extra ∧ CompOf o.toTowerOrigin κ ∧ T.bad = (2 * discr E * l.M').natAbs.primeFactors ∧ T.Proportional ∧ T.T1 II ∧ T.VolEq ∧ T.MeanSlope II C (hostRd E) (hostLval H) := by
  intro hG hTow hVol
  obtain ⟨C, hC, hV⟩ := hVol
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ H Dw l Xo c _ II hII hcl hgood hA hq hpq hcard
  have hN : 1 ≤ Dw.p + Dw.q := by omega
  have hp : 1 ≤ Dw.p := by omega
  obtain ⟨Xf, rfl⟩ : ∃ Xf : ∀ l' : Level H, Moduli Dw l', Xf l = Xo := by
    classical
    refine ⟨Function.update (fun l' => (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l' hN).some) l Xo, ?_⟩
    simp
  obtain ⟨Y, hY⟩ := GlobalTheory.CompanionTheory.Ar.Rec.exists_isGlobal E H Dw Xf l c hN hgood hA
  obtain ⟨T, o, hX⟩ := hTow E H Dw Xf l c Y hY (GlobalTheory.T.split_components_of_alg_closed E H Dw l (Xf l) c Y hcl) hp hq
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.tower_components_equiv_of_given E H Dw l (Xf l) c Y T o.toTowerOrigin hG
  have hbad : T.bad = (2 * discr E * l.M').natAbs.primeFactors := by
    have hne : 2 * discr E * l.M' ≠ 0 := by
      intro h0
      obtain ⟨r, hr, hrp⟩ := Nat.exists_infinite_primes (T.bad.sup id + 1)
      have hmem : r ∈ T.bad := (o.bad_iff r).2 ⟨hrp, by rw [h0]; exact dvd_zero _⟩
      have := Finset.le_sup (f := id) hmem
      simp only [id] at this
      omega
    ext r
    rw [o.bad_iff, Nat.mem_primeFactors, Int.natCast_dvd]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, by simpa using hne⟩
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
  have hc : T.bad.card ≤ 4 * Fintype.card (CMType H) * (Dw.p + Dw.q) ^ 2 := by
    rw [hbad]; exact hcard
  obtain ⟨h1, h2, h3, -, -, h6⟩ := hV E H Dw Xf l c Y T o II hY hX hII hq hpq hc
  exact ⟨Y, T, o, κ, hX, hκ, hbad, h1, h3, h2, h6⟩

end GlobalTheory.CompanionTheory.Ar.Plug
