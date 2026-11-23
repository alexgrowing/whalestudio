import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.ConjNeSelfOfCM
import Formalism.LocalToGlobal.ProjectiveLattices.BetaAtSymm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowMulEqOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory

theorem exists_rootOfUnity_smul_of_pow_eq_one {F N : Type} [Field F] [AddCommGroup N] [Module F N]
    (Φ : Module.End F N) (ζ ξ : F) {M M' : ℕ} (hM : 1 ≤ M) (hM' : 1 ≤ M')
    (h : (ζ • Φ) ^ M = 1) (h' : (ξ • Φ) ^ M' = 1) :
    ∃ u : F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ ξ • Φ = u • (ζ • Φ) := by
  rcases subsingleton_or_nontrivial (Module.End F N) with hs | hn
  · exact ⟨1, ⟨1, Nat.one_pos, one_pow _⟩, Subsingleton.elim _ _⟩
  have hζ : ζ ≠ 0 := by
    rintro rfl
    rw [zero_smul, zero_pow (by omega)] at h
    exact zero_ne_one h
  have e : ξ • Φ = (ξ / ζ) • (ζ • Φ) := by rw [smul_smul, div_mul_cancel₀ _ hζ]
  refine ⟨ξ / ζ, ⟨M * M', by positivity, ?_⟩, e⟩
  have a : (ξ • Φ) ^ (M * M') = 1 := by rw [mul_comm M M', pow_mul, h', one_pow]
  rw [e, smul_pow, pow_mul (ζ • Φ), h, one_pow] at a
  have b : ((ξ / ζ) ^ (M * M') - 1) • (1 : Module.End F N) = 0 := by rw [sub_smul, a, one_smul, sub_self]
  exact sub_eq_zero.1 ((smul_eq_zero.1 b).resolve_right one_ne_zero)

theorem finOrd_ratio_rootOfUnity : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w w' : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))) (ζ ζ' : F), w.IsGen → w'.IsGen → FinOrd D F k p w ζ → FinOrd D F k p w' ζ' → ∃ u : F, (∃ m : ℕ, 0 < m ∧ u ^ m = 1) ∧ ∀ s t₀ t t₀' t' : Fam D.toPre F k, PhiRel D.toPre F k p w s t₀ → Fam.IsSmul D.toPre F ζ t₀ t → PhiRel D.toPre F k p w' s t₀' → Fam.IsSmul D.toPre F ζ' t₀' t' → Fam.IsSmul D.toPre F u t t' := by
  intro V _ _ _ _ ϖ _ D F _ _ k hk p w w' ζ ζ' hw hw' h h'
  have hG : GlobalFnsSt := GlobalTheory.firstFiveLaws.1.globalFns
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hG V _ D F k hk p w hw
  obtain ⟨Φ', hΦ'⟩ := phiFun_of_globalFns hG V _ D F k hk p w' hw'
  obtain ⟨c, hc⟩ := ThetaFinOrd.exists_scalar hG p w' w hw' hw Φ' Φ
    (fun s => (hΦ' _ _).2 rfl) (fun s => (hΦ _ _).2 rfl)
  obtain ⟨M, hM, hU⟩ := (ThetaFinOrd.finOrd_iff p w ζ Φ hΦ).1 h
  obtain ⟨M', hM', hW⟩ := (ThetaFinOrd.finOrd_iff p w' ζ' Φ' hΦ').1 h'
  rw [hc, smul_smul] at hW
  obtain ⟨u, hu, e⟩ := exists_rootOfUnity_smul_of_pow_eq_one (F := F) (N := Fam D.toPre F k) Φ ζ (ζ' * c)
    hM hM' hU hW
  refine ⟨u, hu, fun s t₀ t t₀' t' a b a' b' => ?_⟩
  rw [hΦ] at a
  rw [hΦ'] at a'
  rw [DVR.isSmul_iff] at b b' ⊢
  have f := LinearMap.congr_fun e s
  simp only [LinearMap.smul_apply] at f
  rw [b', a', b, a, hc, LinearMap.smul_apply, smul_smul, f]

end GlobalTheory
