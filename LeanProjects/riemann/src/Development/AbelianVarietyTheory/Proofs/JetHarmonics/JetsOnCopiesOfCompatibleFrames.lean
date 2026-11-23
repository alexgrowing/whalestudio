import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.RoundingSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowFrame
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatementStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsPowerProductStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowJets

theorem exists_position_basis {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {n r : ℕ} (xe : X' ≃+ (Fin n → X))
    (b : Module.Basis (Fin r) ℤ X) :
    ∃ (r' : ℕ) (b' : Module.Basis (Fin r') ℤ X'), ∀ k, ∃ i j, xe (b' k) = Pi.single i (b j) := by
  classical
  let B : Module.Basis (Σ _ : Fin n, Fin r) ℤ (Fin n → X) := Pi.basis fun _ => b
  refine ⟨_, (B.map xe.toIntLinearEquiv.symm).reindex (Fintype.equivFin _), fun k => ?_⟩
  refine ⟨((Fintype.equivFin (Σ _ : Fin n, Fin r)).symm k).1, ((Fintype.equivFin (Σ _ : Fin n, Fin r)).symm k).2, ?_⟩
  simp [B, Pi.basis_apply]

theorem sum_single_add {X : Type} [AddCommGroup X] {n : ℕ} (Q : X → ℤ) (i : Fin n) (x : X) (w : Fin n → X) :
    ∑ k, Q ((Pi.single i x + w : Fin n → X) k) = ∑ k, Q (w k) + (Q (x + w i) - Q (w i)) := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ (fun k => Q (w k)) (Finset.mem_univ i),
    Finset.sum_congr rfl (g := fun k => Q (w k)) fun k hk => by
      rw [Pi.add_apply, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hk), zero_add]]
  simp only [Pi.add_apply, Pi.single_eq_same]
  ring

theorem exists_basis_bounds {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {n r : ℕ} (xe : X' ≃+ (Fin n → X))
    (Q : X → ℤ) (h0 : Q 0 = 0) (hQ : ∀ x, 0 ≤ Q x) (Φ M0 : ℝ) (b : Module.Basis (Fin r) ℤ X)
    (hΦ : ∀ j, (Q (b j) : ℝ) ≤ Φ) (hM : ∀ j z, |((Q (b j + z) - Q (b j) - Q z : ℤ) : ℝ)| ≤ M0 * Q z) :
    ∃ (r' : ℕ) (b' : Module.Basis (Fin r') ℤ X'), (∀ j, (sumQ xe Q (b' j) : ℝ) ≤ Φ) ∧
      ∀ j w, |((sumQ xe Q (b' j + w) - sumQ xe Q (b' j) - sumQ xe Q w : ℤ) : ℝ)| ≤ max M0 0 * sumQ xe Q w := by
  obtain ⟨r', b', hb⟩ := exists_position_basis xe b
  have e1 : ∀ k i j, xe (b' k) = Pi.single i (b j) → sumQ xe Q (b' k) = Q (b j) := fun k i j h => by
    have := sum_single_add Q i (b j) 0
    simpa [sumQ, h, h0] using this
  refine ⟨r', b', fun k => ?_, fun k w => ?_⟩
  · obtain ⟨i, j, h⟩ := hb k
    rw [e1 k i j h]
    exact hΦ j
  · obtain ⟨i, j, h⟩ := hb k
    have e2 : sumQ xe Q (b' k + w) = sumQ xe Q w + (Q (b j + xe w i) - Q (xe w i)) := by
      unfold sumQ
      rw [map_add, h]
      exact sum_single_add Q i (b j) (xe w)
    have e3 : sumQ xe Q (b' k + w) - sumQ xe Q (b' k) - sumQ xe Q w = Q (b j + xe w i) - Q (b j) - Q (xe w i) := by
      rw [e1 k i j h, e2]; ring
    have e4 : Q (xe w i) ≤ sumQ xe Q w :=
      Finset.single_le_sum (f := fun k => Q (xe w k)) (fun k _ => hQ _) (Finset.mem_univ i)
    rw [e3]
    refine (hM j _).trans (mul_le_mul (le_max_left _ _) (by exact_mod_cast e4) (by exact_mod_cast hQ _) (le_max_right _ _))

theorem jets_on_copies : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → JetsOnCopiesCompatibleFrames := by
  intro L1 L2 L4 TB E _ _ _ H Dw l Xo c inst hstar
  obtain rfl : inst = H.starRing := starSt E H inst hstar
  letI := H.starRing
  intro T io y _ C htr P ϖ hϖ Q hQ Φ M0 r b hΦ0 hΦ hM n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ _ v hv q D hq hD f hf
  choose f₀ hf₀ using hf
  obtain ⟨τ, hτ, htrunc, hgerm⟩ := frameNSt_holds E H T.V C.I.G P (chD C.ch) C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT
    C.xT C.eT C.wPT C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  have hu := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n (chD C.ch) pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨r', b', h1, h2⟩ := exists_basis_bounds pD.xe Q (Q_zero hϖ P.D hQ) (RoundingSumAlt.Q_nonneg hϖ hQ) Φ M0 b hΦ hM
  have hD' : (D : ℝ) * max M0 0 < q := by
    rcases le_total M0 0 with h | h
    · rw [max_eq_right h, mul_zero]
      exact_mod_cast (by omega : 0 < q)
    · rwa [max_eq_left h]
  obtain ⟨s, σ', g, lam, a1, a2, a3, a4, a5, a6⟩ := GlobalTheory.UnifJets.jets L1 L2 L4 TB T.V ϖ hϖ D' A' G' U' (Fin n × Fin (chD C.ch))
    (zV pG C.xT) hu τ hτ (htrunc htr) (sumQ pD.xe Q) (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) Φ (max M0 0) r' b' hΦ0
    (le_max_right _ _) h1 h2 F v hv q D hq hD' (fun e => f₀ e)
  refine ⟨s, σ', g, lam, a1, a2, (hgerm F q σ' g).2 a3, a4, a5, fun e he => ?_⟩
  rw [a6 e he, map_smul, MvPowerSeries.coeff_map, ← hf₀ e, smul_eq_mul, ← IsScalarTower.algebraMap_apply]
  rfl

end GlobalTheory.PowJets
