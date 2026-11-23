import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExists
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagHodgeStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.GeoNumOneLin
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesWeightBoundOfFreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptGlobalNefBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

namespace GlobalTheory.CompanionTheory.Ar.Cusp.RootNef

theorem nefOnFibres_of_wt {Ψ : Type} [Fintype Ψ] {N : ℕ} (M : Top.RootModel Ψ N) (n : Ψ × Fin N → ℤ)
    (h : ∀ p : ℕ, p.Prime → M.NefAt p (fun τ i => -(n (τ, i) : ℝ)) 0) :
    NefOnFibres (mCoordIdeal M.y) (∑ r, n r • M.xdeg r) := by
  intro W h1 h2 h3 h4
  obtain ⟨d, -, he⟩ := LevelTowerAlt.geoNum_one_lin W
  have h5 := h _ (PB.prime_charOf_of_ne_zero h1.1 h3) W ⟨h1, h2, rfl, h4⟩
  unfold Top.RootModel.curveDeg at h5
  rw [Fintype.sum_option] at h5
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, neg_neg, M.x_deg, he] at h5
  rw [he]
  have : ∑ k, (∑ r, n r • M.xdeg r) k * d k = ∑ r, n r * ∑ k, M.xdeg r k * d k := by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [_root_.mul_assoc]
  rw [this]
  exact_mod_cast h5

theorem nefThreshold_of_gap_one {Ψ : Type} [Fintype Ψ] {N j : ℕ} (mu : Top.Wt Ψ N) (b : ℕ) (hb : 4 * Fintype.card Ψ + 2 ≤ b)
    (h1 : ∀ τ i, |mu τ i| ≤ 1) (h2 : ∀ τ, Top.gap j mu τ = 1) : Top.NefThreshold j b mu := by
  intro τ
  have hn : ‖mu‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ =>
    (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => h1 τ i
  have hb' : 4 * (Fintype.card Ψ : ℝ) + 2 ≤ b := by exact_mod_cast hb
  rw [h2]
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card Ψ)]

end GlobalTheory.CompanionTheory.Ar.Cusp.RootNef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) [Fintype (CMType H)] (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → Fl.RootLines M.xdeg e → NefOnFibres (mCoordIdeal M.y) (∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => D.p ≤ (i : ℕ)), M.xdeg (τ, i)) ∧ NefOnFibres (mCoordIdeal M.y) (-∑ τ, ∑ i ∈ Finset.univ.filter (fun i : Fin (D.p + D.q) => (i : ℕ) < D.p), M.xdeg (τ, i)) := by
  intro hG E _ _ _ H D Xo l c Y S _ M 𝔐 Fl e hY hp hq hS hS' hR
  obtain ⟨Yl, hg, hYl, -, -, hdom⟩ := hY
  have key : ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → (∀ τ i, |mu τ i| ≤ 1) →
      (∀ τ, Top.gap D.p mu τ = 1) → ∀ r : ℕ, r.Prime → M.NefAt r mu 0 := by
    intro mu hd h1 h2 r hr
    by_cases hrS : r ∈ S
    · exact GlobalTheory.T.root_lines_weight_bound_of_free hG.2.2.2.2.2.2.1 E H D l (Xo l) c _ _ Y S M 𝔐 Fl e r hrS (hS r hrS) hR mu hd
    · obtain ⟨a1, a2, a3⟩ := hS' r hr hrS
      exact GlobalTheory.T.hodge_cpt_global_nef_bound E H D Xo Yl (fun p W hp hW i => ⟨((hYl p W hp hW).2 i).1, ((hYl p W hp hW).2 i).2.1⟩)
        l c hg Y hdom hp hq S M 𝔐 Fl e hR r hr a3 hrS a1 mu hd (GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefThreshold_of_gap_one mu r a2 h1 h2)
  have g1 : D.p - 1 < D.p + D.q := by omega
  have g2 : D.p < D.p + D.q := by omega
  have g3 : ¬ D.p ≤ D.p - 1 := by omega
  have g4 : D.p - 1 < D.p := by omega
  constructor
  · have := GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefOnFibres_of_wt M (fun r => if D.p ≤ (r.2 : ℕ) then 1 else 0) (key _ ?_ ?_ ?_)
    · convert this using 1
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_filter, ite_smul, one_smul, zero_smul]
    · intro τ a b hab
      have : (a : ℕ) ≤ b := hab
      dsimp only
      split_ifs <;> first | omega | norm_num
    · intro τ i
      dsimp only
      split_ifs <;> norm_num
    · intro τ
      simp [Top.gap, Top.ent, g1, g2, g3]
  · have := GlobalTheory.CompanionTheory.Ar.Cusp.RootNef.nefOnFibres_of_wt M (fun r => if (r.2 : ℕ) < D.p then -1 else 0) (key _ ?_ ?_ ?_)
    · convert this using 1
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_filter, ite_smul, neg_smul, one_smul, zero_smul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => ?_
      split_ifs <;> simp
    · intro τ a b hab
      have : (a : ℕ) ≤ b := hab
      dsimp only
      split_ifs <;> first | omega | norm_num
    · intro τ i
      dsimp only
      split_ifs <;> norm_num
    · intro τ
      simp [Top.gap, Top.ent, g1, g2, g4]
