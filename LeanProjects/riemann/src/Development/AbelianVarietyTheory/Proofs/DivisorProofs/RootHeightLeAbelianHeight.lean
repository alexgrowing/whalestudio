import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointHeightDualAndLinearCombStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetricStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.DualRef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmplePullbackOfInducedHermitianBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleSectionsAvoidClosedPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundedBelowOffZeroLocusStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open CategoryTheory AlgebraicGeometry GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.ProjVar
open scoped ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RootHtBound

theorem exists_closed_over {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) {b : Y.X}
    (hb : IsClosed ({b} : Set Y.X)) : ∃ w : V.G, IsClosed ({w} : Set V.G) ∧ V.π w = b := by
  obtain ⟨w₀, h₀⟩ := V.π.surjective b
  have hc : IsClosed (V.π ⁻¹' {b}) := hb.preimage V.π.continuous
  have : CompactSpace V.G := QuasiCompact.compactSpace_of_compactSpace (V.π ≫ Y.str)
  obtain ⟨w, hw, hw'⟩ := hc.exists_closed_singleton ⟨w₀, h₀⟩
  exact ⟨w, hw', hw⟩

theorem abs_le_of_two (n₁ n₂ : ℕ) (c₁ c₂ K a r : ℝ) (hK : 0 ≤ K) (e₁ : -c₁ ≤ n₁ * (K * a) + r)
    (e₂ : -c₂ ≤ n₂ * (K * a) + -r) : |r| ≤ ((max n₁ n₂ : ℕ) * K + |c₁| + |c₂|) * (|a| + 1) := by
  have hKa : 0 ≤ K * |a| := mul_nonneg hK (abs_nonneg a)
  have up (n : ℕ) (hn : n ≤ max n₁ n₂) : (n : ℝ) * (K * a) ≤ ((max n₁ n₂ : ℕ) : ℝ) * (K * |a|) :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self a) hK) (Nat.cast_nonneg n)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hKa)
  have u₁ := up n₂ (le_max_right _ _)
  have u₀ := up n₁ (le_max_left _ _)
  have hc₁ := neg_abs_le c₁
  have hc₂ := le_abs_self c₂
  have hc₁' := le_abs_self c₁
  have hc₂' := neg_abs_le c₂
  have hM : (0 : ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
  have e : ((max n₁ n₂ : ℕ) * K + |c₁| + |c₂|) * (|a| + 1) =
      ((max n₁ n₂ : ℕ) : ℝ) * (K * |a|) + ((max n₁ n₂ : ℕ) * K) + (|c₁| + |c₂|) * |a| + |c₁| + |c₂| := by ring
  have h3 : 0 ≤ (|c₁| + |c₂|) * |a| := by positivity
  rw [e, abs_le]
  constructor <;> linarith

theorem dom : GlobalTheory.Published.ArExists → ∀ {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F} (V : Cover Y)
    (A : Adl C Y) (L : HermLB V.p) (k : ℕ), 0 < k → V.Induces A L k → Y.ample A.D → ∀ M : HermLB V.p,
    ∃ (n : ℕ) (c : ℝ), ∀ w : V.G, IsClosed ({w} : Set V.G) → ∀ a b : ℝ, IsPtHt L (V.j w) a → IsPtHt M (V.j w) b →
      -c ≤ n * a + b := by
  intro hE F _ _ C Y V A L k hk hI hA M
  obtain ⟨n, m, s, hs⟩ := GlobalTheory.T.ample_sections_avoid_closed_points V L M (GlobalTheory.T.ample_pullback_of_induced_hermitian_bundle V A L k hk hI hA)
  choose c hc using fun i => GlobalTheory.T.height_bounded_below_off_zero_locus (𝓞 F) V.X V.p Y.dim V.ar _ (s i)
  refine ⟨n, ∑ i, |c i|, fun w hw a b ha hb => ?_⟩
  obtain ⟨i, hi⟩ := hs w hw
  have halg := GlobalTheory.Mean4O.CoverHt.isAlgPt V w hw
  have hcomb := (GlobalTheory.T.point_height_dual_and_linear_comb hE _ V.X V.p _ V.ar (V.j w) halg).2 (Fin 2) ![L, M] ![a, b]
    (fun j => by fin_cases j <;> assumption) ![(n : ℤ), 1]
  have h1 := hc i (V.j w) hi halg _ hcomb
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Int.cast_natCast,
    Int.cast_one, one_mul] at h1
  have h2 : c i ≤ ∑ j, |c j| := (le_abs_self _).trans
    (Finset.single_le_sum (f := fun j => |c j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  linarith

theorem root_ht_le : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → (∀ (P : Finset ℕ) (c : O.s.Comp), O.LatModel P c) → ∀ (c : O.s.Comp) (x : DV.Rt D.what₂.Tau O.N), ∃ C : ℝ, ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) → |(O.root0 c ∅ x).ht b| ≤ C * (|(O.met.ab c).ht b| + 1) := by
  intro hP _ D O hO mdl c x
  have hE : GlobalTheory.Published.ArExists := hP.p4.arExists
  set W := mdl ∅ c with hW
  have hR : W.V.Induces (O.root0 c ∅ x) (W.root ∅ x) 1 :=
    GlobalTheory.T.lattice_model_induces_root_metric D O hO.dualRef ∅ c W ∅ subset_rfl x
  obtain ⟨n₁, c₁, h₁⟩ := dom hE W.V (O.met.ab c) W.amp W.k W.k_pos W.amp_spec (hO.ample_ab c) (W.root ∅ x)
  obtain ⟨n₂, c₂, h₂⟩ := dom hE W.V (O.met.ab c) W.amp W.k W.k_pos W.amp_spec (hO.ample_ab c) (W.root ∅ x).dual
  set K : ℝ := (W.k : ℝ) * (((O.met.ab c).n : ℕ) : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨((max n₁ n₂ : ℕ) : ℝ) * K + |c₁| + |c₂|, fun b hb => ?_⟩
  obtain ⟨w, hw, hwb⟩ := exists_closed_over W.V hb
  have ha := (GlobalTheory.Mean4O.CoverHt.main hE _ _ _ W.V _ _ _ w hw W.amp_spec).2
  have hr := GlobalTheory.Mean4O.CoverHt.main hE _ _ _ W.V _ _ _ w hw hR
  have hd := (GlobalTheory.T.point_height_dual_and_linear_comb hE _ W.V.X W.V.p _ W.V.ar (W.V.j w) hr.1).1 _ _ hr.2
  have e₁ := h₁ w hw _ _ ha hr.2
  have e₂ := h₂ w hw _ _ ha hd
  rw [hwb] at e₁ e₂
  have hn : ((O.root0 c ∅ x).n : ℕ) = 1 := rfl
  rw [hn] at e₁ e₂
  simp only [Nat.cast_one, one_mul] at e₁ e₂
  exact abs_le_of_two n₁ n₂ c₁ c₂ K _ _ hK0 e₁ e₂

end GlobalTheory.RootHtBound
