import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.NondegenerateCharts
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.BlockAdmissibleChart
import Formalism.LocalToGlobal.CharacterGerms.NegMem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntSOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubstSame
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.DerivJet

variable {C : Type} [Field C] {W : Type} [Fintype W]

theorem jetAt0_mul_lin (c : W → C) (Q : MvPolynomial W C) (G : MvPowerSeries W C) :
    jetAt0 (Q * ∑ w, MvPolynomial.C (c w) * MvPolynomial.X w) G =
      jetAt0 Q (∑ w, c w • MvPowerSeries.pderiv C w G) := by
  rw [Finset.mul_sum, GlobalTheory.MinorShiftJet.jetAt0_sum_left, GlobalTheory.MinorShiftJet.jetAt0_sum_smul_right]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_left_comm, GlobalTheory.MinorShiftJet.jetAt0_C_mul, GlobalTheory.MinorShiftJet.jetAt0_mul_X]

theorem jetAt0_iterate {A : Type} (S : A → MvPowerSeries W C) (D : A → A) (c : W → C) (k : ℕ)
    (h : k ≠ 0 → ∀ G, S (D G) = ∑ w, c w • MvPowerSeries.pderiv C w (S G)) (Q : MvPolynomial W C) (G : A) :
    jetAt0 Q (S (D^[k] G)) = jetAt0 (Q * (∑ w, MvPolynomial.C (c w) * MvPolynomial.X w) ^ k) (S G) := by
  induction k generalizing G with
  | zero => simp
  | succ k ih =>
    have h' := h (Nat.succ_ne_zero k)
    rw [Function.iterate_succ_apply, ih (fun _ => h'), h', ← jetAt0_mul_lin, pow_succ, mul_assoc]

theorem jetAt0_foldr {A ι : Type} (S : A → MvPowerSeries W C) (D : ι → A → A) (c : ι → W → C) (m : ι → ℕ)
    (h : ∀ l, m l ≠ 0 → ∀ G, S (D l G) = ∑ w, c l w • MvPowerSeries.pderiv C w (S G)) (L : List ι)
    (Q : MvPolynomial W C) (G : A) :
    jetAt0 Q (S (L.foldr (fun l g => (D l)^[m l] g) G)) =
      jetAt0 (Q * (L.map fun l => (∑ w, MvPolynomial.C (c l w) * MvPolynomial.X w) ^ m l).prod) (S G) := by
  induction L generalizing Q with
  | nil => simp
  | cons l L ih =>
    rw [List.foldr_cons, jetAt0_iterate S (D l) (c l) (m l) (h l), ih, List.map_cons, List.prod_cons, mul_assoc]

theorem jetAt0_one_left {σ : Type} (G : MvPowerSeries σ C) :
    jetAt0 1 G = MvPowerSeries.constantCoeff G := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', GlobalTheory.MinorShiftJet.jetAt0_monomial]
  simp [mfact]

theorem constantCoeff_DpolyN_eq_jetAt0 : ∀ (C : Type) [Field C] (dd n : ℕ) (F : Fin dd → PS C 2 dd) (ι : Type) [Fintype ι] (cp : ι → Fin n) (uv : ι → Fin dd → C) (W : Type) [Fintype W] (E : Fin n × Fin dd → MvPowerSeries W C), (∀ s, MvPowerSeries.constantCoeff (E s) = 0) → ∀ (co : ι → W → C) (P : MvPolynomial ι C), (∀ ℓ ∈ P.vars, ∀ G : PS C n dd, MvPowerSeries.subst E (DofN F (cp ℓ) (uv ℓ) G) = ∑ w, co ℓ w • MvPowerSeries.pderiv C w (MvPowerSeries.subst E G)) → ∀ G : PS C n dd, MvPowerSeries.constantCoeff (DpolyN F cp uv P G) = jetAt0 (MvPolynomial.aeval (fun ℓ => ∑ w, MvPolynomial.C (co ℓ w) * MvPolynomial.X w) P : MvPolynomial W C) (MvPowerSeries.subst E G) := by
  intro C _ dd n F ι _ cp uv W _ E hE co P h G
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', GlobalTheory.MinorShiftJet.jetAt0_sum_left, DpolyN, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_mul, MvPowerSeries.constantCoeff_C, MvPolynomial.algebraMap_eq, GlobalTheory.MinorShiftJet.jetAt0_C_mul]
  congr 1
  rw [← cc_subst hE, ← jetAt0_one_left, DmonN,
    jetAt0_foldr (fun g => MvPowerSeries.subst E g) (fun l => DofN F (cp l) (uv l)) co m
      (fun l hl => h l ((MvPolynomial.mem_vars l).2 ⟨m, hm, Finsupp.mem_support_iff.2 hl⟩)),
    one_mul, Finset.prod_map_toList]

end GlobalTheory.DerivJet
