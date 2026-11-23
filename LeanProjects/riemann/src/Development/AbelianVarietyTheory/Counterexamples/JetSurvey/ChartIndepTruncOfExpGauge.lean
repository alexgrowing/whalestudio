import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpUniqChart
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffPolyAdd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpTiePf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.LinEig
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GaugeUniqPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAdd
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsNabNotIsNablaPin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.HarmonicFixedCard
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartIndepExpTest

open NumberField MvPowerSeries ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1

theorem psiCover {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : PsiCoverSt H := by
  intro τ
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    have := congrArg (fun a : 𝓞 E => τ (a : E)) H.rt_sq
    rw [H.sqrt_neg_disc_sq]; simpa using this
  have hre : H.rt0.re = 0 := by
    have h2 := congrArg Complex.re H.sqrt_neg_disc_sq
    have h3 := congrArg Complex.im H.sqrt_neg_disc_sq
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im] at h2 h3
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    by_contra hne
    have him : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [him] at h2
    nlinarith [mul_self_nonneg H.rt0.re]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact Or.inl h
  · right
    show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
    rw [h]
    apply Complex.ext <;> simp [hre]

section Quad

variable {S : Type} [CommRing S] {d : ℕ}

abbrev sq2 (i j : Fin d) : Fin 1 × Fin d →₀ ℕ := Finsupp.single (0, i) 1 + Finsupp.single (0, j) 1

theorem exists_sq_of_degree_two (m : Fin 1 × Fin d →₀ ℕ) (hm : m.degree = 2) : ∃ i j, i ≤ j ∧ m = sq2 i j := by
  classical
  have hc : Multiset.card (Finsupp.toMultiset m) = 2 := by
    rw [Finsupp.card_toMultiset, ← hm]; rfl
  obtain ⟨⟨o, a⟩, ⟨o', b⟩, hab⟩ := Multiset.card_eq_two.1 hc
  obtain rfl : o = 0 := Subsingleton.elim _ _
  obtain rfl : o' = 0 := Subsingleton.elim _ _
  have : m = sq2 a b := by
    rw [← Finsupp.toMultiset_toFinsupp m, hab]
    ext x
    simp [Multiset.count_cons, Multiset.count_singleton, Finsupp.single_apply, eq_comm, add_comm]
  rcases le_total a b with h | h
  · exact ⟨a, b, h, this⟩
  · exact ⟨b, a, h, this.trans (add_comm _ _)⟩

theorem sq_monomial_injective {i j a b : Fin d} (hij : i ≤ j) (hab : a ≤ b) (h : sq2 i j = sq2 a b) : i = a ∧ j = b := by
  rcases (Finsupp.single_add_single_eq_single_add_single one_ne_zero one_ne_zero).1 h with
    ⟨h1, h2⟩ | ⟨-, h1, h2⟩ | ⟨h1, -⟩
  · exact ⟨congrArg Prod.snd h1, congrArg Prod.snd h2⟩
  · have e1 : i = b := congrArg Prod.snd h1
    have e2 : j = a := congrArg Prod.snd h2
    subst e1 e2
    exact ⟨le_antisymm hij hab, le_antisymm hab hij⟩
  · omega

def quadMat (q : MvPowerSeries (Fin 1 × Fin d) S) : Matrix (Fin d) (Fin d) S :=
  fun i j => if i ≤ j then coeff (sq2 i j) q else 0

theorem eq_sum_quadMat (q : MvPowerSeries (Fin 1 × Fin d) S) (hq : ∀ m, coeff m q ≠ 0 → m.degree = 2) :
    q = ∑ p : Fin d × Fin d, C (quadMat q p.1 p.2) * X (0, p.1) * X (0, p.2) := by
  classical
  ext m
  have hc : ∀ p : Fin d × Fin d, coeff m (C (quadMat q p.1 p.2) * X ((0 : Fin 1), p.1) * X (0, p.2) :
      MvPowerSeries (Fin 1 × Fin d) S) = if m = sq2 p.1 p.2 then quadMat q p.1 p.2 else 0 := by
    intro p
    rw [mul_assoc, coeff_C_mul, X, X, monomial_mul_monomial, coeff_monomial]
    split_ifs <;> simp
  rw [map_sum]
  simp only [hc]
  by_cases hm : m.degree = 2
  · obtain ⟨a, b, hab, rfl⟩ := exists_sq_of_degree_two m hm
    rw [Finset.sum_eq_single (a, b)]
    · simp [quadMat, hab]
    · rintro ⟨i, j⟩ - hne
      split_ifs with h
      · by_cases hij : i ≤ j
        · obtain ⟨rfl, rfl⟩ := sq_monomial_injective hab hij h
          exact absurd rfl hne
        · simp [quadMat, hij]
      · rfl
    · simp
  · have h0 : coeff m q = 0 := by_contra fun h => hm (hq m h)
    rw [h0]
    refine (Finset.sum_eq_zero fun p _ => if_neg fun h => hm ?_).symm
    rw [h]; simp

end Quad

theorem killAddVal : KillAddValSt := by
  intro E _ _ _ H Dw l c S _ _ _ k n g q hq0 hq2 hqp a P hP
  have hβ : ∀ i j, quadMat q i j ≠ 0 →
      ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1 := by
    intro i j h
    refine hqp _ _ ?_
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    intro h0
    apply h
    unfold quadMat
    split_ifs
    · exact h0
    · rfl
  let r : Fin n → Fin 1 × Fin (dL Dw) → Fin n × Fin (dL Dw) := fun b p => (b, p.2)
  have hK := killAddValCol_of (TB.killAdd_of TB.quadratic_column_derivative) E H Dw l c S k n
    (∏ b, rename (r b) (g b)) (quadMat q) (psiCover H) hβ a P hP
  have hcq : constantCoeff (-((k : S) • q)) = 0 := by simp [hq0]
  have hexp : ∀ b, rename (r b) (PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) =
      Germ.FB.expS S (rename (r b) (-((k : S) • q))) := by
    intro b
    rw [rename_eq_subst, rename_eq_subst]
    simp only [Germ.FB.expS, PowerSeries.subst_def]
    rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun _ => hcq)
      (hasSubst_of_constantCoeff_zero fun _ => by simp)]
  have hsum : ∑ b, rename (r b) (-((k : S) • q)) = -((k : S)) • TB.quadCol (n := n) (quadMat q) := by
    rw [TB.quadCol, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_neg, map_smul, neg_smul]
    congr 2
    conv_lhs => rw [eq_sum_quadMat q hq2]
    rw [map_sum, Fintype.sum_prod_type]
    simp only [map_mul, rename_C, rename_X, r]
  have hprod : ∏ b, rename (r b) (g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) =
      Germ.FB.expS S (-((k : S)) • TB.quadCol (n := n) (quadMat q)) * ∏ b, rename (r b) (g b) := by
    rw [← hsum, GlobalTheory.IndefiniteRowSideFullHecke.HarmonicEigenCriterion.expS_sum _ _ (fun b => by rw [constantCoeff_rename]; exact hcq),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => by rw [map_mul, hexp, mul_comm]
  rw [← hprod] at hK
  simpa only [r, prodCol_holds E H Dw S n] using hK

theorem expUniqTan : ExpUniqTanSt := ExpUniqChart.expUniqTan

theorem frTruncOfGerms : FrTruncOfGermsSt :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ C h => GlobalTheory.NablaPinCompare.compat_of_germs C h

theorem chartIndepTrunc_of_expGauge (hG : ExpGaugeOfSt) : ChartIndepTruncSt :=
  chartIndepTrunc_of (expChartOf_of (expActOf_of LinEig.linEig_holds)) hG tie_holds expUniqTan
    (gaugeUniq_of_global GlobalTheory.SemiRigid.globalFns) killAddVal

theorem four_claims : ExpUniqTanSt ∧ KillAddValSt ∧ FrTruncOfGermsSt ∧ (ExpGaugeOfSt → ChartIndepTruncSt) :=
  ⟨expUniqTan, killAddVal, frTruncOfGerms, chartIndepTrunc_of_expGauge⟩

end GlobalTheory.ChartIndepExpTest
