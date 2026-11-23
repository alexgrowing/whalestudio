import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndExp
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConstantCoeffPolyAdd
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PartialDerivativeExponent
import ReciprocityTheory.ReductiveGroups.Models.FiniteGeneration.FiniteGenerationProofs.SolveV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAddFin

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open MvPowerSeries NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace KAVal

theorem degree_eq_two {σ : Type} (e : σ →₀ ℕ) (he : e.degree = 2) :
    ∃ s t, e = Finsupp.single s 1 + Finsupp.single t 1 := by
  classical
  have hne : e ≠ 0 := by
    rintro rfl
    simp at he
  obtain ⟨s, hs⟩ : ∃ s, e s ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Finsupp.ext h)
  have hle : Finsupp.single s 1 ≤ e := by
    intro x
    by_cases hx : x = s
    · subst hx
      simp only [Finsupp.single_eq_same]
      omega
    · simp [Ne.symm hx]
  have hsplit : e = (e - Finsupp.single s 1) + Finsupp.single s 1 := (tsub_add_cancel_of_le hle).symm
  have he' : (e - Finsupp.single s 1).degree = 1 := by
    have h2 := congrArg Finsupp.degree hsplit
    rw [map_add, Finsupp.degree_single] at h2
    omega
  obtain ⟨t, ht⟩ := Formalism.FG.SolveVAux.degree_eq_one (e - Finsupp.single s 1) he'
  refine ⟨s, t, ?_⟩
  rw [hsplit, ht, add_comm]

end KAVal

namespace KAVal

variable {S : Type} [CommRing S] {N : ℕ}

def qβ (q : MvPowerSeries (Fin 1 × Fin N) S) (i j : Fin N) : S :=
  if i ≤ j then coeff (Finsupp.single ((0 : Fin 1), i) 1 + Finsupp.single ((0 : Fin 1), j) 1) q else 0

theorem coeff_XX (e : Fin 1 × Fin N →₀ ℕ) (s t : Fin 1 × Fin N) :
    coeff e (X s * X t : MvPowerSeries (Fin 1 × Fin N) S) =
      if e = Finsupp.single s 1 + Finsupp.single t 1 then 1 else 0 := by
  rw [X, X, monomial_mul_monomial, mul_one, coeff_monomial]

theorem single_add_single_at (a b x : Fin 1 × Fin N) :
    (Finsupp.single a 1 + Finsupp.single b 1 : Fin 1 × Fin N →₀ ℕ) x = (if a = x then 1 else 0) + (if b = x then 1 else 0) := by
  simp [Finsupp.single_apply]

theorem quad_form (q : MvPowerSeries (Fin 1 × Fin N) S) (hq0 : constantCoeff q = 0)
    (hq2 : ∀ m, coeff m q ≠ 0 → m.degree = 2) :
    q = ∑ i, ∑ j, C (qβ q i j) * X ((0 : Fin 1), i) * X ((0 : Fin 1), j) := by
  classical
  ext e
  rw [map_sum]
  simp only [map_sum, mul_assoc, coeff_C_mul, coeff_XX]
  by_cases hdeg : e.degree = 2
  · obtain ⟨s, t, hst⟩ := degree_eq_two e hdeg
    obtain ⟨o1, p⟩ := s
    obtain ⟨o2, p'⟩ := t
    have h1 : o1 = 0 := Subsingleton.elim _ _
    have h2 : o2 = 0 := Subsingleton.elim _ _
    subst h1 h2

    obtain ⟨a, b, hab, hee⟩ : ∃ a b : Fin N, a ≤ b ∧
        e = Finsupp.single ((0 : Fin 1), a) 1 + Finsupp.single ((0 : Fin 1), b) 1 := by
      rcases le_total p p' with h | h
      · exact ⟨p, p', h, hst⟩
      · exact ⟨p', p, h, by rw [hst, add_comm]⟩
    rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single b]
      · rw [if_pos hee, mul_one, qβ, if_pos hab, ← hee]
      · intro j _ hj
        rw [if_neg, mul_zero]
        intro h
        have := congrArg (fun f => f ((0 : Fin 1), b)) (hee.symm.trans h)
        simp only [single_add_single_at, Prod.mk.injEq, true_and] at this
        split_ifs at this <;> simp_all
      · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h : e = Finsupp.single ((0 : Fin 1), i) 1 + Finsupp.single ((0 : Fin 1), j) 1
      · have hi' := congrArg (fun f => f ((0 : Fin 1), i)) (hee.symm.trans h)
        have hj' := congrArg (fun f => f ((0 : Fin 1), j)) (hee.symm.trans h)
        simp only [single_add_single_at] at hi' hj'
        have hbi : b = i := by
          by_contra hb
          simp [Ne.symm hi, hb] at hi'
          split_ifs at hi' <;> omega
        subst hbi
        have haj : a = j := by
          by_contra ha
          split_ifs at hj' <;> simp_all
        subst haj
        have hlt : ¬ b ≤ a := fun h' => hi (le_antisymm h' hab)
        rw [qβ, if_neg hlt, zero_mul]
      · rw [if_neg h, mul_zero]
    · simp
  · have hz : coeff e q = 0 := by
      by_contra h
      exact hdeg (hq2 e h)
    rw [hz]
    symm
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg, mul_zero]
    rintro rfl
    apply hdeg
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]

end KAVal

namespace KAVal

variable {S : Type} [CommRing S] [Algebra ℚ S]

theorem rename_expS {σ τ : Type} (f : σ → τ) [Filter.TendstoCofinite f]
    (h : MvPowerSeries σ S) (hh : constantCoeff h = 0) :
    MvPowerSeries.rename f (PowerSeries.subst h (PowerSeries.exp S)) =
      PowerSeries.subst (MvPowerSeries.rename f h) (PowerSeries.exp S) := by
  have ha : HasSubst (fun _ : Unit => h) := hasSubst_of_constantCoeff_zero fun _ => hh
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst, PowerSeries.subst, PowerSeries.subst,
    subst_comp_subst_apply ha (HasSubst.X_comp _)]

theorem prod_expS {τ : Type} {ι : Type} (s : Finset ι) (x : ι → MvPowerSeries τ S)
    (hx : ∀ i, constantCoeff (x i) = 0) :
    ∏ i ∈ s, PowerSeries.subst (x i) (PowerSeries.exp S) = PowerSeries.subst (∑ i ∈ s, x i) (PowerSeries.exp S) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    rw [PowerSeries.subst_zero_eq_C_constantCoeff, PowerSeries.constantCoeff_exp, map_one]
    simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, ih,
      ← Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent.expS_add _ _ (hx a) (by rw [map_sum]; exact Finset.sum_eq_zero fun i _ => hx i)]

end KAVal

theorem killAddVal_of (hPsi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), PsiCoverSt H) :
    KillAddValSt := by
  intro E _ _ _ H Dw l c S _ _ _ k n g q hq0 hq2 hqp a P hP
  classical
  set β := KAVal.qβ q with hβdef
  have hβ : ∀ i j, β i j ≠ 0 → ((ltIdx Dw).symm j).1 = ComplexEmbedding.conjugate ((ltIdx Dw).symm i).1 := by
    intro i j h
    simp only [hβdef, KAVal.qβ] at h
    split_ifs at h with hij
    · apply hqp ((ltIdx Dw).symm i) ((ltIdx Dw).symm j)
      simpa using h
    · exact absurd rfl h
  let ren : Fin n → MvPowerSeries (Fin 1 × Fin (dL Dw)) S →ₐ[S] MvPowerSeries (Fin n × Fin (dL Dw)) S :=
    fun b => MvPowerSeries.rename (fun p : Fin 1 × Fin (dL Dw) => ((b, p.2) : Fin n × Fin (dL Dw)))
  have hq_form := KAVal.quad_form q hq0 hq2
  have hren_q : ∀ b, ren b q = ∑ i, ∑ j, MvPowerSeries.C (β i j) * MvPowerSeries.X (b, i) * MvPowerSeries.X (b, j) := by
    intro b
    conv_lhs => rw [hq_form]
    simp only [ren, map_sum, map_mul, MvPowerSeries.rename_C, MvPowerSeries.rename_X]
    rfl
  have hquad : (TB.quadCol (n := n) β : MvPowerSeries (Fin n × Fin (dL Dw)) S) = ∑ b, ren b q := by
    unfold TB.quadCol
    exact Finset.sum_congr rfl fun b _ => (hren_q b).symm
  have hcq : ∀ b, constantCoeff (ren b (-((k : S) • q))) = 0 := by
    intro b
    have : constantCoeff (-((k : S) • q)) = 0 := by simp [hq0]
    rw [MvPowerSeries.rename_eq_subst]
    exact constantCoeff_subst_eq_zero (HasSubst.X_comp _) (fun _ => by simp) this
  have hkey : ∏ b, ren b (g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) =
      Germ.FB.expS S (-((k : S)) • TB.quadCol (n := n) β) * ∏ b, ren b (g b) := by
    simp only [map_mul, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_congr rfl fun b _ => KAVal.rename_expS _ _ (by simp [hq0]), KAVal.prod_expS _ _ hcq, Germ.FB.expS,
      hquad, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_neg, map_smul, neg_smul]
  have hPC := prodCol_holds E H Dw S n
  calc ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          ∏ b, expVal (g b * PowerSeries.subst (-((k : S) • q)) (PowerSeries.exp S)) (colOf m b)
      = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) *
          mVal (Germ.FB.expS S (-((k : S)) • TB.quadCol (n := n) β) * ∏ b, ren b (g b)) m := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← hkey, hPC]
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * mVal (∏ b, ren b (g b)) m :=
        killAddValCol_of ReciprocityTheory.ChartRestriction.G.TB.kernel_additive E H Dw l c S k n _ β (hPsi E H) hβ a P hP
    _ = ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, expVal (g b) (colOf m b) := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [hPC]

end Formalism.MainNotions.ModuliIntegralCharts.H1
