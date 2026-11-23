import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LemmaHCols
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmonicValueIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConnectionSecondOfCommute
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConnectionKillsSeries
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpConjConnectionIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LemmaH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCCols
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.NabTrans
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChgPfTP
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GEWick
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.KillAdd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FormalGroupLawPointMaps
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.G2Assumption
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.FoldrIterateDerivationEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.TruncatedExpSecondEqFull

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Closed

theorem lemma_H_columns : ReciprocityTheory.ChartRestriction.G.TB.LemmaHColsSt :=
  ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.HCols.lemmaHCols_of Val.harmonic_value_integral ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_second_identity ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_kills_series

theorem symmetric_canonical_gauge : ReciprocityTheory.ChartRestriction.G.TB.SCSt :=
  ReciprocityTheory.ChartRestriction.G.TB.SCPf.sc_of ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_first_identity ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_second_identity ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab.connection_kills_series

private theorem prod_mem_pow_of_mem_pow_of_sum_le {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (J : Submodule R A) (hJ : (1 : A) ∈ J) {n : ℕ} (x : Fin n → A) (a : Fin n → ℕ) (e : ℕ)
    (hx : ∀ b, x b ∈ J ^ a b) (ha : ∑ b, a b ≤ e) : ∏ b, x b ∈ J ^ e := by
  have hprod : ∀ s : Finset (Fin n), ∏ b ∈ s, x b ∈ J ^ (∑ b ∈ s, a b) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw [Finset.prod_empty, Finset.sum_empty, pow_zero]
      exact Submodule.one_le.mp le_rfl
    · intro i t hi ih
      rw [Finset.prod_insert hi, Finset.sum_insert hi, pow_add]
      exact Submodule.mul_mem_mul (hx i) ih
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le ha
  have h1 : (1 : A) ∈ J ^ c := by
    first
      | simpa using Submodule.pow_mem_pow J hJ c
      | simpa using Submodule.pow_mem_pow hJ c
  have hm := Submodule.mul_mem_mul (hprod Finset.univ) h1
  rwa [mul_one, ← pow_add, ← hc] at hm

theorem scaled_connection_columns : ReciprocityTheory.ChartRestriction.G.TB.SCColsSt :=
  by
  intro R _ d O _ _ k _ _ _ hRQ J hJ1 B h hB w0 hw0 m ι π _ _ _ c s ξh ψ hξ hψ hp1 hp2 hp3 n P hPc e he f hf
  refine Submodule.sum_mem _ (fun mo _ => ?_)
  obtain ⟨r, hr⟩ := RingHom.mem_range.mp (hPc mo)
  rw [← hr, ← Algebra.smul_def]
  refine Submodule.smul_mem _ r (prod_mem_pow_of_mem_pow_of_sum_le J hJ1 _ _ e (fun b => ?_) (he mo ‹_›))
  refine symmetric_canonical_gauge R d O k hRQ J hJ1 B h hB w0 hw0 m ι π c s ξh ψ hξ hψ hp1 hp2 hp3 _ ?_ _ ?_ (f b) (hf b)
  · intro x
    classical
    rw [MvPolynomial.coeff_monomial]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro x hx
    rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hx)]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Closed
