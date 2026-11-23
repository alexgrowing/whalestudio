import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TorHensel

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem padic_mem_Kur {l : ℕ} [Fact l.Prime] (a : ℚ_[l]) : algebraMap ℚ_[l] ℂ_[l] a ∈ MaximalUnramifiedExtension l := by
  have hcont : Continuous (algebraMap ℚ_[l] ℂ_[l]) := continuous_algebraMap ℚ_[l] ℂ_[l]
  have hclosed : IsClosed ((MaximalUnramifiedExtension l : Set ℂ_[l])) := Subfield.isClosed_topologicalClosure _
  have hpre : IsClosed ((algebraMap ℚ_[l] ℂ_[l]) ⁻¹' (MaximalUnramifiedExtension l : Set ℂ_[l])) := hclosed.preimage hcont
  have hall : Set.range ((↑) : ℚ → ℚ_[l]) ⊆ (algebraMap ℚ_[l] ℂ_[l]) ⁻¹' (MaximalUnramifiedExtension l : Set ℂ_[l]) := by
    rintro _ ⟨q, rfl⟩
    show algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l]) ∈ MaximalUnramifiedExtension l
    rw [map_ratCast]
    exact SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) q
  have hmem : a ∈ closure (Set.range ((↑) : ℚ → ℚ_[l])) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr⟩ := Padic.rat_dense (p := l) a hε
    exact ⟨r, ⟨r, rfl⟩, by rw [dist_eq_norm]; exact hr⟩
  exact hpre.closure_subset_iff.mpr hall hmem

theorem sqrt_mem_Kur {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : ℕ} (hld : ¬ l ∣ d) {s : ℂ_[l]}
    (hs : s ^ 2 = -(d : ℂ_[l])) : s ∈ MaximalUnramifiedExtension l := by
  have hd : ‖(d : ℂ_[l])‖ = 1 := norm_natCast_Cl_of_not_dvd (l := l) hld
  have hc : -(d : ℂ_[l]) ∈ MaximalUnramifiedExtension l := by
    first
    | exact neg_mem (natCast_mem (MaximalUnramifiedExtension l) d)
    | exact neg_mem (by simpa using SubfieldClass.ratCast_mem (MaximalUnramifiedExtension l) (d : ℚ))
  have h2 : ‖s‖ ^ 2 = 1 := by rw [← norm_pow, hs, norm_neg, hd]
  have hy : ‖s‖ = 1 := by
    have h0 := norm_nonneg s
    nlinarith [h2, h0]
  exact sqrt_mem (l := l) hl (-(d : ℂ_[l])) s hc hy hs

def kurAlg (l : ℕ) [Fact l.Prime] : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  ((MaximalUnramifiedExtension l).comap (algebraMap (PadicAlgCl l) ℂ_[l])).toIntermediateField fun a => by
    show algebraMap (PadicAlgCl l) ℂ_[l] (algebraMap ℚ_[l] (PadicAlgCl l) a) ∈ MaximalUnramifiedExtension l
    rw [← IsScalarTower.algebraMap_apply]
    exact padic_mem_Kur a

theorem mem_kurAlg {l : ℕ} [Fact l.Prime] {y : PadicAlgCl l} :
    y ∈ kurAlg l ↔ algebraMap (PadicAlgCl l) ℂ_[l] y ∈ MaximalUnramifiedExtension l := Iff.rfl

theorem kur_le {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) {d : ℕ} (hld : ¬ l ∣ d) {s : PadicAlgCl l}
    (hs : s ^ 2 = -(d : PadicAlgCl l)) {y : PadicAlgCl l}
    (hy : y ∈ ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (IntermediateField.adjoin ℚ_[l] {s})) :
    algebraMap (PadicAlgCl l) ℂ_[l] y ∈ MaximalUnramifiedExtension l := by
  have hK : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {s}) := by
    first
    | exact IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral s)
    | exact IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic s).isIntegral

  have hq2 : 2 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) := by
    by_contra hlt
    push_neg at hlt
    have h1 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 1 - 1 = 0 := by rw [pow_one]; omega
    have h2 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 - 1 = 0 := by
      have : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 ≤ 1 := by
        calc ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left (by omega) 2
          _ = 1 := one_pow 2
      omega
    have e : ReciprocityTheory.DiscreteGroups.LocalClassField.Kn l (IntermediateField.adjoin ℚ_[l] {s}) 1 = ReciprocityTheory.DiscreteGroups.LocalClassField.Kn l (IntermediateField.adjoin ℚ_[l] {s}) 2 := by simp only [ReciprocityTheory.DiscreteGroups.LocalClassField.Kn, h1, h2]
    have d1 := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_Kn (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK (n := 1) one_pos
    have d2 := ReciprocityTheory.DiscreteGroups.LocalClassField.degLK_Kn (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK (n := 2) two_pos
    rw [e, d2] at d1
    omega

  have hlq : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) := by
    by_contra h
    obtain ⟨n, hn, hdvd⟩ := ReciprocityTheory.DiscreteGroups.LocalClassField.exists_dvd_qK_pow_sub_one (p := l) (K := (IntermediateField.adjoin ℚ_[l] {s})) hK h
    have h1 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n := dvd_pow_self _ hn.ne'
    have hpos : 1 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n := Nat.one_le_pow _ _ (by omega)
    have h3 : ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n - (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ n - 1) := by
      first
      | exact Nat.dvd_sub h1 hdvd
      | exact Nat.dvd_sub (by omega) h1 hdvd
    rw [Nat.sub_sub_self hpos] at h3
    have := Nat.le_of_dvd one_pos h3
    omega
  have hnd : ∀ k, 0 < k → ¬ l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - 1 := by
    intro k hk h
    have h1 : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k := hlq.trans (dvd_pow_self _ hk.ne')
    have hpos : 1 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k := Nat.one_le_pow _ _ (by omega)
    have h3 : l ∣ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ k - 1) := by
      first
      | exact Nat.dvd_sub h1 h
      | exact Nat.dvd_sub (by omega) h1 h
    rw [Nat.sub_sub_self hpos] at h3
    exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h3)

  have hle : ReciprocityTheory.DiscreteGroups.LocalClassField.MaximalUnramifiedExtension l (IntermediateField.adjoin ℚ_[l] {s}) ≤ kurAlg l := by
    refine iSup_le fun n => sup_le ?_ ?_
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, mem_kurAlg]
      refine sqrt_mem_Kur hl hld ?_
      rw [← map_pow, hs, map_neg, map_natCast]
    · rw [IntermediateField.adjoin_le_iff]
      intro ζ hζ
      have hζ0 : ζ ^ (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1) = 1 := hζ
      rw [SetLike.mem_coe, mem_kurAlg]
      have hζ' : (algebraMap (PadicAlgCl l) ℂ_[l] ζ) ^ (ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1) = 1 := by
        rw [← map_pow, hζ0, map_one]
      have hN : 0 < ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) - 1 := by
        have : 2 ≤ ReciprocityTheory.DiscreteGroups.LocalClassField.qK l (IntermediateField.adjoin ℚ_[l] {s}) ^ (n + 1) := le_trans hq2 (Nat.le_self_pow (by omega) _)
        omega
      exact Subfield.le_topologicalClosure _
        (Subfield.subset_closure ⟨_, hN, hnd (n + 1) (Nat.succ_pos n), hζ'⟩)
  exact mem_kurAlg.1 (hle hy)

end ReciprocityTheory.ChartRestriction.L1
