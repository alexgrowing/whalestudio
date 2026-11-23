import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsIntEKMulVbar
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RestrictedMultiplicativeH1Subsingleton
import ReciprocityTheory.ClassFieldTheory.LocalClassField.EqZeroOfResEqZeroOfCoprime
import ReciprocityTheory.GroupCohomology.FiniteLevel

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem layer_inflation_h2_injective [(subG p K L).Normal] : Injective ((layerInf p K L).hom.H 2) :=
  multiplicative_inflation_h2_injective p K (subG p K L) (isClosed_subG p K L) _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)

theorem layerInf_layerInfl {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] (n : ℕ) (x : (layer p K L).H n) :
    (layerInf p K L').hom.H n ((layerInfl h).hom.H n x) = (layerInf p K L).hom.H n x := by
  induction x using Cx.H_ind with
  | h x hx => rfl

theorem BrLK_mono {L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] : BrLK p K L ≤ BrLK p K L' := by
  rintro _ ⟨x, rfl⟩
  exact ⟨(layerInfl h).hom.H 2 x, layerInf_layerInfl h 2 x⟩

theorem card_BrLK [(subG p K L).Normal] : Nat.card (BrLK p K L) = Nat.card ((layer p K L).H 2) :=
  (Nat.card_congr (LinearEquiv.ofInjective ((layerInf p K L).hom.H 2) layer_inflation_h2_injective).toEquiv).symm

theorem mem_BrKer_iff (h : K ≤ L) (x : Br p K) :
    x ∈ BrKer h ↔ (resP (kbarT p K) (subG p K L)).hom.H 2 x = 0 := by
  obtain ⟨e, he, hf⟩ := exists_resPair_factor h
  show (resPair h).hom.H 2 x = 0 ↔ _
  rw [hf 2 x]
  exact map_eq_zero_iff _ (he 2).1

theorem BrKer_eq_BrLK (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) [(subG p K L).Normal] :
    BrKer h = BrLK p K L := by
  ext x
  rw [mem_BrKer_iff]
  exact infRes2_exact (kbarT p K) (subG p K L) (isOpen_subG hL) _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)
    (restricted_multiplicative_h1_subsingleton p K _) x

theorem degLK_smul_eq_zero (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K) (hx : x ∈ BrKer h) :
    degLK p K L • x = 0 := by
  have := finiteIndex_subG (K := K) hL
  obtain ⟨cor, -, hcor⟩ := cor_holds ℤ (GK p K) (kbarT p K) (subG p K L) (isOpen_subG hL)
  have h2 := hcor 2 x
  rw [(mem_BrKer_iff h x).1 hx, map_zero] at h2
  exact h2.symm

theorem eq_zero_of_mem_BrKer_of_coprime (hL : FiniteDimensional ℚ_[p] L) (h : K ≤ L) (x : Br p K)
    (hx : x ∈ BrKer h) (k : ℕ) (hk : k • x = 0) (hc : Nat.Coprime k (degLK p K L)) : x = 0 := by
  have h1 := Nat.dvd_gcd (addOrderOf_dvd_of_nsmul_eq_zero hk)
    (addOrderOf_dvd_of_nsmul_eq_zero (degLK_smul_eq_zero hL h x hx))
  rw [Nat.Coprime.gcd_eq_one hc, Nat.dvd_one] at h1
  exact AddMonoid.addOrderOf_eq_one_iff.1 h1

theorem exists_mem_BrKer (hK : FiniteDimensional ℚ_[p] K) (x : Br p K) :
    ∃ (L : IntermediateField ℚ_[p] (PadicAlgCl p)) (h : K ≤ L), FiniteDimensional ℚ_[p] L ∧
      (subG p K L).Normal ∧ x ∈ BrKer h := by
  obtain ⟨N, hN, hNo, hx⟩ := FiniteLevelCohomology.exists_level (kbarT p K) 2 x
  obtain ⟨L, h, hL, rfl⟩ := exists_subG_eq_of_isOpen hK N hNo
  refine ⟨L, h, hL, hN, ?_⟩
  rw [BrKer_eq_BrLK hL h]
  exact hx _ _ (InflationRestrictionInvariants.invariants_isInvRep _ _)

end ReciprocityTheory.DiscreteGroups.LocalClassField
