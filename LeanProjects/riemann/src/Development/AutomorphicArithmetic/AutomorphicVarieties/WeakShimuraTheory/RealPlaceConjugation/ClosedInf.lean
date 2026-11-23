import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import GroundTheory.GlobalFields.CyclotomicCharacters.PadicUnitsLog

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

private theorem addClosed_index (l : ℕ) [Fact l.Prime] (A : AddSubgroup ℤ_[l])
    (hA : IsClosed (A : Set ℤ_[l])) (a : ℤ_[l]) (ha : a ∈ A) (h0 : a ≠ 0) : A.index ≠ 0 := by
  have key : ∀ x : ℤ_[l], a * x ∈ A := by
    intro x
    refine PadicInt.denseRange_intCast.induction_on x ?_ ?_
    · exact hA.preimage (continuous_const.mul continuous_id)
    · intro m
      have hm : a * (m : ℤ_[l]) = m • a := by rw [zsmul_eq_mul, mul_comm]
      rw [hm]
      exact A.zsmul_mem ha m
  have hspec := PadicInt.unitCoeff_spec h0
  set w := PadicInt.unitCoeff h0
  set n := a.valuation
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  let f := (PadicInt.toZModPow (p := l) n).toAddMonoidHom
  have hle : f.ker ≤ A := by
    intro x hx
    have hx' : x ∈ RingHom.ker (PadicInt.toZModPow (p := l) n) := hx
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hx'
    obtain ⟨y, rfl⟩ := hx'
    have hw : (w : ℤ_[l]) * ↑w⁻¹ = 1 := Units.mul_inv w
    have heq : (l : ℤ_[l]) ^ n * y = a * (↑w⁻¹ * y) := by
      conv_rhs => rw [hspec]
      linear_combination (-((l : ℤ_[l]) ^ n * y)) * hw
    rw [heq]
    exact key _
  have hfin : f.ker.index ≠ 0 := by
    rw [AddSubgroup.index_ker]
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  intro hA0
  apply hfin
  exact Nat.eq_zero_of_zero_dvd (hA0 ▸ AddSubgroup.index_dvd_of_le hle)

open GroundTheory.Global.Cyclotomic in
theorem UpperTheory.V.Ws.index_ne_zero_of_isClosed_of_not_isOfFinOrder :
    ∀ (l : ℕ) [Fact l.Prime] (H : Subgroup ℤ_[l]ˣ), IsClosed (H : Set ℤ_[l]ˣ) → (∃ u ∈ H, ¬ IsOfFinOrder u) → H.index ≠ 0 := by
  intro l _ H hH hu
  obtain ⟨u, huH, hu⟩ := hu
  set L := padicUnitsLog l with hL
  have hB : IsClosed ((H.map L : Subgroup (Multiplicative ℤ_[l])) : Set (Multiplicative ℤ_[l])) := by
    rw [Subgroup.coe_map]
    exact ((hH.isCompact).image (continuous_padicUnitsLog l)).isClosed
  let A : AddSubgroup ℤ_[l] := Subgroup.toAddSubgroup' (H.map L)
  have hAc : IsClosed (A : Set ℤ_[l]) := hB
  have haA : Multiplicative.toAdd (L u) ∈ A := by
    rw [Subgroup.mem_toAddSubgroup']
    exact ⟨u, huH, rfl⟩
  have ha0 : Multiplicative.toAdd (L u) ≠ 0 := by
    intro h
    apply hu
    have h1 : L u = 1 := by
      rw [← ofAdd_toAdd (L u), h]
      rfl
    rw [hL, padicUnitsLog_eq_one_iff] at h1
    exact isOfFinOrder_iff_pow_eq_one.2 ⟨_, torsionExponent_pos l, h1⟩
  have hAi : A.index ≠ 0 := addClosed_index l A hAc _ haA ha0
  have hMi : (H.map L).index ≠ 0 := hAi
  have hK : (H ⊔ L.ker).index ≠ 0 := by
    rw [← Subgroup.comap_map_eq, Subgroup.index_comap_of_surjective _ (padicUnitsLog_surjective l)]
    exact hMi
  have hker : L.ker ≤ rootsOfUnity (torsionExponent l) ℤ_[l] := by
    intro x hx
    rw [mem_rootsOfUnity]
    rw [MonoidHom.mem_ker, hL, padicUnitsLog_eq_one_iff] at hx
    exact hx
  have hcard : Nat.card L.ker ≠ 0 := by
    haveI : NeZero (torsionExponent l) := ⟨(torsionExponent_pos l).ne'⟩
    haveI : Finite L.ker := Finite.of_injective (Subgroup.inclusion hker) (Subgroup.inclusion_injective hker)
    exact Nat.card_ne_zero.2 ⟨inferInstance, inferInstance⟩
  have hrel : H.relIndex (H ⊔ L.ker) ≠ 0 := by
    rw [sup_comm, Subgroup.relIndex_sup_right]
    intro h0
    apply hcard
    exact Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_card H L.ker)
  rw [← Subgroup.relIndex_mul_index (le_sup_left : H ≤ H ⊔ L.ker)]
  exact mul_ne_zero hrel hK
