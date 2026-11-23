import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBumpB
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeBumpB
open scoped GlobalTheory.VacAny

theorem UpperTheory.exists_schwartz_character_average :
    ∀ (Y N : Type) [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [AddCommGroup N] [Module ℂ N]
        (S : Submodule ℂ N) (L L' : AddSubgroup Y), IsCompact (L : Set Y) → IsOpen (L' : Set Y) →
        ∀ (p : Y → N) (φ₀ : N), (∀ y, p y ∈ S) → (∀ y ∈ L', p y = φ₀) →
        ∀ ξ : Y → ℂ, (∀ x y, ξ (x + y) = ξ x * ξ y) → (∀ y ∈ L', ξ y = 1) →
        ∃ φ ∈ S, ∀ (J : N → ℂ) (η : Y → ℂ), (∀ x ∈ S, ∀ y ∈ S, J (x + y) = J x + J y) → (∀ (c : ℂ), ∀ x ∈ S, J (c • x) = c * J x) →
          (∀ x y, η (x + y) = η x * η y) → (∀ y, J (p y) = η y * J φ₀) →
          ((∀ y ∈ L, ξ y * η y = 1) → J φ = J φ₀) ∧ (¬ (∀ y ∈ L, ξ y * η y = 1) → J φ = 0) := by
  intro Y N _ _ _ _ _ S L L' hL hL' p φ₀ hp hp' ξ hξ hξ'
  classical
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hU : IsOpen ((L'.addSubgroupOf L : AddSubgroup L) : Set L) :=
    hL'.preimage continuous_subtype_val
  haveI : Finite (L ⧸ L'.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ hU
  letI : Fintype (L ⧸ L'.addSubgroupOf L) := Fintype.ofFinite _
  have hmem : ∀ s : Finset (L ⧸ L'.addSubgroupOf L),
      ∑ q ∈ s, ξ ((q.out : L) : Y) • p ((q.out : L) : Y) ∈ S :=
    fun s => S.sum_mem fun q _ => S.smul_mem _ (hp _)
  have hc : (Fintype.card (L ⧸ L'.addSubgroupOf L) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  refine ⟨(Fintype.card (L ⧸ L'.addSubgroupOf L) : ℂ)⁻¹ •
    ∑ q : L ⧸ L'.addSubgroupOf L, ξ ((q.out : L) : Y) • p ((q.out : L) : Y),
    S.smul_mem _ (hmem _), ?_⟩
  intro J η hadd hsmul hη hJ
  have hJ0 : J 0 = 0 := by
    have := hsmul 0 0 S.zero_mem
    simpa using this
  have hsum : ∀ s : Finset (L ⧸ L'.addSubgroupOf L),
      J (∑ q ∈ s, ξ ((q.out : L) : Y) • p ((q.out : L) : Y)) =
        ∑ q ∈ s, ξ ((q.out : L) : Y) * η ((q.out : L) : Y) * J φ₀ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hJ0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd _ (S.smul_mem _ (hp _)) _ (hmem s), ih,
        hsmul _ _ (hp _), hJ, mul_assoc]
  rw [hsmul _ _ (hmem _), hsum]
  constructor
  · intro h
    rw [Finset.sum_congr rfl (fun q _ => by rw [h _ (q.out : L).2, one_mul]), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  · intro h
    push Not at h
    obtain ⟨y₀, hy₀, hne⟩ := h
    have hinv : ∀ y : Y, ∀ l ∈ L', ξ (y + l) * η (y + l) * J φ₀ = ξ y * η y * J φ₀ := by
      intro y l hl
      have h1 : η l * J φ₀ = J φ₀ := by rw [← hJ, hp' l hl]
      rw [hξ, hη, hξ' l hl, mul_one]
      calc ξ y * (η y * η l) * J φ₀ = ξ y * η y * (η l * J φ₀) := by ring
        _ = _ := by rw [h1]
    have hshift : ∀ q : L ⧸ L'.addSubgroupOf L,
        ξ ((((QuotientAddGroup.mk (⟨y₀, hy₀⟩ : L) : L ⧸ L'.addSubgroupOf L) + q).out : L) : Y) *
          η ((((QuotientAddGroup.mk (⟨y₀, hy₀⟩ : L) : L ⧸ L'.addSubgroupOf L) + q).out : L) : Y) * J φ₀ =
        (ξ y₀ * η y₀) * (ξ ((q.out : L) : Y) * η ((q.out : L) : Y) * J φ₀) := by
      intro q
      have e : (QuotientAddGroup.mk (⟨y₀, hy₀⟩ : L) : L ⧸ L'.addSubgroupOf L) + q =
          QuotientAddGroup.mk ((⟨y₀, hy₀⟩ : L) + q.out) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_mul (L'.addSubgroupOf L) ((⟨y₀, hy₀⟩ : L) + q.out)
      rw [e, hl, AddSubgroup.coe_add, hinv _ _ (AddSubgroup.mem_addSubgroupOf.mp l.2),
        AddSubgroup.coe_add, hξ, hη]
      ring
    have hre := Equiv.sum_comp
      (Equiv.addLeft (QuotientAddGroup.mk (⟨y₀, hy₀⟩ : L) : L ⧸ L'.addSubgroupOf L))
      (fun q : L ⧸ L'.addSubgroupOf L => ξ ((q.out : L) : Y) * η ((q.out : L) : Y) * J φ₀)
    simp only [Equiv.coe_addLeft, hshift, ← Finset.mul_sum] at hre
    have hz : ∑ q : L ⧸ L'.addSubgroupOf L, ξ ((q.out : L) : Y) * η ((q.out : L) : Y) * J φ₀ = 0 := by
      by_contra hz
      exact hne (mul_right_cancel₀ hz (by rw [hre, one_mul]))
    rw [hz, mul_zero]
