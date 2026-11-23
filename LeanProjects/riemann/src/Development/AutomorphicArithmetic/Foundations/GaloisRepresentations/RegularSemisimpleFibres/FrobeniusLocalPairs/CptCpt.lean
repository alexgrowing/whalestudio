import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactGeCompactPartTwistedCentralizer
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.OrbitalIntegrals.QuotFubiniHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsCompactClosureZpowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularTwistedOrbitLocalFiniteness

noncomputable section

open ValuativeRel Matrix

namespace UpperTheory.Gal.InertialTypesAlt.L

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem isOpen_ball (c : (ValueGroupWithZero k)ˣ) :
    IsOpen {y : k | valuation k y ≤ (c : ValueGroupWithZero k)} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rw [IsValuativeTopology.mem_nhds_iff]
  refine ⟨c, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  simp only [Set.mem_setOf_eq] at hz hx ⊢
  exact le_trans (Valuation.map_add _ _ _) (max_le hx (le_of_lt hz))

private theorem isIntegral_of_cpt {n : ℕ} (g : GL (Fin n) k)
    (hg : IsCompact (closure (Subgroup.zpowers g : Set (GL (Fin n) k)))) :
    IsIntegral 𝒪[k] (g : Matrix (Fin n) (Fin n) k) := by
  have hcont : ∀ i j : Fin n, Continuous (fun M : GL (Fin n) k => (M : Matrix (Fin n) (Fin n) k) i j) :=
    fun i j => Units.continuous_val.matrix_elem i j
  set S := ⋃ (i : Fin n) (j : Fin n), (fun M : GL (Fin n) k => (M : Matrix (Fin n) (Fin n) k) i j) ''
    closure (Subgroup.zpowers g : Set (GL (Fin n) k)) with hS
  have hSc : IsCompact S := isCompact_iUnion (fun i => isCompact_iUnion (fun j => hg.image (hcont i j)))
  obtain ⟨c, hc⟩ : ∃ c : (ValueGroupWithZero k)ˣ, S ⊆ {y | valuation k y ≤ (c : ValueGroupWithZero k)} := by
    apply hSc.elim_directed_cover (fun c : (ValueGroupWithZero k)ˣ => {y | valuation k y ≤ (c : ValueGroupWithZero k)})
    · exact fun c => isOpen_ball c
    · intro y _
      rw [Set.mem_iUnion]
      by_cases hy : valuation k y = 0
      · exact ⟨1, by simp [hy]⟩
      · exact ⟨Units.mk0 _ hy, by simp only [Set.mem_setOf_eq, Units.val_mk0, le_refl]⟩
    · intro a b
      rcases le_total (a : ValueGroupWithZero k) b with h | h
      · exact ⟨b, fun y (hy : valuation k y ≤ _) => (le_trans hy h : valuation k y ≤ _), fun y hy => hy⟩
      · exact ⟨a, fun y hy => hy, fun y (hy : valuation k y ≤ _) => (le_trans hy h : valuation k y ≤ _)⟩
  obtain ⟨a, ha⟩ := ValuativeRel.valuation_surjective ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k)
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, map_zero] at ha
    exact (Units.ne_zero _) ha.symm
  apply GlobalTheory.isIntegral_matrix_of_pow_bounded (g : Matrix (Fin n) (Fin n) k) a ha0
  intro m i j
  have hmem : ((g ^ m : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j ∈ S := by
    rw [hS, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    rw [Set.mem_iUnion]
    exact ⟨j, g ^ m, subset_closure (Subgroup.npow_mem_zpowers g m), rfl⟩
  have hle : valuation k (((g : Matrix (Fin n) (Fin n) k) ^ m) i j) ≤ (c : ValueGroupWithZero k) := by
    have h1 := hc hmem
    rw [Units.val_pow_eq_pow_val] at h1
    exact h1
  refine ⟨⟨a * ((g : Matrix (Fin n) (Fin n) k) ^ m) i j, ?_⟩, rfl⟩
  show valuation k (a * ((g : Matrix (Fin n) (Fin n) k) ^ m) i j) ≤ 1
  rw [map_mul, ha]
  calc ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) * valuation k (((g : Matrix (Fin n) (Fin n) k) ^ m) i j)
      ≤ ((c⁻¹ : (ValueGroupWithZero k)ˣ) : ValueGroupWithZero k) * c := by gcongr
    _ = 1 := Units.inv_mul c

private theorem bounded_adjoin {n : ℕ} (N : Matrix (Fin n) (Fin n) k) (hs : N.charpoly.Separable) :
    ∃ c : ValueGroupWithZero k, ∀ g ∈ Algebra.adjoin k {N}, IsIntegral 𝒪[k] g →
      ∀ i j, valuation k (g i j) ≤ c := by
  have hI := Valuation.integer.integers (valuation k)
  exact GlobalTheory.LocBounded.bounded_of_isIntegral_general (valuation k) (fun y => y.2) (fun x hx => ⟨⟨x, hx⟩, rfl⟩)
    (fun x hx => hI.isIntegral_iff_v_le_one.mp hx) N hs

private theorem isCompact_entries (n : ℕ) (c : ValueGroupWithZero k) :
    IsCompact {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} := by
  have h : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
      {x : k | valuation k x ≤ c}) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k c
  have e : {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} =
      (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => {x : k | valuation k x ≤ c}) := by
    ext M
    exact ⟨fun hM i _ j _ => hM i j, fun hM i j => hM i trivial j trivial⟩
  rw [e]
  exact h

end UpperTheory.Gal.InertialTypesAlt.L

private theorem isIntegral_mul_of_mem_adjoin_singleton {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (A x y : Matrix (Fin n) (Fin n) k)
    (hx : x ∈ Algebra.adjoin k {A}) (hy : y ∈ Algebra.adjoin k {A})
    (hxi : IsIntegral 𝒪[k] x) (hyi : IsIntegral 𝒪[k] y) : IsIntegral 𝒪[k] (x * y) := by
  letI : CommRing (Algebra.adjoin k {A}) := Algebra.adjoinCommRingOfComm k (by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb])
  let f : Algebra.adjoin k {A} →ₐ[𝒪[k]] Matrix (Fin n) (Fin n) k :=
    (Algebra.adjoin k {A}).val.restrictScalars 𝒪[k]
  have hinj : Function.Injective f := Subtype.val_injective
  have h1 : IsIntegral 𝒪[k] (⟨x, hx⟩ : Algebra.adjoin k {A}) := (isIntegral_algHom_iff f hinj).mp hxi
  have h2 : IsIntegral 𝒪[k] (⟨y, hy⟩ : Algebra.adjoin k {A}) := (isIntegral_algHom_iff f hinj).mp hyi
  exact (isIntegral_algHom_iff f hinj).mpr (h1.mul h2)

open UpperTheory.Gal.InertialTypesAlt.L in
theorem UpperTheory.Gal.InertialTypesAlt.L.cptCpt :
    UpperTheory.Gal.InertialTypesAlt.L.CptCpt := by
  intro k _ _ _ _ n A T hA hT hcomm
  obtain ⟨-, -, hT2, -, hprop⟩ := UpperTheory.V.Z.Tf.Orb.gLTop_holds k n
  haveI := hT2
  obtain ⟨c, hc⟩ := bounded_adjoin (A : Matrix (Fin n) (Fin n) k) hA
  have hΩ := isCompact_entries (k := k) n c
  have hC := hprop _ _ hΩ hΩ
  let K0 : Subgroup (GL (Fin n) k) :=
    { carrier := {g | (g : Matrix (Fin n) (Fin n) k) ∈ Algebra.adjoin k {(A : Matrix (Fin n) (Fin n) k)} ∧
        IsIntegral 𝒪[k] (g : Matrix (Fin n) (Fin n) k) ∧
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Algebra.adjoin k {(A : Matrix (Fin n) (Fin n) k)} ∧
        IsIntegral 𝒪[k] ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)}
      mul_mem' := by
        rintro g h ⟨hg1, hg2, hg3, hg4⟩ ⟨hh1, hh2, hh3, hh4⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Units.val_mul]
          exact Subalgebra.mul_mem _ hg1 hh1
        · rw [Units.val_mul]
          exact isIntegral_mul_of_mem_adjoin_singleton _ _ _ hg1 hh1 hg2 hh2
        · rw [_root_.mul_inv_rev, Units.val_mul]
          exact Subalgebra.mul_mem _ hh3 hg3
        · rw [_root_.mul_inv_rev, Units.val_mul]
          exact isIntegral_mul_of_mem_adjoin_singleton _ _ _ hh3 hg3 hh4 hg4
      one_mem' := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [Units.val_one]
          exact Subalgebra.one_mem _
        · rw [Units.val_one]
          exact isIntegral_one
        · rw [inv_one, Units.val_one]
          exact Subalgebra.one_mem _
        · rw [inv_one, Units.val_one]
          exact isIntegral_one
      inv_mem' := by
        rintro g ⟨hg1, hg2, hg3, hg4⟩
        refine ⟨hg3, hg4, ?_, ?_⟩
        · rw [inv_inv]
          exact hg1
        · rw [inv_inv]
          exact hg2 }
  have hsub : (K0 : Set (GL (Fin n) k)) ⊆
      {g | (g : Matrix (Fin n) (Fin n) k) ∈ {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c} ∧
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈
          {M : Matrix (Fin n) (Fin n) k | ∀ i j, valuation k (M i j) ≤ c}} := by
    rintro g ⟨hg1, hg2, hg3, hg4⟩
    exact ⟨hc _ hg1 hg2, hc _ hg3 hg4⟩
  have hK1 : IsCompact (K0.topologicalClosure : Set (GL (Fin n) k)) := by
    rw [Subgroup.topologicalClosure_coe]
    exact hC.of_isClosed_subset isClosed_closure (closure_minimal hsub hC.isClosed)
  have hgen : ∀ t ∈ T, IsCompact (closure (Subgroup.zpowers t : Set (GL (Fin n) k))) → t ∈ K0 := by
    intro t ht hcpt
    have hcA : ∀ s ∈ T, (s : Matrix (Fin n) (Fin n) k) * A = A * s := by
      intro s hs
      rw [← Units.val_mul, ← Units.val_mul, (hcomm s hs).eq]
    have hcpt' : IsCompact (closure (Subgroup.zpowers t⁻¹ : Set (GL (Fin n) k))) := by
      rw [Subgroup.zpowers_inv]
      exact hcpt
    exact ⟨GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ _ hA (hcA t ht), isIntegral_of_cpt t hcpt,
      GlobalTheory.Tw.CentralizerAdjoin.mem_adjoin_of_commute _ _ hA (hcA t⁻¹ (T.inv_mem ht)), isIntegral_of_cpt t⁻¹ hcpt'⟩
  have hle : GlobalTheory.BCT.cptPart T ≤ T ⊓ K0.topologicalClosure := by
    unfold GlobalTheory.BCT.cptPart
    rw [Subgroup.closure_le]
    rintro t ⟨ht, hcpt⟩
    exact ⟨ht, Subgroup.le_topologicalClosure K0 (hgen t ht hcpt)⟩
  have hge : T ⊓ K0.topologicalClosure ≤ GlobalTheory.BCT.cptPart T := GlobalTheory.LocFin.inf_le_cptPart T _ hK1
  rw [le_antisymm hle hge, Subgroup.coe_inf]
  exact hK1.inter_left hT
