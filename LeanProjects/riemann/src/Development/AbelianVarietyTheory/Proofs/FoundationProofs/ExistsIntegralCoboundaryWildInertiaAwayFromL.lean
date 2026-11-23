import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoc
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WildEqOneOfCharpolyUnipotentModL
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix

namespace GlobalTheory.WildCob

theorem eq_one_of_pow_near {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (h1 : ∀ i j, ‖(A - 1) i j‖ < 1)
    (h : ∀ ε : ℝ, 0 < ε → ∃ m : ℕ, ‖(m : K)‖ = 1 ∧ ∀ i j, ‖(A ^ m - 1) i j‖ < ε) : A = 1 := by
  obtain ⟨X, rfl⟩ : ∃ X, A = 1 + X := ⟨A - 1, by abel⟩
  simp only [add_sub_cancel_left] at h1
  by_contra hne
  have hX : ∃ i j, X i j ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (by rw [show X = 0 from Matrix.ext hc, add_zero])
  obtain ⟨i₀, j₀, h0⟩ := hX
  obtain ⟨⟨a, b⟩, -, hab⟩ := Finset.exists_max_image (Finset.univ : Finset (n × n)) (fun p => ‖X p.1 p.2‖)
    ⟨(i₀, j₀), Finset.mem_univ _⟩
  set r := ‖X a b‖ with hr
  have hle : ∀ i j, ‖X i j‖ ≤ r := fun i j => hab (i, j) (Finset.mem_univ _)
  have hr0 : 0 < r := (norm_pos_iff.2 h0).trans_le (hle _ _)
  have hr1 : r < 1 := h1 a b
  have hmul : ∀ (Y Z : Matrix n n K) (s t : ℝ), 0 ≤ s → 0 ≤ t → (∀ i j, ‖Y i j‖ ≤ s) → (∀ i j, ‖Z i j‖ ≤ t) →
      ∀ i j, ‖(Y * Z) i j‖ ≤ s * t := by
    intro Y Z s t hs ht hY hZ i j
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hs ht) fun k _ => ?_
    rw [norm_mul]
    exact mul_le_mul (hY _ _) (hZ _ _) (norm_nonneg _) hs
  have hrr : 0 ≤ r * r := mul_nonneg hr0.le hr0.le
  have key : ∀ m : ℕ, ∀ i j, ‖((1 + X) ^ m - 1 - (m : K) • X) i j‖ ≤ r * r := by
    intro m
    induction m with
    | zero => intro i j; simpa using hrr
    | succ m ih =>
      intro i j
      have e : (1 + X) ^ (m + 1) - 1 - ((m + 1 : ℕ) : K) • X =
          ((1 + X) ^ m - 1 - (m : K) • X) + (((1 + X) ^ m - 1 - (m : K) • X) * X + (m : K) • (X * X)) := by
        simp only [pow_succ, mul_add, sub_mul, mul_one, one_mul, Nat.cast_succ, add_smul, one_smul, Matrix.smul_mul]
        abel
      rw [e, Matrix.add_apply, Matrix.add_apply]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (ih i j)
        ((IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)))
      · exact (hmul _ _ _ _ hrr hr0.le ih hle i j).trans (mul_le_of_le_one_right hrr hr1.le)
      · rw [Matrix.smul_apply, smul_eq_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K m)).trans
          (hmul _ _ _ _ hr0.le hr0.le hle hle i j)
  obtain ⟨m, hm, hm'⟩ := h r hr0
  have e : (m : K) * X a b = ((1 + X) ^ m - 1) a b + -(((1 + X) ^ m - 1 - (m : K) • X) a b) := by
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have h2 : ‖(m : K) * X a b‖ < r := by
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hm' a b) ?_)
    rw [norm_neg]
    exact (key m a b).trans_lt (mul_lt_of_lt_one_right hr0 hr1)
  rw [norm_mul, hm, one_mul] at h2
  exact lt_irrefl _ h2

theorem exists_open_subgroup {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (V : Set (G ℚ Ω)) (hV : V ∈ nhds (1 : G ℚ Ω)) :
    ∃ H : Subgroup (G ℚ Ω), IsOpen (H : Set (G ℚ Ω)) ∧ H.index ≠ 0 ∧ (H : Set (G ℚ Ω)) ⊆ V := by
  obtain ⟨L, hL, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).mp hV
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  refine ⟨L.fixingSubgroup, L.fixingSubgroup_isOpen, ?_, hsub⟩
  rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
  exact Module.finrank_pos.ne'

theorem exists_pow_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (B : ValuationSubring Ω) {l : ℕ} (hl : l.Prime)
    (hvl : ¬ B.valuation (l : Ω) < 1) {σ : G ℚ Ω} (hσ : σ ∈ GlobalTheory.WeilDeligne.Wild ℚ B) (V : Set (G ℚ Ω))
    (hV : V ∈ nhds (1 : G ℚ Ω)) : ∃ m : ℕ, ¬ l ∣ m ∧ σ ^ m ∈ V := by
  obtain ⟨H, ho, hidx, hsub⟩ := exists_open_subgroup V hV
  have hvl1 : B.valuation (l : Ω) = 1 :=
    le_antisymm ((B.valuation_le_one_iff _).mpr (natCast_mem B l)) (not_lt.mp hvl)
  obtain ⟨N, hN, -, hmem⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hidx σ
  obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN.ne' l hl.ne_one
  refine ⟨m, hm, hsub (GlobalTheory.WildKill.mem_of_wild B H ho (σ ^ m) (l ^ a) ?_
    ((GlobalTheory.WeilDeligne.Wild ℚ B).pow_mem hσ m) ?_)⟩
  · rw [Nat.cast_pow, map_pow, hvl1, one_pow]; exact lt_irrefl _
  · rw [← pow_mul, mul_comm]; exact hmem

theorem isUnit_natCast {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : ¬ l ∣ m) : IsUnit (m : ℤ_[l]) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm

theorem norm_natCast_eq_one {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : ¬ l ∣ m) : ‖(m : Qbar l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hm

noncomputable def aff {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] (W : R2 Ω l) (z : G ℚ Ω → Fin 2 → Qbar l)
    (s : G ℚ Ω) : Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) :=
  Matrix.fromBlocks (mat W s) (Matrix.of fun i _ => z s i) 0 1

theorem main : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (c : Coef l) (B : ValuationSubring Ω) (q : Pl), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ z ∈ coc W c (Ine (F := ℚ) B), ∃ v : Fin 2 → Qbar l, (∀ i, v i ∈ c.O) ∧ ∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = mat W σ *ᵥ v - v := by
  intro l hl Ω _ _ _ W c B q hW _ hB hq z hz
  obtain ⟨hzc, hzO, hzm⟩ := mem_coc.1 hz
  have hvl : ¬ B.valuation (l : Ω) < 1 := by
    intro h
    apply hq
    rw [← hB]
    simpa using h
  set P := GlobalTheory.WeilDeligne.Wild ℚ B with hP
  have hPI : P ≤ Ine (F := ℚ) B := GlobalTheory.WeilDeligne.Wild_le_Ine
  have hz1 : z 1 = 0 := by
    have := hzm 1 (one_mem _) 1 (one_mem _)
    rw [mul_one, mat, map_one, Units.val_one, Matrix.one_mulVec] at this
    exact left_eq_add.1 this
  have ha1 : aff W z 1 = 1 := by
    rw [aff, ← Matrix.fromBlocks_one]
    congr 1
    · simp
    · ext i j; simp [hz1]
  let M : P →* Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) :=
    { toFun := fun s => aff W z s
      map_one' := ha1
      map_mul' := fun s t => by
        simp only [aff, Matrix.fromBlocks_multiply, Subgroup.coe_mul]
        congr 1
        · simp [mat]
        · ext i j
          rw [hzm s (hPI s.2) t (hPI t.2), Matrix.mul_one]
          exact add_comm _ _
        · simp
        · simp }
  have hM : ∀ s : P, M s = aff W z s := fun _ => rfl
  have hcont : ∀ i j, Continuous fun s => aff W z s i j := by
    have hWc : Continuous fun s => mat W s := Units.continuous_val.comp hW
    rintro (i | i) (j | j)
    · exact hWc.matrix_elem i j
    · exact hzc i
    · exact continuous_const
    · exact continuous_const
  have hV : ∀ ε : ℝ, 0 < ε → {s : G ℚ Ω | ∀ i j, ‖(aff W z s - 1) i j‖ < ε} ∈ nhds (1 : G ℚ Ω) := by
    intro ε hε
    refine IsOpen.mem_nhds ?_ (by simp [ha1, hε])
    simp only [Set.setOf_forall]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact isOpen_lt ((hcont i j).sub continuous_const).norm continuous_const
  have hker : ∀ s : P, (∀ i j, ‖(aff W z s - 1) i j‖ < 1) → s ∈ M.ker := by
    intro s hs
    refine eq_one_of_pow_near (M s) hs fun ε hε => ?_
    obtain ⟨m, hm, hm'⟩ := exists_pow_mem B hl.out hvl s.2 _ (hV ε hε)
    exact ⟨m, norm_natCast_eq_one hm, by rw [← map_pow]; exact hm'⟩
  have hfi : M.ker.FiniteIndex := by
    obtain ⟨H, -, hidx, hsub⟩ := exists_open_subgroup _ (hV 1 one_pos)
    have : H.FiniteIndex := ⟨hidx⟩
    exact Subgroup.finiteIndex_of_le (H := H.subgroupOf P) fun s hs => hker s (hsub hs)
  classical
  let Q := P ⧸ M.ker
  letI : Fintype Q := Fintype.ofFinite _
  have hcard : ¬ l ∣ Fintype.card Q := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card l hd
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨m, hm, hm'⟩ := exists_pow_mem B hl.out hvl s.2 _ (hV 1 one_pos)
    apply hm
    rw [← hx, orderOf_dvd_iff_pow_eq_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hker _ hm'
  let Mq : Q →* Matrix (Fin 2 ⊕ Unit) (Fin 2 ⊕ Unit) (Qbar l) := QuotientGroup.lift M.ker M fun _ h => h
  have hMq : ∀ x : Q, Mq x = aff W z (x.out : P) := fun x => by
    conv_lhs => rw [← QuotientGroup.out_eq' x]
    rfl
  have hS : ∀ s : P, aff W z s * ∑ x : Q, Mq x = ∑ x : Q, Mq x := fun s => by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (s : Q)) _ _ fun x => by
      rw [Equiv.coe_mulLeft, map_mul]; rfl
  obtain ⟨u, hu⟩ := isUnit_natCast hcard
  have hinv : (Fintype.card Q : Qbar l) * algebraMap ℤ_[l] (Qbar l) (↑u⁻¹) = 1 := by
    rw [← map_natCast (algebraMap ℤ_[l] (Qbar l)), ← hu, ← map_mul, Units.mul_inv, map_one]
  refine ⟨fun i => -(algebraMap ℤ_[l] (Qbar l) (↑u⁻¹) * ∑ x : Q, z (x.out : P) i), fun i =>
    c.O.neg_mem (c.O.mul_mem (c.O.algebraMap_mem _) (c.O.sum_mem fun x _ => hzO _ _)), fun σ hσ => ?_⟩
  funext i
  have h1 := congrFun (congrFun (hS ⟨σ, hσ⟩) (Sum.inl i)) (Sum.inr ())
  simp only [hMq, Matrix.mul_apply, Matrix.sum_apply, aff, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, Matrix.one_apply_eq, Fin.sum_univ_two,
    Finset.univ_unique, Finset.sum_singleton, Finset.sum_const, Finset.card_univ, Finset.card_singleton, one_smul, nsmul_eq_mul, Nat.cast_one,
    one_mul, mul_one] at h1
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  linear_combination (algebraMap ℤ_[l] (Qbar l) (↑u⁻¹)) * h1 - z σ i * hinv

end GlobalTheory.WildCob
