import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem UpperTheory.V.AlgebraTools.tnAlg_smul_mem {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R) (a : A) {y : M}
    (hy : y ∈ (I • ⊤ : Submodule R M)) : a • y ∈ (I • ⊤ : Submodule R M) := by
  refine Submodule.smul_induction_on hy ?_ ?_
  · intro r hr n _
    rw [← algebraMap_smul A r n, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  · intro u v hu hv
    rw [smul_add]
    exact Submodule.add_mem _ hu hv

private theorem UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem {R A M : Type} [CommRing R] [CommRing A]
    [Algebra R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] (I : Ideal R)
    {a : A} (ha : a ∈ I.map (algebraMap R A)) (y : M) : a • y ∈ (I • ⊤ : Submodule R M) := by
  unfold Ideal.map at ha
  induction ha using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨r, hr, rfl⟩ := hb
    rw [algebraMap_smul]
    exact Submodule.smul_mem_smul hr trivial
  | zero => rw [zero_smul]; exact Submodule.zero_mem _
  | add b c _ _ hb hc => rw [add_smul]; exact Submodule.add_mem _ hb hc
  | smul b c _ hc =>
    rw [smul_eq_mul, mul_smul]
    exact UpperTheory.V.AlgebraTools.tnAlg_smul_mem I b hc

private theorem UpperTheory.V.AlgebraTools.tnAlg_mem_radical {R A : Type} [CommRing R] [IsLocalRing R]
    [CommRing A] [Algebra R A] [Module.Finite R A] {a : A}
    (ha : ∀ n : Ideal A, n.IsMaximal → a ∈ n) :
    a ∈ ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).radical := by
  haveI : Algebra.IsIntegral R A := Algebra.IsIntegral.of_finite R A
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  apply ha
  have hle' : IsLocalRing.maximalIdeal R ≤ Ideal.comap (algebraMap R A) P := by
    intro r hr
    rw [Ideal.mem_comap]
    exact hle (Ideal.mem_map_of_mem _ hr)
  have hne : Ideal.comap (algebraMap R A) P ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
  have hc : Ideal.comap (algebraMap R A) P = IsLocalRing.maximalIdeal R :=
    ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hne hle').symm
  have hcm : (Ideal.comap (algebraMap R A) P).IsMaximal := by
    rw [hc]
    exact IsLocalRing.maximalIdeal.isMaximal R
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P hcm

theorem UpperTheory.V.AlgebraTools.topNil_eq_idem :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (A κ : Type) [CommRing A] [Algebra R A] [Module.Finite R A] (t : κ → A),
      ∃ e : A, IsIdempotentElem e ∧ (∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n)) ∧
        ∀ (M : Type) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Finite R M] (x : M),
          x ∈ topNil (IsLocalRing.maximalIdeal R) (fun i => (Algebra.lsmul R R M (t i) : Module.End R M)) ↔ e • x = x := by
  intro R _ _ _ _ A κ _ _ _ t
  haveI : HenselianLocalRing R := GlobalTheory.henselianLocalRing_of_henselianRing R
  obtain ⟨e, he, hT⟩ := GlobalTheory.exists_idempotent_notMem_iff_mem_of_henselian R (S := A)
    {n : MaximalSpectrum A | ∀ i, t i ∈ n.asIdeal}
  have hmax : ∀ n : Ideal A, n.IsMaximal → (e ∉ n ↔ ∀ i, t i ∈ n) := fun n hn => hT ⟨n, hn⟩
  refine ⟨e, he, hmax, ?_⟩
  intro M _ _ _ _ _ x
  have hpow : ∀ (a : A) (r : ℕ) (y : M),
      ((Algebra.lsmul R R M a : Module.End R M) ^ r) y = a ^ r • y := by
    intro a r y
    rw [← map_pow, Algebra.lsmul_coe]
  rw [mem_topNil_iff_exists]
  simp only [hpow]
  set m := IsLocalRing.maximalIdeal R with hm
  have hA : ∀ j : ℕ, ∀ a : A, ∀ y ∈ (m ^ j • ⊤ : Submodule R M), a • y ∈ (m ^ j • ⊤ : Submodule R M) :=
    fun j a y hy => UpperTheory.V.AlgebraTools.tnAlg_smul_mem (m ^ j) a hy
  constructor
  · intro hx
    set y := x - e • x with hy
    have hey : e • y = 0 := by rw [hy, smul_sub, smul_smul, he.eq, sub_self]
    suffices y = 0 by rw [sub_eq_zero] at this; exact this.symm
    have hall : ∀ j : ℕ, y ∈ (m ^ j • ⊤ : Submodule R M) := by
      intro j
      let P : Submodule A M :=
        { carrier := (m ^ j • ⊤ : Submodule R M)
          add_mem' := fun ha hb => Submodule.add_mem _ ha hb
          zero_mem' := Submodule.zero_mem _
          smul_mem' := fun a _ hb => hA j a _ hb }
      let K : Ideal A := P.comap (LinearMap.toSpanSingleton A M y)
      have hKe : e ∈ K := by
        show e • y ∈ P
        rw [hey]
        exact P.zero_mem
      have hKt : ∀ i, t i ∈ K.radical := by
        intro i
        obtain ⟨r, hr⟩ := hx i j
        refine ⟨r, ?_⟩
        show t i ^ r • y ∈ (m ^ j • ⊤ : Submodule R M)
        rw [hy, smul_sub]
        refine Submodule.sub_mem _ hr ?_
        rw [smul_comm (t i ^ r) e x]
        exact hA j e _ hr
      have htop : K.radical = ⊤ := by
        by_contra hne
        obtain ⟨n, hn, hle⟩ := Ideal.exists_le_maximal _ hne
        exact ((hmax n hn).mpr (fun i => hle (hKt i))) (hle (Ideal.le_radical hKe))
      have h1 : (1 : A) ∈ K.radical := htop ▸ Submodule.mem_top
      obtain ⟨r, hr⟩ := h1
      have h2 : (1 : A) ^ r • y ∈ (m ^ j • ⊤ : Submodule R M) := hr
      rw [one_pow, one_smul] at h2
      exact h2
    have hbot := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) m
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top])
    have hyi : y ∈ (⨅ i, m ^ i • ⊤ : Submodule R M) := Submodule.mem_iInf _ |>.mpr hall
    rw [hbot] at hyi
    exact hyi
  · intro hx i j
    have hin : ∀ n : Ideal A, n.IsMaximal → t i * e ∈ n := by
      intro n hn
      by_cases h : e ∈ n
      · exact n.mul_mem_left _ h
      · exact n.mul_mem_right _ ((hmax n hn).mp h i)
    obtain ⟨N, hN⟩ := UpperTheory.V.AlgebraTools.tnAlg_mem_radical (R := R) hin
    refine ⟨N * j, ?_⟩
    have hex : ∀ k : ℕ, e ^ k • x = x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, mul_smul, hx, ih]
    have hmem : (t i * e) ^ (N * j) ∈ (m ^ j).map (algebraMap R A) := by
      rw [Ideal.map_pow, pow_mul]
      exact Ideal.pow_mem_pow hN j
    have h3 := UpperTheory.V.AlgebraTools.tnAlg_map_smul_mem (m ^ j) hmem x
    rwa [mul_pow, mul_smul, hex] at h3
