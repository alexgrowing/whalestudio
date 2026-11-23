import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CoB
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.IsInternalCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FibreClosed

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem gr_nak {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    (h1 : DirectSum.IsInternal 𝒜) (h2 : SetLike.GradedMonoid 𝒜) (m : Ideal B) (hm : m ≤ Ideal.jacobson ⊥)
    (η : Ideal A) (hη : η = Ideal.span {x | x ∈ η ∧ ∃ j, x ∈ 𝒜 j}) (j : ℤ) (hfg : (𝒜 j).FG)
    (h : ∀ y ∈ 𝒜 j, y ∈ η ⊔ m.map (algebraMap B A)) : ∀ y ∈ 𝒜 j, y ∈ η := by
  classical
  letI : DirectSum.Decomposition 𝒜 := h1.chooseDecomposition
  letI : GradedRing 𝒜 := { toGradedMonoid := h2, toDecomposition := ‹_› }
  have hhom : η.IsHomogeneous 𝒜 := by
    rw [hη]
    exact Ideal.homogeneous_span 𝒜 _ (fun x hx => ⟨hx.2.choose, hx.2.choose_spec⟩)
  let p : A →ₗ[B] A := (𝒜 j).subtype ∘ₗ (DirectSum.component B ℤ (fun i => 𝒜 i) j) ∘ₗ
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap
  have hp : ∀ x, p x = (DirectSum.decompose 𝒜 x j : A) := fun x => rfl
  have key : 𝒜 j ≤ (η.restrictScalars B ⊓ 𝒜 j) ⊔ m • 𝒜 j := by
    intro y hy
    obtain ⟨e, he, f, hf, rfl⟩ := Submodule.mem_sup.1 (h y hy)
    have hpy : p (e + f) = e + f := by
      rw [hp]
      exact DirectSum.decompose_of_mem_same 𝒜 hy
    rw [← hpy, map_add]
    refine Submodule.add_mem_sup ⟨?_, ?_⟩ ?_
    · rw [hp]
      exact hhom j he
    · rw [hp]
      exact (DirectSum.decompose 𝒜 e j).2
    · have hf' : f ∈ m • (⊤ : Submodule B A) := by
        rw [Ideal.smul_top_eq_map]
        exact hf
      have hmem := Submodule.mem_map_of_mem (f := p) hf'
      rw [Submodule.map_smul''] at hmem
      refine Submodule.smul_mono le_rfl (fun z hz => ?_) hmem
      obtain ⟨a, -, rfl⟩ := hz
      rw [hp]
      exact (DirectSum.decompose 𝒜 a j).2
  intro y hy
  exact (Submodule.le_of_le_smul_of_le_jacobson_bot hfg hm key hy).1

private theorem w_ge {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) : -2 ≤ w n i - w n j := by
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp [w]

private theorem w_lt {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) (h : j < i) : w n i - w n j ≤ -1 := by
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all [w] <;> omega

private theorem w_nlt {n : ℕ} (hn : n = 2 ∨ n = 3) (i j : Fin n) (h : ¬ j < i) : 0 ≤ w n i - w n j := by
  rcases hn with rfl | rfl <;> fin_cases i <;> fin_cases j <;> simp_all [w] <;> omega

private theorem mon_mem_pow {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    (hn : n = 2 ∨ n = 3) {K : Type} [CommRing K] (ρ : NRep F n K) (L : List (F.G0 × Fin n × Fin n)) :
    ∀ M : ℕ, (L.map fun s => w n s.2.1 - w n s.2.2).sum ≤ -2 * (M : ℤ) →
      (L.map fun s => ρ.r s.1 s.2.1 s.2.2).prod ∈ ρ.triP ^ M := by
  induction L with
  | nil =>
    intro M hM
    have : M = 0 := by
      simp only [List.map_nil, List.sum_nil] at hM
      omega
    subst this
    simp
  | cons s L ih =>
    intro M hM
    simp only [List.map_cons, List.sum_cons, List.prod_cons] at hM ⊢
    by_cases h : s.2.2 < s.2.1
    · rcases M with _ | M
      · simp
      · rw [pow_succ']
        refine Ideal.mul_mem_mul (Ideal.subset_span ⟨s.1, s.2.1, s.2.2, h, rfl⟩) (ih M ?_)
        have := w_ge hn s.2.1 s.2.2
        push_cast at hM
        omega
    · refine Ideal.mul_mem_left _ _ (ih M ?_)
      have := w_nlt hn s.2.1 s.2.2 h
      omega

theorem UpperTheory.V.Fr.l41 :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ η : Ideal S.A, η.IsPrime → S.IsHom η → ¬ S.u.triP ≤ η → ∃ x : PrimeSpectrum S.A, x.asIdeal.IsMaximal ∧ x ∈ S.BB ∧ η ≤ x.asIdeal := by
  intro l _ O _ _ _ _ F C₀ n hF hn S η hp hη hT
  obtain ⟨hco, hm⟩ := UpperTheory.V.Fr.co_B hF hn S
  obtain ⟨h1, h2, -, hfg, -, hnoeth, hr⟩ := UpperTheory.V.Fr.gr_A hF hn S
  have hrad : ¬ S.u.triP ≤ (η ⊔ S.mB.map (algebraMap S.B S.A)).radical := by
    intro hrad
    obtain ⟨M, hM⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
    have hj : S.mB ≤ Ideal.jacobson ⊥ := by
      rw [← hm]
      exact maximalIdeal_le_jacobson _
    apply hT
    refine Ideal.span_le.2 ?_
    rintro _ ⟨g, i, j, hij, rfl⟩
    have hw := w_lt hn i j hij
    have hpow := SetLike.pow_mem_graded (2 * M) (hr g i j)
    refine hp.mem_of_pow_mem (2 * M) (gr_nak S.gr h1 h2 S.mB hj η hη _ (hfg _) (fun y hy => hM ?_) _ hpow)
    have : S.gr ((2 * M) • (w n i - w n j)) ≤ (S.u.triP ^ M).restrictScalars S.B := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨L, hL, rfl⟩
      refine mon_mem_pow hn S.u L M ?_
      rw [hL, nsmul_eq_mul]
      push_cast
      nlinarith [Int.natCast_nonneg M]
    exact this hy
  rw [Ideal.radical_eq_sInf, le_sInf_iff] at hrad
  push Not at hrad
  obtain ⟨p, ⟨hp1, hp2⟩, hp3⟩ := hrad
  obtain ⟨x, ⟨⟨hx1, -⟩, hx2⟩, hx3⟩ := UpperTheory.V.Fr.jac hF hn S (PrimeSpectrum.zeroLocus (η : Set S.A))
    (PrimeSpectrum.isClosed_zeroLocus _) Set.univ isOpen_univ
    ⟨⟨p, hp2⟩, ⟨le_sup_left.trans hp1, trivial⟩, Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hp1), hp3⟩
  exact ⟨x, hx3, hx2, hx1⟩
