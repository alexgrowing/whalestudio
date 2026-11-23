import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.GrAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.AlghomOfUnits

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.CA UpperTheory.V.Pa Polynomial
open scoped TensorProduct

theorem UpperTheory.V.Pa.gr_ss :
    ∀ {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [Field F] [Algebra B F] {n : ℕ} {a : ℕ} {T : TrInv B E} {r : E →ₐ[B] Matrix (Fin n) (Fin n) F} {ep : Fin n → E} (g : GrAlg T n a r ep) (κ : Type) [Field κ] [Algebra B κ] (s : B), algebraMap B κ s ≠ 0 → s ∈ Module.annihilator B g.N → IsSemisimpleRing (κ ⊗[B] E) := by
  intro B E F _ _ _ _ _ _ n a T r ep g κ _ _ s hs hann
  classical
  let M : Fin n → Fin n → Matrix (Fin n) (Fin n) g.AA :=
    fun i k => Matrix.single i k (if ((i : ℕ) < a ↔ (k : ℕ) < a) then 1 else 0)
  have hM : ∀ i k, ∃ x : E, g.φ x = M i k := by
    intro i k
    rw [← Set.mem_range, g.range]
    intro p q
    refine ⟨fun _ => ?_, fun hpq => ?_⟩
    · simp only [M, Matrix.single_apply]
      split_ifs
      · exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · exact zero_mem _
      · exact zero_mem _
    · simp only [M, Matrix.single_apply]
      split_ifs with h1 h2
      · obtain ⟨rfl, rfl⟩ := h1
        exact absurd h2 hpq
      · exact zero_mem _
      · exact zero_mem _
  choose e he using hM
  have hmul : ∀ i k l : Fin n, ((i : ℕ) < a ↔ (k : ℕ) < a) → ((k : ℕ) < a ↔ (l : ℕ) < a) →
      e i k * e k l = e i l := by
    intro i k l hik hkl
    apply g.φ_inj
    rw [map_mul, he, he, he]
    simp only [M, if_pos hik, if_pos hkl, if_pos (hik.trans hkl), Matrix.single_mul_single_same,
      mul_one]
  have hzero : ∀ i k l m : Fin n, k ≠ l → e i k * e l m = 0 := by
    intro i k l m hkl
    apply g.φ_inj
    rw [map_mul, he, he, map_zero]
    exact Matrix.single_mul_single_of_ne _ _ _ _ hkl _
  have hcross : ∀ i k : Fin n, ¬((i : ℕ) < a ↔ (k : ℕ) < a) → e i k = 0 := by
    intro i k hik
    apply g.φ_inj
    rw [he, map_zero]
    simp only [M, if_neg hik, Matrix.single_zero]
  have hsum : ∑ i, e i i = 1 := by
    apply g.φ_inj
    rw [map_sum, map_one]
    simp only [he, M, iff_self, if_true]
    ext p q
    rw [Matrix.sum_apply]
    simp only [Matrix.single_apply]
    by_cases hpq : p = q
    · subst hpq
      simp
    · rw [Matrix.one_apply_ne hpq]
      exact Finset.sum_eq_zero (fun x _ => if_neg (fun h => hpq (h.1.symm.trans h.2)))
  have hdec : ∀ y : E, ∃ b : Fin n → Fin n → B, s • y = ∑ i, ∑ k, b i k • e i k := by
    intro y
    have hent : ∀ i k, ∃ c : B, s • g.φ y i k = c • (if ((i : ℕ) < a ↔ (k : ℕ) < a) then 1 else 0) := by
      intro i k
      obtain ⟨h1, h2⟩ := (g.range (g.φ y)).mp ⟨y, rfl⟩ i k
      by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
      · obtain ⟨c, hc⟩ := Submodule.mem_one.mp (h1 hik)
        refine ⟨s * c, ?_⟩
        rw [if_pos hik, ← hc, Algebra.algebraMap_eq_smul_one, smul_smul]
      · refine ⟨0, ?_⟩
        rw [if_neg hik, smul_zero]
        have := (Module.mem_annihilator.mp hann) ⟨_, h2 hik⟩
        simpa using congrArg Subtype.val this
    choose c hc using hent
    refine ⟨c, g.φ_inj ?_⟩
    rw [map_smul, map_sum]
    ext p q
    simp only [map_sum, map_smul, he, M, Matrix.smul_apply, Matrix.sum_apply, Matrix.single_apply]
    rw [hc, Finset.sum_eq_single p (fun i _ hi => Finset.sum_eq_zero (fun k _ => by
        rw [if_neg (fun h => hi h.1), smul_zero])) (by simp),
      Finset.sum_eq_single q (fun k _ hk => by rw [if_neg (fun h => hk h.2), smul_zero]) (by simp)]
    simp
  let bf : Fin n → Bool := fun i => decide ((i : ℕ) < a)
  let cl : Fin n → Set.range bf := Set.rangeFactorization bf
  have hcl : ∀ i k : Fin n, cl i = cl k ↔ ((i : ℕ) < a ↔ (k : ℕ) < a) := by
    intro i k
    simp only [cl, bf, Set.rangeFactorization, Subtype.mk.injEq, decide_eq_decide]
  let d : Set.range bf → Type := fun t => {i : Fin n // cl i = t}
  haveI : ∀ t, Nonempty (d t) := fun t => by
    obtain ⟨i, hi⟩ := Set.rangeFactorization_surjective t
    exact ⟨⟨i, hi⟩⟩
  let ee : (t : Set.range bf) → d t → d t → κ ⊗[B] E := fun t i k => (1 : κ) ⊗ₜ[B] e i.1 k.1
  obtain ⟨j, hj⟩ := alghom_of_units (K := κ) (E := κ ⊗[B] E) d ee
    (fun t i k l => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hmul _ _ _ ((hcl _ _).mp (i.2.trans k.2.symm)) ((hcl _ _).mp (k.2.trans l.2.symm))])
    (fun t i k l m hkl => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hzero _ _ _ _ (fun h => hkl (Subtype.ext h)), TensorProduct.tmul_zero])
    (fun t u i k l m htu => by
      simp only [ee, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [hzero _ _ _ _ (fun h => htu (by rw [← k.2, ← l.2, h])), TensorProduct.tmul_zero])
    (by
      simp only [ee]
      rw [Fintype.sum_fiberwise cl (fun i => (1 : κ) ⊗ₜ[B] e i i), ← TensorProduct.tmul_sum, hsum,
        Algebra.TensorProduct.one_def])
  have hgen : ∀ i k : Fin n, (1 : κ) ⊗ₜ[B] e i k ∈ j.range := by
    intro i k
    by_cases hik : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hk : cl k = cl i := (hcl k i).mpr hik.symm
      exact (AlgHom.mem_range j).mpr
        ⟨Pi.single (cl i) (Matrix.single ⟨i, rfl⟩ ⟨k, hk⟩ 1), hj (cl i) ⟨i, rfl⟩ ⟨k, hk⟩⟩
    · rw [hcross i k hik, TensorProduct.tmul_zero]
      exact Subalgebra.zero_mem _
  have hone : ∀ y : E, (1 : κ) ⊗ₜ[B] y ∈ j.range := by
    intro y
    obtain ⟨b, hb⟩ := hdec y
    have h1 : (1 : κ) ⊗ₜ[B] y = (algebraMap B κ s)⁻¹ • ((1 : κ) ⊗ₜ[B] (s • y)) := by
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one,
        smul_eq_mul, inv_mul_cancel₀ hs]
    rw [h1, hb, TensorProduct.tmul_sum]
    refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ (fun i _ => ?_)) _
    rw [TensorProduct.tmul_sum]
    refine Subalgebra.sum_mem _ (fun k _ => ?_)
    have h2 : (1 : κ) ⊗ₜ[B] (b i k • e i k) = (algebraMap B κ (b i k)) • ((1 : κ) ⊗ₜ[B] e i k) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [h2]
    exact Subalgebra.smul_mem _ (hgen i k) _
  refine RingHom.isSemisimpleRing_of_surjective j.toRingHom ?_
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul u y =>
    obtain ⟨z, hz⟩ := (AlgHom.mem_range j).mp (hone y)
    refine ⟨u • z, ?_⟩
    show j (u • z) = _
    rw [map_smul, hz, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  | add x y hx hy =>
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, hw⟩ := hy
    exact ⟨z + w, by rw [map_add, hz, hw]⟩
