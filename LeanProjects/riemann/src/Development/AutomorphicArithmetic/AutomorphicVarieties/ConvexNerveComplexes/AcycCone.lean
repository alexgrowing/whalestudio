import Development.AutomorphicArithmetic.AutomorphicVarieties.ConvexNerveComplexes.NerveFaceClosed

open Set UpperTheory.V.ConeExtensionAcyclic

private noncomputable def kap {I : Type} (a : I) (n : ℕ) : Ch I n →ₗ[ℤ] Ch I (n + 1) :=
  Finsupp.lmapDomain ℤ ℤ (fun t : Fin n → I => (Fin.cons a t : Fin (n + 1) → I))

private theorem kap_single {I : Type} (a : I) (n : ℕ) (t : Fin n → I) (m : ℤ) :
    kap a n (Finsupp.single t m) = Finsupp.single (Fin.cons a t : Fin (n + 1) → I) m := by
  simp [kap, Finsupp.mapDomain_single]

private theorem bd_single {I : Type} (n : ℕ) (t : Fin (n + 1) → I) :
    bd I n (Finsupp.single t 1) =
      ∑ j : Fin (n + 1), ((-1 : ℤ) ^ (j : ℕ)) • Finsupp.single (t ∘ j.succAbove) (1 : ℤ) := by
  simp only [bd, Finsupp.linearCombination_single, one_smul]

private theorem cons_zero_succAbove {I : Type} (a : I) (n : ℕ) (t : Fin n → I) :
    (Fin.cons a t : Fin (n + 1) → I) ∘ (0 : Fin (n + 1)).succAbove = t := by
  funext i
  simp

private theorem cons_succ_succAbove {I : Type} (a : I) (n : ℕ) (t : Fin (n + 1) → I)
    (j : Fin (n + 1)) :
    (Fin.cons a t : Fin (n + 2) → I) ∘ (j.succ).succAbove =
      (Fin.cons a (t ∘ j.succAbove) : Fin (n + 1) → I) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · simp

private theorem bd_kap_zero {I : Type} (a : I) (c : Ch I 0) : bd I 0 (kap a 0 c) = c := by
  have hlin : (bd I 0).comp (kap a 0) = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro t m
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [kap_single]
    have e1 : Finsupp.single (Fin.cons a t : Fin 1 → I) m = m • Finsupp.single (Fin.cons a t : Fin 1 → I) 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e1, map_smul, bd_single, Fin.sum_univ_one, cons_zero_succAbove]
    simp [Finsupp.smul_single]
  exact LinearMap.congr_fun hlin c

private theorem bd_kap_succ {I : Type} (a : I) (n : ℕ) (c : Ch I (n + 1)) :
    bd I (n + 1) (kap a (n + 1) c) = c - kap a n (bd I n c) := by
  have hlin : (bd I (n + 1)).comp (kap a (n + 1)) = LinearMap.id - (kap a n).comp (bd I n) := by
    apply Finsupp.lhom_ext
    intro t m
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply]
    rw [kap_single]
    have e1 : Finsupp.single (Fin.cons a t : Fin (n + 2) → I) m = m • Finsupp.single (Fin.cons a t : Fin (n + 2) → I) 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have e2 : Finsupp.single t m = m • Finsupp.single t 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e1, e2, map_smul, map_smul, map_smul, bd_single, bd_single, Fin.sum_univ_succ, map_sum]
    simp only [map_smul, kap_single, cons_zero_succAbove, cons_succ_succAbove, Fin.val_zero, pow_zero, one_smul, Fin.val_succ, pow_succ]
    simp only [mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib, smul_add, smul_neg, sub_eq_add_neg]
  exact LinearMap.congr_fun hlin c

private theorem kap_mem {I : Type} (S : ∀ n, Set (Fin n → I)) (a : I) (n : ℕ)
    (h : ∀ t : Fin n → I, t ∈ S n → (Fin.cons a t : Fin (n + 1) → I) ∈ S (n + 1))
    (c : Ch I n) (hc : c ∈ Finsupp.supported ℤ ℤ (S n)) :
    kap a n c ∈ Finsupp.supported ℤ ℤ (S (n + 1)) := by
  classical
  rw [Finsupp.mem_supported] at hc ⊢
  intro u hu
  have hu' := Finsupp.mapDomain_support (Finset.mem_coe.1 hu)
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hu'
  exact h t (hc ht)

theorem UpperTheory.V.ConeExtensionAcyclic.acyc_cone :
    ∀ {I : Type} (S : ∀ n, Set (Fin n → I)) (a : I), (∀ (n : ℕ) (t : Fin n → I), t ∈ S n → (Fin.cons a t : Fin (n + 1) → I) ∈ S (n + 1)) → Acyc S := by
  intro I S a h
  refine ⟨fun c hc => ⟨kap a 0 c, kap_mem S a 0 (h 0) c hc, bd_kap_zero a c⟩,
    fun n c hc h0 => ⟨kap a (n + 1) c, kap_mem S a (n + 1) (h (n + 1)) c hc, ?_⟩⟩
  rw [bd_kap_succ, h0, map_zero, sub_zero]
