import Mathlib

namespace GlobalTheory

theorem natAbs_det_of_transpose_mul_self (m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ)
    (h : al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ)) :
    al.det.natAbs = m ^ 2 := by
  have h1 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one] at h1
  have h2 := congrArg Int.natAbs h1
  simp only [Int.natAbs_mul, Fintype.card_fin, mul_one, Int.natAbs_pow, Int.natAbs_natCast] at h2
  have h3 : al.det.natAbs ^ 2 = (m ^ 2) ^ 2 := by rw [sq, h2]; ring
  exact Nat.pow_left_injective (by norm_num) h3

theorem card_quotient_range_mulVecLin {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (hA : A.det ≠ 0) :
    Nat.card ((ι → ℤ) ⧸ LinearMap.range (Matrix.toLin' A)) = A.det.natAbs := by
  have hinj : Function.Injective (Matrix.toLin' A) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    exact Matrix.eq_zero_of_mulVec_eq_zero hA (by simpa using hv)
  rw [← Submodule.natAbs_det_equiv _ (LinearEquiv.ofInjective _ hinj)]
  congr 1
  rw [← LinearMap.det_toLin' A]
  congr 1

theorem exists_representatives_mod_similitude_transpose :
    ∀ (g m : ℕ) (al : Matrix (Fin 4) (Fin 4) ℤ), 1 ≤ m → al.transpose * al = (m : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) → ∃ k n : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, ∀ k' n' : (Fin 4 → Fin (m ^ g)) → Fin 4 → Fin g → ℤ, (∀ I I', I ≠ I' → ¬ ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k' I' c + ∑ r, al r c • d r ∧ n' I c = n' I' c + ∑ r, al r c • e r) → ∃ σ : Equiv.Perm (Fin 4 → Fin (m ^ g)), ∀ I, ∃ d e : Fin 4 → Fin g → ℤ, ∀ c, k' I c = k (σ I) c + ∑ r, al r c • d r ∧ n' I c = n (σ I) c + ∑ r, al r c • e r := by
  intro g m al hm h
  classical
  have hdet := natAbs_det_of_transpose_mul_self m al h
  have hne : al.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    intro h0
    rw [h0] at hdet
    have : 0 < m ^ 2 := by positivity
    simp at hdet
    omega
  set L := LinearMap.range (Matrix.toLin' al.transpose) with hL
  have hQ : Nat.card ((Fin 4 → ℤ) ⧸ L) = m ^ 2 := by
    rw [hL, card_quotient_range_mulVecLin _ hne, Matrix.det_transpose, hdet]
  haveI : Finite ((Fin 4 → ℤ) ⧸ L) := Nat.finite_of_card_ne_zero (by rw [hQ]; positivity)
  let cl : (Fin 4 → Fin g → ℤ) → Fin g → ((Fin 4 → ℤ) ⧸ L) :=
    fun x j => Submodule.Quotient.mk (fun c => x c j)
  have hsurj : Function.Surjective cl := by
    intro q
    choose f hf using fun j => Submodule.Quotient.mk_surjective L (q j)
    exact ⟨fun c j => f j c, funext hf⟩
  have hrel : ∀ x y, cl x = cl y → ∃ d : Fin 4 → Fin g → ℤ,
      ∀ c, x c = y c + ∑ r, al r c • d r := by
    intro x y hxy
    have : ∀ j, ∃ v : Fin 4 → ℤ, Matrix.toLin' al.transpose v
        = (fun c => x c j) - (fun c => y c j) := fun j =>
      (Submodule.Quotient.eq L).1 (congrFun hxy j)
    choose v hv using this
    refine ⟨fun r j => v j r, fun c => ?_⟩
    funext j
    have := congrFun (hv j) c
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Pi.sub_apply] at this
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [this]; ring
  have hcard : Nat.card (Fin 4 → Fin (m ^ g)) =
      Nat.card ((Fin g → ((Fin 4 → ℤ) ⧸ L)) × (Fin g → ((Fin 4 → ℤ) ⧸ L))) := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fun, hQ]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    ring
  obtain ⟨β⟩ := Finite.card_eq.1 hcard
  choose s hs using hsurj
  refine ⟨fun I => s (β I).1, fun I => s (β I).2, fun k' n' hkn => ?_⟩
  let f : (Fin 4 → Fin (m ^ g)) → (Fin 4 → Fin (m ^ g)) :=
    fun I => β.symm (cl (k' I), cl (n' I))
  have hf : Function.Injective f := by
    intro I I' hI
    by_contra hne'
    have h1 := β.symm.injective hI
    obtain ⟨d, hd⟩ := hrel _ _ (congrArg Prod.fst h1)
    obtain ⟨e, he⟩ := hrel _ _ (congrArg Prod.snd h1)
    exact hkn I I' hne' ⟨d, e, fun c => ⟨hd c, he c⟩⟩
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf), fun I => ?_⟩
  obtain ⟨d, hd⟩ := hrel (k' I) (s (β (f I)).1) (by rw [hs]; simp [f])
  obtain ⟨e, he⟩ := hrel (n' I) (s (β (f I)).2) (by rw [hs]; simp [f])
  exact ⟨d, e, fun c => ⟨hd c, he c⟩⟩

end GlobalTheory
