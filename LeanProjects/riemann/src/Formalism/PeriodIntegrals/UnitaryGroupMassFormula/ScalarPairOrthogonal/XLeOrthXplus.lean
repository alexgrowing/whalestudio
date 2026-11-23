import Mathlib
import Formalism.PeriodIntegrals.ScalarPairDr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PairCorankPositivity.EqZeroOfMulVec

noncomputable section

open scoped Classical

namespace PI.ScalarPairDr.W

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [StarRing E]

section Orth

variable (S : HSpace E)

theorem hT_swap (x y : S.V) : S.hT y x = star (S.hT x y) := PI.PairCorankPos.W.hT_swap S x y

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]

theorem hT_add_left (x y v : S.V) : S.hT (x + y) v = S.hT x v + S.hT y v := by
  rw [map_add, LinearMap.add_apply]

theorem hT_sub_left (x y v : S.V) : S.hT (x - y) v = S.hT x v - S.hT y v := by
  rw [map_sub, LinearMap.sub_apply]

theorem hT_smul_left (a : E) (x v : S.V) : S.hT (a • x) v = star a * S.hT x v := by
  rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem mem_orth_span {s : Set S.V} {v : S.V} :
    v ∈ orth S (Submodule.span E s) ↔ ∀ x ∈ s, S.hT x v = 0 := by
  rw [mem_orth]
  refine ⟨fun h x hx => h x (Submodule.subset_span hx), fun h x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => rw [map_zero, LinearMap.zero_apply]
  | add x y _ _ hx hy => rw [hT_add_left, hx, hy, add_zero]
  | smul a x _ hx => rw [hT_smul_left, hx, mul_zero]

theorem finrank_orth (U : Submodule E S.V) :
    finrank E U + finrank E (orth S U) = finrank E S.V := by
  let b := Module.finBasis E U
  let u : Fin (finrank E U) → S.V := fun i => (b i : S.V)
  let φ : Fin (finrank E U) → Module.Dual E S.V := fun i => S.hT (u i)
  have hu : LinearIndependent E u := b.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  have hφ : LinearIndependent E φ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h1 : S.hT (∑ i, star (c i) • u i) = 0 := by
      rw [map_sum]
      simp only [LinearMap.map_smulₛₗ, starRingEnd_apply, star_star]
      exact hc
    have h2 : ∑ i, star (c i) • u i = 0 :=
      S.nondeg.1 _ (fun y => by rw [h1, LinearMap.zero_apply])
    have h3 := Fintype.linearIndependent_iff.1 hu _ h2
    intro i
    simpa using congrArg star (h3 i)
  have hW : finrank E (Submodule.span E (Set.range φ)) = finrank E U := by
    rw [finrank_span_eq_card hφ, Fintype.card_fin]
  have hco : (Submodule.span E (Set.range φ)).dualCoannihilator = orth S U := by
    ext v
    rw [Submodule.mem_dualCoannihilator, mem_orth]
    constructor
    · intro h x hx
      have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • u i := by
        have e := congrArg U.subtype (b.sum_repr ⟨x, hx⟩)
        simp only [map_sum, map_smul, Submodule.subtype_apply] at e
        exact e.symm
      have hmem : S.hT x ∈ Submodule.span E (Set.range φ) := by
        rw [hx', map_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [LinearMap.map_smulₛₗ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      exact h _ hmem
    · intro h ψ hψ
      induction hψ using Submodule.span_induction with
      | mem ψ hψ =>
        obtain ⟨i, rfl⟩ := hψ
        exact h _ (b i).2
      | zero => rfl
      | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
      | smul a x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
  have := Subspace.finrank_add_finrank_dualCoannihilator_eq (Submodule.span E (Set.range φ))
  rw [hco, hW] at this
  exact this

theorem le_orth_orth (U : Submodule E S.V) : U ≤ orth S (orth S U) := by
  intro x hx
  rw [mem_orth]
  intro v hv
  rw [hT_swap S x v, (mem_orth S).1 hv x hx, star_zero]

theorem orth_orth (U : Submodule E S.V) : orth S (orth S U) = U := by
  refine (Submodule.eq_of_le_of_finrank_eq (le_orth_orth S U) ?_).symm
  have h1 := finrank_orth S U
  have h2 := finrank_orth S (orth S U)
  omega

end Orth

section Flag

variable {S : HSpace E} {r : ℕ} {T T' : E}

theorem fvec_castSucc (F : FlagG S r T) (a : Fin r) : F.fvec (Fin.castSucc a) = F.e a := by
  simp [FlagG.fvec]

theorem fvec_last (F : FlagG S r T) : F.fvec (Fin.last r) = F.z := by
  simp [FlagG.fvec]

theorem zhat_apply (F : FlagG S r T) (F' : FlagG S r T') (i j : Fin (r + 1)) :
    Zhat F F' i j = S.hT (F.fvec i) (F'.fvec j) := by
  simp only [Zhat, brS]

theorem Xplus_eq (F : FlagG S r T) : F.Xplus = Submodule.span E (Set.range F.e ∪ {F.z}) := by
  rw [FlagG.Xplus, FlagG.X, Submodule.span_union]

theorem mem_orth_Xplus (F : FlagG S r T) {v : S.V} :
    v ∈ orth S F.Xplus ↔ (∀ a, S.hT (F.e a) v = 0) ∧ S.hT F.z v = 0 := by
  rw [Xplus_eq, mem_orth_span]
  constructor
  · intro h
    exact ⟨fun a => h _ (Or.inl ⟨a, rfl⟩), h _ (Or.inr rfl)⟩
  · rintro ⟨h1, h2⟩ x (⟨a, rfl⟩ | hx)
    · exact h1 a
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact h2

theorem X_le_orth_Xplus (F : FlagG S r T) : F.X ≤ orth S F.Xplus := by
  rw [FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  rw [SetLike.mem_coe, mem_orth_Xplus]
  exact ⟨fun a' => F.e_iso a' a, by rw [hT_swap, F.z_orth a, star_zero]⟩

theorem G_eq (F : FlagG S r T) (F' : FlagG S r T') :
    Gflag F F' = (Zhat F F').det * star (Zhat F F').det -
      T * T' * (((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det *
        star ((Zhat F F').submatrix Fin.castSucc Fin.castSucc).det) := by
  simp only [Gflag, PI.PairCorankPos.W.Dl_top, PI.PairCorankPos.W.Dl_r]

theorem exists_b (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (hD : Dl F F' r = 0) :
    ∃ b ∈ F'.X, (∀ a, S.hT (F.e a) b = 0) ∧ S.hT F.z b = T := by
  rw [PI.PairCorankPos.W.Dl_r] at hD
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hD
  let v' : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) v 0
  let w : S.V := ∑ j, v j • F'.e j
  have hrow : ∀ i, (Zhat F F' *ᵥ v') i = S.hT (F.fvec i) w := by
    intro i
    simp only [v', w, Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.snoc_last, mul_zero, add_zero, map_sum, map_smul, smul_eq_mul, zhat_apply, fvec_castSucc]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hsub : ∀ a, (Zhat F F' *ᵥ v') (Fin.castSucc a) =
      ((Zhat F F').submatrix Fin.castSucc Fin.castSucc *ᵥ v) a := by
    intro a
    simp only [v', Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      mul_zero, add_zero, Matrix.submatrix_apply]
  have he : ∀ a, S.hT (F.e a) w = 0 := by
    intro a
    rw [← fvec_castSucc F a, ← hrow, hsub, hv]
    rfl
  have hc : S.hT F.z w ≠ 0 := by
    intro hc
    apply hG
    have hZ : Zhat F F' *ᵥ v' = 0 := by
      funext i
      rw [hrow]
      induction i using Fin.lastCases with
      | last => rw [fvec_last]; exact hc
      | cast a => rw [fvec_castSucc]; exact he a
    have hne : v' ≠ 0 := by
      intro h
      apply hv0
      funext j
      have := congrFun h (Fin.castSucc j)
      simpa [v'] using this
    have hdet := Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hne, hZ⟩
    rw [G_eq, hdet, hD]
    simp
  refine ⟨(T * (S.hT F.z w)⁻¹) • w, ?_, ?_, ?_⟩
  · exact Submodule.smul_mem _ _
      (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  · intro a
    rw [map_smul, he a, smul_zero]
  · rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hc, mul_one]

theorem Dr_zero_of (F : FlagG S r T) (F' : FlagG S r T') {w : S.V} (hw : w ∈ F'.X) (hw0 : w ≠ 0)
    (he : ∀ a, S.hT (F.e a) w = 0) : Dl F F' r = 0 := by
  rw [PI.PairCorankPos.W.Dl_r]
  rw [FlagG.X, Submodule.mem_span_range_iff_exists_fun] at hw
  obtain ⟨v, rfl⟩ := hw
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, ?_, ?_⟩
  · rintro rfl
    apply hw0
    simp
  · funext a
    have := he a
    simp only [map_sum, map_smul, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, zhat_apply, fvec_castSucc,
      Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem eq_zero_of_orth (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) {x : S.V}
    (hx : x ∈ F.X) (ho : ∀ b, S.hT (F'.fvec b) x = 0) : x = 0 := by
  rw [FlagG.X, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  by_contra hne
  have hc0 : (fun a => star (c a)) ≠ 0 := by
    intro h
    apply hne
    have : c = 0 := by
      funext a
      have := congrFun h a
      simpa using this
    subst this
    simp
  have hrow : ∀ b, ∑ a, star (c a) * Zhat F F' (Fin.castSucc a) b = 0 := by
    intro b
    have h := ho b
    rw [hT_swap S (∑ a, c a • F.e a) (F'.fvec b), star_eq_zero] at h
    rw [← h]
    simp only [map_sum, LinearMap.sum_apply, hT_smul_left, zhat_apply, fvec_castSucc]
  apply hG
  let v' : Fin (r + 1) → E := Fin.snoc (α := fun _ => E) (fun a => star (c a)) 0
  have hne' : v' ≠ 0 := by
    intro h
    apply hc0
    funext a
    have := congrFun h (Fin.castSucc a)
    simpa [v'] using this
  have h1 : v' ᵥ* Zhat F F' = 0 := by
    funext b
    simp only [v', Matrix.vecMul, dotProduct, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      zero_mul, add_zero, Pi.zero_apply]
    exact hrow b
  have h2 : (fun a => star (c a)) ᵥ* ((Zhat F F').submatrix Fin.castSucc Fin.castSucc) = 0 := by
    funext b
    simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Pi.zero_apply]
    exact hrow (Fin.castSucc b)
  rw [G_eq, Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hne', h1⟩,
    Matrix.exists_vecMul_eq_zero_iff.1 ⟨_, hc0, h2⟩]
  simp

end Flag

end PI.ScalarPairDr.W
