import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.ArInt

namespace GlobalTheory.CompanionTheory.MixZ.PolarProof

theorem multilinear_eq_zero {V : Type} [AddCommGroup V] {N : ℕ}
    (M : MultilinearMap ℤ (fun _ : Fin N => V) ℝ)
    (hs : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), M (a ∘ σ) = M a)
    (hd : ∀ x : V, M (fun _ => x) = 0) (a : Fin N → V) : M a = 0 := by
  classical
  have hsurj : ∀ f : Fin N → Fin N, Function.Surjective f → M (a ∘ f) = M a := fun f hf =>
    hs a (Equiv.ofBijective f ⟨Finite.injective_iff_surjective.2 hf, hf⟩)
  have expand : ∀ T : Finset (Fin N), M (fun _ => ∑ i, if i ∈ T then 0 else a i) =
      ∑ f : Fin N → Fin N, if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0 := by
    intro T
    rw [M.map_sum (fun _ i => if i ∈ T then 0 else a i)]
    refine Finset.sum_congr rfl fun f _ => ?_
    split_ifs with h
    · congr 1
      funext j
      have : f j ∉ T := fun hj => Finset.mem_compl.1 (h hj) (Finset.mem_image_of_mem f (Finset.mem_univ j))
      simp [this]
    · obtain ⟨t, ht, hc⟩ := Finset.not_subset.1 h
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 (Finset.notMem_compl.1 hc)
      exact M.map_coord_zero j (if_pos ht)
  have hinner : ∀ f : Fin N → Fin N, ∑ T : Finset (Fin N), (-1 : ℝ) ^ T.card *
      (if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0) =
      if Function.Surjective f then M a else 0 := by
    intro f
    have h1 : ∑ T : Finset (Fin N), (-1 : ℝ) ^ T.card *
        (if T ⊆ (Finset.univ.image f)ᶜ then M (a ∘ f) else 0) =
        (∑ T ∈ ((Finset.univ.image f)ᶜ).powerset, (-1 : ℝ) ^ T.card) * M (a ∘ f) := by
      rw [Finset.sum_mul, ← Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun T : Finset (Fin N) => T ⊆ (Finset.univ.image f)ᶜ)]
      have h2 : Finset.univ.filter (fun T : Finset (Fin N) => T ⊆ (Finset.univ.image f)ᶜ) =
          ((Finset.univ.image f)ᶜ).powerset := by
        ext T; simp
      rw [h2, Finset.sum_eq_zero (s := Finset.univ.filter _) (fun T hT => by
        rw [if_neg (Finset.mem_filter.1 hT).2, mul_zero]), add_zero]
      refine Finset.sum_congr rfl fun T hT => ?_
      rw [if_pos (Finset.mem_powerset.1 hT)]
    have h3 : (∑ T ∈ ((Finset.univ.image f)ᶜ).powerset, (-1 : ℝ) ^ T.card) =
        if (Finset.univ.image f)ᶜ = ∅ then 1 else 0 := by
      have := congrArg (Int.cast : ℤ → ℝ)
        (Finset.sum_powerset_neg_one_pow_card (x := (Finset.univ.image f)ᶜ))
      push_cast at this
      exact this
    have h4 : (Finset.univ.image f)ᶜ = ∅ ↔ Function.Surjective f := by
      rw [Finset.compl_eq_empty_iff, Finset.eq_univ_iff_forall]
      simp [Function.Surjective]
    rw [h1, h3]
    by_cases h : Function.Surjective f
    · rw [if_pos (h4.2 h), if_pos h, one_mul, hsurj f h]
    · rw [if_neg (fun e => h (h4.1 e)), if_neg h, zero_mul]
  have htot : ∑ f : Fin N → Fin N, (if Function.Surjective f then M a else 0) = 0 := by
    simp only [← hinner]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun T _ => ?_
    rw [← Finset.mul_sum, ← expand, hd, mul_zero]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at htot
  rcases mul_eq_zero.1 htot with h | h
  · have hc : (Finset.univ.filter fun f : Fin N → Fin N => Function.Surjective f).card ≠ 0 :=
      Finset.card_ne_zero.2 ⟨id, by simp [Function.surjective_id]⟩
    exact absurd (by exact_mod_cast h) hc
  · exact h

theorem eq_of_diag {V : Type} [AddCommGroup V] {N : ℕ} (S T : (Fin N → V) → ℝ)
    (hS : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), S (a ∘ σ) = S a)
    (hT : ∀ (a : Fin N → V) (σ : Equiv.Perm (Fin N)), T (a ∘ σ) = T a)
    (aS : ∀ (a : Fin N → V) (j : Fin N) (b c : V), S (Function.update a j (b + c)) =
      S (Function.update a j b) + S (Function.update a j c))
    (aT : ∀ (a : Fin N → V) (j : Fin N) (b c : V), T (Function.update a j (b + c)) =
      T (Function.update a j b) + T (Function.update a j c))
    (hd : ∀ x : V, S (fun _ => x) = T (fun _ => x)) (a : Fin N → V) : S a = T a := by
  have aG : ∀ (a : Fin N → V) (j : Fin N) (b c : V),
      (S - T) (Function.update a j (b + c)) =
        (S - T) (Function.update a j b) + (S - T) (Function.update a j c) := by
    intro a j b c
    simp only [Pi.sub_apply, aS, aT]
    ring
  let M : MultilinearMap ℤ (fun _ : Fin N => V) ℝ :=
    { toFun := S - T
      map_update_add' := by
        intro inst m j b c
        rw [Subsingleton.elim inst (fun a b => instDecidableEqFin N a b)]
        exact aG m j b c
      map_update_smul' := by
        intro inst m j c x
        obtain rfl : inst = (fun a b => instDecidableEqFin N a b) := Subsingleton.elim _ _
        exact map_zsmul (AddMonoidHom.mk' (fun y => (S - T) (Function.update m j y)) (aG m j)) c x }
  have h := multilinear_eq_zero M
    (fun a σ => by
      change (S - T) (a ∘ σ) = (S - T) a
      simp only [Pi.sub_apply, hS, hT])
    (fun x => by
      change (S - T) (fun _ => x) = 0
      simp only [Pi.sub_apply, hd, sub_self]) a
  have h' : (S - T) a = 0 := h
  exact sub_eq_zero.1 h'

section Line

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem hermLine_ext {A B : HermLine ι} (h₁ : A.a = B.a) (h₂ : A.h = B.h) : A = B := by
  cases A
  cases B
  simp_all

theorem combLine_add {κ : Type} [Fintype κ] (A : κ → HermLine ι) (a b : κ → ℤ) :
    combLine A (a + b) = (combLine A a).tensor (combLine A b) := by
  refine hermLine_ext ?_ ?_
  · simp only [combLine, HermLine.tensor, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  · funext z
    simp only [combLine, HermLine.tensor]
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · rw [if_pos hz, if_pos hz, if_pos hz, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun o _ => zpow_add₀ ((A o).pos z hz).ne' _ _
    · rw [if_neg hz, if_neg hz, if_neg hz, mul_zero]

theorem combLine_elim_zero {κ : Type} [Fintype κ] (A₀ : HermLine ι) (A : κ → HermLine ι) (n : κ → ℤ) :
    combLine (fun o : Option κ => o.elim A₀ A) (fun o => o.elim 0 n) = combLine A n := by
  refine hermLine_ext ?_ ?_
  · simp [combLine, Fintype.sum_option]
  · funext z
    simp [combLine, Fintype.prod_option]

theorem combLine_elim_one {κ : Type} [Fintype κ] (A₀ : HermLine ι) (A : κ → HermLine ι)
    (c₀ : ∀ z, (¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A₀.h z = 0) :
    combLine (fun o : Option κ => o.elim A₀ A) (fun o => o.elim 1 fun _ => 0) = A₀ := by
  refine hermLine_ext ?_ ?_
  · simp [combLine, Fintype.sum_option]
  · funext z
    by_cases hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0
    · simp only [combLine]
      rw [if_pos hz]
      simp [Fintype.prod_option]
    · simp only [combLine]
      rw [if_neg hz, c₀ z hz]

end Line

section Lin

variable {κ : Type} [Fintype κ]

theorem lin_add (a b : κ → ℤ) : lin (fun o => ((a + b) o : ℝ)) = lin (fun o => (a o : ℝ)) + lin (fun o => (b o : ℝ)) := by
  simp only [lin, Pi.add_apply, Int.cast_add, map_add, add_mul, Finset.sum_add_distrib]

theorem lin_elim_zero (n : κ → ℤ) :
    lin (fun o : Option κ => (((o.elim 0 n : ℤ)) : ℝ)) = rename some (lin fun i => (n i : ℝ)) := by
  simp [lin, Fintype.sum_option, map_sum, rename_X]

theorem lin_elim_one :
    lin (fun o : Option κ => (((o.elim 1 fun _ => 0 : ℤ)) : ℝ)) = MvPolynomial.X none := by
  simp [lin, Fintype.sum_option]

end Lin

theorem polar : Polar := by
  classical
  intro K _ ι _ F D κ _ A₀ A s₀ sA c₀ cA hsym hadd Φ hΦ n
  let A' : Option κ → HermLine ι := fun o => o.elim A₀ A
  have sA' : ∀ o, IsSmoothHerm (A' o) := by
    rintro (_ | j)
    exacts [s₀, sA j]
  have sC : ∀ a, IsSmoothHerm (combLine A' a) := isSmoothHerm_combLine sA'
  let l : (Option κ → ℤ) → MvPolynomial (Option κ) ℝ := fun a => lin fun o => (a o : ℝ)
  let S : (Fin (D + 1) → Option κ → ℤ) → ℝ := fun a => Φ (∏ j, l (a j))
  let T : (Fin (D + 1) → Option κ → ℤ) → ℝ := fun a => F (D + 1) fun j => combLine A' (a j)
  have hST : ∀ a, S a = T a := by
    refine eq_of_diag S T ?_ ?_ ?_ ?_ ?_
    · intro a σ
      change Φ (∏ j, l (a (σ j))) = Φ (∏ j, l (a j))
      rw [Equiv.prod_comp σ fun j => l (a j)]
    · intro a σ
      exact hsym (fun j => combLine A' (a j)) σ fun j => sC _
    · intro a j b c
      change Φ (∏ i, l (Function.update a j (b + c) i)) =
        Φ (∏ i, l (Function.update a j b i)) + Φ (∏ i, l (Function.update a j c i))
      have e : ∀ x : Option κ → ℤ, ∏ i, l (Function.update a j x i) =
          l x * ∏ i ∈ Finset.univ \ {j}, l (a i) := by
        intro x
        have := Finset.prod_update_of_mem (Finset.mem_univ j) (fun i => l (a i)) (l x)
        rw [← this]
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h]
      rw [e, e, e, ← map_add, ← add_mul]
      congr 2
      exact lin_add b c
    · intro a j b c
      have e : ∀ x : Option κ → ℤ, T (Function.update a j x) =
          F (D + 1) (Function.update (fun i => combLine A' (a i)) j (combLine A' x)) := by
        intro x
        change F (D + 1) (fun i => combLine A' (Function.update a j x i)) = _
        congr 1
        funext i
        by_cases h : i = j
        · subst h; simp
        · simp [Function.update_of_ne h]
      rw [e, e, e, combLine_add]
      exact hadd _ j _ _ (fun _ => sC _) (sC _) (sC _)
    · intro x
      change Φ (∏ _j : Fin (D + 1), l x) = F (D + 1) fun _ => combLine A' x
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact hΦ x
  have key := hST (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0)
  have eS : S (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0) =
      Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) := by
    change Φ _ = _
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h₁ := lin_elim_zero n
    have h₂ := lin_elim_one (κ := κ)
    simp only [l]
    rw [h₁, h₂, mul_comm]
  have eT : T (Fin.snoc (fun _ : Fin D => fun o : Option κ => o.elim 0 n) fun o => o.elim 1 fun _ => 0) =
      F (D + 1) (Fin.snoc (fun _ : Fin D => combLine A n) A₀) := by
    change F (D + 1) _ = _
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Fin.snoc_last]
      exact combLine_elim_one A₀ A c₀
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      exact combLine_elim_zero A₀ A n
  rw [← eS, key, eT]

end GlobalTheory.CompanionTheory.MixZ.PolarProof
