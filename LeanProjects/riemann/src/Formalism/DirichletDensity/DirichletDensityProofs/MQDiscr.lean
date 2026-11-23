import Mathlib
import Formalism.DirichletDensity.Statement
import Formalism.CMTypeGalois.HalfTypesFromGeneral

open NumberField IntermediateField NumberField.InfinitePlace Formalism.Q3

noncomputable section

namespace Formalism.HF.P

theorem not_isSquare_prod {k : ℕ} (q : Fin k → ℕ) (hq : ∀ i, (q i).Prime)
    (hinj : Function.Injective q) (S : Finset (Fin k)) (hS : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, (((fun i => -(q i : ℤ)) i : ℤ) : ℚ)) := by
  classical
  have hcast : (∏ i ∈ S, (((fun i => -(q i : ℤ)) i : ℤ) : ℚ)) =
      ((∏ i ∈ S, (-(q i : ℤ)) : ℤ) : ℚ) := by push_cast; rfl
  rw [hcast, Rat.isSquare_intCast_iff]
  rintro ⟨m, hm⟩
  obtain ⟨j, hj⟩ := hS
  have hp : Prime (q j : ℤ) := Nat.prime_iff_prime_int.mp (hq j)
  have hsplit : (∏ i ∈ S, (-(q i : ℤ))) = (-(q j : ℤ)) * ∏ i ∈ S.erase j, (-(q i : ℤ)) :=
    (Finset.mul_prod_erase S _ hj).symm
  have hdn : (q j : ℤ) ∣ ∏ i ∈ S, (-(q i : ℤ)) := by
    rw [hsplit]; exact Dvd.dvd.mul_right (dvd_neg.mpr dvd_rfl) _
  rw [hm] at hdn
  have hdm : (q j : ℤ) ∣ m := by
    rcases hp.dvd_or_dvd hdn with h | h <;> exact h
  have hsq : (q j : ℤ) * q j ∣ ∏ i ∈ S, (-(q i : ℤ)) := by
    rw [hm]; exact mul_dvd_mul hdm hdm
  rw [hsplit] at hsq
  obtain ⟨c, hc⟩ := hsq
  have hne : (q j : ℤ) ≠ 0 := by exact_mod_cast (hq j).ne_zero
  have hP : (q j : ℤ) ∣ ∏ i ∈ S.erase j, (-(q i : ℤ)) := by
    refine ⟨-c, ?_⟩
    have : (q j : ℤ) * (∏ i ∈ S.erase j, (-(q i : ℤ))) = (q j : ℤ) * ((q j : ℤ) * -c) := by
      linear_combination (-1 : ℤ) * hc
    exact mul_left_cancel₀ hne this
  obtain ⟨i, hi, hdi⟩ := (Prime.dvd_finset_prod_iff hp _).mp hP
  have hdi' : q j ∣ q i := by
    have := (dvd_neg.mp hdi)
    exact_mod_cast this
  have heq : q j = q i := (Nat.prime_dvd_prime_iff_eq (hq j) (hq i)).mp hdi'
  exact (Finset.ne_of_mem_erase hi) (hinj heq).symm

theorem adjoin_top_of_lift {E : Type} [Field E] [Algebra ℚ E] (K : IntermediateField ℚ E) (S : Set K)
    (h : adjoin ℚ (Subtype.val '' S) = K) : adjoin ℚ S = ⊤ := by
  have key : @IntermediateField.adjoin ℚ _ K _ K.algebra' S = ⊤ := by
    apply IntermediateField.lift_injective K
    rw [IntermediateField.lift_adjoin, h, IntermediateField.lift_top]
  have gen : ∀ (inst : Algebra ℚ K), inst = K.algebra' →
      @IntermediateField.adjoin ℚ _ K _ inst S = ⊤ := by
    rintro inst rfl
    exact key
  exact gen _ (Subsingleton.elim _ _)

theorem nrRealPlaces_zero {E : Type} [Field E] [NumberField E] (x : E) (c : ℤ) (hc : c < 0)
    (hx : x ^ 2 = (c : E)) : nrRealPlaces E = 0 := by
  haveI : IsEmpty {w : InfinitePlace E // w.IsReal} := ⟨fun ⟨w, hw⟩ => by
    have h1 := congrArg (embedding_of_isReal hw) hx
    rw [map_pow, map_intCast] at h1
    have h2 : (0 : ℝ) ≤ (embedding_of_isReal hw x) ^ 2 := sq_nonneg _
    rw [h1] at h2
    have h3 : (c : ℝ) < 0 := by exact_mod_cast hc
    linarith⟩
  simp [nrRealPlaces]

theorem sqf_neg (p : ℕ) (hp : p.Prime) : Squarefree (-(p : ℤ)) :=
  (Nat.prime_iff_prime_int.mp hp).neg.squarefree

theorem natAbs_discr (hQ : QuadDiscr) : ∀ (m : ℕ) (q : Fin (m + 1) → ℕ),
    (∀ i, (q i).Prime ∧ q i % 4 = 3) → Function.Injective q →
    ∀ (E : Type) [Field E] [NumberField E] (α : Fin (m + 1) → E),
      IsMQ (fun i => -(q i : ℤ)) α → (discr E).natAbs = ∏ i, q i ^ (2 ^ m) := by
  intro m
  induction m with
  | zero =>
    intro q hq hinj E _ _ α hMQ
    have htop : adjoin ℚ {α 0} = ⊤ := by
      have hr : Set.range α = {α 0} := by
        ext x
        exact ⟨fun ⟨i, hi⟩ => by rw [← hi, Fin.fin_one_eq_zero i]; rfl, fun h => ⟨0, h.symm⟩⟩
      rw [← hr]
      exact hMQ.2
    have h := hQ E (-(q 0 : ℤ)) (α 0) (hMQ.1 0) htop (sqf_neg _ (hq 0).1)
      (by have := (hq 0).2; omega)
    rw [h]
    simp
  | succ m ih =>
    intro q hq hinj E _ _ α hMQ
    classical
    set K₁ : IntermediateField ℚ E :=
      adjoin ℚ (Set.range (fun i : Fin (m + 1) => α i.castSucc)) with hK₁
    set K₂ : IntermediateField ℚ E := adjoin ℚ {α (Fin.last (m + 1))} with hK₂
    let β : Fin (m + 1) → K₁ := fun i => ⟨α i.castSucc, subset_adjoin _ _ ⟨i, rfl⟩⟩
    let γ : K₂ := ⟨α (Fin.last _), mem_adjoin_simple_self _ _⟩
    have hβ : IsMQ (fun i => -(q i.castSucc : ℤ)) β := by
      refine ⟨fun i => Subtype.ext (by simpa using hMQ.1 i.castSucc), ?_⟩
      apply adjoin_top_of_lift
      rw [← Set.range_comp]
      rfl
    have hγsq : γ ^ 2 = ((-(q (Fin.last _) : ℤ) : ℤ) : K₂) :=
      Subtype.ext (by simpa using hMQ.1 (Fin.last _))
    have hγtop : adjoin ℚ {γ} = ⊤ := by
      apply adjoin_top_of_lift
      rw [Set.image_singleton]
    have hq' : ∀ i : Fin (m + 1), (q i.castSucc).Prime ∧ q i.castSucc % 4 = 3 := fun i => hq _
    have hinj' : Function.Injective (fun i : Fin (m + 1) => q i.castSucc) :=
      hinj.comp (Fin.castSucc_injective _)
    have hd₁ := ih (fun i => q i.castSucc) hq' hinj' K₁ β hβ
    have hd₂ : discr K₂ = -(q (Fin.last _) : ℤ) :=
      hQ K₂ _ γ hγsq hγtop (sqf_neg _ (hq _).1) (by have := (hq (Fin.last _)).2; omega)
    have hf₁ : Module.finrank ℚ K₁ = 2 ^ (m + 1) :=
      (mqKummer (m + 1) K₁ _ β hβ
        (not_isSquare_prod _ (fun i => (hq' i).1) hinj')).1
    have hγMQ : IsMQ (fun _ : Fin 1 => -(q (Fin.last (m + 1)) : ℤ)) (fun _ => γ) := by
      refine ⟨fun _ => hγsq, ?_⟩
      rw [Set.range_const]
      exact hγtop
    have hf₂ : Module.finrank ℚ K₂ = 2 :=
      (mqKummer 1 K₂ _ (fun _ => γ) hγMQ
        (not_isSquare_prod (fun _ : Fin 1 => q (Fin.last (m + 1))) (fun _ => (hq _).1)
          (fun a b _ => Subsingleton.elim a b))).1
    have : IsGalois ℚ K₁ := (mqGalois _ K₁ _ β hβ
      (fun i => neg_ne_zero.2 (Nat.cast_ne_zero.2 (hq' i).1.ne_zero))).1
    have hcop : IsCoprime (discr K₁) (discr K₂) := by
      rw [hd₂, IsCoprime.neg_right_iff, isCoprime_comm]
      have hp : Prime (q (Fin.last _) : ℤ) := Nat.prime_iff_prime_int.1 (hq _).1
      rw [Prime.coprime_iff_not_dvd hp, Int.natCast_dvd, hd₁]
      intro hdvd
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff (hq (Fin.last _)).1.prime _).1 hdvd
      have h1 := (hq (Fin.last _)).1.dvd_of_dvd_pow hi
      have h2 := (Nat.prime_dvd_prime_iff_eq (hq (Fin.last _)).1 (hq' i).1).1 h1
      exact (Fin.castSucc_lt_last i).ne (hinj h2).symm
    have hld := linearDisjoint_of_isGalois_isCoprime_discr E K₁ K₂ hcop
    have hsup : K₁ ⊔ K₂ = ⊤ := by
      rw [hK₁, hK₂, ← adjoin_union]
      convert hMQ.2 using 2
      ext x
      simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro (⟨i, rfl⟩ | rfl) <;> exact ⟨_, rfl⟩
      · rintro ⟨i, rfl⟩
        induction i using Fin.lastCases with
        | last => exact Or.inr rfl
        | cast j => exact Or.inl ⟨j, rfl⟩
    have hnat := natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow E K₁ K₂ hld hsup
      (isCoprime_differentIdeal_of_isCoprime_discr E hcop)
    rw [hnat, hd₁, hd₂, hf₁, hf₂,
      Fin.prod_univ_castSucc (n := m + 1) (f := fun i => q i ^ 2 ^ (m + 1)), ← Finset.prod_pow]
    simp only [← pow_mul, Int.natAbs_neg, Int.natAbs_natCast]
    congr 1

end Formalism.HF.P

namespace Formalism.HF

theorem mqDiscr_of (hQ : QuadDiscr) : MQDiscr := by
  intro k q hk hq hinj E _ _ α hMQ
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hnat := P.natAbs_discr hQ m q hq hinj E α hMQ
  have hfin : Module.finrank ℚ E = 2 ^ (m + 1) :=
    (mqKummer (m + 1) E _ α hMQ (P.not_isSquare_prod q (fun i => (hq i).1) hinj)).1
  have hr : InfinitePlace.nrRealPlaces E = 0 :=
    P.nrRealPlaces_zero (α 0) (-(q 0 : ℤ)) (by have := (hq 0).1.pos; omega) (hMQ.1 0)
  have hc : InfinitePlace.nrComplexPlaces E = 2 ^ m := by
    have := InfinitePlace.card_add_two_mul_card_eq_rank (K := E)
    rw [hr, hfin, pow_succ] at this
    linarith
  have hs : (discr E).sign = (-1) ^ (2 ^ m) := by rw [sign_discr, hc]
  rw [← Int.sign_mul_natAbs (discr E), hs, hnat]
  simp

theorem hostDiscr_of (h : MQDiscr) : HostDiscr := by
  intro q hq E _ _ α hα
  unfold Formalism.Q3.Hyp3 at hq
  obtain ⟨hq1, hinj⟩ := hq
  rw [h 3 q (by norm_num) hq1 hinj E α hα, Fin.prod_univ_three]
  push_cast
  ring

end Formalism.HF
