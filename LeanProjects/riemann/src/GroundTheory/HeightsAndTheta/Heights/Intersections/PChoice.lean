import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsArith
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace Choice

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]

theorem homog_mul {f g : MRingOver R ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem homog_one : IsMultiHomog (1 : MRingOver R ι) 0 := by
  classical
  intro m hm k
  have hm' : m = 0 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (by simp [MvPolynomial.coeff_one, Ne.symm h])
  subst hm'
  simp

open Classical in

theorem homog_X (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRingOver R ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  have hm' : m = Finsupp.single ⟨k, i⟩ 1 := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hm) (by rw [MvPolynomial.coeff_X]; simp [Ne.symm h])
  subst hm'
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem homog_pow {f : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (homog_one (R := R) (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih hf

theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRingOver R ι) a := by
  intro m hm
  simp at hm

theorem homog_add {f g : MRingOver R ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g a) : IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem homog_sum {β : Type*} (s : Finset β) (f : β → MRingOver R ι) {a : K → ℕ}
    (h : ∀ b ∈ s, IsMultiHomog (f b) a) : IsMultiHomog (∑ b ∈ s, f b) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_zero (R := R) (ι := ι) a
  | insert b s hb ih =>
    rw [Finset.sum_insert hb]
    exact homog_add (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem homog_prod {β : Type*} (s : Finset β) (f : β → MRingOver R ι) (a : β → K → ℕ)
    (h : ∀ b ∈ s, IsMultiHomog (f b) (a b)) : IsMultiHomog (∏ b ∈ s, f b) (∑ b ∈ s, a b) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using homog_one (R := R) (ι := ι)
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, Finset.sum_insert hb]
    exact homog_mul (h b (Finset.mem_insert_self b s))
      (ih fun b' hb' => h b' (Finset.mem_insert_of_mem hb'))

theorem homog_coordProd (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (homog_one (R := R) (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact homog_mul (homog_pow (homog_X k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem coordProd_not_mem {V : Ideal (MRingOver R ι)} (hV : V.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRingOver R ι) ∉ V) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRingOver R ι) ^ d k) ∉ V := by
  intro h
  obtain ⟨k, -, hk⟩ := (hV.prod_mem_iff).mp h
  exact hc k (hV.mem_of_pow_mem _ hk)

theorem exists_form_avoid (S : Set (Ideal (MRingOver R ι))) (hS : S.Finite)
    (hS' : ∀ W ∈ S, IsMultiProjPrime W) :
    ∃ d₀ : K → ℕ, ∀ d : K → ℕ, d₀ ≤ d →
      ∃ f : MRingOver R ι, IsMultiHomog f d ∧ ∀ W ∈ S, f ∉ W := by
  classical
  set T : Finset (Ideal (MRingOver R ι)) :=
    hS.toFinset.filter (fun W => ∀ W' ∈ S, W ≤ W' → W' = W) with hT
  have hTS : ∀ W ∈ T, W ∈ S := fun W hW => hS.mem_toFinset.mp (Finset.mem_filter.mp hW).1
  have hTmax : ∀ W ∈ T, ∀ W' ∈ S, W ≤ W' → W' = W := fun W hW => (Finset.mem_filter.mp hW).2
  have hle : ∀ W ∈ S, ∃ W' ∈ T, W ≤ W' := by
    intro W hW
    obtain ⟨W', hWW', hW'⟩ := hS.exists_le_maximal hW
    exact ⟨W', Finset.mem_filter.mpr ⟨hS.mem_toFinset.mpr hW'.prop,
      fun W'' hW'' h => le_antisymm (hW'.2 hW'' h) h⟩, hWW'⟩
  have hgen : ∀ W ∈ T, ∀ W' ∈ T, W' ≠ W →
      ∃ g : MRingOver R ι, ∃ a : K → ℕ, IsMultiHomog g a ∧ g ∈ W' ∧ g ∉ W := by
    intro W hW W' hW' hne
    obtain ⟨S', hS'h, hS'eq⟩ := (hS' W' (hTS W' hW')).2.1
    by_contra hc
    simp only [not_exists, not_and, not_not] at hc
    apply hne
    refine (hTmax W' hW' W (hTS W hW) ?_).symm
    rw [hS'eq, Ideal.span_le]
    intro g hg
    obtain ⟨a, ha⟩ := hS'h g hg
    exact hc g a ha (hS'eq ▸ Ideal.subset_span hg)
  choose! gen degG hgenH hgenMem hgenNot using hgen
  set a : Ideal (MRingOver R ι) → MRingOver R ι := fun W => ∏ W' ∈ T.erase W, gen W W' with ha
  set δ : Ideal (MRingOver R ι) → K → ℕ := fun W => ∑ W' ∈ T.erase W, degG W W' with hδ
  have haH : ∀ W ∈ T, IsMultiHomog (a W) (δ W) := fun W hW =>
    homog_prod _ _ _ fun W' hW' =>
      hgenH W hW W' (Finset.mem_of_mem_erase hW') (Finset.ne_of_mem_erase hW')
  have haNot : ∀ W ∈ T, a W ∉ W := by
    intro W hW h
    obtain ⟨W', hW', hg⟩ := ((hS' W (hTS W hW)).1.prod_mem_iff).mp h
    exact hgenNot W hW W' (Finset.mem_of_mem_erase hW') (Finset.ne_of_mem_erase hW') hg
  have haMem : ∀ W ∈ T, ∀ W'' ∈ T, W'' ≠ W → a W ∈ W'' := by
    intro W hW W'' hW'' hne
    have hmem : W'' ∈ T.erase W := Finset.mem_erase.mpr ⟨hne, hW''⟩
    show (∏ W' ∈ T.erase W, gen W W') ∈ W''
    rw [← Finset.mul_prod_erase _ _ hmem]
    exact Ideal.mul_mem_right _ _ (hgenMem W hW W'' hW'' hne)
  refine ⟨∑ W ∈ T, δ W, fun d hd => ?_⟩
  have hδd : ∀ W ∈ T, δ W ≤ d := fun W hW =>
    le_trans (Finset.single_le_sum (f := δ) (fun _ _ _ => Nat.zero_le _) hW) hd
  have hrel : ∀ W ∈ T, IsRelevant W := fun W hW => (hS' W (hTS W hW)).2.2
  set m : Ideal (MRingOver R ι) → MRingOver R ι := fun W =>
    if h : IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRingOver R ι) ^ (d k - δ W k) else 0
    with hm
  have hmH : ∀ W ∈ T, IsMultiHomog (m W) (d - δ W) := by
    intro W hW
    simp only [hm, dif_pos (hrel W hW)]
    exact homog_coordProd _ _
  have hmNot : ∀ W ∈ T, m W ∉ W := by
    intro W hW
    simp only [hm, dif_pos (hrel W hW)]
    exact coordProd_not_mem (hS' W (hTS W hW)).1 _ (fun k => ((hrel W hW) k).choose_spec) _
  refine ⟨∑ W ∈ T, a W * m W, ?_, ?_⟩
  · apply homog_sum
    intro W hW
    have := homog_mul (haH W hW) (hmH W hW)
    rwa [add_tsub_cancel_of_le (hδd W hW)] at this
  · have key : ∀ W₀ ∈ T, (∑ W ∈ T, a W * m W) ∉ W₀ := by
      intro W₀ hW₀ h
      rw [← Finset.add_sum_erase _ _ hW₀] at h
      have hrest : (∑ W ∈ T.erase W₀, a W * m W) ∈ W₀ :=
        Ideal.sum_mem _ fun W hW => Ideal.mul_mem_right _ _
          (haMem W (Finset.mem_of_mem_erase hW) W₀ hW₀ (Finset.ne_of_mem_erase hW).symm)
      have h1 := (Ideal.add_mem_iff_left _ hrest).mp h
      rcases (hS' W₀ (hTS W₀ hW₀)).1.mem_or_mem h1 with h2 | h2
      · exact haNot W₀ hW₀ h2
      · exact hmNot W₀ hW₀ h2
    intro W hW h
    obtain ⟨W', hW', hle'⟩ := hle W hW
    exact key W' hW' (hle' h)

end Choice

theorem Choice.proof : Choice.Statement := by
  intro K _ ι _ P d a m Y x _ hY
  obtain ⟨d₀, hd₀⟩ := Choice.exists_form_avoid (R := ℤ) (Set.range x) (Set.finite_range x)
    (by rintro _ ⟨i, rfl⟩; exact (hY i).2.2.2.1)
  refine ⟨∑ l, (d₀ l + (a l).natAbs), fun k hk => ?_⟩
  have hle : ∀ l, d₀ l + (a l).natAbs ≤ k := fun l =>
    le_trans (Finset.single_le_sum (f := fun l => d₀ l + (a l).natAbs)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)) hk
  have hnn : ∀ l, (d₀ l : ℤ) ≤ a l + k := by
    intro l
    have h1 := hle l
    omega
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs, hsx⟩ := hd₀ (fun l => (a l + k).toNat) (fun l => by
      have := hnn l
      show d₀ l ≤ (a l + k).toNat
      omega)
    exact ⟨fun l => (a l + k).toNat, s, fun l => Int.toNat_of_nonneg (le_trans (by positivity) (hnn l)),
      hs, fun i => hsx (x i) ⟨i, rfl⟩⟩
  · obtain ⟨t, ht, htx⟩ := hd₀ (fun _ => k) (fun l => le_trans (Nat.le_add_right _ _) (hle l))
    exact ⟨t, ht, fun i => htx (x i) ⟨i, rfl⟩⟩

end GroundTheory.Heights₂.Heights.Inter
