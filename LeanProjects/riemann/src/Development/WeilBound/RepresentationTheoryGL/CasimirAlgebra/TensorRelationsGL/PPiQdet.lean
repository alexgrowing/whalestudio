import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace QuantumDeterminantProducts

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def sg (σ : Equiv.Perm (Fin n)) : ℂ := ((Equiv.Perm.sign σ : ℤ) : ℂ)

theorem sg_swap {i j : Fin n} (h : i ≠ j) : sg (Equiv.swap i j) = -1 := by
  simp [sg, Equiv.Perm.sign_swap h]

def IsAnti (g : TV n M (Fin n)) : Prop := ∀ σ : Equiv.Perm (Fin n), pm σ g = sg σ • g

theorem anti_apply {g : TV n M (Fin n)} (hg : IsAnti g) (σ : Equiv.Perm (Fin n)) (I : Fin n → Fin n) :
    g (I ∘ σ) = sg σ • g I := by
  have h := congrFun (hg σ) I
  simpa [pm] using h

theorem anti_zero {g : TV n M (Fin n)} (hg : IsAnti g) {I : Fin n → Fin n} (hI : ¬ Function.Injective I) :
    g I = 0 := by
  simp only [Function.Injective] at hI
  push_neg at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  have hIs : I ∘ Equiv.swap i j = I := by
    funext k
    simp only [Function.comp_apply]
    rcases eq_or_ne k i with rfl | hki
    · simp [Equiv.swap_apply_left, hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [Equiv.swap_apply_right, hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h := anti_apply hg (Equiv.swap i j) I
  rw [hIs, sg_swap hne] at h
  have h2 : (2 : ℂ) • g I = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    simp
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

theorem anti_ext {g : TV n M (Fin n)} (hg : IsAnti g) (h0 : g id = 0) : g = 0 := by
  funext I
  by_cases hI : Function.Injective I
  · have hb : Function.Bijective I := Finite.injective_iff_bijective.mp hI
    have h := anti_apply hg (Equiv.ofBijective I hb) id
    have hc : (id ∘ ⇑(Equiv.ofBijective I hb)) = I := by
      funext k
      rfl
    rw [hc, h0, smul_zero] at h
    simpa using h
  · simpa using anti_zero hg hI

theorem alt_anti (f : TV n M (Fin n)) : IsAnti (alt Finset.univ f) := by
  intro σ
  funext I
  have key : ∀ J : Fin n → Fin n, alt Finset.univ f J = ∑ τ : Equiv.Perm (Fin n), sg τ • f (J ∘ ⇑τ) := by
    intro J
    simp [alt, pm, sg]
  have hp : pm σ (alt Finset.univ f) I = alt Finset.univ f (I ∘ σ) := by
    simp [pm]
  rw [hp]
  show alt Finset.univ f (I ∘ σ) = sg σ • alt Finset.univ f I
  rw [key (I ∘ σ), key I, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft σ) _ _ ?_
  intro τ
  have hs : sg σ * sg (σ * τ) = sg τ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [sg, Equiv.Perm.sign_mul, h]
  simp only [Equiv.coe_mulLeft]
  rw [smul_smul, hs]
  rfl

def X (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) : Module.End ℂ (TV n M (Fin n)) :=
  algebraMap ℂ _ u + xJ E j

def T (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) : Module.End ℂ (TV n M (Fin n)) :=
  algebraMap ℂ _ (u - (j : ℂ)) + Om E j

theorem X_eq_T_of_antisymm_below (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (j : Fin n) (w : TV n M (Fin n))
    (hw : ∀ i, i < j → pm (Equiv.swap i j) w = -w) : X E u j w = T E u j w := by
  have hs : (∑ i ∈ Finset.univ.filter (fun i : Fin n => i < j), pm (Equiv.swap i j)) w = -(((j : ℕ) : ℂ) • w) := by
    rw [LinearMap.sum_apply]
    rw [Finset.sum_congr rfl (fun i hi => hw i (Finset.mem_filter.mp hi).2)]
    rw [Finset.sum_neg_distrib, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, Nat.cast_smul_eq_nsmul]
  simp only [X, T, xJ, LinearMap.add_apply]
  rw [hs, Module.algebraMap_end_apply, Module.algebraMap_end_apply, sub_smul]
  abel

theorem T_comm (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (u : ℂ) (σ : Equiv.Perm (Fin n))
    (j : Fin n) (hj : σ j = j) : Commute (pm σ) (T E u j) := by
  refine Commute.add_right (Algebra.commutes _ _).symm ?_
  have := (hT n M (Fin n) E hE ∅).2.2.2 σ j
  rw [hj] at this
  exact this

theorem step1 (hT : TensorGl) (E : Fin n → Fin n → Module.End ℂ M) (hE : GlRel E) (u : ℂ) (g : TV n M (Fin n))
    (hg : IsAnti g) (l : List (Fin n)) (hl : l.Pairwise (· < ·)) :
    (l.map (X E u)).prod g = (l.map (T E u)).prod g := by
  induction l with
  | nil => rfl
  | cons k l ih =>
    rw [List.pairwise_cons] at hl
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [ih hl.2]
    apply X_eq_T_of_antisymm_below
    intro i hi
    have hc : Commute (pm (Equiv.swap i k)) (l.map (T E u)).prod := by
      apply Commute.list_prod_right
      intro b hb
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hb
      have hkj := hl.1 j hj
      apply T_comm hT E hE u
      apply Equiv.swap_apply_of_ne_of_ne
      · exact ne_of_gt (lt_trans hi hkj)
      · exact ne_of_gt hkj
    rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply]
    rw [hg (Equiv.swap i k), sg_swap (ne_of_lt hi)]
    simp

def ev (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) : List (Fin n) → (Fin n → Fin n) → TV n M (Fin n) → M
  | [], I, h => h I
  | k :: l, I, h => ∑ a, Tm E (u - (k : ℂ)) a (I k) (ev E u l (Function.update I k a) h)

theorem T_apply (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (k : Fin n) (h : TV n M (Fin n)) (I : Fin n → Fin n) :
    T E u k h I = ∑ a, Tm E (u - (k : ℂ)) a (I k) (h (Function.update I k a)) := by
  simp [T, Om, lift, eAt, Tm, Finset.sum_add_distrib, LinearMap.add_apply]
  congr 1
  · rw [Finset.sum_eq_single (I k)]
    · simp [sub_smul]
    · intro b _ hb
      simp [hb]
    · simp
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single (I k)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

theorem evA (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (I : Fin n → Fin n) :
    (l.map (T E u)).prod h I = ev E u l I h := by
  induction l generalizing I with
  | nil => rfl
  | cons k l ih => simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, ev, T_apply, ih]

theorem evB (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (h : TV n M (Fin n)) (l : List (Fin n)) (hl : l.Nodup)
    (I : Fin n → Fin n) :
    ev E u l I h = ∑ c ∈ Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ l → c p = I p),
      (l.map fun k : Fin n => Tm E (u - (k : ℂ)) (c k) (I k)).prod (h c) := by
  induction l generalizing I with
  | nil =>
    rw [Finset.sum_eq_single I]
    · simp [ev]
    · intro c hc hne
      exfalso
      apply hne
      funext p
      exact (Finset.mem_filter.mp hc).2 p (by simp)
    · intro hI
      exfalso
      apply hI
      simp
  | cons k l ih =>
    have hk : k ∉ l := (List.nodup_cons.mp hl).1
    have hl' := (List.nodup_cons.mp hl).2
    simp only [ev, ih hl']
    conv_rhs => rw [← Finset.sum_fiberwise _ (fun c : Fin n → Fin n => c k)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr ?_ fun c hc => ?_
    · ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, List.mem_cons, not_or]
      constructor
      · intro H
        refine ⟨fun p hp => ?_, ?_⟩
        · rw [H p hp.2, Function.update_of_ne hp.1]
        · rw [H k hk, Function.update_self]
      · rintro ⟨H, hca⟩ p hp
        by_cases hpk : p = k
        · subst hpk
          rw [hca, Function.update_self]
        · rw [H p ⟨hpk, hp⟩, Function.update_of_ne hpk]
    · simp only [Finset.mem_filter] at hc
      have hca : c k = a := hc.2
      have hm : l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (Function.update I k a k'))
          = l.map (fun k' : Fin n => Tm E (u - (k' : ℂ)) (c k') (I k')) := by
        apply List.map_congr_left
        intro x hx
        have hxk : x ≠ k := by
          rintro rfl
          exact hk hx
        rw [Function.update_of_ne hxk]
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, hca, hm]

theorem evQ (E : Fin n → Fin n → Module.End ℂ M) (u : ℂ) (g : TV n M (Fin n)) (hg : IsAnti g) :
    ev E u (List.finRange n) id g = qdet E u (g id) := by
  rw [evB E u g _ (List.nodup_finRange n) id]
  have hfilt : Finset.univ.filter (fun c : Fin n → Fin n => ∀ p, p ∉ List.finRange n → c p = id p) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro c _ p hp
    exact absurd (List.mem_finRange p) hp
  rw [hfilt]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map ⟨fun σ : Equiv.Perm (Fin n) => ⇑σ, DFunLike.coe_injective⟩)), Finset.sum_map]
  · simp only [qdet, qminor, LinearMap.sum_apply, Function.Embedding.coeFn_mk]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have ha := anti_apply hg σ id
    simp only [Function.id_comp] at ha
    rw [ha, map_smul, Module.End.mul_apply, Module.End.intCast_apply, List.ofFn_eq_map, sg, Int.cast_smul_eq_zsmul]
    rfl
  · intro c _ hc
    have hnc : ¬ Function.Injective c := by
      intro hinj
      apply hc
      rw [Finset.mem_map]
      exact ⟨Equiv.ofBijective c (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
    rw [anti_zero hg hnc, map_zero]

end QuantumDeterminantProducts

open QuantumDeterminantProducts in
theorem piQdet_of : TensorGl → JMComm → PiQdet := by
  intro hT hJ n M _ _ E hE u
  apply LinearMap.ext
  intro f
  set g := alt Finset.univ f with hgdef
  have hg : IsAnti g := alt_anti f
  rw [Module.End.mul_apply, Module.End.mul_apply]
  have hPX : PiJ n E u = ((List.finRange n).map (X E u)).prod := by
    unfold PiJ
    rw [List.ofFn_eq_map]
    rfl
  have hA : IsAnti (PiJ n E u g) := by
    intro σ
    have hc := ((hJ n M E hE n).2.2 u σ).eq
    calc pm σ (PiJ n E u g) = ((pm σ * PiJ n E u : Module.End ℂ (TV n M (Fin n))) g) := rfl
      _ = ((PiJ n E u * pm σ : Module.End ℂ (TV n M (Fin n))) g) := by rw [hc]
      _ = PiJ n E u (pm σ g) := rfl
      _ = sg σ • PiJ n E u g := by rw [hg σ, map_smul]
  have hB : IsAnti (lift (qdet E u) g) := by
    intro σ
    have hl : pm σ (lift (qdet E u) g) = lift (qdet E u) (pm σ g) := by
      funext I
      simp [pm, lift]
    rw [hl, hg σ, map_smul]
  have hD : IsAnti (PiJ n E u g - lift (qdet E u) g) := by
    intro σ
    rw [map_sub, hA σ, hB σ, smul_sub]
  have h0 : (PiJ n E u g - lift (qdet E u) g) id = 0 := by
    rw [Pi.sub_apply, hPX, step1 hT E hE u g hg _ (List.pairwise_lt_finRange n), evA, evQ E u g hg]
    simp [lift]
  exact sub_eq_zero.mp (anti_ext hD h0)

end PositivityTheory.Rg.Cz

end
