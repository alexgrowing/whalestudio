import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero

namespace ReciprocityTheory.ChartRestriction.G.AI

theorem symm_eq_of_card {V : Type*} [AddCommGroup V] [Module ℝ V] [DecidableEq V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (v w : Fin n → V)
    (h : ∀ x : V, (Finset.univ.filter fun i => v i = x).card = (Finset.univ.filter fun i => w i = x).card) :
    I v = I w := by
  have e : ∀ c : V, {a // w a = c} ≃ {b // v b = c} := fun c =>
    Fintype.equivOfCardEq (by rw [Fintype.card_subtype, Fintype.card_subtype]; exact (h c).symm)
  have hσ : v ∘ (Equiv.ofFiberEquiv e) = w := funext fun i => Equiv.ofFiberEquiv_map e i
  rw [← hσ, hI]

theorem symm_piecewise_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (s t : Finset (Fin n))
    (hst : s.card = t.card) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (t.piecewise (fun _ => x) fun _ => y) := by
  classical
  have e : ∀ c : Bool, {a // decide (a ∈ t) = c} ≃ {b // decide (b ∈ s) = c} := fun c =>
    Fintype.equivOfCardEq (by
      rw [Fintype.card_subtype, Fintype.card_subtype]
      cases c
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = false) = tᶜ := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = false) = sᶜ := by ext; simp
        rw [h1, h2, Finset.card_compl, Finset.card_compl, hst]
      · have h1 : (Finset.univ.filter fun a => decide (a ∈ t) = true) = t := by ext; simp
        have h2 : (Finset.univ.filter fun b => decide (b ∈ s) = true) = s := by ext; simp
        rw [h1, h2, hst])
  have hσ : ∀ i, (Equiv.ofFiberEquiv e i ∈ s ↔ i ∈ t) := fun i => by
    have := Equiv.ofFiberEquiv_map e i
    rw [← decide_eq_decide]
    exact this
  have hfun : (s.piecewise (fun _ => x) fun _ => y) ∘ (Equiv.ofFiberEquiv e) =
      t.piecewise (fun _ => x) fun _ => y := by
    funext i
    rw [Function.comp_apply]
    by_cases hi : i ∈ t
    · rw [Finset.piecewise_eq_of_mem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ ((hσ i).2 hi)]
    · have hi' : Equiv.ofFiberEquiv e i ∉ s := fun h => hi ((hσ i).1 h)
      first
        | rw [Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_notMem _ _ _ hi']
        | rw [Finset.piecewise_eq_of_not_mem _ _ _ hi, Finset.piecewise_eq_of_not_mem _ _ _ hi']
  rw [← hfun, hI]

theorem symm_piecewise_eq_mix {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (s : Finset (Fin n)) :
    I (s.piecewise (fun _ => x) fun _ => y) = I (mix s.card x y) := by
  classical
  set t : Finset (Fin n) := Finset.univ.filter fun i : Fin n => (i : ℕ) < s.card with ht_def
  have ht : t.card = s.card := by
    have hle : s.card ≤ n := by simpa using Finset.card_le_univ s
    have hmap : t.map Fin.valEmbedding = Finset.range s.card := by
      ext m
      simp only [ht_def, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
        Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hm
        exact ⟨⟨m, by omega⟩, hm, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hmap, Finset.card_range]
  rw [symm_piecewise_eq I hI x y s t ht.symm]
  congr 1
  funext i
  simp [ht_def, mix, Finset.piecewise]

theorem symm_expand {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (I : MultilinearMap ℝ (fun _ : Fin n => V) ℝ) (hI : IsSymmForm I) (x y : V) (c : ℝ) :
    I (fun _ => y + c • x) =
      ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * c ^ j * I (mix j x y) := by
  classical
  have h1 : (fun _ : Fin n => y + c • x) = (fun _ => c • x) + (fun _ => y) := by
    funext i
    simp [add_comm]
  rw [h1, MultilinearMap.map_add_univ]
  have h2 : ∀ s : Finset (Fin n),
      I (s.piecewise (fun _ => c • x) fun _ => y) = c ^ s.card * I (mix s.card x y) := by
    intro s
    have h3 : (s.piecewise (fun _ => c • x) fun _ => y) =
        s.piecewise (fun i => c • (s.piecewise (fun _ => x) (fun _ => y)) i)
          (s.piecewise (fun _ => x) fun _ => y) := by
      funext i
      by_cases hi : i ∈ s <;> simp [Finset.piecewise, hi]
    rw [h3, MultilinearMap.map_piecewise_smul, symm_piecewise_eq_mix I hI, Finset.prod_const, smul_eq_mul]
  simp only [h2]
  have h4 := Finset.sum_powerset_apply_card (f := fun k => c ^ k * I (mix k x y))
    (x := (Finset.univ : Finset (Fin n)))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at h4
  rw [h4]
  simp only [nsmul_eq_mul, mul_assoc]

end ReciprocityTheory.ChartRestriction.G.AI
