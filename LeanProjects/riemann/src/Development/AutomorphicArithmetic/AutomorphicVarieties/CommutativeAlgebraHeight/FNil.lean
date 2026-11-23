import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

private theorem idempotent_sandwich_list_prod_eq_of_kernel {k E : Type} [Field k] [Ring E] [Algebra k E] {n : ℕ}
    (π : E →ₐ[k] (Fin n → k)) (e g g' : E) (hg : g = e + g')
    (hJ : ∀ z, π z = 0 → e * z * e = 0) (t : List E) :
    ∀ a, π a = 0 → e * a * (g * (t.map (· * g)).prod) = e * a * (g' * (t.map (· * g')).prod) := by
  induction t with
  | nil =>
    intro a ha
    simp only [List.map_nil, List.prod_nil, mul_one]
    rw [hg, mul_add, hJ a ha, zero_add]
  | cons z s ih =>
    intro a ha
    simp only [List.map_cons, List.prod_cons]
    have hmem : π (a * g' * z) = 0 := by simp [map_mul, ha]
    calc e * a * (g * (z * g * (s.map (· * g)).prod))
        = (e * a * g) * (z * (g * (s.map (· * g)).prod)) := by simp only [mul_assoc]
      _ = (e * a * e + e * a * g') * (z * (g * (s.map (· * g)).prod)) := by rw [← mul_add, ← hg]
      _ = e * (a * g' * z) * (g * (s.map (· * g)).prod) := by
          rw [hJ a ha, zero_add]; simp only [mul_assoc]
      _ = e * (a * g' * z) * (g' * (s.map (· * g')).prod) := ih _ hmem
      _ = e * a * (g' * (z * g' * (s.map (· * g')).prod)) := by simp only [mul_assoc]

theorem UpperTheory.V.CA.f_nil :
    ∀ {n : ℕ} {k E : Type} [Field k] [Ring E] [Algebra k E] (e : Fin n → E) (π : E →ₐ[k] (Fin n → k)), CompleteOrthogonalIdempotents e → (∀ i, π (e i) = Pi.single i 1) → (∀ i x, ∃ a : k, e i * x * e i = a • e i) → (∀ x, π x = 0 ↔ ∀ i, e i * x * e i = 0) ∧ ∀ x : Fin n → E, (∀ s, π (x s) = 0) → (List.ofFn x).prod = 0 := by
  intro n k E _ _ _ e π he hπ hsc
  have hJ : ∀ z, π z = 0 → ∀ i, e i * z * e i = 0 := by
    intro z hz i
    obtain ⟨a, ha⟩ := hsc i z
    have ha0 : a = 0 := by
      simpa [map_mul, hz, hπ] using (congrFun (congrArg π ha) i).symm
    rw [ha, ha0, zero_smul]
  refine ⟨fun x => ⟨fun hz i => hJ x hz i, fun h => ?_⟩, fun x hx => ?_⟩
  · funext i
    have h2 := congrFun (congrArg π (h i)) i
    simpa [map_mul, hπ] using h2
  · obtain ⟨F, hF⟩ : ∃ F : Finset (Fin n) → E, ∀ T, F T = ∑ i ∈ T, e i := ⟨_, fun _ => rfl⟩
    have D : ∀ (m : ℕ) (T : Finset (Fin n)), T.card = m → ∀ t : List E, (∀ y ∈ t, π y = 0) →
        m ≤ t.length → F T * (t.map (· * F T)).prod = 0 := by
      intro m
      induction m with
      | zero =>
        intro T hT t _ _
        rw [Finset.card_eq_zero] at hT
        subst hT
        simp [hF]
      | succ m ih =>
        intro T hT t ht hlen
        cases t with
        | nil => simp at hlen
        | cons y s =>
          rw [show F T * ((y :: s).map (· * F T)).prod =
              ∑ i ∈ T, e i * ((y :: s).map (· * F T)).prod by rw [hF T, Finset.sum_mul]]
          apply Finset.sum_eq_zero
          intro i hi
          simp only [List.map_cons, List.prod_cons]
          rw [show e i * (y * F T * (s.map (· * F T)).prod) =
              e i * y * (F T * (s.map (· * F T)).prod) by simp only [mul_assoc]]
          have hsplit : F T = e i + F (T.erase i) := by
            rw [hF, hF, Finset.add_sum_erase T e hi]
          rw [idempotent_sandwich_list_prod_eq_of_kernel π (e i) (F T) (F (T.erase i)) hsplit (fun z hz => hJ z hz i) s y
            (ht y (by simp))]
          rw [ih (T.erase i) (by rw [Finset.card_erase_of_mem hi, hT]; rfl) s
            (fun z hz => ht z (by simp [hz])) (by simp at hlen; omega), mul_zero]
    have key := D n Finset.univ (by simp) (List.ofFn x)
      (by
        intro y hy
        rw [List.mem_ofFn] at hy
        obtain ⟨s, rfl⟩ := hy
        exact hx s)
      (by simp)
    have h1 : F Finset.univ = 1 := by rw [hF]; exact he.complete
    rw [h1, one_mul, show (fun y : E => y * 1) = id from funext mul_one, List.map_id] at key
    exact key
