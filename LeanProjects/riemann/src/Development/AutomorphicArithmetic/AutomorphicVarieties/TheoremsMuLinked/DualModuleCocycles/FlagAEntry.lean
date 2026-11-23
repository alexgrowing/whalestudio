import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.DualModuleCocycles.RepRSingle
open Matrix IsLocalRing UpperTheory.V UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.Pa UpperTheory.V.Th UpperTheory.V.Th.Coc

private theorem UpperTheory.V.Th.Coc.flagA_full {P M : Type} [CommMonoid P] [Monoid M] (φ : P →* M) {n : ℕ} (p : Fin n → P) :
    (List.ofFn fun j => φ (p j)).prod = φ (∏ j, p j) := by
  rw [← List.prod_ofFn, map_list_prod, List.map_ofFn]
  rfl

private theorem UpperTheory.V.Th.Coc.flagA_split {P M : Type} [CommMonoid P] [Monoid M] (φ : P →* M) :
    ∀ {n : ℕ} (p : Fin n → P) (F : Fin n → M) (i : Fin n), (∀ j, j ≠ i → F j = φ (p j)) →
      (List.ofFn F).prod = φ (∏ j, if j < i then p j else 1) * F i * φ (∏ j, if i < j then p j else 1) := by
  intro n
  induction n with
  | zero => intro p F i; exact i.elim0
  | succ n ih =>
    intro p F i
    refine Fin.cases ?_ (fun k => ?_) i
    · intro h
      have h1 : (fun j : Fin n => F j.succ) = fun j => φ (p j.succ) := funext fun j => h _ (Fin.succ_ne_zero j)
      rw [List.ofFn_succ, List.prod_cons, h1, flagA_full φ fun j : Fin n => p j.succ]
      simp [Fin.prod_univ_succ]
    · intro h
      rw [List.ofFn_succ, List.prod_cons,
        ih (fun j => p j.succ) (fun j => F j.succ) k (fun j hj => h _ (fun e => hj (Fin.succ_injective _ e))),
        h 0 (Fin.succ_ne_zero k).symm]
      simp [Fin.prod_univ_succ, mul_assoc]

private theorem UpperTheory.V.Th.Coc.flagA_entry {A : Type} [CommRing A] {n : ℕ} (u Z : Matrix (Fin n) (Fin n) A) (α : Fin n → A)
    (a b : Fin n) : (kS u α * Z * kT u α) a b = (kEl u α a * Z * kEl u α b) a b := by
  simp [kS, kT, Matrix.mul_apply]

theorem UpperTheory.V.Th.Coc.flagA :
    ∀ {A H : Type} [CommRing A] {n : ℕ} (r : H → Matrix (Fin n) (Fin n) A) (ψ : Fin n → H → A) (s : H), (∀ g : Fin n → H, (List.ofFn fun i => r (g i) - ψ i (g i) • (1 : Matrix (Fin n) (Fin n) A)).prod = 0) → (∀ a b, a ≠ b → (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) a b = 0) ∧ ∀ g, (∀ a b, b < a → (kS (r s) (fun i => ψ i s) * r g * kT (r s) (fun i => ψ i s)) a b = 0) ∧ ∀ i, (kS (r s) (fun i => ψ i s) * r g * kT (r s) (fun i => ψ i s)) i i = ψ i g * (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) i i := by
  intro A H _ n r ψ s hrel
  let φ : Polynomial A →* Matrix (Fin n) (Fin n) A := (Polynomial.aeval (r s)).toRingHom.toMonoidHom
  let p : Fin n → Polynomial A := fun j => Polynomial.X - Polynomial.C (ψ j s)
  have hp : ∀ j, φ (p j) = r s - ψ j s • (1 : Matrix (Fin n) (Fin n) A) := by
    intro j
    simp [φ, p, Algebra.algebraMap_eq_smul_one]
  have hk : ∀ a, kEl (r s) (fun i => ψ i s) a = φ (∏ j ∈ Finset.univ.erase a, p j) := fun a => rfl
  have hfull : φ (∏ j, p j) = 0 := by
    rw [← flagA_full φ p]
    simp only [hp]
    exact hrel fun _ => s
  have h0 : ∀ a b, a ≠ b → kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b = 0 := by
    intro a b hab
    obtain ⟨q, hq⟩ : p a ∣ ∏ j ∈ Finset.univ.erase b, p j := Finset.dvd_prod_of_mem _ (by simp [hab])
    rw [hk, hk, ← map_mul, hq, ← mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ a), map_mul, hfull, zero_mul]
  have h1 : ∀ g a b, b ≤ a → kEl (r s) (fun i => ψ i s) a * r g * kEl (r s) (fun i => ψ i s) b =
      ψ a g • (kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b) := by
    intro g a b hab
    have h := hrel (Function.update (fun _ => s) a g)
    rw [flagA_split φ p _ a (fun j hj => by rw [Function.update_of_ne hj, hp])] at h
    rw [Function.update_self, ← Finset.prod_filter, ← Finset.prod_filter] at h
    obtain ⟨q, hq⟩ : ∏ j ∈ Finset.univ.filter (· < a), p j ∣ ∏ j ∈ Finset.univ.erase a, p j :=
      Finset.prod_dvd_prod_of_subset _ _ _ fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [hj.ne]
    obtain ⟨q', hq'⟩ : ∏ j ∈ Finset.univ.filter (a < ·), p j ∣ ∏ j ∈ Finset.univ.erase b, p j :=
      Finset.prod_dvd_prod_of_subset _ _ _ fun j hj => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
        simp [(lt_of_le_of_lt hab hj).ne']
    have h2 : kEl (r s) (fun i => ψ i s) a * (r g - ψ a g • (1 : Matrix (Fin n) (Fin n) A)) *
        kEl (r s) (fun i => ψ i s) b = 0 := by
      rw [hk, hk, hq, hq', mul_comm _ q, map_mul, map_mul]
      calc _ = φ q * (φ (∏ j ∈ Finset.univ.filter (· < a), p j) * (r g - ψ a g • (1 : Matrix (Fin n) (Fin n) A)) *
            φ (∏ j ∈ Finset.univ.filter (a < ·), p j)) * φ q' := by simp only [mul_assoc]
        _ = 0 := by rw [h, mul_zero, zero_mul]
    rw [mul_sub, sub_mul, sub_eq_zero, mul_smul_comm, mul_one, smul_mul_assoc] at h2
    exact h2
  have he : ∀ a b, (kS (r s) (fun i => ψ i s) * kT (r s) (fun i => ψ i s)) a b =
      (kEl (r s) (fun i => ψ i s) a * kEl (r s) (fun i => ψ i s) b) a b := by
    intro a b
    simpa using flagA_entry (r s) 1 (fun i => ψ i s) a b
  refine ⟨fun a b hab => ?_, fun g => ⟨fun a b hab => ?_, fun i => ?_⟩⟩
  · rw [he, h0 a b hab]; rfl
  · rw [flagA_entry, h1 g a b hab.le, h0 a b hab.ne', smul_zero]; rfl
  · rw [flagA_entry, h1 g i i le_rfl, he]; rfl
