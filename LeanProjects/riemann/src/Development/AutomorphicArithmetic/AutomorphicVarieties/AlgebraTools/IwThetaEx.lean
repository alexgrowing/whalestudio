import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwMonoidExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem thetaEx_split {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun _ _ i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  set c : kˣ := t p.2 * (t p.1)⁻¹ with hc
  have h1 : valuation k (c : k) ≤ 1 := by simpa using hp (p.1, p.1)
  refine ⟨c, fun s hs i j hij => ?_⟩
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  have h2 : valuation k (s i : k) * valuation k (c : k) ≤ valuation k (s j : k) := by
    rcases hs with rfl | rfl
    · simpa using h1
    · have := mul_le_mul_right (hp (i, j)) (valuation k (s i : k))
      refine this.trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
  have hj := j.2
  have hlt' : (i : ℕ) < j := hlt
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  exact mul_le_mul' h2 (mul_le_of_le_one_right' (pow_le_one' h1 _))

theorem UpperTheory.V.AlgebraTools.thetaEx :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M), IsUnit (resCard k : A) → ∃! θ : (Fin n → kˣ) →* (Module.End A (fixd ρ (iwC k n C)))ˣ, ∀ t, Dom t → (θ t : Module.End A (fixd ρ (iwC k n C))) = hk ρ (iwC k n C) (diagT k (Fin n) t) := by
  intro k _ _ _ _ n C A M _ _ _ ρ hq
  obtain ⟨hmul, hunit, -⟩ := domMul k n C A M ρ
  let P : Submonoid (Fin n → kˣ) :=
    { carrier := {t | Dom t}
      one_mem' := dom_one
      mul_mem' := fun {a b} ha hb i j hij => by
        simp only [Pi.mul_apply, Units.val_mul, map_mul]
        exact mul_le_mul' (ha i j hij) (hb i j hij) }
  refine monoidExt (Fin n → kˣ) _ P (fun t => hk ρ (iwC k n C) (diagT k (Fin n) t)) (fun t => ?_) ?_
    (fun a ha b hb => (hmul a b ha hb).symm) (fun a ha => hunit hq a ha)
  · obtain ⟨c, hc⟩ := thetaEx_split t
    refine ⟨t * (fun i : Fin n => c ^ (n - (i : ℕ))), hc t (Or.inr rfl), (1 : Fin n → kˣ) * (fun i : Fin n => c ^ (n - (i : ℕ))), hc 1 (Or.inl rfl), ?_⟩
    simp
  · have h := hmul 1 1 dom_one dom_one
    rw [mul_one] at h
    exact (hunit hq 1 dom_one).mul_left_cancel (h.trans (mul_one _).symm)
