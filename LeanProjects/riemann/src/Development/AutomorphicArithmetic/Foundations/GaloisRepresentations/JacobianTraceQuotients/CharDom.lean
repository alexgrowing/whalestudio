import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.JacobianTraceQuotients.TraceQuot

noncomputable section

open ValuativeRel
open scoped Classical

namespace UpperTheory.Gal.Join

private theorem indep {T : Type} [CommGroup T] (M : Submonoid T) (hM : ∀ t : T, ∃ s ∈ M, s * t ∈ M) (t₀ : T)
    (E E' : Multiset (T →* ℂˣ)) (c c' : ℂ) (hc : c ≠ 0)
    (h : ∀ t ∈ M, c * (E.map fun μ => (μ (t₀ * t) : ℂ)).sum = c' * (E'.map fun μ => (μ (t₀ * t) : ℂ)).sum) :
    ∀ μ ∈ E, μ ∈ E' := by
  classical
  let ρ : (T →* ℂˣ) → (M →* ℂ) := fun μ => (Units.coeHom ℂ).comp (μ.comp M.subtype)
  have hρm : ∀ μ (m : M), ρ μ m = (μ m : ℂ) := fun _ _ => rfl
  have hρinj : Function.Injective ρ := by
    intro μ ν hμν
    have hM' : ∀ m ∈ M, μ m = ν m := by
      intro m hm
      apply Units.ext
      have := DFunLike.congr_fun hμν ⟨m, hm⟩
      rw [hρm, hρm] at this
      exact this
    refine MonoidHom.ext fun t => ?_
    obtain ⟨s, hs, hst⟩ := hM t
    have e : t = s⁻¹ * (s * t) := by rw [inv_mul_cancel_left]
    rw [e, map_mul μ, map_mul ν, map_inv μ, map_inv ν, hM' s hs, hM' _ hst]
  have hli : LinearIndependent ℂ (fun μ : T →* ℂˣ => ((ρ μ : M →* ℂ) : M → ℂ)) :=
    (linearIndependent_monoidHom M ℂ).comp ρ hρinj
  intro μ hμ
  by_contra hμ'
  let S := (E + E').toFinset
  let g : (T →* ℂˣ) → ℂ := fun ν => (c * E.count ν - c' * E'.count ν) * (ν t₀ : ℂ)
  have conv : ∀ F : Multiset (T →* ℂˣ), F.toFinset ⊆ S → ∀ t : T,
      (F.map fun ν => (ν (t₀ * t) : ℂ)).sum = ∑ ν ∈ S, (F.count ν : ℂ) * ((ν t₀ : ℂ) * (ν t : ℂ)) := by
    intro F hF t
    rw [Finset.sum_multiset_map_count, Finset.sum_subset hF]
    · apply Finset.sum_congr rfl
      intro ν _
      rw [nsmul_eq_mul, map_mul, Units.val_mul]
    · intro ν _ hν
      rw [Multiset.count_eq_zero.mpr (by simpa using hν)]
      simp
  have hsum : ∑ ν ∈ S, g ν • ((ρ ν : M →* ℂ) : M → ℂ) = 0 := by
    funext m
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h1 := h m m.2
    rw [conv E (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inl (Multiset.mem_toFinset.mp hx)))) m,
      conv E' (fun x hx => Multiset.mem_toFinset.mpr
        (Multiset.mem_add.mpr (Or.inr (Multiset.mem_toFinset.mp hx)))) m,
      Finset.mul_sum, Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
    rw [← h1]
    apply Finset.sum_congr rfl
    intro ν _
    rw [hρm]
    simp only [g]
    ring
  have h0 := linearIndependent_iff'.mp hli S g hsum μ
    (Multiset.mem_toFinset.mpr (Multiset.mem_add.mpr (Or.inl hμ)))
  simp only [g, Multiset.count_eq_zero.mpr hμ', Nat.cast_zero, mul_zero, sub_zero] at h0
  rcases mul_eq_zero.mp h0 with h2 | h2
  · rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hc h3
    · exact (Multiset.count_pos.mpr hμ).ne' (by exact_mod_cast h3)
  · exact (μ t₀).ne_zero h2

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private def domM (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    Submonoid (Fin n → kˣ) where
  carrier := {t | Dom t}
  mul_mem' := by
    intro a b ha hb i j hij
    simp only [Pi.mul_apply, Units.val_mul, map_mul]
    exact mul_le_mul' (ha i j hij) (hb i j hij)
  one_mem' := by
    intro i j _
    simp

private theorem dom_translate (t : Fin n → kˣ) : ∃ s ∈ domM k n, s * t ∈ domM k n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, (domM k 0).one_mem, ?_⟩
    show Dom _
    intro i
    exact i.elim0
  · obtain ⟨p, -, hp⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n × Fin n))
      (fun p => valuation k ((t p.1 / t p.2 : kˣ) : k)) ⟨(⟨0, hn⟩, ⟨0, hn⟩), Finset.mem_univ _⟩
    have hx1 : 1 ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) := by
      have := hp (⟨0, hn⟩, ⟨0, hn⟩) (Finset.mem_univ _)
      simpa using this
    have hxt : ∀ i j, valuation k (t i : k) ≤
        valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k) := by
      intro i j
      have := hp (i, j) (Finset.mem_univ _)
      have e : (t i : k) = ((t i / t j : kˣ) : k) * (t j : k) := by simp
      rw [e, map_mul]
      gcongr
    refine ⟨fun i => (t p.1 / t p.2) ^ (i : ℕ), ?_, ?_⟩
    · show Dom _
      intro i j hij
      simp only [Units.val_pow_eq_pow_val, map_pow]
      exact pow_le_pow_right₀ hx1 (le_of_lt hij)
    · show Dom _
      intro i j hij
      simp only [Pi.mul_apply, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow]
      have hij' : (i : ℕ) + 1 ≤ j := hij
      have hpw := pow_le_pow_right₀ hx1 hij'
      calc valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) * valuation k (t i : k)
          ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (i : ℕ) *
            (valuation k ((t p.1 / t p.2 : kˣ) : k) * valuation k (t j : k)) := by
            gcongr
            exact hxt i j
        _ = valuation k ((t p.1 / t p.2 : kˣ) : k) ^ ((i : ℕ) + 1) * valuation k (t j : k) := by
            rw [pow_succ, mul_assoc]
        _ ≤ valuation k ((t p.1 / t p.2 : kˣ) : k) ^ (j : ℕ) * valuation k (t j : k) := by
            gcongr

theorem charDom : CharDom := by
  intro k _ _ _ _ n t₀ E E' c c' hc h
  have hind := indep (domM k n) (fun t => dom_translate t) t₀ E E' c c' hc h
  refine ⟨hind, fun hE => ?_⟩
  by_contra hne
  push_neg at hne
  obtain ⟨μ, hμ⟩ := Multiset.exists_mem_of_ne_zero hE
  have := indep (domM k n) (fun t => dom_translate t) t₀ E 0 1 0 one_ne_zero
    (fun t ht => by rw [one_mul, hne t ht]; simp) μ hμ
  simp at this

end UpperTheory.Gal.Join
