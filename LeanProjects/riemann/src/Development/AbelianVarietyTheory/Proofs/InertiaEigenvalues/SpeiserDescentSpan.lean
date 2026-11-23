import Mathlib

namespace GlobalTheory

open Finset

theorem ringHom_evalVectors_span_eq_top {L Ω : Type} [Field L] [Field Ω]
    (S : Set (L →+* Ω)) [Fintype S] :
    Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c) = ⊤ := by
  classical
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne) inferInstance
  have hli : LinearIndependent Ω (fun h : S => ((h : L →+* Ω) : L → Ω)) := by
    have := (linearIndependent_monoidHom L Ω).comp
      (fun h : S => ((h : L →+* Ω) : L →* Ω)) (by
        intro x y hxy
        apply Subtype.ext
        apply RingHom.ext
        intro c
        exact DFunLike.congr_fun hxy c)
    exact this
  rw [Fintype.linearIndependent_iff] at hli
  apply hf0
  apply LinearMap.ext
  intro x
  rw [LinearMap.pi_apply_eq_sum_univ f x]
  have hc : ∀ h : S, f (fun j => if h = j then (1 : Ω) else 0) = 0 := by
    apply hli
    funext c
    have hmem : (fun h : S => (h : L →+* Ω) c) ∈
        Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c) :=
      Submodule.subset_span ⟨c, rfl⟩
    have h0 : f (fun h : S => (h : L →+* Ω) c) = 0 := by
      have : f (fun h : S => (h : L →+* Ω) c) ∈ Submodule.map f
          (Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c)) :=
        Submodule.mem_map_of_mem hmem
      rw [hf] at this
      exact (Submodule.mem_bot Ω).mp this
    rw [LinearMap.pi_apply_eq_sum_univ f] at h0
    simpa [Finset.sum_apply, mul_comm] using h0
  simp [hc]

theorem speiser_descent_span :
    ∀ {G L Ω M : Type} [Group G] [Field L] [Field Ω] [Algebra L Ω] [AddCommGroup M] [Module Ω M]
      [Module L M] [IsScalarTower L Ω M] (b : G → Ω → Ω) (a : G → L →+* Ω) (σ : G → M →+ M)
      (W : Submodule L M), (∀ g h c, a (g * h) c = b g (a h c)) →
      (∀ c, a 1 c = algebraMap L Ω c) → (∀ m, σ 1 m = m) →
      (∀ g h m, σ (g * h) m = σ g (σ h m)) → (∀ g (c : L) m, σ g (c • m) = a g c • σ g m) →
      (Set.range a).Finite → (∀ g, ∀ m ∈ W, σ g m ∈ W) →
      (∀ g, (∀ c, a g c = algebraMap L Ω c) → ∀ m ∈ W, σ g m = m) →
      ∀ m ∈ W, m ∈ Submodule.span Ω {m | m ∈ W ∧ ∀ g, σ g m = m} := by
  intro G L Ω M _ _ _ _ _ _ _ _ b a σ W hb ha1 _hσ1 hσmul hσsmul hfin hstab hker m hm
  classical
  let S : Set (L →+* Ω) := Set.range a
  haveI : Fintype S := hfin.fintype
  have hrep : ∀ h : S, ∃ g, a g = h := fun h => h.2
  choose gs hgs using hrep
  have hleft : ∀ g x c, a x c = b g⁻¹ (a (g * x) c) := by
    intro g x c; rw [← hb, inv_mul_cancel_left]
  let δ : S → Ω := fun h => if (h : L →+* Ω) = a 1 then 1 else 0
  have hδ : δ ∈ Submodule.span Ω (Set.range fun c : L => fun h : S => (h : L →+* Ω) c) := by
    rw [ringHom_evalVectors_span_eq_top S]; trivial
  obtain ⟨β, hβ⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 hδ
  have hβh : ∀ h : S, ∑ c ∈ β.support, β c * (h : L →+* Ω) c = δ h := by
    intro h
    have := congrFun hβ h
    simpa [Finsupp.sum, Finset.sum_apply] using this
  let t : L → M := fun c => ∑ h : S, σ (gs h) (c • m)
  have htW : ∀ c, t c ∈ W := fun c => W.sum_mem fun h _ => hstab _ _ (W.smul_mem c hm)
  have hperm : ∀ g : G, ∀ y ∈ W, σ g (∑ h : S, σ (gs h) y) = ∑ h : S, σ (gs h) y := by
    intro g y hy
    let π : S → S := fun h => ⟨a (g * gs h), Set.mem_range_self _⟩
    have hπ : Function.Injective π := by
      intro h1 h2 e
      have e' : a (g * gs h1) = a (g * gs h2) := congrArg Subtype.val e
      have : a (gs h1) = a (gs h2) := by
        ext c; rw [hleft g (gs h1) c, hleft g (gs h2) c, e']
      apply Subtype.ext
      rw [← hgs h1, ← hgs h2, this]
    have hbij : Function.Bijective π := Finite.injective_iff_bijective.1 hπ
    have hsw : ∀ h, σ (g * gs h) y = σ (gs (π h)) y := by
      intro h
      have hk : a (gs (π h)) = a (g * gs h) := hgs (π h)
      have hu : ∀ c, a ((gs (π h))⁻¹ * (g * gs h)) c = algebraMap L Ω c := by
        intro c
        rw [hb, ← hk, ← hb, inv_mul_cancel, ha1]
      calc σ (g * gs h) y = σ (gs (π h) * ((gs (π h))⁻¹ * (g * gs h))) y := by
            rw [mul_inv_cancel_left]
        _ = σ (gs (π h)) (σ ((gs (π h))⁻¹ * (g * gs h)) y) := hσmul _ _ _
        _ = σ (gs (π h)) y := by rw [hker _ hu y hy]
    rw [map_sum]
    simp_rw [← hσmul, hsw]
    exact Function.Bijective.sum_comp hbij (fun h => σ (gs h) y)
  have htinv : ∀ c g, σ g (t c) = t c := fun c g => hperm g _ (W.smul_mem c hm)
  have h1S : a 1 ∈ S := Set.mem_range_self 1
  have hrec : ∑ c ∈ β.support, β c • t c = m := by
    have e1 : ∑ c ∈ β.support, β c • t c = ∑ h : S, δ h • σ (gs h) m := by
      simp only [t, Finset.smul_sum, hσsmul, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Finset.sum_smul, hgs h, hβh h]
    rw [e1, Fintype.sum_eq_single ⟨a 1, h1S⟩]
    · have hg1 : ∀ c, a (gs ⟨a 1, h1S⟩) c = algebraMap L Ω c := by
        intro c; rw [hgs]; exact ha1 c
      simp only [δ, if_pos rfl, one_smul]
      exact hker _ hg1 m hm
    · intro h hne
      have : (h : L →+* Ω) ≠ a 1 := fun e => hne (Subtype.ext e)
      simp [δ, this]
  rw [← hrec]
  exact Submodule.sum_mem _ fun c _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨htW c, htinv c⟩)

end GlobalTheory
