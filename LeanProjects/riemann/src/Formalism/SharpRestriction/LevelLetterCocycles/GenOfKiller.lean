import Mathlib

namespace Formalism.MainNotions.UnusedSlot80.UGen

theorem span_le_card {R M : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup M] [Module R M] {g : ℕ} (v : Fin g → M) (N : Submodule R M)
    (hN : N ≤ Submodule.span R (Set.range v)) :
    ∃ (g₀ : ℕ) (w : Fin g₀ → M), g₀ ≤ g ∧ (∀ i, w i ∈ N) ∧
      N = Submodule.span R (Set.range w) := by
  classical
  obtain ⟨n, b⟩ := Submodule.basisOfPid (Finsupp.basisSingleOne : Module.Basis (Fin g) R (Fin g →₀ R))
    (N.comap (Finsupp.linearCombination R v))
  refine ⟨n, fun i => Finsupp.linearCombination R v (b i : Fin g →₀ R), ?_, ?_, ?_⟩
  · have h1 := Module.finrank_eq_card_basis b
    have h2 := Submodule.finrank_le (N.comap (Finsupp.linearCombination R v))
    have h3 := Module.finrank_eq_card_basis
      (Finsupp.basisSingleOne : Module.Basis (Fin g) R (Fin g →₀ R))
    simp only [Fintype.card_fin] at h1 h3
    omega
  · intro i
    exact (b i).2
  · have hb : Submodule.span R (Set.range fun i => ((b i : _) : Fin g →₀ R)) =
        N.comap (Finsupp.linearCombination R v) := by
      have e : (Set.range fun i => ((b i : _) : Fin g →₀ R)) =
          (N.comap (Finsupp.linearCombination R v)).subtype '' Set.range b := by
        ext x; simp
      rw [e, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]
    have e2 : (Set.range fun i => Finsupp.linearCombination R v (b i : Fin g →₀ R)) =
        (Finsupp.linearCombination R v) '' Set.range fun i => ((b i : _) : Fin g →₀ R) := by
      ext x; simp
    rw [e2, ← Submodule.map_span, hb, Submodule.map_comap_eq,
      Finsupp.range_linearCombination, inf_eq_right.mpr hN]

private theorem mkQ_mem_span_of_mem_sup_lemma {R V ι : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (P : Submodule R V) (u : ι → V) {x : V} (hx : x ∈ Submodule.span R (Set.range u) ⊔ P) :
    P.mkQ x ∈ Submodule.span R (Set.range fun i => P.mkQ (u i)) := by
  obtain ⟨a, ha, p, hp, rfl⟩ := Submodule.mem_sup.mp hx
  have hp0 : P.mkQ p = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hp
  rw [map_add, hp0, add_zero]
  have hle : (Submodule.span R (Set.range u)).map P.mkQ ≤
      Submodule.span R (Set.range fun i => P.mkQ (u i)) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  exact hle (Submodule.mem_map_of_mem ha)

theorem gen_of_killer {R V : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [AddCommGroup V] [Module R V] (Msub Psub Isub : Submodule R V) (hIM : Isub ≤ Msub)
    {ι : Type*} [Finite ι] (F : ι → V) (hfg : Msub ≤ Submodule.span R (Set.range F) ⊔ Psub)
    (lR t : R) {g : ℕ} (v : Fin g → V)
    (hK : ∀ f ∈ Isub, ∃ K : ℕ, (lR ^ K * t) • f ∈ Submodule.span R (Set.range v) ⊔ Psub)
    (hsat : ∀ K : ℕ, ∀ f ∈ Msub, (lR ^ K * t) • f ∈ Psub → f ∈ Psub) :
    ∃ (g₀ : ℕ) (J : Fin g₀ → V), g₀ ≤ g ∧ (∀ i, J i ∈ Isub) ∧
      ∀ f ∈ Isub, ∃ o : Fin g₀ → R, f - ∑ i, o i • J i ∈ Psub := by
  classical
  let W : Submodule R (V ⧸ Psub) := Submodule.span R (Set.range fun i => Psub.mkQ (v i))
  let B : ℕ → Submodule R (V ⧸ Psub) := fun K =>
    W.comap ((lR ^ K * t) • (LinearMap.id : (V ⧸ Psub) →ₗ[R] V ⧸ Psub))
  have hBmono : Monotone B := by
    intro K K' hKK' q hq
    change (lR ^ K * t) • q ∈ W at hq
    change (lR ^ K' * t) • q ∈ W
    have e : lR ^ K' * t = lR ^ (K' - K) * (lR ^ K * t) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hKK']
    rw [e, mul_smul]
    exact W.smul_mem _ hq
  have hmemB : ∀ f ∈ Isub, ∃ K, Psub.mkQ f ∈ B K := by
    intro f hf
    obtain ⟨K, hKf⟩ := hK f hf
    refine ⟨K, ?_⟩
    change (lR ^ K * t) • Psub.mkQ f ∈ W
    rw [← map_smul]
    exact mkQ_mem_span_of_mem_sup_lemma Psub v hKf
  have hIle : Isub.map Psub.mkQ ≤ Submodule.span R (Set.range fun i => Psub.mkQ (F i)) := by
    intro q hq
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hq
    exact mkQ_mem_span_of_mem_sup_lemma Psub F (hfg (hIM hf))
  haveI hT : IsNoetherian R (Submodule.span R (Set.range fun i => Psub.mkQ (F i))) :=
    isNoetherian_of_fg_of_noetherian _ (Submodule.fg_span (Set.finite_range _))
  haveI hIN : IsNoetherian R (Isub.map Psub.mkQ) := isNoetherian_of_le hIle
  have hfgI : (Isub.map Psub.mkQ).FG :=
    (Submodule.fg_top _).mp (IsNoetherian.noetherian _)
  obtain ⟨S, hS⟩ := hfgI
  have hSB : ∀ x ∈ S, ∃ K, x ∈ B K := by
    intro x hx
    have hxI : x ∈ Isub.map Psub.mkQ := by
      rw [← hS]; exact Submodule.subset_span (Finset.mem_coe.mpr hx)
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hxI
    exact hmemB f hf
  choose! Kf hKf using hSB
  obtain ⟨K, hIB⟩ : ∃ K, Isub.map Psub.mkQ ≤ B K := by
    refine ⟨S.sup Kf, ?_⟩
    rw [← hS, Submodule.span_le]
    intro x hx
    exact hBmono (Finset.le_sup (Finset.mem_coe.mp hx)) (hKf x (Finset.mem_coe.mp hx))
  have hN : Isub.map ((lR ^ K * t) • Psub.mkQ) ≤
      Submodule.span R (Set.range fun i => Psub.mkQ (v i)) := by
    intro y hy
    obtain ⟨f, hf, rfl⟩ := Submodule.mem_map.mp hy
    have h1 := hIB (Submodule.mem_map_of_mem hf)
    change (lR ^ K * t) • Psub.mkQ f ∈ W at h1
    rw [LinearMap.smul_apply]
    exact h1
  obtain ⟨g₀, w, hg₀, hwN, hNw⟩ := span_le_card (fun i => Psub.mkQ (v i)) _ hN
  have hJ : ∀ i, ∃ f ∈ Isub, ((lR ^ K * t) • Psub.mkQ) f = w i :=
    fun i => Submodule.mem_map.mp (hwN i)
  choose J hJI hJw using hJ
  refine ⟨g₀, J, hg₀, hJI, ?_⟩
  intro f hf
  have hφf : ((lR ^ K * t) • Psub.mkQ) f ∈ Submodule.span R (Set.range w) := by
    rw [← hNw]; exact Submodule.mem_map_of_mem hf
  obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (R := R)).mp hφf
  refine ⟨o, hsat K _ ?_ ?_⟩
  · apply hIM
    exact Isub.sub_mem hf (Isub.sum_mem fun i _ => Isub.smul_mem _ (hJI i))
  · have h0 : ((lR ^ K * t) • Psub.mkQ) (f - ∑ i, o i • J i) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_smul, hJw]
      rw [ho, sub_self]
    rw [LinearMap.smul_apply, ← map_smul] at h0
    rw [← Submodule.Quotient.mk_eq_zero]
    exact h0

end Formalism.MainNotions.UnusedSlot80.UGen
