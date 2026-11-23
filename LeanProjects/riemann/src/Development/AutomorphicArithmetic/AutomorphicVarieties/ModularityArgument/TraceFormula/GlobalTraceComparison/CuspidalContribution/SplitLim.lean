import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.CuspidalContribution.LevShrink
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.CuspSupportOf

open NumberField IsDedekindDomain Matrix Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.LFun UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp

private theorem rel_le_mono {s t : Multiset ℂ} {a b : ℝ} (hab : a ≤ b)
    (h : Multiset.Rel (fun x y => ‖x - y‖ ≤ a) s t) :
    Multiset.Rel (fun x y => ‖x - y‖ ≤ b) s t :=
  h.mono fun _ _ _ _ hxy => hxy.trans hab

private theorem rel_shift {s c : Multiset ℂ} {ε : ℝ} (α : ℂ)
    (h : Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) (s.map (· + α)) c) :
    Multiset.Rel (fun x y => ‖x - y‖ ≤ ε) s (c.map (· - α)) := by
  rw [Multiset.rel_map_left] at h
  rw [Multiset.rel_map_right]
  refine h.mono fun x _ y _ hxy => ?_
  have : x - (y - α) = x + α - y := by ring
  rw [this]
  exact hxy

theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp.splitLim :
    SplitLim := by
  classical
  intro E _ _ _ m₀ α β
  let A : (E →+* ℂ) → Set (Multiset ℂ × Multiset ℂ) := fun t => {x | x.1 + x.2 = m₀ t}
  have hA : ∀ t, (A t).Finite := fun t => by
    refine ((Multiset.antidiagonal (m₀ t)).toFinset.finite_toSet).subset ?_
    intro x hx
    simpa [A, Multiset.mem_antidiagonal] using hx
  have hS : (Set.pi Set.univ A).Finite := Set.Finite.pi' hA |>.subset (fun σ hσ t => hσ t (Set.mem_univ t))
  let F : ((E →+* ℂ) → Multiset ℂ × Multiset ℂ) →
      ((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ) :=
    fun σ => (fun t => (σ t).1.map (· - α), fun t => (σ t).2.map (· - β))
  refine ⟨(hS.image F).toFinset, ?_⟩
  intro m m₁ m₂ hm hto
  let Good : ((E →+* ℂ) → Multiset ℂ × Multiset ℂ) → ℕ → ℕ → Prop := fun σ j k =>
    ∀ t, Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) (m₁ k t) ((F σ).1 t) ∧
      Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) (m₂ k t) ((F σ).2 t)
  have hmono : ∀ σ {i j : ℕ} {k : ℕ}, i ≤ j → Good σ j k → Good σ i k := by
    intro σ i j k hij h t
    have hle : 1 / ((j : ℝ) + 1) ≤ 1 / ((i : ℝ) + 1) :=
      Nat.one_div_le_one_div hij
    exact ⟨rel_le_mono hle (h t).1, rel_le_mono hle (h t).2⟩
  have step1 : ∀ j, ∀ᶠ k in atTop, ∃ σ ∈ Set.pi Set.univ A, Good σ j k := by
    intro j
    have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := Nat.one_div_pos_of_nat
    have hall : ∀ᶠ k in atTop, ∀ t, Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) (m k t) (m₀ t) :=
      eventually_all.2 fun t => hto t _ hpos
    filter_upwards [hall] with k hk
    have hsplit : ∀ t, ∃ x : Multiset ℂ × Multiset ℂ, x.1 + x.2 = m₀ t ∧
        Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) ((m₁ k t).map (· + α)) x.1 ∧
        Multiset.Rel (fun x y => ‖x - y‖ ≤ 1 / ((j : ℝ) + 1)) ((m₂ k t).map (· + β)) x.2 := by
      intro t
      have h := hk t
      rw [hm k t, Multiset.rel_add_left] at h
      obtain ⟨c₁, c₂, h₁, h₂, hc⟩ := h
      exact ⟨(c₁, c₂), hc.symm, h₁, h₂⟩
    choose σ hσ h₁ h₂ using hsplit
    exact ⟨σ, fun t _ => hσ t, fun t => ⟨rel_shift α (h₁ t), rel_shift β (h₂ t)⟩⟩
  have step2 : ∃ σ ∈ Set.pi Set.univ A, ∀ j, ∃ᶠ k in atTop, Good σ j k := by
    by_contra hcon
    have hJ : ∀ σ, ∃ j, σ ∈ Set.pi Set.univ A → ∀ᶠ k in atTop, ¬ Good σ j k := by
      intro σ
      by_cases hσ : σ ∈ Set.pi Set.univ A
      · by_contra hno
        refine hcon ⟨σ, hσ, fun j => ?_⟩
        intro hev
        exact hno ⟨j, fun _ => hev⟩
      · exact ⟨0, fun h => absurd h hσ⟩
    choose J hJ using hJ
    let N := hS.toFinset.sup J
    have hN : ∀ᶠ k in atTop, ∀ σ ∈ Set.pi Set.univ A, ¬ Good σ N k := by
      refine (Filter.eventually_all_finite hS).2 fun σ hσ => ?_
      filter_upwards [hJ σ hσ] with k hk hg
      exact hk (hmono σ (Finset.le_sup (f := J) (hS.mem_toFinset.2 hσ)) hg)
    obtain ⟨k, hk₁, hk₂⟩ := (hN.and (step1 N)).exists
    obtain ⟨σ, hσ, hg⟩ := hk₂
    exact hk₁ σ hσ hg
  obtain ⟨σ, hσ, hfreq⟩ := step2
  obtain ⟨s, hs, hgood⟩ := Filter.extraction_forall_of_frequently hfreq
  have hlim : ∀ (ε : ℝ), 0 < ε → ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) ≤ ε := by
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop j₀] with k hk
    exact (Nat.one_div_le_one_div hk).trans hj₀.le
  refine ⟨F σ, ?_, s, hs, ?_, ?_⟩
  · simpa using Set.mem_image_of_mem F hσ
  · intro τ ε hε
    filter_upwards [hlim ε hε] with k hk
    exact rel_le_mono hk (hgood k τ).1
  · intro τ ε hε
    filter_upwards [hlim ε hε] with k hk
    exact rel_le_mono hk (hgood k τ).2
