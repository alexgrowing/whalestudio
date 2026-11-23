import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CornerUnits

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.frobenius_corner_mem_cone :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (K : Type) [CommRing K] [Algebra C K] (ρ : NRep F 3 K) (σ : NRep F 2 K), IsCorner ρ σ → Cone O C ρ → Cone O C σ := by
  intro l _ O _ _ F C _ _ _ K _ _ ρ σ hc hC
  have cinj : Function.Injective cor := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [cor]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro g i
    obtain ⟨c, h1, h2⟩ := hC.dg g (cor i)
    exact ⟨c, by rw [h1, hc.r], by rw [h2, w_cor]⟩
  · intro L hs hne
    have hs' : (List.map (fun s => w 3 s.2.1 - w 3 s.2.2) (L.map fun s => (s.1, cor s.2.1, cor s.2.2))).sum = 0 := by
      rw [← hs, List.map_map]
      congr 1
      apply List.map_congr_left
      intro s _
      simp [w_cor]
    have hne' : ∃ s ∈ L.map (fun s => (s.1, cor s.2.1, cor s.2.2)), s.2.1 ≠ s.2.2 := by
      obtain ⟨s, hs1, hs2⟩ := hne
      exact ⟨(s.1, cor s.2.1, cor s.2.2), List.mem_map_of_mem hs1, fun h => hs2 (cinj h)⟩
    obtain ⟨c, hcm, he⟩ := hC.cyc _ hs' hne'
    refine ⟨c, hcm, ?_⟩
    rw [he, List.map_map]
    congr 1
    apply List.map_congr_left
    intro s _
    simp [hc.r]
  · intro i j
    simp only [hc.r]
    exact hC.fg _ _
  · intro i j N
    have e : (fun g => σ.r g i j) = fun g => ρ.r g (cor i) (cor j) := funext fun g => hc.r g i j
    have h := hC.cont (cor i) (cor j) N
    rw [← e] at h
    have e3 : (fun g => (maximalIdeal C ^ N • Submodule.span C (Set.range fun g => σ.r g i j)).mkQ (σ.r g i j)) =
        fun g => (maximalIdeal C ^ N • Submodule.span C (Set.range fun g => σ.r g i j)).mkQ (ρ.r g (cor i) (cor j)) :=
      funext fun g => by rw [hc.r]
    rw [e3]
    exact h
  · obtain ⟨χ, hχ, hχρ⟩ := hC.psi
    refine ⟨fun v i g => χ v (cor i) g, fun v i => ⟨(hχ v (cor i)).1, fun g => ?_⟩, fun v i g => ?_⟩
    · rw [(hχ v (cor i)).2 g, w_cor]
    · rw [hχρ, hc.ψ]
