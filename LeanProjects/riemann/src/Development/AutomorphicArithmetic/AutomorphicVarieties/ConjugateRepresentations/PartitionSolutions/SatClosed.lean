import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.OrbClosed
open UpperTheory.V.Cj.A

theorem UpperTheory.V.Cj.A.satClosed :
    SatClosed := by
  intro Γ V S _ _ _ _ d G hP hC l hl T K hT hK hKY s
  have hcont : ∀ s', ContinuousOn (fun p : V => l s' p • p) G.Y := fun s' =>
    (hl.1 s').1.continuousOn.smul continuousOn_id
  have hmem : ∀ s', ∀ p ∈ G.Y, l s' p • p ∈ G.Y := fun s' p hp =>
    hC _ ((hl.1 s').2.1 p hp) p hp
  have horb : ∀ s', IsOpen (G.Y \ {p | ∃ γ : Γ, G.σ γ s = s' ∧ G.ρ γ p ∈ (fun p : V => l s' p • p) '' K}) := fun s' =>
    orbClosed Γ V S d G hP _ (by rintro _ ⟨k, hk, rfl⟩; exact hmem s' k (hKY hk))
      (hK.image_of_continuousOn ((hcont s').mono hKY)) s s'
  have hopen := (hcont s).isOpen_inter_preimage G.isOpen (hT.isOpen_biInter fun s' _ => horb s')
  convert hopen using 1
  ext p
  simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq]
  refine and_congr_right fun hp => ⟨fun h s' hs' => ⟨hmem s p hp, ?_⟩, fun h => ?_⟩
  · rintro ⟨γ, rfl, k, hk, hk'⟩
    have h1 := (hl.1 (G.σ γ s)).2.1 k (hKY hk)
    have h2 := (hl.1 s).2.1 p hp
    refine h ⟨γ, (l (G.σ γ s) k)⁻¹ * l s p, mul_pos (inv_pos.2 h1) h2, hs', ?_⟩
    have h3 : l (G.σ γ s) k • k = l s p • G.ρ γ p := by rw [← map_smul]; exact hk'
    rw [mul_smul, ← h3, inv_smul_smul₀ h1.ne']
    exact hk
  · rintro ⟨γ, t, ht, hs', hk⟩
    refine (h _ hs').2 ⟨γ, rfl, _, hk, ?_⟩
    show l (G.σ γ s) (t • G.ρ γ p) • t • G.ρ γ p = _
    rw [(hl.1 _).2.2 t ht _ (G.maps γ p hp), hl.2 γ s p hp, map_smul, smul_smul]
    congr 1
    field_simp
