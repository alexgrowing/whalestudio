import Development.EtaleCohomology.CohomologicalPurity.LeafHensCutDef

noncomputable section

namespace LateralTheory.CohomologicalPurity.Hz

theorem good_iso (A S : Type) [CommRing A] [CommRing S] (e : A ≃+* S) (I : Ideal A) : Good (e : A →+* S) I := by
  refine ⟨RingHom.Etale.of_bijective e.bijective, ⟨(Ideal.Quotient.mk I).comp (e.symm : S →+* A), ?_⟩, fun s => ⟨e.symm s, ?_⟩, ?_⟩
  · ext a; simp
  · simp
  · intro B _ J _ ψ _
    refine ⟨ψ.comp (e.symm : S →+* A), ?_, fun χ hχ => ?_⟩
    · ext a; simp
    · ext s
      have := congrArg (fun f : A →+* B => f (e.symm s)) hχ
      simpa using this

theorem good_comp (A S T : Type) [CommRing A] [CommRing S] [CommRing T] (φ : A →+* S) (ψ : S →+* T) (I : Ideal A)
    (h1 : Good φ I) (h2 : Good ψ (I.map φ)) : Good (ψ.comp φ) I := by
  obtain ⟨r1, hr1⟩ := h1.retr
  obtain ⟨r2, hr2⟩ := h2.retr
  have hk : I.map φ ≤ RingHom.ker r1 := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change (r1.comp φ) a = 0
    rw [hr1]
    exact Ideal.Quotient.eq_zero_iff_mem.2 ha
  refine ⟨RingHom.Etale.stableUnderComposition φ ψ h1.etale h2.etale,
    ⟨(Ideal.Quotient.lift (I.map φ) r1 (fun a ha => hk ha)).comp r2, ?_⟩, fun t => ?_, ?_⟩
  · ext a
    have e2 : r2 (ψ (φ a)) = Ideal.Quotient.mk (I.map φ) (φ a) := congrArg (fun f : S →+* S ⧸ I.map φ => f (φ a)) hr2
    simp only [RingHom.comp_apply, e2, Ideal.Quotient.lift_mk]
    exact congrArg (fun f : A →+* A ⧸ I => f a) hr1
  · obtain ⟨s, hs⟩ := h2.surj t
    obtain ⟨a, ha⟩ := h1.surj s
    refine ⟨a, ?_⟩
    rw [Ideal.map_map] at hs
    have h3 : ψ (s - φ a) ∈ (I.map φ).map ψ := Ideal.mem_map_of_mem ψ ha
    rw [Ideal.map_map] at h3
    have : t - (ψ.comp φ) a = (t - ψ s) + ψ (s - φ a) := by simp [map_sub]
    rw [this]
    exact Ideal.add_mem _ hs h3
  · intro B _ J hB χ0 hI
    obtain ⟨χ1, hχ1, hu1⟩ := h1.univ B J hB χ0 hI
    have hI2 : I.map φ ≤ J.comap χ1 := by
      rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, hχ1]
      exact hI
    obtain ⟨χ2, hχ2, hu2⟩ := h2.univ B J hB χ1 hI2
    refine ⟨χ2, ?_, fun χ hχ => ?_⟩
    · show χ2.comp (ψ.comp φ) = χ0
      rw [← RingHom.comp_assoc, hχ2, hχ1]
    · apply hu2
      apply hu1
      show (χ.comp ψ).comp φ = χ0
      rw [RingHom.comp_assoc]
      exact hχ

theorem LeafComp_of : LeafComp := ⟨good_iso, good_comp⟩

end LateralTheory.CohomologicalPurity.Hz
