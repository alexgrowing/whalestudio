import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CrDefs

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg UpperTheory.V.Pr UpperTheory.V

theorem UpperTheory.frame_criterion_projection :
    UpperTheory.V.Pr.CrPi := by
  unfold UpperTheory.V.Pr.CrPi
  intro Ω _ _ _ l _ O _ _ η Ψ σ g₁ B M L _ _ _ _ _ Φ k s x V hS
  have hup : Continuous (toUpl Ω L) := by
    unfold UpperTheory.V.Pr.toUpl
    exact (continuous_restrictScalarsHom ℚ (W.Lp L) Ω).subtype_mk _
  let f : G (W.Lp L) Ω →* Φ.Γ := k.p.comp (toUpl Ω L)
  have hf : Continuous f := k.p_cont.comp hup
  have hclosed : IsClosed (f.ker : Set (G (W.Lp L) Ω)) := by
    have h := (isClosed_singleton (x := (1 : Φ.Γ))).preimage hf
    exact h
  have hNS : NS Ω V.S' ≤ f.ker := by
    unfold ReciprocityTheory.Gal.NS
    apply Subgroup.topologicalClosure_minimal _ _ hclosed
    apply Subgroup.normalClosure_le_normal
    intro t ht
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_compl_iff] at ht
    obtain ⟨v, hv, A, hA, ht⟩ := ht
    rw [hS] at hv
    unfold UpperTheory.V.W.HidaSetting.S at hv
    simp only [Set.mem_setOf_eq, not_or] at hv
    obtain ⟨hl, hSt, -⟩ := hv
    have hMv := fun hM => hSt ((x.St v).2 ⟨hM, hl⟩)
    have hti : galEmb ℚ (W.Lp L) Ω t ∈ Ine A := (galEmb_mem_Ine A t).2 ht
    rw [SetLike.mem_coe, MonoidHom.mem_ker]
    show k.p (toUpl Ω L t) = 1
    rw [← MonoidHom.mem_ker, k.p_ker]
    apply Subgroup.le_topologicalClosure
    apply Subgroup.subset_normalClosure
    refine ⟨A, ?_, hti, ?_, ?_⟩
    · rw [natCast_place hA]
      exact hl
    · exact k.unr A ⟨hti, (toUpl Ω L t).2⟩
    · have hΨ : Ψ (galEmb ℚ (W.Lp L) Ω t) = 1 :=
        x.unr A (by rw [natCast_place hA]; exact hMv) hti
      unfold barChar
      show Units.map _ (Ψ (galEmb ℚ (W.Lp L) Ω t)) = 1
      rw [hΨ, map_one]
  let πt : GS Ω V.S' →* Φ.Γ := QuotientGroup.lift (NS Ω V.S') f hNS
  have hπt : ∀ t, πt (toGS Ω V.S' t) = f t := fun t => rfl
  have hπtc : Continuous πt := continuous_coinduced_dom.2 hf
  have hmem : ∀ y : V.η.ker, πt y.1 ∈ Φ.del.ker := by
    intro y
    obtain ⟨g, hg⟩ := pr_surj V y
    rw [← hg]
    exact (k.p0 g).2
  let π : V.η.ker →* Φ.del.ker := (πt.comp V.η.ker.subtype).codRestrict _ hmem
  have hcs : f s.c = Φ.c := by
    obtain ⟨h, hpc⟩ := k.c
    have h2 : toUpl Ω L s.c = ⟨σ, h⟩ := Subtype.ext x.c
    show k.p (toUpl Ω L s.c) = Φ.c
    rw [h2, hpc]
  refine ⟨π, ?_, ?_, ?_, ?_⟩
  · exact (hπtc.comp continuous_subtype_val).subtype_mk _
  · intro g
    rfl
  · intro y0
    let y : V.η.ker := y0
    apply Subtype.ext
    show πt (toGS Ω V.S' s.c * y.1 * (toGS Ω V.S' s.c)⁻¹) = Φ.c * πt y.1 * Φ.c⁻¹
    rw [map_mul, map_mul, map_inv, hπt, hcs]
  · intro y0
    let y : V.η.ker := y0
    obtain ⟨t, ht⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') y.1
    show Φ.eps (πt y.1) = V.ε y.1
    have ht' : toGS Ω V.S' t = y.1 := ht
    rw [← ht', hπt]
    show Φ.eps (k.p (toUpl Ω L t)) = V.ε (toGS Ω V.S' t)
    rw [k.eps, ← MonoidHom.comp_apply V.ε, V.hε]
    rfl
