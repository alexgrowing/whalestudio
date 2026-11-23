import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open NumberField Pointwise UpperTheory.V UpperTheory.V.KT UpperTheory.V.Af.BA

private theorem minVec_smul' {L : Type} [Field L] [NumberField L] {N : ℕ} (g : Gm L N) (h : HS L N) :
    minVec (g • h) = g • minVec h := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  simp [minVec, q_smul]

private theorem vert_ext' {L : Type} [Field L] [NumberField L] {N : ℕ} (a b : ↥(HR L N))
    (ha : ConeExtensionAcyclic.IsVert (qr L N) a) (e : minVec a.1 = minVec b.1) : a = b := by
  have : a - b = 0 := ha.2 _ fun y hy => by
    have h1 : y.1 ∈ minVec a.1 := hy
    rw [e] at h1
    have h2 : qr L N y b = 1 := h1
    rw [map_sub, hy, h2, sub_self]
  exact sub_eq_zero.1 this

theorem UpperTheory.orbRe_of_minimal_vector_stabilizer :
    UpperTheory.V.Af.BA.FixOrb → UpperTheory.V.Af.BA.ReInv → UpperTheory.V.Af.BA.ActRe → UpperTheory.V.Af.BA.SpanRe → UpperTheory.V.Af.BA.MinOrb → UpperTheory.V.Af.BA.MinStab → UpperTheory.V.Af.BA.OrbRe := by
  intro hFix hInv hAct hSpan hOrb hStab L _ _ _ N σ hσ p
  obtain ⟨hinv, hre⟩ := hInv L N σ hσ
  obtain ⟨inst, hval, -⟩ := hAct L N σ hσ
  have hRy : ∀ v : ConeExtensionAcyclic.Vert (qr L N), v.1.1 ∈ Ry L N := fun v y hy => v.2.1 ⟨y, hy⟩
  obtain ⟨R₁, hR₁, hR₁'⟩ := hOrb L N p
  obtain ⟨R₀, hR₀, hR₀'⟩ := hFix (Gm L N) (Fin (p + 1) → Set (Lat L N)) (sGm N σ)
    (fun z j => sLat σ '' z j)
    (fun g z => by
      funext j
      change sLat σ '' ((fun y => g • y) '' z j) = (fun y => sGm N σ g • y) '' (sLat σ '' z j)
      simp only [Set.image_image, sLat_smul])
    {z | ∃ t ∈ ConeExtensionAcyclic.simp (qr L N) (Tr L N) (p + 1), z = fun j => minVec (t j).1.1}
    (by
      rintro _ ⟨t, -, rfl⟩
      funext j
      ext y
      have hq := (hre _ (t j).1.2).1
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (hq x).trans hx
      · intro hy
        exact ⟨sLat σ y, (hq y).trans hy, funext fun a => hinv _⟩)
    (by
      rintro _ ⟨t, ht, rfl⟩
      have hs : Spans (minVec (t 0).1.1) := by
        have := hSpan L N σ hσ p t ht
        unfold Spans spanL at *
        refine top_le_iff.1 (this ▸ Submodule.span_mono (Set.image_mono fun y hy => hy 0))
      haveI := hStab L N _ (hRy (t 0)) hs
      have hle : MulAction.stabilizer (Gm L N) (fun j => minVec (t j).1.1) ≤
          MulAction.stabilizer (Gm L N) (minVec (t 0).1.1) := fun g hg => congrFun hg 0
      exact Finite.of_injective _ (Subgroup.inclusion_injective hle))
    ⟨R₁, hR₁, by
      rintro _ ⟨t, ht, rfl⟩
      exact hR₁' (fun j => (t j).1.1) (fun j => hRy _) (hSpan L N σ hσ p t ht)⟩
  refine ⟨{h | (∀ j, ∃ v : ConeExtensionAcyclic.Vert (qr L N), v.1.1 = h j) ∧ (fun j => minVec (h j)) ∈ R₀}, ?_, ?_⟩
  · refine Set.Finite.of_finite_image (f := fun h j => minVec (h j)) (hR₀.subset ?_) ?_
    · rintro _ ⟨h, hh, rfl⟩
      exact hh.2
    · intro a ha b hb e
      funext j
      obtain ⟨v, hv⟩ := ha.1 j
      obtain ⟨w, hw⟩ := hb.1 j
      have ej : minVec (a j) = minVec (b j) := congrFun e j
      rw [← hv, ← hw] at ej ⊢
      rw [vert_ext' _ _ v.2 ej]
  · intro t ht
    obtain ⟨g, hg, hgR⟩ := hR₀' _ ⟨t, ht, rfl⟩
    refine ⟨g, hg, fun j => ⟨(⟨g, hg⟩ : ↥(Fix N σ)) • t j, hval _ _⟩, ?_⟩
    simp only [minVec_smul']
    exact hgR
