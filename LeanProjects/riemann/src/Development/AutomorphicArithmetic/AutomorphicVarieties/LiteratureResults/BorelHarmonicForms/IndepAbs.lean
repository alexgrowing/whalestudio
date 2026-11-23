import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.indepAbs :
    UpperTheory.V.Lit.Bor.IndepAbs := by
  classical
  intro O W _ _ A s V h hs hn
  have hsup : ∀ P Q : Submodule ℂ W, (∀ o, ∀ x ∈ P, A o x ∈ P) → (∀ o, ∀ x ∈ Q, A o x ∈ Q) →
      ∀ o, ∀ x ∈ P ⊔ Q, A o x ∈ P ⊔ Q := by
    intro P Q hP hQ o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem_sup (hP o y hy) (hQ o z hz)
  have hfs : ∀ t : Finset (Fin s), ∀ o, ∀ x ∈ t.sup V, A o x ∈ t.sup V := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro o x hx
      simp only [Finset.sup_empty, Submodule.mem_bot] at hx ⊢
      rw [hx, map_zero]
    | insert j t hj ih =>
      rw [Finset.sup_insert]
      exact hsup _ _ (h j) ih
  have key : ∀ t : Finset (Fin s), ∀ i, i ∉ t → Disjoint (V i) (t.sup V) := by
    intro t
    induction t using Finset.induction_on with
    | empty => intro i _; simp
    | insert j t hj ih =>
      intro i hi
      rw [Finset.mem_insert, not_or] at hi
      obtain ⟨hij, hit⟩ := hi
      have hSinv := hfs t
      have hiS := ih i hit
      have hjS := ih j hj
      rw [Finset.sup_insert, disjoint_iff]
      set S := t.sup V with hSdef
      by_cases hVi : V i = ⊥
      · rw [hVi, bot_inf_eq]
      have hM : ∀ o, ∀ x ∈ V i ⊓ (V j ⊔ S), A o x ∈ V i ⊓ (V j ⊔ S) :=
        fun o x hx => ⟨h i o x hx.1, hsup _ _ (h j) hSinv o x hx.2⟩
      rcases hs i _ inf_le_left hM with hbot | htop
      · exact hbot
      exfalso
      have hle : V i ≤ V j ⊔ S := inf_eq_left.mp htop
      have huniq : ∀ y y' : V j, ((y : W) - y') ∈ S → y = y' := by
        intro y y' hyy
        have h0 : ((y : W) - y') ∈ V j ⊓ S := ⟨sub_mem y.2 y'.2, hyy⟩
        rw [disjoint_iff.mp hjS, Submodule.mem_bot, sub_eq_zero] at h0
        exact Subtype.ext h0
      let fj : V j →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V j).subtype
      have hfj : Function.Injective fj := by
        intro a b hab
        exact huniq a b ((Submodule.Quotient.eq S).mp hab)
      let ej := LinearEquiv.ofInjective fj hfj
      let fi : V i →ₗ[ℂ] W ⧸ S := S.mkQ ∘ₗ (V i).subtype
      have hrange : ∀ x : V i, fi x ∈ LinearMap.range fj := by
        intro x
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hle x.2)
        refine ⟨⟨y, hy⟩, ?_⟩
        show S.mkQ y = S.mkQ x
        rw [← hyz, map_add, Submodule.mkQ_apply S z, (Submodule.Quotient.mk_eq_zero S).mpr hz,
          add_zero]
      let T : V i →ₗ[ℂ] V j := ej.symm.toLinearMap ∘ₗ (fi.codRestrict (LinearMap.range fj) hrange)
      have hT : ∀ x : V i, ((T x : W) - x) ∈ S := by
        intro x
        have e0 : T x = ej.symm ⟨fi x, hrange x⟩ := rfl
        have e1 := ej.apply_symm_apply ⟨fi x, hrange x⟩
        rw [Subtype.ext_iff, LinearEquiv.ofInjective_apply, ← e0] at e1
        exact (Submodule.Quotient.eq S).mp e1
      have hTeq : ∀ o (x : V i), T ((A o).restrict (h i o) x) = (A o).restrict (h j o) (T x) := by
        intro o x
        apply huniq
        have e1 := hT ((A o).restrict (h i o) x)
        have e2 : A o ((T x : W) - x) ∈ S := hSinv o _ (hT x)
        have e3 : ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h j o) (T x) : W))
            = ((T ((A o).restrict (h i o) x) : W) - ((A o).restrict (h i o) x : W))
              - A o ((T x : W) - x) := by
          simp only [LinearMap.restrict_coe_apply, map_sub]
          abel
        rw [e3]
        exact sub_mem e1 e2
      have hTinj : Function.Injective T := by
        rw [← LinearMap.ker_eq_bot, eq_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker] at hx
        have e1 := hT x
        rw [hx, Submodule.coe_zero, zero_sub] at e1
        have hxS : (x : W) ∈ S := by simpa using S.neg_mem e1
        have e2 : (x : W) ∈ V i ⊓ S := ⟨x.2, hxS⟩
        rw [disjoint_iff.mp hiS, Submodule.mem_bot] at e2
        exact (Submodule.mem_bot ℂ).mpr (Subtype.ext e2)
      let N := (LinearMap.range T).map (V j).subtype
      have hNle : N ≤ V j := Submodule.map_subtype_le _ _
      have hNinv : ∀ o, ∀ x ∈ N, A o x ∈ N := by
        intro o x hx
        obtain ⟨y, ⟨z, rfl⟩, rfl⟩ := hx
        refine ⟨T ((A o).restrict (h i o) z), ⟨_, rfl⟩, ?_⟩
        rw [hTeq]
        rfl
      have hTsurj : Function.Surjective T := by
        rcases hs j N hNle hNinv with hN0 | hNj
        · exfalso
          obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hVi
          have hmem : ((T ⟨x, hx⟩ : V j) : W) ∈ N := ⟨T ⟨x, hx⟩, ⟨_, rfl⟩, rfl⟩
          rw [hN0, Submodule.mem_bot] at hmem
          have : T ⟨x, hx⟩ = T 0 := by rw [map_zero]; exact Subtype.ext hmem
          exact hx0 (congrArg Subtype.val (hTinj this))
        · intro y
          have hy : (y : W) ∈ N := by rw [hNj]; exact y.2
          obtain ⟨y', ⟨z, rfl⟩, hz⟩ := hy
          exact ⟨z, Subtype.ext hz⟩
      exact hn i j hij ⟨LinearEquiv.ofBijective T ⟨hTinj, hTsurj⟩, hTeq⟩
  rw [iSupIndep_iff_supIndep]
  intro t u _ i _ hiu
  exact key u i hiu
