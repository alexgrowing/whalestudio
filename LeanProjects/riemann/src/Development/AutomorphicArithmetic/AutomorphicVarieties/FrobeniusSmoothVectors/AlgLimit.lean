import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgFamily
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgGlue

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.alg_limit :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ} (S : Space O F n) (C : Type) [CommRing C] [Algebra O C] [IsCO O C] {D : Type} [CommRing D] [Algebra O D] [Algebra C D] [IsScalarTower O C D] (𝔪 : Ideal D) (ρ : NRep F n D), IsVertexRing C 𝔪 → IsModel O C 𝔪 ρ → ∃ (ξ : S.A →ₐ[O] D) (β : S.B →ₐ[O] C), S.u.map (ξ : S.A →+* D) = ρ ∧ ∀ b, ξ (S.inc b) = algebraMap C D (β b) := by
  intro l _ O _ _ F n S C _ _ _ D _ _ _ _ 𝔪 ρ hV hM
  obtain ⟨f, hf1, hf2, hf3⟩ := alg_family S C 𝔪 ρ hV hM
  haveI : IsAdicComplete (maximalIdeal C) C := IsCO.complete (O := O)
  have hsep : ∀ d d' : D, (∀ N : ℕ, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = Ideal.Quotient.mk (𝔪 ^ (N + 1)) d') → d = d' := by
    intro d d' h
    have hmem : d - d' ∈ ⨅ N, 𝔪 ^ N := by
      refine (Submodule.mem_iInf _).2 fun N => ?_
      cases N with
      | zero => simp
      | succ N => exact Ideal.Quotient.eq.1 (h N)
    rw [hV.sep] at hmem
    exact sub_eq_zero.1 ((Submodule.mem_bot _).1 hmem)
  have hr : ∀ N g i j, f N (S.ρ.r g i j) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ρ.r g i j) := by
    intro N g i j
    have := congrArg (fun σ => σ.r g i j) (hf1 N)
    simpa only [NRep.map_r, AlgHom.coe_toRingHom] using this
  have hψ : ∀ N v i g, f N ((S.ρ.ψ v i g : S.R)) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ρ.ψ v i g : D) := by
    intro N v i g
    have := congrArg (fun σ => ((σ.ψ v i g : Units _) : D ⧸ 𝔪 ^ (N + 1))) (hf1 N)
    simpa only [NRep.map_ψ, AlgHom.coe_toRingHom] using this
  let T' : Subalgebra O S.R :=
    { carrier := {x | ∃ c : C, ∀ N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D c) = f N x}
      mul_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c * c', fun N => by simp only [map_mul, hc, hc']⟩
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c + c', fun N => by simp only [map_add, hc, hc']⟩
      algebraMap_mem' := fun a => ⟨algebraMap O C a, fun N => by
        rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
        rfl⟩ }
  let T : Subalgebra O S.R :=
    { carrier := {x | ∃ d : D, ∀ N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) d = f N x}
      mul_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c * c', fun N => by simp only [map_mul, hc, hc']⟩
      add_mem' := by
        rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
        exact ⟨c + c', fun N => by simp only [map_add, hc, hc']⟩
      algebraMap_mem' := fun a => ⟨algebraMap O D a, fun N => by
        rw [AlgHom.commutes]
        rfl⟩ }
  have hgen : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ↑((S.ρ.ψ v i) g)}) ≤ T' := by
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨v, i, g, rfl⟩)
    · obtain ⟨L, hL, rfl⟩ := hx
      obtain ⟨c, hc⟩ := hM.mon _ ⟨L, hL, rfl⟩
      refine ⟨c, fun N => ?_⟩
      rw [hc, map_list_prod, map_list_prod, List.map_map, List.map_map]
      congr 1
      refine List.map_congr_left ?_
      intro s _
      simp only [Function.comp, hr]
    · obtain ⟨c, hc, -⟩ := hM.psi v i g
      exact ⟨c, fun N => by rw [hc, hψ]⟩
  have hB : S.B ≤ T' := by
    intro x hx
    have hx' : ∀ N : ℕ, ∃ y ∈ Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = ↑((S.ρ.ψ v i) g)}), x - y ∈ maximalIdeal S.R ^ N := hx
    choose y hy hxy using hx'
    choose c hc using fun N => hgen (hy (N + 1))
    have hfx : ∀ N M, N + 1 ≤ M → f N x = f N (y M) := by
      intro N M hNM
      have h0 := hf3 N _ (Ideal.pow_le_pow_right hNM (hxy M))
      rw [map_sub, sub_eq_zero] at h0
      exact h0
    have hcau : ∀ N : ℕ, algebraMap C D (c (N + 1) - c N) ∈ 𝔪 ^ (N + 1) := by
      intro N
      rw [map_sub]
      refine Ideal.Quotient.eq.1 ?_
      rw [hc, hc, ← hfx N (N + 1 + 1) (by omega), ← hfx N (N + 1) le_rfl]
    obtain ⟨z, hz⟩ := alg_closed C 𝔪 hV c hcau
    refine ⟨z, fun N => ?_⟩
    have h1 : Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D z) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D (c N)) := by
      refine Ideal.Quotient.eq.2 ?_
      rw [← map_sub]
      exact hz N
    rw [h1, hc, ← hfx N (N + 1) le_rfl]
  have hA : S.A ≤ T := by
    show Algebra.adjoin O ((S.B : Set S.R) ∪ {x | ∃ g i j, x = S.ρ.r g i j}) ≤ T
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · obtain ⟨c, hc⟩ := hB hx
      exact ⟨algebraMap C D c, hc⟩
    · exact ⟨ρ.r g i j, fun N => (hr N g i j).symm⟩
  obtain ⟨ξ, hξ⟩ := alg_glue (A := S.A) 𝔪 hV.sep (fun N => (f N).comp S.A.val) (fun a => by
    obtain ⟨d, hd⟩ := hA a.2
    exact ⟨d, fun N => by simpa using hd N⟩)
  have hξ' : ∀ (a : S.A) N, Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ξ a) = f N (a : S.R) := by
    intro a N
    simpa using hξ a N
  let φ := IsScalarTower.toAlgHom O C D
  have hmem : ∀ b, (ξ.comp S.inc) b ∈ φ.range := by
    intro b
    obtain ⟨c, hc⟩ := hB b.2
    refine (AlgHom.mem_range φ).2 ⟨c, ?_⟩
    refine hsep _ _ fun N => ?_
    show Ideal.Quotient.mk (𝔪 ^ (N + 1)) (algebraMap C D c) = Ideal.Quotient.mk (𝔪 ^ (N + 1)) (ξ (S.inc b))
    rw [hc, hξ']
    rfl
  let e := AlgEquiv.ofInjective φ hV.inj
  refine ⟨ξ, e.symm.toAlgHom.comp ((ξ.comp S.inc).codRestrict φ.range hmem), ?_, ?_⟩
  · refine NRep.ext ?_ ?_
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      rw [NRep.map_r]
      refine hsep _ _ fun N => ?_
      rw [← hr]
      exact hξ' _ N
    · funext v i
      refine MonoidHom.ext fun g => Units.ext ?_
      rw [NRep.map_ψ]
      refine hsep _ _ fun N => ?_
      rw [← hψ]
      exact hξ' _ N
  · intro b
    have h1 : ((e (e.symm ⟨ξ (S.inc b), hmem b⟩) : φ.range) : D) = φ (e.symm ⟨ξ (S.inc b), hmem b⟩) :=
      AlgEquiv.ofInjective_apply _ _ _
    rw [AlgEquiv.apply_symm_apply] at h1
    exact h1
