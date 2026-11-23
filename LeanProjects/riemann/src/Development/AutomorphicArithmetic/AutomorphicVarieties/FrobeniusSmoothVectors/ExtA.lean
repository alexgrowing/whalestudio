import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MemPowSmulLe

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ext_A :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [Algebra O C] (ξ ξ' : S.A →ₐ[O] C), S.u.map (ξ : S.A →+* C) = S.u.map (ξ' : S.A →+* C) → S.x0 ≤ (maximalIdeal C).comap (ξ : S.A →+* C) → S.x0 ≤ (maximalIdeal C).comap (ξ' : S.A →+* C) → ξ = ξ' := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ _ ξ ξ' hu h1 h2
  obtain ⟨-, -, -, hc⟩ := UpperTheory.V.Fr.cont_u hF hn S
  let E : Subalgebra O S.R := (AlgHom.equalizer ξ ξ').map S.A.val
  have hE : ∀ a : S.A, (a : S.R) ∈ E ↔ ξ a = ξ' a := fun a =>
    ⟨fun ⟨b, hb, h⟩ => (Subtype.ext h : b = a) ▸ hb, fun h => ⟨a, h, rfl⟩⟩
  have hr : ∀ g i j, S.ρ.r g i j ∈ E := fun g i j =>
    (hE (S.u.r g i j)).2 (congrArg (fun ρ : NRep F n C => ρ.r g i j) hu)
  have hψ : ∀ v i g, (S.ρ.ψ v i g : S.R) ∈ E := fun v i g =>
    (hE (S.u.ψ v i g : S.A)).2 (congrArg (fun ρ : NRep F n C => (ρ.ψ v i g : C)) hu)
  have h0 : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ E := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨L, -, rfl⟩ | ⟨v, i, g, rfl⟩)
    · refine Subalgebra.list_prod_mem E fun y hy => ?_
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
      exact hr _ _ _
    · exact hψ v i g
  have hpow : ∀ (f : S.A →ₐ[O] C), S.x0 ≤ (maximalIdeal C).comap (f : S.A →+* C) → ∀ (N : ℕ) (a : S.A),
      a ∈ S.mB ^ N • S.gr 0 → f a ∈ maximalIdeal C ^ N := by
    intro f hf N a ha
    refine Submodule.smul_induction_on ha (fun b hb y _ => ?_) fun x y hx hy => ?_
    · rw [Algebra.smul_def, map_mul]
      refine Ideal.mul_mem_right _ _ ?_
      have h3 : algebraMap S.B S.A b ∈ S.x0 ^ N := by
        have := Ideal.mem_map_of_mem (S.inc : S.B →+* S.A) hb
        rw [Ideal.map_pow] at this
        exact this
      have h4 := Ideal.pow_right_mono hf N h3
      exact Ideal.le_comap_pow (f : S.A →+* C) N h4
    · rw [map_add]
      exact add_mem hx hy
  have hB : S.B ≤ E := by
    intro b hb
    refine (hE ⟨b, S.B_le_A hb⟩).2 ?_
    rw [← sub_eq_zero, ← Ideal.mem_bot,
      ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal C) (maximalIdeal.isMaximal C).ne_top, Ideal.mem_iInf]
    intro N
    obtain ⟨M, hM⟩ := hc 0 N
    obtain ⟨y, hy, hby⟩ := hb M
    have hyB : y ∈ S.B := le_adicClosure _ hy
    have hg : S.inc ⟨b - y, sub_mem hb hyB⟩ ∈ S.gr 0 := by
      have h5 : (1 : S.A) ∈ S.gr 0 := Submodule.subset_span ⟨[], by simp, by simp⟩
      have h6 := Submodule.smul_mem _ (⟨b - y, sub_mem hb hyB⟩ : S.B) h5
      rw [Algebra.smul_def, mul_one] at h6
      exact h6
    have hm := hM _ hg hby
    have he : ξ ⟨y, S.B_le_A hyB⟩ = ξ' ⟨y, S.B_le_A hyB⟩ := (hE _).1 (h0 hy)
    have hs : (⟨b, S.B_le_A hb⟩ : S.A) = S.inc ⟨b - y, sub_mem hb hyB⟩ + ⟨y, S.B_le_A hyB⟩ :=
      Subtype.ext (sub_add_cancel b y).symm
    rw [hs, map_add, map_add, he, add_sub_add_right_eq_sub]
    exact sub_mem (hpow ξ h1 N _ hm) (hpow ξ' h2 N _ hm)
  have hA : S.A ≤ E := by
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · exact hB hx
    · exact hr g i j
  exact AlgHom.ext fun a => (hE a).1 (hA a.2)
