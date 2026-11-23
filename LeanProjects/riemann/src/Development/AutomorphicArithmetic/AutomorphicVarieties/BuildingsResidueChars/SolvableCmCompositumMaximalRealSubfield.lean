import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SignAgreement.ExistsCompositumWithPrimeDegreeGalois
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Published UpperTheory.V.Af.Sol

private theorem rcsup_mem_real {L M' : Type} [Field L] [Field M'] (f : L →+* M') (hL : IsTotallyReal L) (x : L) :
    f x ∈ maximalRealSubfield M' := by
  intro φ
  have h : x ∈ maximalRealSubfield L := by
    rw [IsTotallyReal.maximalRealSubfield_eq_top]; trivial
  exact h (φ.comp f)

private theorem rcsup_map_real {M M' : Type} [Field M] [Field M'] (g : M →+* M') {x : M}
    (hx : x ∈ maximalRealSubfield M) : g x ∈ maximalRealSubfield M' :=
  fun φ => hx (φ.comp g)

private theorem rcsup_cm_of_pair {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (d : K) (hd0 : d ≠ 0)
    (hd : ∀ φ : K →+* ℂ, star (φ d) = - φ d)
    (hspan : ∀ y : K, ∃ a ∈ maximalRealSubfield K, ∃ b ∈ maximalRealSubfield K, y = a + b * d) :
    IsCMField K := by
  have hli : LinearIndependent (maximalRealSubfield K) ![(1 : K), d] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    let φ : K →+* ℂ := Classical.choice (inferInstance : Nonempty _)
    have h0 : (s : K) + (t : K) * d = 0 := by
      simpa [Subfield.smul_def] using hst
    have h1 : φ s + φ t * φ d = 0 := by
      rw [← map_mul, ← map_add, h0, map_zero]
    have h2 : φ s - φ t * φ d = 0 := by
      have := congrArg star h1
      rw [star_add, star_mul', s.2 φ, t.2 φ, hd φ, star_zero] at this
      linear_combination this
    have h3 : φ s = 0 := by linear_combination (h1 + h2) / 2
    have hs : (s : K) = 0 := (map_eq_zero φ).mp h3
    have ht : (t : K) = 0 := by
      rw [hs, zero_add] at h0
      exact (mul_eq_zero.mp h0).resolve_right hd0
    exact ⟨Subtype.ext hs, Subtype.ext ht⟩
  have hsp : ⊤ ≤ Submodule.span (maximalRealSubfield K) (Set.range ![(1 : K), d]) := by
    intro y _
    obtain ⟨a, ha, b, hb, rfl⟩ := hspan y
    have e : a + b * d = (⟨a, ha⟩ : maximalRealSubfield K) • (1 : K) + (⟨b, hb⟩ : maximalRealSubfield K) • d := by
      simp [Subfield.smul_def]
    rw [e]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  have hrk : Module.finrank (maximalRealSubfield K) K = 2 := by
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)]
    simp
  haveI : Algebra.IsQuadraticExtension (maximalRealSubfield K) K := { finrank_eq_two' := hrk }
  exact {}

theorem UpperTheory.solvable_cm_compositum_maximalRealSubfield :
    UpperTheory.V.Af.Sol.RCSup := by
  intro L M M' _ _ _ _ _ _ _ f hL htop hM
  rcases hM with hM | hM
  · left
    rw [← maximalRealSubfield_eq_top_iff_isTotallyReal, eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx => obtain ⟨z, rfl⟩ := hx; exact rcsup_mem_real f hL z
    | algebraMap r => exact rcsup_mem_real _ hM r
    | add x y _ _ hx hy => exact add_mem (hx trivial) (hy trivial)
    | mul x y _ _ hx hy => exact mul_mem (hx trivial) (hy trivial)
  · right
    haveI : IsTotallyComplex M' := isTotallyComplex_of_algebra M M'
    obtain ⟨x, hx⟩ : ∃ x : M, IsCMField.complexConj M x ≠ x := by
      by_contra h
      apply IsCMField.complexConj_ne_one M
      ext x
      by_contra h'
      exact h ⟨x, h'⟩
    set δ : M := x - IsCMField.complexConj M x with hδ
    have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hx.symm
    have hcδ : IsCMField.complexConj M δ = -δ := by
      rw [hδ, map_sub, IsCMField.complexConj_apply_apply]; ring
    have hd : ∀ φ : M' →+* ℂ, star (φ (algebraMap M M' δ)) = - φ (algebraMap M M' δ) := by
      intro φ
      have := IsCMField.complexEmbedding_complexConj M (φ.comp (algebraMap M M')) δ
      rw [hcδ, map_neg] at this
      exact this.symm
    have hsq : algebraMap M M' δ * algebraMap M M' δ ∈ maximalRealSubfield M' := by
      intro φ
      rw [map_mul, star_mul', hd φ]; ring
    refine rcsup_cm_of_pair (algebraMap M M' δ) ((_root_.map_ne_zero _).mpr hδ0) hd ?_
    intro y
    have hy : y ∈ Algebra.adjoin M (Set.range f) := htop ▸ Algebra.mem_top
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨z, rfl⟩ := hx
      exact ⟨f z, rcsup_mem_real f hL z, 0, zero_mem _, by simp⟩
    | algebraMap r =>
      refine ⟨algebraMap M M' ((r + IsCMField.complexConj M r) / 2), rcsup_map_real _ ?_,
        algebraMap M M' ((r - IsCMField.complexConj M r) / (2 * δ)), rcsup_map_real _ ?_, ?_⟩
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_add, IsCMField.complexConj_apply_apply, map_ofNat, add_comm]
      · rw [← IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, IsCMField.complexConj_apply_apply, map_ofNat, hcδ]
        field_simp
        ring
      · rw [← map_mul, ← map_add]
        congr 1
        field_simp
        ring
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a + a', add_mem ha ha', b + b', add_mem hb hb', by ring⟩
    | mul x y _ _ hx hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨a', ha', b', hb', rfl⟩ := hy
      exact ⟨a * a' + b * b' * (algebraMap M M' δ * algebraMap M M' δ),
        add_mem (mul_mem ha ha') (mul_mem (mul_mem hb hb') hsq),
        a * b' + b * a', add_mem (mul_mem ha hb') (mul_mem hb ha'), by ring⟩
