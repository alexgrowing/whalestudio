import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.SymmetricPowerSymbols.SymExOf

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

private def Nr (X : Tower Ω ε) (f : X.K) : Prop :=
  ∃ T : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ z ∈ T, s z = z) → X.gal s f = f

private theorem exp_inj (X : Tower Ω ε) : Function.Injective X.exp := X.exp.toRingHom.injective

private theorem nr_j (X : Tower Ω ε) : Nr X X.jK := by
  refine ⟨∅, fun s _ => exp_inj X ?_⟩
  ext r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [X.gal_exp, hn, map_intCast]

private theorem nr_c (X : Tower Ω ε) (c : Ω) : Nr X (algebraMap Ω X.K c) := by
  refine ⟨{c}, fun s hs => exp_inj X ?_⟩
  ext r
  rw [X.gal_exp, AlgHom.commutes, HahnSeries.algebraMap_apply']
  by_cases h : r = 0 <;> simp [h, hs c (Finset.mem_singleton_self c)]

private theorem nr_two (X : Tower Ω ε) {f g : X.K} (hf : Nr X f) (hg : Nr X g) :
    ∃ T : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ z ∈ T, s z = z) → X.gal s f = f ∧ X.gal s g = g := by
  classical
  obtain ⟨A, hA⟩ := hf
  obtain ⟨B, hB⟩ := hg
  exact ⟨A ∪ B, fun s hs => ⟨hA s fun z hz => hs z (Finset.mem_union_left _ hz),
    hB s fun z hz => hs z (Finset.mem_union_right _ hz)⟩⟩

private theorem nr_adj (X : Tower Ω ε) (f : X.K) (hf : f ∈ IntermediateField.adjoin Ω {X.jK}) : Nr X f := by
  induction hf using IntermediateField.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact nr_j X
  | algebraMap c => exact nr_c X c
  | add x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := nr_two X hx hy
    exact ⟨T, fun s hs => by rw [map_add, (hT s hs).1, (hT s hs).2]⟩
  | inv x _ hx =>
    obtain ⟨T, hT⟩ := hx
    exact ⟨T, fun s hs => by rw [map_inv₀, hT s hs]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨T, hT⟩ := nr_two X hx hy
    exact ⟨T, fun s hs => by rw [map_mul, (hT s hs).1, (hT s hs).2]⟩

end

theorem UpperTheory.V.Z.Kato.Sym.PC.galNear :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (f : X.K), ∃ T : Finset Ω, ∀ s : Ω ≃ₐ[ℚ] Ω, (∀ z ∈ T, s z = z) → X.gal s f = f := by
  intro Ω _ _ _ ε X f
  classical
  obtain ⟨p, hp0, hpf⟩ := X.alg_j f
  set q : Polynomial X.K := p.map (algebraMap _ X.K) with hq
  have hq0 : q ≠ 0 := Polynomial.map_ne_zero hp0
  have hqf : q.eval f = 0 := by
    rw [hq, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hpf
  have hc : ∀ i, Nr X (q.coeff i) := fun i => by
    rw [hq, Polynomial.coeff_map, IntermediateField.algebraMap_apply]
    exact nr_adj X _ (p.coeff i).2
  have hd : ∀ b, b ≠ f → ∃ r, (X.exp b).coeff r ≠ (X.exp f).coeff r := by
    intro b hb
    by_contra h
    push_neg at h
    exact hb (exp_inj X (HahnSeries.ext (funext h)))
  choose TC hTC using hc
  choose! rr hrr using hd
  refine ⟨(q.support.biUnion TC) ∪ ((q.roots.toFinset.erase f).image (fun b => (X.exp f).coeff (rr b))), ?_⟩
  intro s hs
  have hfix : ∀ i, X.gal s (q.coeff i) = q.coeff i := by
    intro i
    by_cases hi : i ∈ q.support
    · exact hTC i s fun z hz => hs z (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, hi, hz⟩))
    · rw [Polynomial.notMem_support_iff.mp hi, map_zero]
  have hmap : q.map (X.gal s).toRingHom = q := by
    ext i
    rw [Polynomial.coeff_map]
    exact hfix i
  have hroot : q.eval (X.gal s f) = 0 := by
    have h1 : (q.map (X.gal s).toRingHom).eval ((X.gal s).toRingHom f) = (X.gal s).toRingHom (q.eval f) := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    rw [hmap, hqf, map_zero] at h1
    exact h1
  by_contra hne
  have hb : X.gal s f ∈ q.roots.toFinset.erase f :=
    Finset.mem_erase.mpr ⟨hne, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq0).mpr hroot)⟩
  have hsz := hs ((X.exp f).coeff (rr (X.gal s f)))
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hb, rfl⟩))
  apply hrr _ hne
  rw [X.gal_exp, hsz]
