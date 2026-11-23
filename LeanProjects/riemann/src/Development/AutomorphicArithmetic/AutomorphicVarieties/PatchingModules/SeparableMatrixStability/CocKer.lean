import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem closed_zero {Γ K : Type} [TopologicalSpace Γ] [Field K] {f : Γ → PowerSeries K}
    (hf : AdicCont (Ideal.span {(PowerSeries.X : PowerSeries K)}) f) : IsClosed {g | f g = 0} := by
  have hset : {g | f g = 0} = ⋂ N : ℕ,
      {g | Ideal.Quotient.mk ((Ideal.span {(PowerSeries.X : PowerSeries K)}) ^ N) (f g) = 0} := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    constructor
    · intro h N
      rw [h]
      exact dvd_zero _
    · intro h
      ext n
      have := (PowerSeries.X_pow_dvd_iff).1 (h (n + 1)) n (Nat.lt_succ_self n)
      simpa using this
  rw [hset]
  exact isClosed_iInter fun N => (hf N).isClosed_fiber 0

theorem UpperTheory.V.Pa.coc_ker :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (s : Set G.G₀) (z : G.G₀ → Matrix (Fin n) (Fin n) x.A), h.p.ker ≤ (Subgroup.normalClosure (Subtype.val '' s)).topologicalClosure → (∀ a ∈ s, h.p₀ a = 1 ∧ z a = 0) → z ∈ SelM h x x.A → ∃ y : G0.G₀ → Matrix (Fin n) (Fin n) x.A, ∀ g, y (h.p₀ g) = z g := by
  intro l _ L G G0 h n x s z hker hs hz
  obtain ⟨-, hcont, hcoc, hconj, -, -⟩ := hz
  have coc : ∀ g k : G.G₀,
      z (g * k) = z g + x.ρX x.A (h.p₀ g) * z k * x.ρX x.A (h.p₀ g⁻¹) := hcoc
  have hρ1 : ∀ g : G.G₀, h.p₀ g = 1 → x.ρX x.A (h.p₀ g) = 1 := by
    intro g hg
    rw [hg]
    simp [NP.ρX]
  have hz1 : z 1 = 0 := by
    have e := coc 1 1
    rw [hρ1 1 (map_one _), inv_one, hρ1 1 (map_one _), one_mul, mul_one] at e
    simpa using e
  have hR : ∀ g k : G.G₀, z k = 0 → z (g * k) = z g := by
    intro g k hk
    rw [coc, hk]
    simp
  let H : Subgroup G.G₀ :=
    { carrier := {k | h.p₀ k = 1 ∧ z k = 0}
      one_mem' := ⟨map_one _, hz1⟩
      mul_mem' := by
        rintro a b ⟨ha, za⟩ ⟨hb, zb⟩
        refine ⟨by rw [map_mul, ha, hb, one_mul], ?_⟩
        rw [hR a b zb, za]
      inv_mem' := by
        rintro a ⟨ha, za⟩
        refine ⟨by rw [map_inv, ha, inv_one], ?_⟩
        have e := hR a⁻¹ a za
        rw [inv_mul_cancel, hz1] at e
        exact e.symm }
  have hHconj : ∀ g k : G.G₀, k ∈ H → g * k * g⁻¹ ∈ H := by
    rintro g k ⟨hk1, hk2⟩
    refine ⟨by rw [map_mul, map_mul, hk1, mul_one, map_inv, mul_inv_cancel], ?_⟩
    have hkg : z (k * g⁻¹) = z g⁻¹ := by
      rw [coc, hk2, hρ1 k hk1]
      have : h.p₀ k⁻¹ = 1 := by rw [map_inv, hk1, inv_one]
      rw [hρ1 _ this]
      simp
    rw [mul_assoc, coc, hkg, ← coc, mul_inv_cancel, hz1]
  have hHc : ∀ k : G.G₀, k ∈ H → G.frame.conj k ∈ H := by
    rintro k ⟨hk1, hk2⟩
    refine ⟨?_, ?_⟩
    · rw [h.p₀_conj, hk1, map_one]
    · rw [hconj, hk2]
      simp
  let N : Subgroup G.Γ := H.map G.η.ker.subtype
  have hN : N.Normal := by
    constructor
    intro m hm γ
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hm
    rcases Int.units_eq_one_or (G.η γ) with hγ | hγ
    · have e : γ * (k : G.Γ) * γ⁻¹ = (((⟨γ, hγ⟩ : G.G₀) * k * (⟨γ, hγ⟩ : G.G₀)⁻¹ : G.G₀) : G.Γ) := rfl
      exact Subgroup.mem_map.2 ⟨_, hHconj _ _ hk, e.symm⟩
    · have hg : G.c⁻¹ * γ ∈ G.η.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, G.η_c, hγ]
        rfl
      let g : G.G₀ := ⟨G.c⁻¹ * γ, hg⟩
      have e : γ * (k : G.Γ) * γ⁻¹ = ((G.frame.conj (g * k * g⁻¹) : G.G₀) : G.Γ) := by
        show γ * (k : G.Γ) * γ⁻¹ = G.c * ((G.c⁻¹ * γ) * (k : G.Γ) * (G.c⁻¹ * γ)⁻¹) * G.c⁻¹
        group
      exact Subgroup.mem_map.2 ⟨_, hHc _ (hHconj _ _ hk), e.symm⟩
  have hHclosed : IsClosed (H : Set G.G₀) := by
    have e1 : (H : Set G.G₀) = {k | h.p₀ k = 1} ∩ ⋂ i, ⋂ j, {k | z k i j = 0} := by
      ext k
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, fun i j => by rw [h2]; rfl⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, Matrix.ext fun i j => h2 i j⟩
    rw [e1]
    exact IsClosed.inter ((isClosed_singleton (x := (1 : G0.G₀))).preimage h.p₀_cont)
      (isClosed_iInter fun i => isClosed_iInter fun j => closed_zero (hcont i j))
  have hNclosed : IsClosed (N : Set G.Γ) := by
    show IsClosed (Subtype.val '' (H : Set G.G₀))
    exact hHclosed.trans (Subgroup.isClosed_of_isOpen _ G.η_open)
  have hsN : Subtype.val '' s ⊆ (N : Set G.Γ) := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.2 ⟨a, ⟨(hs a ha).1, (hs a ha).2⟩, rfl⟩
  have hkerN : h.p.ker ≤ N :=
    hker.trans (Subgroup.topologicalClosure_minimal _
      (Subgroup.normalClosure_le_normal (N := N) hsN) hNclosed)
  have hfac : ∀ g g' : G.G₀, h.p₀ g = h.p₀ g' → z g = z g' := by
    intro g g' e
    have h1 : h.p₀ (g⁻¹ * g') = 1 := by rw [map_mul, map_inv, e, inv_mul_cancel]
    have h2 : ((g⁻¹ * g' : G.G₀) : G.Γ) ∈ h.p.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val h1
    obtain ⟨k, hk, hk'⟩ := Subgroup.mem_map.1 (hkerN h2)
    have hkk : k = g⁻¹ * g' := Subtype.ext hk'
    rw [hkk] at hk
    have e2 := hR g _ hk.2
    rw [mul_inv_cancel_left] at e2
    exact e2.symm
  exact ⟨fun g0 => z (Classical.choose (h.p₀_surj g0)),
    fun g => hfac _ _ (Classical.choose_spec (h.p₀_surj (h.p₀ g)))⟩
