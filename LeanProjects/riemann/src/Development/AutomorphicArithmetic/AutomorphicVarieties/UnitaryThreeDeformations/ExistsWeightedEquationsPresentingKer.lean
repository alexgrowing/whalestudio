import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.AbsDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HomogSpan
open IsLocalRing MvPowerSeries UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia.Abs

private theorem coeff_single_mul {O σ : Type} [CommRing O] (i : σ) (a g : MvPowerSeries σ O)
    (hg : constantCoeff g = 0) :
    coeff (Finsupp.single i 1) (a * g) = constantCoeff a * coeff (Finsupp.single i 1) g := by
  classical
  rw [coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
  simp [Finset.Nat.antidiagonal_succ, hg]

private noncomputable def pad {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) (n : ℕ) (k : Fin n) : FA O wt :=
  if h : k.val < b then mkF (f ⟨k.val, h⟩) (hf _) else 0

private theorem pad_ind {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) (n : ℕ) (k : Fin n)
    (P : FA O wt → Prop) (h0 : P 0) (h1 : ∀ i, P (mkF (f i) (hf i))) : P (pad f hf n k) := by
  unfold pad
  split_ifs
  · exact h1 _
  · exact h0

private theorem pad_range {O σ : Type} [CommRing O] [Fintype σ] {wt : σ → ℤ} {j : ℤ} {b : ℕ}
    (f : Fin b → MvPowerSeries σ O) (hf : ∀ i, f i ∈ wtPart O wt j) {n : ℕ} (h : b ≤ n) (i : Fin b) :
    mkF (f i) (hf i) ∈ Set.range (pad f hf n) :=
  ⟨⟨i.val, lt_of_lt_of_le i.2 h⟩, by simp [pad]⟩

private theorem der_zero {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R) (ho : W.HasOrigin)
    (b : ℤ → ℕ) (f : (j : ℤ) → Fin (b j) → MvPowerSeries W.σ O) (hf : ∀ j i, f j i ∈ wtPart O W.wt j)
    (hk : RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j))) (j0 : ℤ) (n : ℕ) (hn : b j0 ≤ n)
    (N : Type) [AddCommGroup N] [Module O N] (d : W.σ → N) (hd : ∀ i, W.wt i ≠ j0 → d i = 0)
    (hF : ∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (pad (f j0) (hf j0) n k)) • d i = 0)
    (g : MvPowerSeries W.σ O) (hg : W.π g = 0) : ∑ i, coeff (Finsupp.single i 1) g • d i = 0 := by
  have hg' : g ∈ Ideal.span (⋃ j, Set.range (f j)) := hk ▸ hg
  clear hg
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.1 hx
    by_cases hj : j = j0
    · subst hj
      obtain ⟨k, e⟩ := pad_range (f j) (hf j) hn i
      have := hF k
      rwa [e] at this
    · refine Finset.sum_eq_zero fun v _ => ?_
      by_cases hv : W.wt v = j0
      · rw [hf j i _ (by simpa [Finsupp.weight_single, hv] using Ne.symm hj), zero_smul]
      · rw [hd v hv, smul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, add_smul, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul a x hx ih =>
    have h0 : constantCoeff x = 0 := ho x (hk.ge hx)
    simp only [smul_eq_mul, coeff_single_mul _ a x h0, mul_smul, ← Finset.smul_sum, ih, smul_zero]

theorem UpperTheory.exists_weighted_equations_presenting_ker :
    ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R), W.HasOrigin →
        ∀ (b : ℤ → ℕ) (f : (j : ℤ) → Fin (b j) → MvPowerSeries W.σ O), (∀ j i, f j i ∈ wtPart O W.wt j) →
        RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j)) → ∀ r s r' s' m : ℕ,
        b (-1) ≤ r + 1 → b (-2) ≤ s → b 1 ≤ r' → b 2 ≤ s' → b 0 ≤ m → (∀ j, j < -2 ∨ 2 < j → b j = 0) →
        ∃ Q : Eqns (Fgr O W.wt) (x0 O W.wt) r s r' s' m, Q.ideal = RingHom.ker (toA W) ∧
          ∀ (N : Type) [AddCommGroup N] [Module O N] (d : W.σ → N),
            (((∀ i, W.wt i ≠ -1 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.F k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0) ∧
            ((∀ i, W.wt i ≠ -2 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.G k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0) ∧
            ((∀ i, W.wt i ≠ 0 → d i = 0) → (∀ k, ∑ i, coeff (Finsupp.single i 1) (ser (Q.Z k)) • d i = 0) →
              ∀ g, W.π g = 0 → ∑ i, coeff (Finsupp.single i 1) g • d i = 0)) := by
  intro O R _ _ _ W ho b f hf hk r s r' s' m h1 h2 h3 h4 h5 h6
  have hker : ∀ j i, W.π (f j i) = 0 := fun j i => by
    have : f j i ∈ RingHom.ker W.π := hk ▸ Ideal.subset_span (Set.mem_iUnion.2 ⟨j, i, rfl⟩)
    exact this
  have hmem : ∀ j n k, pad (f j) (hf j) n k ∈ Fgr O W.wt j := fun j n k =>
    pad_ind _ _ n k (· ∈ Fgr O W.wt j) (zero_mem _) fun i => mkF_mem _ _
  have hkA : ∀ j n, Set.range (pad (f j) (hf j) n) ⊆ RingHom.ker (toA W) := by
    rintro j n _ ⟨k, rfl⟩
    exact pad_ind _ _ n k (· ∈ RingHom.ker (toA W)) (zero_mem _) fun i => Subtype.ext (hker j i)
  refine ⟨⟨pad (f (-1)) (hf _) _, pad (f (-2)) (hf _) _, pad (f 1) (hf _) _, pad (f 2) (hf _) _,
    pad (f 0) (hf _) _, hmem _ _, hmem _ _, hmem _ _, hmem _ _, fun k => ⟨hmem _ _ _, ?_⟩⟩, ?_,
    fun N _ _ d => ⟨der_zero W ho b f hf hk _ _ h1 N d, der_zero W ho b f hf hk _ _ h2 N d,
      der_zero W ho b f hf hk _ _ h5 N d⟩⟩
  · exact pad_ind _ _ m k (fun y => x0 O W.wt y = 0) (map_zero _) fun i => by
      rw [weightedSeriesOrigin_apply]; exact ho _ (hker 0 i)
  · refine le_antisymm (Ideal.span_le.2 ?_) fun x hx => ?_
    · simp only [Set.union_subset_iff]
      exact ⟨⟨⟨⟨hkA _ _, hkA _ _⟩, hkA _ _⟩, hkA _ _⟩, hkA _ _⟩
    · have hx1 : ser x ∈ RingHom.ker W.π := congrArg Subtype.val (show toA W x = 0 from hx)
      rw [hk] at hx1
      have H := (homog_span O _ ℤ (WPres.free O W.wt) (Σ j : Finset.Icc (-2 : ℤ) 2, Fin (b j))
        (fun p => mkF (f p.1 p.2) (hf _ _)) (fun p => p.1) (fun p => mkF_mem _ _)).2 x
      refine Ideal.span_mono ?_ (H.1 (Ideal.span_mono ?_ hx1))
      · rintro _ ⟨⟨⟨j, hj⟩, i⟩, rfl⟩
        have hj' := Finset.mem_Icc.1 hj
        have : j = -1 ∨ j = -2 ∨ j = 1 ∨ j = 2 ∨ j = 0 := by omega
        rcases this with rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (Or.inl (Or.inl (Or.inl (pad_range _ _ h1 i))))
        · exact Or.inl (Or.inl (Or.inl (Or.inr (pad_range _ _ h2 i))))
        · exact Or.inl (Or.inl (Or.inr (pad_range _ _ h3 i)))
        · exact Or.inl (Or.inr (pad_range _ _ h4 i))
        · exact Or.inr (pad_range _ _ h5 i)
      · intro y hy
        obtain ⟨j, i, rfl⟩ := Set.mem_iUnion.1 hy
        have hj : j ∈ Finset.Icc (-2 : ℤ) 2 := by
          by_contra hc
          have := h6 j (by rw [Finset.mem_Icc] at hc; omega)
          have := i.2
          omega
        exact ⟨⟨⟨j, hj⟩, i⟩, rfl⟩
