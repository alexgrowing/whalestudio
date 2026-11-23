import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.WPresEx

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

private theorem wtPart_decomp {O σ : Type} [CommRing O] (wt : σ → ℤ) (j : ℤ) (s : Finset σ) :
    ∀ f ∈ wtPart O wt j, (∀ n : σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0) →
      ∃ g : σ → MvPowerSeries σ O, (∀ i, g i ∈ wtPart O wt (j - wt i)) ∧
        f = ∑ i ∈ s, MvPowerSeries.X i * g i := by
  classical
  intro f hf hs
  let P : (σ →₀ ℕ) → σ → Prop := fun n i => ∃ h : ∃ k ∈ s, n k ≠ 0, h.choose = i
  let g : σ → MvPowerSeries σ O := fun i m =>
    if P (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hg : ∀ i m, MvPowerSeries.coeff m (g i) =
      if P (m + Finsupp.single i 1) i then MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 :=
    fun _ _ => rfl
  refine ⟨g, fun i m hm => ?_, ?_⟩
  · rw [hg]
    split_ifs
    · apply hf
      rw [map_add]
      intro h
      apply hm
      have : (Finsupp.weight wt) (Finsupp.single i 1) = wt i := by
        rw [Finsupp.weight_apply, Finsupp.sum_single_index] <;> simp
      omega
    · rfl
  · have key : ∀ n i, MvPowerSeries.coeff n (MvPowerSeries.X i * g i) =
        if P n i then MvPowerSeries.coeff n f else 0 := by
      intro n i
      rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
      by_cases hle : Finsupp.single i 1 ≤ n
      · rw [if_pos hle, one_mul, hg, tsub_add_cancel_of_le hle]
      · have hP : ¬ P n i := by
          rintro ⟨h, hc⟩
          apply hle
          rw [Finsupp.single_le_iff, ← hc]
          exact Nat.one_le_iff_ne_zero.mpr h.choose_spec.2
        rw [if_neg hle, if_neg hP]
    ext n
    rw [map_sum]
    simp_rw [key]
    by_cases h : ∃ k ∈ s, n k ≠ 0
    · have hP : ∀ i, P n i ↔ h.choose = i := fun i => ⟨fun ⟨_, e⟩ => e, fun e => ⟨h, e⟩⟩
      simp_rw [hP]
      rw [Finset.sum_ite_eq, if_pos h.choose_spec.1]
    · have hP : ∀ i, ¬ P n i := fun i ⟨h', _⟩ => h h'
      simp only [hP, if_false, Finset.sum_const_zero]
      push_neg at h
      exact hs n h

private theorem vanish_of_entries {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [Group Γ]
    (F : Frame O G Γ ι) {R : Type} [CommRing R] [Algebra O R] (u : Γ →* GG 3 R) (W : WPres O ℤ R)
    (hW : F.Adapted u W) {K : Type} [CommRing K] [Algebra O K] (ξ : Sring O u →ₐ[O] K) (M : AddSubmonoid ℤ)
    (h : ∀ g, F.η g = 1 → ∀ a b, wt a b ∉ M → ptMat u ξ g a b = 0) (j : ℤ) (hj : j ∉ M) (x : R)
    (hx : x ∈ wpart O u j) : ξ ⟨x, mem_Sring u hx⟩ = 0 := by
  classical
  haveI := W.fin
  have hmemz : ∀ i, W.z i ∈ Sring O u := fun i =>
    mem_Sring u (j := W.wt i) (by rw [← hW.part]; exact W.z_mem i)
  have hzero : ∀ i, W.wt i ∉ M → ξ ⟨W.z i, hmemz i⟩ = 0 := by
    intro i hi
    obtain ⟨g, a, b, hη, hw, hz⟩ := hW.var i
    have hab : a ≠ b := by
      rintro rfl
      apply hi
      rw [hw]
      simp [wt]
    have hrz : ((F.rz R) g).mat a b = 0 := by
      show algebraMap O R ((((tor O) (F.Ψ g) : GL (Fin 3) O) : Matrix (Fin 3) (Fin 3) O) a b) = 0
      rw [tor_val, Matrix.diagonal_apply_ne _ hab, map_zero]
    have h1 : ξ ⟨W.z i, hmemz i⟩ = ptMat u ξ g a b := by
      show ξ ⟨W.z i, hmemz i⟩ = ξ ⟨(u g).mat a b, _⟩
      congr 1
      exact Subtype.ext (show W.z i = (u g).mat a b by rw [hz, hrz, sub_zero])
    rw [h1]
    exact h g hη a b (hw ▸ hi)
  rw [← hW.part] at hx
  obtain ⟨f, hf, hfx⟩ := hx
  subst hfx
  let s := Finset.univ.filter (fun i => W.wt i ∉ M)
  have hs : ∀ n : W.σ →₀ ℕ, (∀ i ∈ s, n i = 0) → MvPowerSeries.coeff n f = 0 := by
    intro n hn
    apply hf
    intro hw
    apply hj
    rw [← hw, Finsupp.weight_apply]
    refine AddSubmonoid.sum_mem M fun c hc => ?_
    by_cases hcM : W.wt c ∈ M
    · exact nsmul_mem hcM _
    · exact absurd (hn c (by simp [s, hcM])) (Finsupp.mem_support_iff.mp hc)
  obtain ⟨g, hg, hfg⟩ := wtPart_decomp W.wt j s f hf hs
  have hmemg : ∀ i, W.π (g i) ∈ Sring O u := fun i =>
    mem_Sring u (j := j - W.wt i) (by rw [← hW.part]; exact ⟨g i, hg i, rfl⟩)
  have hsum : (⟨W.π.toLinearMap f, mem_Sring u (by rw [← hW.part]; exact ⟨f, hf, rfl⟩)⟩ : Sring O u) =
      ∑ i ∈ s, (⟨W.z i, hmemz i⟩ : Sring O u) * ⟨W.π (g i), hmemg i⟩ := by
    apply Subtype.ext
    simp [hfg, map_sum, WPres.z]
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [map_mul, hzero i (Finset.mem_filter.mp hi).2, zero_mul]

theorem UpperTheory.V.UnitaryThreeInertia.isPtHom_sign :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    ∀ {K : Type} [CommRing K] [Algebra O K] (ξ : Sring O u →ₐ[O] K) (r : Γ →* GG 3 K), IsPtHom u ξ r →
      (Upper F.η r ↔ ∀ j < 0, ∀ x (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) ∧ (Lower F.η r ↔ ∀ j > 0, ∀ x (hx : x ∈ wpart O u j), ξ ⟨x, mem_Sring u hx⟩ = 0) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF g₁ hg₁ R _ _ _ u hu K _ _ ξ r hr
  obtain ⟨W, hW, _⟩ := exists_adapted F hF g₁ hg₁ u hu
  have hent : ∀ g a b, (r g).mat a b = ptMat u ξ g a b := fun g a b => by rw [(hr g).2]
  let Mp : AddSubmonoid ℤ :=
    { carrier := {n | 0 ≤ n}
      add_mem' := by
        intro a b ha hb
        show 0 ≤ a + b
        exact add_nonneg ha hb
      zero_mem' := le_refl (0 : ℤ) }
  let Mn : AddSubmonoid ℤ :=
    { carrier := {n | n ≤ 0}
      add_mem' := by
        intro a b ha hb
        show a + b ≤ 0
        exact add_nonpos ha hb
      zero_mem' := le_refl (0 : ℤ) }
  have hMp : ∀ n : ℤ, n ∈ Mp ↔ 0 ≤ n := fun _ => Iff.rfl
  have hMn : ∀ n : ℤ, n ∈ Mn ↔ n ≤ 0 := fun _ => Iff.rfl
  refine ⟨⟨fun hU j hj x hx => ?_, fun hv g hg a b hab => ?_⟩, ⟨fun hL j hj x hx => ?_, fun hv g hg a b hab => ?_⟩⟩
  · refine vanish_of_entries F u W hW ξ Mp (fun g hg a b hab => ?_) j (by rw [hMp]; omega) x hx
    rw [← hent]
    exact hU g ((MonoidHom.mem_ker).mpr hg) a b (by rw [hMp] at hab; omega)
  · rw [hent]
    exact hv (wt a b) hab _ (entry_mem u g a b)
  · refine vanish_of_entries F u W hW ξ Mn (fun g hg a b hab => ?_) j (by rw [hMn]; omega) x hx
    rw [← hent]
    exact hL g ((MonoidHom.mem_ker).mpr hg) a b (by rw [hMn] at hab; omega)
  · rw [hent]
    exact hv (wt a b) hab _ (entry_mem u g a b)
