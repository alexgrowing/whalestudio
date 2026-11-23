import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.gr_internal :
    ∀ (O X R : Type) [CommRing O] [AddCommGroup X] [DecidableEq X] [CommRing R] [Algebra O R] (W : WPres O X R), DirectSum.IsInternal W.gr := by
  intro O X R _ _ _ _ _ W
  have hhom := W.homog
  unfold IsHomog at hhom
  have hK : ∀ (j : X) (f g : MvPowerSeries W.σ O), W.π f = W.π g →
      W.π (wcomp O W.wt j f) = W.π (wcomp O W.wt j g) := by
    intro j f g hfg
    have hker : f - g ∈ RingHom.ker W.π := by
      rw [RingHom.mem_ker]
      simp [hfg]
    have h2 := hhom (f - g) hker j
    rw [RingHom.mem_ker] at h2
    simp only [map_sub] at h2
    exact sub_eq_zero.mp (by simpa using h2)
  have hself : ∀ (j : X) (f : MvPowerSeries W.σ O), f ∈ wtPart O W.wt j →
      wcomp O W.wt j f = f := by
    intro j f hf
    ext n
    rw [coeff_wcomp]
    split_ifs with h
    · rfl
    · exact (hf n h).symm
  have hoff : ∀ (i j : X) (f : MvPowerSeries W.σ O), f ∈ wtPart O W.wt i → i ≠ j →
      wcomp O W.wt j f = 0 := by
    intro i j f hf hij
    ext n
    rw [coeff_wcomp, map_zero]
    split_ifs with h
    · exact hf n (fun h' => hij (h'.symm.trans h))
    · rfl
  have hgr : ∀ (i : X) (y : W.A), y ∈ W.gr i ↔ y.1 ∈ W.part i := fun i y => Iff.rfl
  have hpart : ∀ (i : X) (x : R), x ∈ W.part i ↔ ∃ f ∈ wtPart O W.wt i, W.π f = x := by
    intro i x
    exact Submodule.mem_map
  let T : X → Submodule O W.A := fun j =>
    { carrier := {y | ∀ f, W.π f = y.1 → W.π (wcomp O W.wt j f) = 0}
      add_mem' := by
        intro a b ha hb f hf
        obtain ⟨fa, hfa⟩ := W.surj a.1
        obtain ⟨fb, hfb⟩ := W.surj b.1
        have e : W.π f = W.π (fa + fb) := by
          rw [hf, map_add, hfa, hfb]
          rfl
        rw [hK j f (fa + fb) e, map_add, map_add, ha fa hfa, hb fb hfb, add_zero]
      zero_mem' := by
        intro f hf
        have e : W.π f = W.π 0 := by
          rw [hf, map_zero]
          rfl
        rw [hK j f 0 e, map_zero, map_zero]
      smul_mem' := by
        intro c a ha f hf
        obtain ⟨fa, hfa⟩ := W.surj a.1
        have e : W.π f = W.π (c • fa) := by
          rw [hf, map_smul, hfa]
          rfl
        rw [hK j f (c • fa) e, map_smul, map_smul, ha fa hfa, smul_zero] }
  have hT : ∀ (i j : X), i ≠ j → W.gr i ≤ T j := by
    intro i j hij y hy f hf
    obtain ⟨g, hg, hgy⟩ := (hpart i y.1).mp ((hgr i y).mp hy)
    rw [hK j f g (hf.trans hgy.symm), hoff i j g hg hij, map_zero]
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · rw [iSupIndep_def]
    intro j
    rw [Submodule.disjoint_def]
    intro x hx hx'
    have hle : (⨆ i, ⨆ (_ : i ≠ j), W.gr i) ≤ T j := iSup₂_le fun i hij => hT i j hij
    have hxT := hle hx'
    obtain ⟨g, hg, hgx⟩ := (hpart j x.1).mp ((hgr j x).mp hx)
    have h0 := hxT g hgx
    rw [hself j g hg, hgx] at h0
    exact Subtype.ext h0
  · rw [eq_top_iff]
    rintro ⟨a, ha⟩ -
    have hle : ∀ i, W.part i ≤ LinearMap.range W.A.val.toLinearMap := by
      intro i x hx
      exact ⟨⟨x, W.part_le_A hx⟩, rfl⟩
    have hmap : Submodule.map W.A.val.toLinearMap (⨆ i, W.gr i) = ⨆ i, W.part i := by
      rw [Submodule.map_iSup]
      exact iSup_congr fun i => Submodule.map_comap_eq_self (hle i)
    have hmem : a ∈ Submodule.map W.A.val.toLinearMap (⨆ i, W.gr i) := by
      rw [hmap]
      exact ha
    obtain ⟨b, hb, hba⟩ := hmem
    have : b = ⟨a, ha⟩ := Subtype.ext hba
    rw [← this]
    exact hb
