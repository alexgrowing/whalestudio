import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem locF_eq_loc (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (L : Submodule (𝓞 K) V) :
    locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = Formalism.HermitianLatticesTheory.loc (K := K) P L := by
  have hPp := hP.isPrime
  have hp : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime := Ideal.comap_isPrime _ _
  ext x
  rw [LocF.mem_locF_iff hp]
  unfold Formalism.HermitianLatticesTheory.loc
  rw [Formalism.HermitianLatticesTheory.locBasic_mem_locS]
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨_, ?_, hx⟩
    rw [WA.mem_hcompl_iff hPp, WA.mem_conjIdeal_iff,
      (conjO_eq_iff_mem_range hF _).mpr ⟨t, rfl⟩]
    exact ⟨ht, ht⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨h1, h2⟩ := (WA.mem_hcompl_iff hPp s).mp hs
    rw [WA.mem_conjIdeal_iff] at h2
    obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF (conjO K s * s)).mp
      (by rw [map_mul, conjO_conjO, mul_comm])
    refine ⟨t, ?_, ?_⟩
    · rw [Ideal.mem_comap, ht]
      exact fun h => (hPp.mem_or_mem h).elim h2 h1
    · rw [ht, mul_smul]
      exact L.smul_mem _ hx

theorem isUnimodularAt_iff_vd (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h P L ↔ vd h L (P.comap (algebraMap (𝓞 F) (𝓞 K))) = 0 := by
  have hPp := hP.isPrime
  have hda := LocF.aniso_of_totPosDef hd
  have hEP : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P := Ideal.map_comap_le
  constructor
  · intro hu
    apply LocF.vd_eq_zero_of_not_le
    obtain ⟨x, hxM, hxo, hxu⟩ := LocF.exists_orth_unit_frame (WA.isHermSemilocal_locRing hK hP)
      (LocF.locRing_local hPp) hs hda (WA.isSelfDualMod_loc hL hPp hu)
    choose s hs' hsx using fun i => Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp
      (show x i ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) P) L from hxM i)
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi (fun i => s i • x i) hsx
    have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨_, hsx, hdet⟩
    have hunit : WA.IsUnitIn (WA.locRing P) (algebraMap (𝓞 K) K g.det) := by
      rw [hdet]
      have hdiag : (Matrix.of fun i j => h (s i • x i) (s j • x j)) = Matrix.diagonal fun i =>
          star (algebraMap (𝓞 K) K (s i)) * algebraMap (𝓞 K) K (s i) * h (x i) (x i) := by
        ext i j
        rw [Matrix.of_apply, Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right]
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq]
          ring
        · rw [Matrix.diagonal_apply_ne _ hij, hxo i j hij]
          ring
      rw [hdiag, Matrix.det_diagonal]
      apply LocF.isUnitIn_prod
      intro i _
      refine LocF.isUnitIn_mul (LocF.isUnitIn_mul ?_ ?_) (hxu i)
      · rw [← WA.algebraMap_conjO, LocF.isUnitIn_algebraMap_iff hPp]
        exact WA.conjO_mem_hcompl (hs' i)
      · rw [LocF.isUnitIn_algebraMap_iff hPp]
        exact hs' i
    have hnP : g.det ∉ P :=
      ((WA.mem_hcompl_iff hPp _).mp ((LocF.isUnitIn_algebraMap_iff hPp _).mp hunit)).1
    exact fun hle => hnP (hEP (hle hmem))
  · intro h0
    have hn := LocF.not_le_of_vd_eq_zero (LocF.discrIdeal_ne_bot hda hL hLi)
      (ne_top_of_le_ne_top hP.ne_top hEP) h0
    unfold discrIdeal at hn
    rw [Ideal.span_le, Set.not_subset] at hn
    obtain ⟨z, ⟨x, hx, hz⟩, hzn⟩ := hn
    have hzfix : conjO K z = z := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      change star (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K z
      rw [hz, LocF.star_gram_det h hs]
    obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF z).mp hzfix
    have hzP : z ∉ P := by
      intro hmem
      apply hzn
      rw [← ht] at hmem ⊢
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr hmem)
    have hzc : z ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
      rw [WA.mem_hcompl_iff hPp, WA.mem_conjIdeal_iff, hzfix]
      exact ⟨hzP, hzP⟩
    have hz0 : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0 := by
      rw [← hz]
      exact WA.algebraMap_ne_zero_of_mem_hcompl hPp hzc
    have hspan : Submodule.span K (Set.range x) = ⊤ :=
      (LocF.linearIndependent_of_gram_det_ne_zero h x hz0).span_eq_top_of_card_eq_finrank'
        (by simp)
    obtain ⟨g, hg, hdet⟩ := LocF.exists_gram hLi x hx
    have hgz : g.det = z := RingOfIntegers.ext (hdet.trans hz.symm)
    obtain ⟨hA, hB⟩ := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs (fun r => ⟨conjO K r, rfl⟩) L hL.fg).1
      P hPp
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
    rw [hB, ← hA]
    apply le_antisymm
    · have hle : Formalism.HermitianLatticesTheory.dual h L ≤ Formalism.HermitianLatticesTheory.loc (K := K) P L := by
        intro y hy
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
        exact Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨g.det, hgz ▸ hzc,
          LocF.det_smul_mem h x hx hspan g hg y (fun i => hy _ (hx i))⟩
      calc Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.dual h L)
          ≤ Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.loc (K := K) P L) :=
            Formalism.HermitianLatticesTheory.locBasic_locS_mono _ hle
        _ = Formalism.HermitianLatticesTheory.loc (K := K) P L := Formalism.HermitianLatticesTheory.locBasic_locS_idem _ _
    · apply Formalism.HermitianLatticesTheory.locBasic_locS_mono
      intro y hy
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      exact fun w hw => hLi w hw y hy

theorem finite_vd_ne_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | vd h L 𝔭.1 ≠ 0}.Finite := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hD' : (discrIdeal h L).comap (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := by
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    exact Ideal.comap_ne_bot_of_integral_mem hz0 hz (Algebra.IsIntegral.isIntegral z)
  refine ((Ideal.finite_factors hD').image (fun v =>
    (⟨v.asIdeal, v.isMaximal⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))).subset ?_
  intro 𝔭 h𝔭
  have hle : discrIdeal h L ≤ extP K 𝔭.1 := by
    by_contra hn
    exact h𝔭 (LocF.vd_eq_zero_of_not_le hn)
  obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
  have h2 : extP K 𝔭.1 ≤ P := by
    rw [← hP𝔭]
    exact Ideal.map_comap_le
  have h1 : (discrIdeal h L).comap (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭.1 := by
    rw [← hP𝔭]
    exact Ideal.comap_mono (hle.trans h2)
  have hne : 𝔭.1 ≠ ⊥ := fun e => hD' (eq_bot_iff.mpr (e ▸ h1))
  exact ⟨⟨𝔭.1, 𝔭.2.isPrime, hne⟩, Ideal.dvd_iff_le.mpr h1, rfl⟩

theorem exists_unique_patch (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {L₀ : Submodule (𝓞 K) V} (hL₀ : Submodule.IsLattice K L₀)
    (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (T : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V)
    (hT : ∀ 𝔭 ∈ s, locF 𝔭.1 (T 𝔭) = T 𝔭 ∧ ∃ A : Submodule (𝓞 K) V, Submodule.IsLattice K A ∧
      locF 𝔭.1 A = T 𝔭) :
    ∃! Λ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ ∧ (∀ 𝔭 ∈ s, locF 𝔭.1 Λ = T 𝔭) ∧
      ∀ 𝔭 ∉ s, locF 𝔭.1 Λ = locF 𝔭.1 L₀ := by
  classical
  let B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V := fun 𝔭 =>
    if h : 𝔭 ∈ s then (hT 𝔭 h).2.choose else L₀
  have hB1 : ∀ 𝔭 (h : 𝔭 ∈ s), Submodule.IsLattice K (B 𝔭) ∧ locF 𝔭.1 (B 𝔭) = T 𝔭 := by
    intro 𝔭 h
    simp only [B, dif_pos h]
    exact (hT 𝔭 h).2.choose_spec
  have hB2 : ∀ 𝔭 ∉ s, B 𝔭 = L₀ := by
    intro 𝔭 h
    simp only [B, dif_neg h]
  have hB : ∀ 𝔭, Submodule.IsLattice K (B 𝔭) := by
    intro 𝔭
    by_cases h : 𝔭 ∈ s
    · exact (hB1 𝔭 h).1
    · rw [hB2 𝔭 h]
      exact hL₀
  obtain ⟨hlat, hloc⟩ := LocF.patch hL₀ s B hB hB2
  refine ⟨_, ⟨hlat, fun 𝔭 h => (hloc 𝔭).trans (hB1 𝔭 h).2,
    fun 𝔭 h => (hloc 𝔭).trans (by rw [hB2 𝔭 h])⟩, ?_⟩
  rintro Λ ⟨-, h1, h2⟩
  rw [← LocF.iInf_locF (F := F) Λ]
  congr 1
  funext 𝔭
  by_cases h : 𝔭 ∈ s
  · rw [h1 𝔭 h, (hB1 𝔭 h).2]
  · rw [h2 𝔭 h, hB2 𝔭 h]

end Formalism.HermitianLattices.Ext.L3
