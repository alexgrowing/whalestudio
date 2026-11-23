import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ConjOMemHcompl

open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

structure VecSplit (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K) where
  x₀ : V
  ι : V' →ₗ[K] V
  inj : Function.Injective ι
  hx₀ : h x₀ x₀ ≠ 0
  isom : ∀ a b, h (ι a) (ι b) = h' a b
  orth : ∀ a, h x₀ (ι a) = 0
  cover : ∀ v, ∃ (c : K) (a : V'), v = c • x₀ + ι a

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def VecSplit.adjoin (S : VecSplit h h') (L' : Submodule (𝓞 K) V') : Submodule (𝓞 K) V :=
  Submodule.span (𝓞 K) {S.x₀} ⊔ L'.map (S.ι.restrictScalars (𝓞 K))

def VecSplit.cut (S : VecSplit h h') (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) V' :=
  L.comap (S.ι.restrictScalars (𝓞 K))

namespace VecSplit

variable (S : VecSplit h h')

theorem h_x₀_comb (c : K) (a : V') : h S.x₀ (c • S.x₀ + S.ι a) = c * h S.x₀ S.x₀ := by
  rw [map_add, map_smul, S.orth a, smul_eq_mul, add_zero]

theorem comb_eq_iff {c c' : K} {a a' : V'} :
    c • S.x₀ + S.ι a = c' • S.x₀ + S.ι a' ↔ c = c' ∧ a = a' := by
  constructor
  · intro he
    have hc : c = c' := by
      have := congrArg (h S.x₀) he
      rw [S.h_x₀_comb, S.h_x₀_comb] at this
      exact mul_right_cancel₀ S.hx₀ this
    subst hc
    exact ⟨rfl, S.inj (add_left_cancel he)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem x₀_not_mem_range (a : V') : S.ι a ≠ S.x₀ := by
  intro he
  apply S.hx₀
  have := S.orth a
  rwa [he] at this

theorem mem_adjoin_iff (L' : Submodule (𝓞 K) V') (v : V) :
    v ∈ S.adjoin L' ↔ ∃ (r : 𝓞 K) (a : V'), a ∈ L' ∧ v = (algebraMap (𝓞 K) K r) • S.x₀ + S.ι a := by
  unfold VecSplit.adjoin
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, rfl⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
    exact ⟨r, a, ha, by simp only [algebraMap_smul, LinearMap.coe_restrictScalars]⟩
  · rintro ⟨r, a, ha, rfl⟩
    exact ⟨r • S.x₀, Submodule.mem_span_singleton.mpr ⟨r, rfl⟩, S.ι a,
      Submodule.mem_map.mpr ⟨a, ha, rfl⟩, by simp only [algebraMap_smul, LinearMap.coe_restrictScalars]⟩

theorem x₀_mem_adjoin' (L' : Submodule (𝓞 K) V') : S.x₀ ∈ S.adjoin L' := by
  unfold VecSplit.adjoin
  exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)

theorem mem_cut_iff (L : Submodule (𝓞 K) V) (a : V') : a ∈ S.cut L ↔ S.ι a ∈ L := Iff.rfl

theorem cut_adjoin' (L' : Submodule (𝓞 K) V') : S.cut (S.adjoin L') = L' := by
  ext a
  rw [S.mem_cut_iff, S.mem_adjoin_iff]
  constructor
  · rintro ⟨r, b, hb, he⟩
    have h0 : (0 : K) • S.x₀ + S.ι a = (algebraMap (𝓞 K) K r) • S.x₀ + S.ι b := by
      rw [zero_smul, zero_add]
      exact he
    rw [(S.comb_eq_iff.mp h0).2]
    exact hb
  · intro ha
    exact ⟨0, a, ha, by simp⟩

theorem adjoin_cut' (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L) : S.adjoin (S.cut L) = L := by
  apply le_antisymm
  · unfold VecSplit.adjoin VecSplit.cut
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx) (Submodule.map_comap_le _ _)
  · intro v hv
    obtain ⟨c, a, rfl⟩ := S.cover v
    have hc : c ∈ (1 : Submodule (𝓞 K) K) := by
      have := hL S.x₀ hx _ hv
      rwa [S.h_x₀_comb, h1, mul_one] at this
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hc
    rw [S.mem_adjoin_iff]
    refine ⟨r, a, ?_, by rw [hr]⟩
    rw [S.mem_cut_iff]
    have e : S.ι a = (c • S.x₀ + S.ι a) - (algebraMap (𝓞 K) K r) • S.x₀ := by
      rw [hr]
      abel
    rw [e]
    refine L.sub_mem hv ?_
    rw [algebraMap_smul]
    exact L.smul_mem r hx

end VecSplit

namespace VecSplit

variable (S : VecSplit h h')

theorem orth' (hs : h.IsSymm) (a : V') : h (S.ι a) S.x₀ = 0 := by
  rw [← hs.eq S.x₀ (S.ι a), S.orth a, map_zero]

theorem h_comb (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1) (d c : K) (b a : V') :
    h (d • S.x₀ + S.ι b) (c • S.x₀ + S.ι a) = starRingEnd K d * c + h' b a := by
  simp [S.orth, S.orth' hs, S.isom, h1]

theorem star_alg_mem_one (r : 𝓞 K) : starRingEnd K (algebraMap (𝓞 K) K r) ∈ (1 : Submodule (𝓞 K) K) := by
  refine Submodule.mem_one.mpr ⟨⟨starRingEnd K (algebraMap (𝓞 K) K r), ?_⟩, rfl⟩
  exact (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom

theorem isLattice_adjoin_iff' (L' : Submodule (𝓞 K) V') :
    Submodule.IsLattice K (S.adjoin L') ↔ Submodule.IsLattice K L' := by
  constructor
  · intro hL
    have hFG : (L'.map (S.ι.restrictScalars (𝓞 K))).FG :=
      hL.fg.of_le (by unfold VecSplit.adjoin; exact le_sup_right)
    refine ⟨Submodule.fg_of_fg_map_injective (S.ι.restrictScalars (𝓞 K)) S.inj hFG, ?_⟩
    rw [eq_top_iff]
    intro a _
    have key : ∀ v ∈ Submodule.span K (S.adjoin L' : Set V), ∃ (c : K) (b : V'),
        b ∈ Submodule.span K (L' : Set V') ∧ v = c • S.x₀ + S.ι b := by
      intro v hv
      induction hv using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨r, b, hb, rfl⟩ := (S.mem_adjoin_iff L' x).1 hx
        exact ⟨_, b, Submodule.subset_span hb, rfl⟩
      | zero => exact ⟨0, 0, zero_mem _, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨c, b, hb, rfl⟩ := hx
        obtain ⟨c', b', hb', rfl⟩ := hy
        exact ⟨c + c', b + b', add_mem hb hb', by rw [map_add, add_smul]; abel⟩
      | smul k x _ hx =>
        obtain ⟨c, b, hb, rfl⟩ := hx
        exact ⟨k * c, k • b, Submodule.smul_mem _ k hb, by rw [smul_add, map_smul, smul_smul]⟩
    have hmem : S.ι a ∈ Submodule.span K (S.adjoin L' : Set V) := by
      rw [hL.span_eq_top]
      exact Submodule.mem_top
    obtain ⟨c, b, hb, he⟩ := key _ hmem
    have hc : (0 : K) • S.x₀ + S.ι a = c • S.x₀ + S.ι b := by
      rw [zero_smul, zero_add]
      exact he
    rw [(S.comb_eq_iff.1 hc).2]
    exact hb
  · intro hL
    refine ⟨?_, ?_⟩
    · unfold VecSplit.adjoin
      exact (Submodule.fg_span_singleton _).sup (hL.fg.map _)
    · rw [eq_top_iff]
      intro v _
      obtain ⟨c, a, rfl⟩ := S.cover v
      refine add_mem (Submodule.smul_mem _ c (Submodule.subset_span (S.x₀_mem_adjoin' L'))) ?_
      have ha : a ∈ Submodule.span K (L' : Set V') := by
        rw [hL.span_eq_top]
        exact Submodule.mem_top
      have hle : Submodule.map S.ι (Submodule.span K (L' : Set V')) ≤
          Submodule.span K (S.adjoin L' : Set V) := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨b, hb, rfl⟩
        unfold VecSplit.adjoin
        exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hb)
      exact hle (Submodule.mem_map_of_mem ha)

theorem isIntegralLat_adjoin_iff' (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1) (L' : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsIntegralLat h' L' := by
  unfold Formalism.HermitianLatticesTheory.IsIntegralLat
  constructor
  · intro H b hb a ha
    have hb' : S.ι b ∈ S.adjoin L' := (S.mem_adjoin_iff L' _).mpr ⟨0, b, hb, by simp⟩
    have ha' : S.ι a ∈ S.adjoin L' := (S.mem_adjoin_iff L' _).mpr ⟨0, a, ha, by simp⟩
    rw [← S.isom]
    exact H _ hb' _ ha'
  · intro H x hx y hy
    obtain ⟨r, b, hb, rfl⟩ := (S.mem_adjoin_iff L' x).mp hx
    obtain ⟨r', a, ha, rfl⟩ := (S.mem_adjoin_iff L' y).mp hy
    rw [S.h_comb hs h1]
    refine Submodule.add_mem _ ?_ (H b hb a ha)
    obtain ⟨u, hu⟩ := Submodule.mem_one.mp (star_alg_mem_one r)
    exact Submodule.mem_one.mpr ⟨u * r', by rw [map_mul, hu]⟩

theorem isOrthoLattice_adjoin' (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1)
    {I' : Submodule (𝓞 K) V'} {n : ℕ} (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice h (S.adjoin I') (n + 1) := by
  obtain ⟨e', hli, hspan, hI'eq, horth⟩ := hI'
  refine ⟨Fin.cons S.x₀ (fun j => S.ι (e' j)), ?_, ?_, ?_, ?_⟩
  · rw [linearIndependent_fin_cons]
    refine ⟨hli.map' S.ι (LinearMap.ker_eq_bot.mpr S.inj), fun hmem => ?_⟩
    have hle : Submodule.span K (Set.range (fun j => S.ι (e' j))) ≤ LinearMap.range S.ι := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨e' j, rfl⟩
    obtain ⟨a, ha⟩ := hle hmem
    exact S.x₀_not_mem_range a ha
  · rw [eq_top_iff]
    intro v _
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [Fin.range_cons]
    have ha : a ∈ Submodule.span K (Set.range e') := by
      rw [hspan]
      exact Submodule.mem_top
    refine Submodule.add_mem _ (Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_insert _ _))) ?_
    have hm : S.ι a ∈ (Submodule.span K (Set.range e')).map S.ι := Submodule.mem_map_of_mem ha
    rw [Submodule.map_span] at hm
    refine Submodule.span_mono ?_ hm
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact Set.mem_insert_of_mem _ ⟨j, rfl⟩
  · rw [Fin.range_cons, Submodule.span_insert, hI'eq]
    unfold VecSplit.adjoin
    congr 1
    rw [Submodule.map_span]
    congr 1
    ext v
    simp
  · intro i j
    cases i using Fin.cases <;> cases j using Fin.cases
    · simp [h1]
    · simp [S.orth, (Fin.succ_ne_zero _).symm]
    · simp [S.orth' hs, Fin.succ_ne_zero]
    · simp [S.isom, horth]

end VecSplit

theorem exists_vecSplit_ortho' {I : Submodule (𝓞 K) V} {I' : Submodule (𝓞 K) V'} {n : ℕ}
    (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I (n + 1)) (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    ∃ S : VecSplit h h', h S.x₀ S.x₀ = 1 ∧ S.adjoin I' = I := by
  obtain ⟨e, hli, hspan, hIe, horth⟩ := hI
  obtain ⟨e', hli', hspan', hIe', horth'⟩ := hI'
  have hsucc : LinearIndependent K (fun j : Fin n => e j.succ) := hli.comp _ (Fin.succ_injective n)
  let b' : Basis (Fin n) K V' := Basis.mk hli' hspan'.ge
  let bs : Basis (Fin n) K (Submodule.span K (Set.range fun j : Fin n => e j.succ)) := Basis.span hsucc
  let ι : V' →ₗ[K] V := (Submodule.subtype _).comp (b'.equiv bs (Equiv.refl _)).toLinearMap
  have hιe : ∀ j, ι (e' j) = e j.succ := by
    intro j
    have h1 : e' j = b' j := (Basis.mk_apply hli' hspan'.ge j).symm
    rw [h1]
    simp only [ι, bs, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply,
      Submodule.subtype_apply, Basis.span_apply]
  have hinj : Function.Injective ι := Subtype.val_injective.comp (LinearEquiv.injective _)
  let b : Basis (Fin (n + 1)) K V := Basis.mk hli hspan.ge
  have hisom : ∀ a c, h (ι a) (ι c) = h' a c := by
    have hB : (h.comp ι).compl₂ ι = h' := by
      refine LinearMap.ext_basis b' b' (fun i j => ?_)
      simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, b', Basis.mk_apply, hιe, horth, horth',
        Fin.succ_inj]
    intro a c
    exact congrArg (fun B : V' →ₗ⋆[K] V' →ₗ[K] K => B a c) hB
  have horthι : ∀ a, h (e 0) (ι a) = 0 := by
    have hz : (h (e 0)).comp ι = 0 := by
      refine b'.ext (fun j => ?_)
      simp [b', hιe, horth, (Fin.succ_ne_zero j).symm]
    intro a
    exact LinearMap.congr_fun hz a
  have hcover : ∀ v, ∃ (c : K) (a : V'), v = c • e 0 + ι a := by
    intro v
    refine ⟨b.repr v 0, ∑ j : Fin n, b.repr v j.succ • e' j, ?_⟩
    conv_lhs => rw [← b.sum_repr v]
    rw [Fin.sum_univ_succ, map_sum]
    simp only [b, Basis.mk_apply, map_smul, hιe]
  refine ⟨⟨e 0, ι, hinj, ?_, hisom, horthι, hcover⟩, ?_, ?_⟩
  · rw [horth 0 0]
    simp
  · show h (e 0) (e 0) = 1
    rw [horth 0 0]
    simp
  · show Submodule.span (𝓞 K) {e 0} ⊔ I'.map (ι.restrictScalars (𝓞 K)) = I
    rw [hIe', hIe, Submodule.map_span]
    have hr : Set.range e = insert (e 0) (Set.range fun j : Fin n => e j.succ) := by
      ext v
      simp only [Set.mem_range, Set.mem_insert_iff]
      rw [Fin.exists_fin_succ]
      exact or_congr_left eq_comm
    rw [hr, Submodule.span_insert]
    congr 2
    ext v
    simp [hιe]

namespace VecSplit

variable (S : VecSplit h h')

theorem smul_comb (s : 𝓞 K) (c : K) (a : V') :
    s • (c • S.x₀ + S.ι a) = (s • c) • S.x₀ + S.ι (s • a) := by
  rw [smul_add, smul_assoc, ← LinearMap.map_smul_of_tower]

theorem comb_mem_adjoin_iff (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ S.adjoin L' ↔ c ∈ (1 : Submodule (𝓞 K) K) ∧ a ∈ L' := by
  rw [S.mem_adjoin_iff]
  constructor
  · rintro ⟨r, b, hb, he⟩
    obtain ⟨rfl, rfl⟩ := S.comb_eq_iff.mp he
    exact ⟨Submodule.mem_one.mpr ⟨r, rfl⟩, hb⟩
  · rintro ⟨hc, ha⟩
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hc
    exact ⟨r, a, ha, rfl⟩

theorem comb_mem_loc_adjoin_iff (p : Ideal (𝓞 K)) (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L') ↔
      c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ∧ a ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L' := by
  simp only [Formalism.HermitianLatticesTheory.locR, Formalism.HermitianLatticesTheory.loc, Formalism.HermitianLatticesTheory.locS, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · rintro ⟨s, hs, hmem⟩
    rw [S.smul_comb, S.comb_mem_adjoin_iff] at hmem
    exact ⟨⟨s, hs, hmem.1⟩, ⟨s, hs, hmem.2⟩⟩
  · rintro ⟨⟨s₁, hs₁, h₁⟩, ⟨s₂, hs₂, h₂⟩⟩
    refine ⟨s₁ * s₂, mul_mem hs₁ hs₂, ?_⟩
    rw [S.smul_comb, S.comb_mem_adjoin_iff]
    refine ⟨?_, ?_⟩
    · rw [mul_comm, mul_smul]
      exact Submodule.smul_mem _ s₂ h₁
    · rw [mul_smul]
      exact L'.smul_mem s₁ h₂

theorem comb_mem_dualAt_iff (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1) (p : Ideal (𝓞 K))
    (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ Formalism.HermitianLatticesTheory.dualAt h p (Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L')) ↔
      c ∈ Formalism.HermitianLatticesTheory.locR (K := K) p ∧
        a ∈ Formalism.HermitianLatticesTheory.dualAt h' p (Formalism.HermitianLatticesTheory.loc (K := K) p L') := by
  rw [mem_dualAt_iff', mem_dualAt_iff']
  constructor
  · intro H
    refine ⟨?_, fun b hb => ?_⟩
    · have hx : (1 : K) • S.x₀ + S.ι 0 ∈ Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L') :=
        (S.comb_mem_loc_adjoin_iff p L' 1 0).mpr ⟨one_mem_locR p, Submodule.zero_mem _⟩
      have := H _ hx
      rwa [S.h_comb hs h1, map_one, one_mul, map_zero, LinearMap.zero_apply, add_zero] at this
    · have hy : (0 : K) • S.x₀ + S.ι b ∈ Formalism.HermitianLatticesTheory.loc (K := K) p (S.adjoin L') :=
        (S.comb_mem_loc_adjoin_iff p L' 0 b).mpr ⟨Submodule.zero_mem _, hb⟩
      have := H _ hy
      rwa [S.h_comb hs h1, map_zero, zero_mul, zero_add] at this
  · rintro ⟨hc, ha⟩ y hy
    obtain ⟨d, b, rfl⟩ := S.cover y
    obtain ⟨hd, hb⟩ := (S.comb_mem_loc_adjoin_iff p L' d b).mp hy
    rw [S.h_comb hs h1]
    exact Submodule.add_mem _ (mul_mem_locR p (star_mem_locR p hd) hc) (ha b hb)

theorem isUnimodularAt_adjoin_iff' (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1)
    (L' : Submodule (𝓞 K) V') (p : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L' := by
  unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
  constructor
  · intro H
    ext a
    have h1' := S.comb_mem_dualAt_iff hs h1 p L' 0 a
    have h2' := S.comb_mem_loc_adjoin_iff p L' 0 a
    rw [H, h2'] at h1'
    simpa [Submodule.zero_mem] using h1'.symm
  · intro H
    ext v
    obtain ⟨c, a, rfl⟩ := S.cover v
    rw [S.comb_mem_dualAt_iff hs h1, S.comb_mem_loc_adjoin_iff, H]

end VecSplit

theorem exists_vecSplit_ortho {I : Submodule (𝓞 K) V} {I' : Submodule (𝓞 K) V'} {n : ℕ}
    (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I (n + 1)) (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    ∃ S : VecSplit h h', h S.x₀ S.x₀ = 1 ∧ S.adjoin I' = I := exists_vecSplit_ortho' hI hI'

theorem VecSplit.isOrthoLattice_adjoin (hs : h.IsSymm) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1)
    {I' : Submodule (𝓞 K) V'} {n : ℕ} (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice h (S.adjoin I') (n + 1) := S.isOrthoLattice_adjoin' hs h1 hI'

theorem VecSplit.cut_adjoin (S : VecSplit h h') (L' : Submodule (𝓞 K) V') :
    S.cut (S.adjoin L') = L' := S.cut_adjoin' L'

theorem VecSplit.adjoin_cut (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L) : S.adjoin (S.cut L) = L := S.adjoin_cut' h1 hL hx

theorem VecSplit.x₀_mem_adjoin (S : VecSplit h h') (L' : Submodule (𝓞 K) V') :
    S.x₀ ∈ S.adjoin L' := S.x₀_mem_adjoin' L'

theorem VecSplit.isLattice_adjoin_iff (S : VecSplit h h') (L' : Submodule (𝓞 K) V') :
    Submodule.IsLattice K (S.adjoin L') ↔ Submodule.IsLattice K L' := S.isLattice_adjoin_iff' L'

theorem VecSplit.isIntegralLat_adjoin_iff (hs : h.IsSymm) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1)
    (L' : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsIntegralLat h' L' := S.isIntegralLat_adjoin_iff' hs h1 L'

theorem VecSplit.isUnimodularAt_adjoin_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (S : VecSplit h h')
    (h1 : h S.x₀ S.x₀ = 1) (L' : Submodule (𝓞 K) V') (p : Ideal (𝓞 K)) (hp : p.IsMaximal) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L' := S.isUnimodularAt_adjoin_iff' hs h1 L' p

end Formalism.HermitianLattices.Ext.L3
