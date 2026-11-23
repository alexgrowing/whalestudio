import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefinitePartLatticeDiscriminantEqQuotienStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsHermIsometryGraphModScalarFlagPairIotaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBoundStatement

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.ToLift

open GlobalTheory.Mass GlobalTheory.DegCnt.DelScale

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {S I C : Submodule K V}

omit [NumberField K] [StarRing K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem exists_proj (hS : S = C ⊔ I) (hd : C ⊓ I = ⊥) : ∃ p : V →ₗ[K] V, (∀ x ∈ S, p x ∈ C) ∧
    (∀ x, x - p x ∈ I) ∧ (∀ x ∈ I, p x = 0) ∧ ∀ x ∈ C, p x = x := by
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl S
  have hc : IsCompl (C ⊔ W) I := by
    constructor
    · rw [Submodule.disjoint_def]
      intro x hxJ hxI
      obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.1 hxJ
      have hcS : c ∈ S := hS ▸ Submodule.mem_sup_left hc
      have hxS : c + w ∈ S := hS ▸ Submodule.mem_sup_right hxI
      have hwS : w ∈ S := by simpa using S.sub_mem hxS hcS
      have hw0 : w = 0 := (Submodule.disjoint_def.1 hW.disjoint) w hwS hw
      subst hw0
      rw [add_zero] at hxI ⊢
      have hcCI : c ∈ C ⊓ I := Submodule.mem_inf.2 ⟨hc, hxI⟩
      rw [hd] at hcCI
      exact hcCI
    · rw [codisjoint_iff, sup_right_comm, ← hS]
      exact hW.sup_eq_top
  have hI0 : ∀ x ∈ I, (C ⊔ W).projection I hc x = 0 := fun x hx =>
    Submodule.projection_apply_of_mem_right hc hx
  have hC1 : ∀ x ∈ C, (C ⊔ W).projection I hc x = x := fun x hx =>
    Submodule.projection_apply_of_mem_left hc (Submodule.mem_sup_left hx)
  refine ⟨(C ⊔ W).projection I hc, ?_, fun x => Submodule.sub_projection_mem hc x, hI0, hC1⟩
  intro x hx
  rw [hS] at hx
  obtain ⟨c, hc', i, hi, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add, hC1 c hc', hI0 i hi, add_zero]
  exact hc'

theorem genBy_latIn (hS : S = C ⊔ I) (hd : C ⊓ I = ⊥) {A B : Submodule (𝓞 K) V} {e : ℕ}
    (hB : rs (𝓞 K) I ≤ B) (hA : A ≤ rs (𝓞 K) S) (h : GenBy A B e) : GenBy (latIn C A) (latIn C B) e := by
  obtain ⟨p, hpC, hpI, -, hpC1⟩ := exists_proj hS hd
  unfold GenBy at h ⊢
  obtain ⟨t, ht, rfl⟩ := h
  have hBA : B ≤ B ⊔ Submodule.span (𝓞 K) (t : Set V) := le_sup_left
  have htA : Submodule.span (𝓞 K) (t : Set V) ≤ B ⊔ Submodule.span (𝓞 K) (t : Set V) := le_sup_right
  have hpB : ∀ x ∈ B, p x ∈ B := fun x hx => by
    have h1 : x - p x ∈ B := hB (hpI x)
    simpa using B.sub_mem hx h1
  have hpA : ∀ x ∈ B ⊔ Submodule.span (𝓞 K) (t : Set V),
      p x ∈ B ⊔ Submodule.span (𝓞 K) (t : Set V) := fun x hx => by
    have h1 : x - p x ∈ B ⊔ Submodule.span (𝓞 K) (t : Set V) := hBA (hB (hpI x))
    simpa using (B ⊔ Submodule.span (𝓞 K) (t : Set V)).sub_mem hx h1
  refine ⟨(t.image p).subtype (· ∈ C), ?_, ?_⟩
  · rw [Finset.card_subtype]
    exact (Finset.card_filter_le _ _).trans (Finset.card_image_le.trans ht)
  apply le_antisymm
  · intro y hy
    change (y : V) ∈ B ⊔ Submodule.span (𝓞 K) (t : Set V) at hy
    obtain ⟨b, hb, s, hs, hbs⟩ := Submodule.mem_sup.1 hy
    have hbS : b ∈ S := hA (hBA hb)
    have key : p s ∈ (Submodule.span (𝓞 K) (((t.image p).subtype (· ∈ C) : Finset C) : Set C)).map
        (C.subtype.restrictScalars (𝓞 K)) := by
      have hmap : p s ∈ (Submodule.span (𝓞 K) (t : Set V)).map (p.restrictScalars (𝓞 K)) := ⟨s, hs, rfl⟩
      rw [Submodule.map_span] at hmap
      refine (Submodule.span_le.2 ?_) hmap
      rintro _ ⟨v, hv, rfl⟩
      have hvC : p v ∈ C := hpC v (hA (htA (Submodule.subset_span hv)))
      refine ⟨⟨p v, hvC⟩, Submodule.subset_span ?_, rfl⟩
      exact Finset.mem_subtype.2 (Finset.mem_image_of_mem p hv)
    obtain ⟨z, hz, hzs⟩ := key
    have hpbC : p b ∈ C := hpC b hbS
    have hpb : (⟨p b, hpbC⟩ : C) ∈ latIn C B := hpB b hb
    have hy' : y = ⟨p b, hpbC⟩ + z := by
      apply Subtype.ext
      rw [Submodule.coe_add]
      show (y : V) = p b + (C.subtype.restrictScalars (𝓞 K)) z
      rw [hzs, ← map_add, hbs, hpC1 y y.2]
    rw [hy']
    exact Submodule.add_mem_sup hpb hz
  · rw [sup_le_iff]
    constructor
    · intro x hx
      exact Submodule.mem_sup_left hx
    · rw [Submodule.span_le]
      intro z hz
      have hz' : (z : V) ∈ t.image p := Finset.mem_subtype.1 hz
      obtain ⟨v, hv, hvz⟩ := Finset.mem_image.1 hz'
      show (z : V) ∈ B ⊔ Submodule.span (𝓞 K) (t : Set V)
      rw [← hvz]
      exact hpA v (htA (Submodule.subset_span hv))

omit [StarRing K] in
theorem le_smulLat {g : ℕ} (hg : 1 ≤ g) {L : Submodule (𝓞 K) V} (hL : rs (𝓞 K) I ≤ L) :
    rs (𝓞 K) I ≤ smulLat (g : 𝓞 K) L := by
  intro x hx
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨(g : K)⁻¹ • x, hL (I.smul_mem _ hx), ?_⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul K,
    smul_smul, mul_inv_cancel₀ hg0, one_smul]

omit [StarRing K] in
theorem mem_smulLat_latIn {g : ℕ} (hg : 1 ≤ g) {L : Submodule (𝓞 K) V} (y : C) :
    y ∈ smulLat (g : 𝓞 K) (latIn C L) ↔ (y : V) ∈ smulLat (g : 𝓞 K) L := by
  have hg0 : (g : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(z : V), hz, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rfl
  · rintro ⟨x, hx, hxy⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
    have hxC : x ∈ C := by
      have hx' : x = (g : K)⁻¹ • (y : V) := by
        rw [← hxy, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hg0,
          one_smul]
      rw [hx']
      exact C.smul_mem _ y.2
    refine ⟨⟨x, hxC⟩, hx, ?_⟩
    apply Subtype.ext
    refine Eq.trans ?_ hxy
    rfl

theorem isModIso_latIn (hS : S = C ⊔ I) (H : HermSpace K V) (H' : HermSpace K C)
    (hH : ∀ x y, H'.B x y = H.B x y) {g : ℕ} (hg : 1 ≤ g) {L' L : Submodule (𝓞 K) V}
    {Γ : Submodule (𝓞 K) (V × V)} (a' : rs (𝓞 K) I ≤ L') (b' : L' ≤ rs (𝓞 K) S) (a : rs (𝓞 K) I ≤ L)
    (b : L ≤ rs (𝓞 K) S) (h : IsModIso H (g : 𝓞 K) L' L Γ) :
    IsModIso H' (g : 𝓞 K) (latIn C L') (latIn C L)
      (Γ.comap ((C.subtype.prodMap C.subtype).restrictScalars (𝓞 K))) := by
  unfold IsModIso at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hIL : rs (𝓞 K) I ≤ smulLat (g : 𝓞 K) L := le_smulLat hg a
  have hIL' : rs (𝓞 K) I ≤ smulLat (g : 𝓞 K) L' := le_smulLat hg a'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨y', y⟩ hp
    exact h1 hp
  · rintro ⟨y', y⟩ ⟨hy', hy⟩
    exact h2 ⟨(mem_smulLat_latIn hg y').1 hy', (mem_smulLat_latIn hg y).1 hy⟩
  · intro y' hy'
    obtain ⟨y, hy⟩ := h3 (y' : V) hy'
    have hyS : y ∈ S := b (Submodule.mem_prod.1 (h1 hy)).2
    rw [hS] at hyS
    obtain ⟨c, hc, i, hi, rfl⟩ := Submodule.mem_sup.1 hyS
    refine ⟨⟨c, hc⟩, ?_⟩
    have h0i : ((0 : V), i) ∈ Γ := h2 (Submodule.mem_prod.2 ⟨Submodule.zero_mem _, hIL hi⟩)
    show ((y' : V), c) ∈ Γ
    simpa using Γ.sub_mem hy h0i
  · intro y hy
    obtain ⟨y', hy'⟩ := h4 (y : V) hy
    have hyS : y' ∈ S := b' (Submodule.mem_prod.1 (h1 hy')).1
    rw [hS] at hyS
    obtain ⟨c, hc, i, hi, rfl⟩ := Submodule.mem_sup.1 hyS
    refine ⟨⟨c, hc⟩, ?_⟩
    have hi0 : (i, (0 : V)) ∈ Γ := h2 (Submodule.mem_prod.2 ⟨hIL' hi, Submodule.zero_mem _⟩)
    show (c, (y : V)) ∈ Γ
    simpa using Γ.sub_mem hy' hi0
  · intro y hy
    exact (mem_smulLat_latIn hg y).2 (h5 (y : V) hy)
  · intro y hy
    exact (mem_smulLat_latIn hg y).2 (h6 (y : V) hy)
  · rintro ⟨p1, p2⟩ hp ⟨q1, q2⟩ hq
    obtain ⟨t, ht⟩ := h7 _ hp _ hq
    exact ⟨t, by simpa [hH] using ht⟩

theorem dual_latIn (hS : S = C ⊔ I) (H : HermSpace K V) (H' : HermSpace K C)
    (hH : ∀ x y, H'.B x y = H.B x y) (ho : ∀ y ∈ S, ∀ i ∈ I, H.B y i = 0) {M : Submodule (𝓞 K) V}
    (hM : IsLatMod M S I) : rs (𝓞 K) I ≤ dual H M ∧ dual H M ≤ rs (𝓞 K) S ∧
      latIn C (dual H M) = Formalism.HermitianLatticesTheory.dual H'.B.flip (latIn C M) := by
  obtain ⟨⟨N, -, hMN⟩, hspan⟩ := hM
  have hIM : rs (𝓞 K) I ≤ M := hMN ▸ le_sup_right
  have hMS : ∀ x ∈ M, x ∈ S := fun x hx => hspan ▸ Submodule.subset_span hx
  have hCS : C ≤ S := hS ▸ le_sup_left
  have hIS : I ≤ S := hS ▸ le_sup_right
  have memD : ∀ x, x ∈ dual H M ↔ x ∈ S ∧ ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x
    rw [GlobalTheory.HermLat.mem_dual_iff, hspan]
  have memR : ∀ y : C, y ∈ Formalism.HermitianLatticesTheory.dual H'.B.flip (latIn C M) ↔
      ∀ z : C, z ∈ latIn C M → H'.B y z ∈ (1 : Submodule (𝓞 K) K) := by
    intro y
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, LinearMap.flip_apply]
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [memD]
    refine ⟨hIS hi, fun y hy => ?_⟩
    have hiy : H.B i y = 0 := by rw [← H.herm, ho y (hMS y hy) i hi, star_zero]
    rw [hiy]
    exact Submodule.zero_mem _
  · intro x hx
    exact ((memD x).1 hx).1
  · ext y
    change (y : V) ∈ dual H M ↔ _
    rw [memD, memR]
    constructor
    · rintro ⟨-, hy⟩ z hz
      rw [hH]
      exact hy _ hz
    · intro hy
      refine ⟨hCS y.2, fun x hx => ?_⟩
      have hxS := hMS x hx
      rw [hS] at hxS
      obtain ⟨c, hc, i, hi, rfl⟩ := Submodule.mem_sup.1 hxS
      have hcM : c ∈ M := by simpa using M.sub_mem hx (hIM hi)
      have h1 := hy ⟨c, hc⟩ hcM
      rw [hH] at h1
      rw [map_add, ho _ (hCS y.2) i hi, add_zero]
      exact h1

theorem intLat_latIn (hS : S = C ⊔ I) (hd : C ⊓ I = ⊥) (H : HermSpace K V) (H' : HermSpace K C)
    (hH : ∀ x y, H'.B x y = H.B x y) (ho : ∀ y ∈ S, ∀ i ∈ I, H.B y i = 0) {M : Submodule (𝓞 K) V}
    (hM : IsLatMod M S I) (hi : ∀ x ∈ M, ∀ y ∈ M, H.B x y ∈ (1 : Submodule (𝓞 K) K)) :
    IsIntLat H'.B.flip (latIn C M) ∧ (discN H'.B.flip (latIn C M) : ℝ) = del H M ^ 2 := by
  obtain ⟨p, hpC, hpI, hpI0, hpC1⟩ := exists_proj hS hd
  have hCS : C ≤ S := hS ▸ le_sup_left
  obtain ⟨hID, hDS, hDeq⟩ := dual_latIn hS H H' hH ho hM
  obtain ⟨hIM, hMS⟩ := le_of_latMod hM
  have hMD : M ≤ dual H M := by
    intro x hx
    rw [GlobalTheory.HermLat.mem_dual_iff, hM.2]
    exact ⟨hM.2 ▸ Submodule.subset_span hx, fun y hy => hi x hx y hy⟩
  refine ⟨?_, ?_⟩
  · unfold GlobalTheory.Mass.IsIntLat
    refine ⟨latIn_isLattice p hCS hpC hpI hpI0 hpC1 hM, ?_⟩
    intro x hx y hy
    rw [LinearMap.flip_apply, hH]
    exact hi _ hy _ hx
  · have h1 : GlobalTheory.HermLat.idx M (dual H M) = 1 := by
      show (dual H M).toAddSubgroup.relIndex M.toAddSubgroup = 1
      exact AddSubgroup.relIndex_eq_one.2 ((Submodule.toAddSubgroup_le _ _).2 hMD)
    unfold GlobalTheory.Mass.discN
    rw [← hDeq, ← idx_eq, idx_latIn p hpC hpI hID hDS hIM]
    unfold GlobalTheory.HermLat.del GlobalTheory.HermLat.gidx
    rw [h1, Nat.cast_one, div_one, Real.sq_sqrt (Nat.cast_nonneg _)]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem exists_res (H : HermSpace K V) (hpd : PD (hRes H.B.flip C)) :
    ∃ H' : HermSpace K C, (∀ x y, H'.B x y = H.B x y) ∧ PD H'.B.flip := by
  refine ⟨⟨H.B.domRestrict₁₂ C C, fun x y => H.herm x y, fun x hx => ?_⟩, fun x y => rfl, fun τ x hx => ?_⟩
  · by_contra hne
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have h1 := hpd τ x hne
    have h2 : (hRes H.B.flip C) x x = 0 := by
      simpa [hRes, LinearMap.domRestrict₁₂_apply, LinearMap.flip_apply] using hx x
    rw [h2, map_zero, Complex.zero_re] at h1
    exact lt_irrefl _ h1
  · simpa [hRes, LinearMap.domRestrict₁₂_apply, LinearMap.flip_apply] using hpd τ x hx

omit [NumberField K] [StarRing K] in
theorem fixLat_comap (Γ : Submodule (𝓞 K) (V × V)) :
    fixLat (Γ.comap ((C.subtype.prodMap C.subtype).restrictScalars (𝓞 K))) = latIn C (fixLat Γ) := by
  ext y
  exact Iff.rfl

private theorem flag_X_isotropic {H : HermSpace K V} {r : ℕ} (F : FlagD H r) :
    ∀ x ∈ F.X, ∀ y ∈ F.X, H.B x y = 0 := by
  have hgen : ∀ a : Fin r, F.X ≤ LinearMap.ker (H.B (F.e a.castSucc)) := by
    intro a
    unfold FlagD.X FlagD.Xa
    rw [Submodule.span_le]
    rintro _ ⟨b, -, rfl⟩
    simpa using F.iso a b
  intro x hx y hy
  have hXy : F.X ≤ LinearMap.ker (H.B.flip y) := by
    unfold FlagD.X FlagD.Xa
    rw [Submodule.span_le]
    rintro _ ⟨a, -, rfl⟩
    simpa using hgen a hy
  simpa using hXy hx

private theorem apply_mem_one_of_mem_flagPairDefinitePartLattice {H : HermSpace K V} {r : ℕ} (F F' : FlagD H r) {Λ : Submodule (𝓞 K) V}
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) :
    ∀ x ∈ flagPairDefinitePartLattice F F' Λ, ∀ y ∈ flagPairDefinitePartLattice F F' Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
  intro x hx y hy
  have hx1 := Submodule.mem_inf.1 (Submodule.mem_inf.1 hx).1
  have hy1 := Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1
  have hxp : ∀ w ∈ F.X ⊔ F'.X, H.B x w = 0 := (GlobalTheory.HermLat.mem_perp_iff H (F.X ⊔ F'.X) x).1 hx1.1
  have hyp : ∀ w ∈ F.X ⊔ F'.X, H.B y w = 0 := (GlobalTheory.HermLat.mem_perp_iff H (F.X ⊔ F'.X) y).1 hy1.1
  obtain ⟨l, hl, u, hu, rfl⟩ := Submodule.mem_sup.1 hx1.2
  obtain ⟨m, hm, v, hv, rfl⟩ := Submodule.mem_sup.1 hy1.2
  have huX : u ∈ F.X ⊔ F'.X := Submodule.mem_sup_left hu
  have hvX : v ∈ F.X ⊔ F'.X := Submodule.mem_sup_left hv
  have a1 : H.B (l + u) v = 0 := hxp v hvX
  have a2 : H.B u (m + v) = 0 := by rw [← H.herm, hyp u huX, star_zero]
  have a3 : H.B u v = 0 := flag_X_isotropic F u hu v hv
  have a4 : H.B u m = 0 := by
    have h' := a2
    rw [map_add (H.B u) m v, a3, add_zero] at h'
    exact h'
  rw [map_add (H.B (l + u)) m v, a1, add_zero, map_add H.B l u, LinearMap.add_apply, a4, add_zero]
  exact hΛ l hl m hm

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ H' : HermSpace K N.Wt, (∀ x y, H'.B x y = H.B x y) ∧ GlobalTheory.Mass.PD H'.B.flip ∧ GlobalTheory.Mass.IsIntLat H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) ∧ (GlobalTheory.Mass.discN H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) : ℝ) = N.NT ^ 2 ∧ GenBy (Formalism.HermitianLatticesTheory.dual H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ))) (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) 1 ∧ IsDat H' g (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) N.j (N.gI g Λ) (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F' N.F Λ), (iotaGraph N.F N.F' Λ (g : 𝓞 K)).comap ((N.Wt.subtype.prodMap N.Wt.subtype).restrictScalars (𝓞 K))) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT
  obtain ⟨-, hLift, -, -, -, -, hwS, -, hPD, -, -, -⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hdel, hdel', hgen, hM, hM', -⟩ := GlobalTheory.T.flagPairDefinitePartLattice_discriminant_eq_quotient K V H hK r N g Λ hg hT
  have hiso := GlobalTheory.T.isHermIsometryGraphModScalar_flagPairIota K V H hK r N g Λ hg hT
  obtain ⟨hThLa, -, -, -, -, hgenLa, -, hTh⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hT
  obtain ⟨H', hH, hPD'⟩ := exists_res H hPD
  have hd : N.Wt ⊓ II N.F N.F' = ⊥ := hLift.2.1
  have ho : ∀ y ∈ wSp N.F N.F', ∀ i ∈ II N.F N.F', H.B y i = 0 := fun y hy i hi =>
    (GlobalTheory.HermLat.mem_perp_iff H (V0 N.F N.F') y).1 hy i
      (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_inf.1 hi).1))
  have hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx y hy
    have hdu : dual H Λ = Λ := hT.1.1.2
    rw [← hdu] at hx
    exact ((GlobalTheory.HermLat.mem_dual_iff H _ x).1 hx).2 y (hdu.symm ▸ hy)
  obtain ⟨p, hpC, hpI, -, -⟩ := exists_proj hwS hd
  obtain ⟨hIM, hMS⟩ := le_of_latMod hM
  obtain ⟨hIM', hMS'⟩ := le_of_latMod hM'
  obtain ⟨hInt, hdisc⟩ := intLat_latIn hwS hd H H' hH ho hM (apply_mem_one_of_mem_flagPairDefinitePartLattice N.F N.F' hΛ)
  obtain ⟨hInt', hdisc'⟩ := intLat_latIn hwS hd H H' hH ho hM' (apply_mem_one_of_mem_flagPairDefinitePartLattice N.F' N.F hΛ)
  obtain ⟨-, hDS, hDeq⟩ := dual_latIn hwS H H' hH ho hM
  have hILa : rs (𝓞 K) (II N.F N.F') ≤ latLa N.F N.F' Λ (g : 𝓞 K) := (le_of_latMod hTh).1.trans hThLa
  have hfix := fixLat_comap (C := N.Wt) (iotaGraph N.F N.F' Λ (g : 𝓞 K))
  refine ⟨H', hH, hPD', hInt, ?_, ?_, ?_⟩
  · rw [hdisc, hdel]
  · rw [← hDeq]
    exact genBy_latIn hwS hd hIM hDS hgen
  · unfold IsDat
    dsimp only
    refine ⟨hInt', ?_, isModIso_latIn hwS H H' hH hg hIM' hMS' hIM hMS hiso, ?_, ?_⟩
    · have hr : (GlobalTheory.Mass.discN H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F' N.F Λ)) : ℝ) =
          GlobalTheory.Mass.discN H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) := by
        rw [hdisc', hdisc, hdel, hdel']
      exact_mod_cast hr
    · rw [hfix]
      change GlobalTheory.HermLat.idx (latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) (latIn N.Wt (latLa N.F N.F' Λ (g : 𝓞 K))) = _
      rw [idx_latIn p hpC hpI hIM hMS hILa]
      rfl
    · rw [hfix]
      exact genBy_latIn hwS hd hILa hMS hgenLa

end GlobalTheory.DegCnt.ToLift
