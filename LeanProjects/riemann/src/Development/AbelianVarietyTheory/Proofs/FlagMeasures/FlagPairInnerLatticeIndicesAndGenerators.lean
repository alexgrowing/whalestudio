import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeQuotientGensAndIntermediateCount
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLocalizedModuleSubtype
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeOfLatMod
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdxSupRight
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairIdealKillsDiscriminantModules

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.InnerIndex

section General
variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W]

theorem idx_le_of_rel {A B A' B' : Submodule R W} (ρ : W → W → Prop) (hfin : idx B' A' ≠ 0)
    (hex : ∀ y ∈ B, ∃ z ∈ B', ρ y z)
    (hinj : ∀ y ∈ B, ∀ y₂ ∈ B, ∀ z z₂, ρ y z → ρ y₂ z₂ → -z + z₂ ∈ A' → -y + y₂ ∈ A) :
    idx B A ≤ idx B' A' := by
  unfold idx AddSubgroup.relIndex AddSubgroup.index at *
  haveI := Nat.finite_of_card_ne_zero hfin
  choose f hf hρ using hex
  refine Nat.card_le_card_of_injective
    (fun q => QuotientAddGroup.mk (⟨f q.out.1 q.out.2, hf _ _⟩ : B'.toAddSubgroup)) ?_
  intro q q' h
  have h1 := QuotientAddGroup.eq.1 h
  rw [← q.out_eq, ← q'.out_eq]
  exact QuotientAddGroup.eq.2 (hinj _ q.out.2 _ q'.out.2 _ _ (hρ _ _) (hρ _ _) h1)

theorem gidx_of_le' {A B : Submodule R W} (h : B ≤ A) : gidx A B = idx A B := by
  have : idx B A = 1 := AddSubgroup.relIndex_eq_one.2 h
  simp [gidx, this]

theorem exists_fg_proj {N Y I : Submodule R W} (hN : N.FG) (h : N ≤ Y ⊔ I) :
    ∃ G : Submodule R W, G.FG ∧ G ≤ Y ∧ G ⊔ I = N ⊔ I := by
  obtain ⟨s, rfl⟩ := hN
  have : ∀ x : s, ∃ y ∈ Y, ∃ i ∈ I, y + i = x := fun x =>
    Submodule.mem_sup.1 (h (Submodule.subset_span x.2))
  choose y hy i hi e using this
  refine ⟨Submodule.span R (Set.range y), Submodule.fg_span (Set.finite_range y),
    Submodule.span_le.2 (by rintro _ ⟨x, rfl⟩; exact hy x), le_antisymm ?_ ?_⟩
  · refine sup_le (Submodule.span_le.2 ?_) le_sup_right
    rintro _ ⟨x, rfl⟩
    rw [eq_sub_of_add_eq (e x)]
    exact sub_mem (Submodule.mem_sup_left (Submodule.subset_span x.2)) (Submodule.mem_sup_right (hi x))
  · refine sup_le (Submodule.span_le.2 ?_) le_sup_right
    intro x hx
    have := e ⟨x, hx⟩
    simp only at this
    rw [← this]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨_, rfl⟩) (hi _)

end General

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] [FiniteDimensional K V] in
theorem latMod_inf {M : Submodule (𝓞 K) V} {S I T : Submodule K V} (hM : IsLatMod M S I)
    (hI : I ≤ T) (hT : T ≤ S) : IsLatMod (M ⊓ rs (𝓞 K) T) T I := by
  refine ⟨?_, Compl.span_inf (hM.2 ▸ hT)⟩
  obtain ⟨⟨N, hN, rfl⟩, -⟩ := hM
  refine ⟨N ⊓ rs (𝓞 K) T, hN.of_le inf_le_left, ?_⟩
  have hI' : rs (𝓞 K) I ≤ rs (𝓞 K) T := hI
  rw [sup_comm, sup_inf_assoc_of_le _ hI', sup_comm]

omit [NumberField K] [StarRing K] [FiniteDimensional K V] in
theorem latMod_sup {M M' : Submodule (𝓞 K) V} {S S' I : Submodule K V} (hM : IsLatMod M S I)
    (hM' : IsLatMod M' S' I) : IsLatMod (M ⊔ M') (S ⊔ S') I := by
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨N, hN, rfl⟩, -⟩ := hM
    obtain ⟨⟨N', hN', rfl⟩, -⟩ := hM'
    exact ⟨N ⊔ N', hN.sup hN', (sup_sup_distrib_right _ _ _).symm⟩
  · rw [← hM.2, ← hM'.2, ← Submodule.span_union]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
      exact add_mem (Submodule.subset_span (Or.inl ha)) (Submodule.subset_span (Or.inr hb))
    · rintro x (hx | hx)
      exacts [Submodule.mem_sup_left hx, Submodule.mem_sup_right hx]

omit [StarRing K] in

theorem gens_of_torsion {A D : Submodule (𝓞 K) V} {Y I : Submodule K V} (hA : IsLatMod A (Y ⊔ I) I)
    (hAD : A ≤ D) {n : ℕ} (hn : n ≠ 0) (hD : ∀ x ∈ D, (n : 𝓞 K) • x ∈ A) :
    ∃ t : Finset V, t.card ≤ Module.finrank K Y ∧ D = A ⊔ Submodule.span (𝓞 K) (t : Set V) := by
  have hle := (DelScale.le_of_latMod hA).2
  obtain ⟨⟨N, hN, rfl⟩, -⟩ := hA
  have h1 : N ≤ rs (𝓞 K) Y ⊔ rs (𝓞 K) I := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (show x ∈ Y ⊔ I from hle (Submodule.mem_sup_left hx))
    exact Submodule.add_mem_sup ha hb
  obtain ⟨G, hG, hGY, e⟩ := exists_fg_proj hN h1
  rw [← e] at hAD hD ⊢
  let ι : Y →ₗ[𝓞 K] V := Y.subtype.restrictScalars (𝓞 K)
  have hι : Function.Injective ι := Subtype.val_injective
  have hmap : (G.comap ι).map ι = G := by
    rw [Submodule.map_comap_eq]
    refine inf_eq_right.2 fun x hx => ⟨⟨x, hGY hx⟩, rfl⟩
  have hfg : (G.comap ι).FG := Submodule.fg_of_fg_map_injective ι hι (hmap.symm ▸ hG)
  obtain ⟨c, t, hc, htc, hct, hspan⟩ := GlobalTheory.Mass.LatticeGens.exists_scaled_span K Y _ hfg
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hcan : ∀ x : V, (n : 𝓞 K) • ((n : K)⁻¹ • x) = x := fun x => by
    rw [← IsScalarTower.algebraMap_smul K, map_natCast, smul_smul, mul_inv_cancel₀ hn', one_smul]
  have hcan' : ∀ x : V, (n : K)⁻¹ • ((n : 𝓞 K) • x) = x := fun x => by
    rw [← IsScalarTower.algebraMap_smul K (n : 𝓞 K), map_natCast, smul_smul, inv_mul_cancel₀ hn', one_smul]
  let κ : Y →ₗ[𝓞 K] V := ((n : K)⁻¹ • Y.subtype).restrictScalars (𝓞 K)
  obtain ⟨t', h1, h2⟩ := GlobalTheory.Mass.LatticeGens.exists_gens_of_between (G ⊔ rs (𝓞 K) I) (c * n)
    (mul_ne_zero hc (Nat.cast_ne_zero.2 hn)) (t.image κ) (by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      rw [mul_smul]
      refine Submodule.mem_sup_left ?_
      have : (n : 𝓞 K) • κ y = ι y := hcan _
      rw [this, ← map_smul]
      exact hct y hy) D hAD (by
      intro x hx
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hD x hx)
      rw [← hcan' x, ← hab, smul_add, add_comm]
      refine Submodule.add_mem_sup (Submodule.mem_sup_right (I.smul_mem _ hb)) ?_
      rw [Finset.coe_image, ← Submodule.map_span]
      exact ⟨⟨a, hGY ha⟩, hspan ha, rfl⟩)
  exact ⟨t', h1.trans (Finset.card_image_le.trans htc), h2⟩

section Pair
open GlobalTheory.UnimodQuot GlobalTheory.DegCnt.Kill

variable (H : HermSpace K V) {X X' : Submodule K V} {Λ : Submodule (𝓞 K) V}
  (hX : ∀ x ∈ X, ∀ y ∈ X, H.B x y = 0) (hX' : ∀ x ∈ X', ∀ y ∈ X', H.B x y = 0)
  (hr : ∀ x ∈ X, (∀ y ∈ X', H.B x y = 0) → x ∈ X') (hr' : ∀ x ∈ X', (∀ y ∈ X, H.B x y = 0) → x ∈ X)

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem perp_anti {S T : Submodule K V} (h : S ≤ T) : perp H T ≤ perp H S := fun y hy =>
  (mem_perp_iff H S y).2 fun x hx => (mem_perp_iff H T y).1 hy x (h hx)

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
include hX hX' hr hr' in

theorem rad_sup : ∀ x ∈ X ⊔ X', (∀ y ∈ X ⊔ X', H.B x y = 0) ↔ x ∈ X ⊓ X' := by
  intro x hx
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
    have h1 : a ∈ X' := hr a ha fun y hy => by
      simpa [hX' b hb y hy] using h y (Submodule.mem_sup_right hy)
    have h2 : b ∈ X := hr' b hb fun y hy => by
      simpa [hX a ha y hy] using h y (Submodule.mem_sup_left hy)
    exact ⟨add_mem ha h2, add_mem h1 hb⟩
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, hX x h1 a ha, hX' x h2 b hb, add_zero]

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem rad_perp {U I : Submodule K V} (hIU : I ≤ U) (h : ∀ x ∈ U, (∀ y ∈ U, H.B x y = 0) ↔ x ∈ I) :
    ∀ x ∈ perp H U, (∀ y ∈ perp H U, H.B x y = 0) ↔ x ∈ I := by
  intro x hx
  constructor
  · intro h1
    exact (h x (mem_of_perp_perp H U fun y hy => swap0 (h1 y hy))).1 ((mem_perp_iff H U x).1 hx)
  · intro h1 y hy
    exact swap0 ((mem_perp_iff H U y).1 hy x (hIU h1))

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
include hX hr' in
theorem perp_le_sup : perp H X ≤ perp H (X ⊔ X') ⊔ X := by
  intro v hv
  refine mem_of_perp_perp H _ fun w hw => ?_
  rw [mem_perp_iff] at hw hv
  have h1 : w ∈ X ⊔ X' := mem_of_perp_perp H _ fun x hx => swap0 (hw x (Submodule.mem_sup_left hx))
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h1
  have h2 : b ∈ X := hr' b hb fun y hy => by
    simpa [hX a ha y hy] using hw y (Submodule.mem_sup_right hy)
  exact swap0 (hv _ (add_mem ha h2))

omit [NumberField K] [FiniteDimensional K V] in

theorem inf_sup_eq {U I : Submodule K V} (hIX : I ≤ X) (hIU : I ≤ U) (hI : ∀ x ∈ X, ∀ y ∈ I, H.B x y = 0) :
    rs (𝓞 K) (perp H U) ⊓ (Λ ⊔ rs (𝓞 K) X) =
      rs (𝓞 K) (perp H U) ⊓ (((Λ ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I) ⊔ rs (𝓞 K) X) := by
  refine le_antisymm ?_ (inf_le_inf_left _ (sup_le (sup_le (inf_le_left.trans le_sup_left)
    (le_trans (show rs (𝓞 K) I ≤ rs (𝓞 K) X from hIX) le_sup_right)) le_sup_right))
  rintro y ⟨hy, hy'⟩
  refine ⟨hy, ?_⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
  refine Submodule.add_mem_sup (Submodule.mem_sup_left ⟨ha, (mem_perp_iff H I a).2 fun i hi => ?_⟩) hb
  simpa [hI b hb i hi] using (mem_perp_iff H U _).1 hy i (hIU hi)

include hX hX' hr hr' in

theorem inner_unimod (hU : IsUnimod H Λ) :
    IsUnimodMod H (rs (𝓞 K) (perp H (X ⊔ X')) ⊓ (Λ ⊔ rs (𝓞 K) X)) (perp H (X ⊔ X')) (X ⊓ X') := by
  have hM := isUnimodMod_quot H hU hX
  rw [inf_sup_eq H (I := X) le_rfl le_sup_left hX, sup_assoc, sup_idem]
  generalize (Λ ⊓ rs (𝓞 K) (perp H X)) ⊔ rs (𝓞 K) X = M at hM
  have hle := DelScale.le_of_latMod hM.1
  have hdec : M ≤ rs (𝓞 K) (perp H (X ⊔ X')) ⊔ rs (𝓞 K) X := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (perp_le_sup H hX hr' (hle.2 hx))
    exact Submodule.add_mem_sup ha hb
  have hsp : Submodule.span K ((rs (𝓞 K) (perp H (X ⊔ X')) ⊓ M : Submodule (𝓞 K) V) : Set V) =
      perp H (X ⊔ X') := by
    rw [inf_comm]
    exact Compl.span_inf (hM.1.2 ▸ perp_anti H le_sup_left)
  refine ⟨⟨?_, hsp⟩, ?_⟩
  · obtain ⟨N, hN, rfl⟩ := hM.1.1
    obtain ⟨G, hG, hGU, e⟩ := exists_fg_proj hN (le_sup_left.trans hdec)
    refine ⟨G, hG, ?_⟩
    rw [← e, inf_comm, sup_inf_assoc_of_le _ hGU]
    congr 1
    ext x
    constructor
    · rintro ⟨h1, h2⟩
      exact (rad_sup H hX hX' hr hr' x (Submodule.mem_sup_left h1)).1 ((mem_perp_iff H _ x).1 h2)
    · intro h
      exact ⟨h.1, (mem_perp_iff H _ x).2
        ((rad_sup H hX hX' hr hr' x (Submodule.mem_sup_left h.1)).2 h)⟩
  · ext y
    rw [mem_dual_iff, hsp]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← hM.2, SetLike.mem_coe, mem_dual_iff, hM.1.2]
      refine ⟨perp_anti H le_sup_left h1, fun m hm => ?_⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hdec hm)
      rw [map_add, (mem_perp_iff H _ y).1 h1 b (Submodule.mem_sup_left hb), add_zero]
      exact h2 a ⟨ha, by simpa using sub_mem hm (hle.1 hb)⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun x hx => ?_⟩
      rw [← hM.2, SetLike.mem_coe, mem_dual_iff] at h2
      exact h2.2 x hx.2

omit [NumberField K] [FiniteDimensional K V] in

theorem quot_inf {I : Submodule K V} (hIX : I ≤ X) (hI : ∀ x ∈ X, ∀ y ∈ I, H.B x y = 0) :
    ((Λ ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I) ⊓ rs (𝓞 K) X = (Λ ⊓ rs (𝓞 K) X) ⊔ rs (𝓞 K) I := by
  have h1 : rs (𝓞 K) I ≤ rs (𝓞 K) X := hIX
  have h2 : rs (𝓞 K) X ≤ rs (𝓞 K) (perp H I) := fun x hx => (mem_perp_iff H I x).2 (hI x hx)
  rw [sup_comm, sup_inf_assoc_of_le _ h1, sup_comm, inf_assoc, inf_eq_right.2 h2]

include hX hX' hr hr' in

theorem idx_eq_del (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hU : IsUnimod H Λ) {U I : Submodule K V}
    (eU : U = X ⊔ X') (eI : I = X ⊓ X') {M : Submodule (𝓞 K) V}
    (eM : M = (Λ ⊓ rs (𝓞 K) (perp H I)) ⊔ rs (𝓞 K) I) :
    rs (𝓞 K) (perp H U) ⊓ (Λ ⊔ rs (𝓞 K) X) = rs (𝓞 K) (perp H U) ⊓ (M ⊔ rs (𝓞 K) X) ∧
    idx (rs (𝓞 K) (perp H U) ⊓ (M ⊔ rs (𝓞 K) X)) (M ⊓ rs (𝓞 K) (perp H U)) ≠ 0 ∧
    (idx (rs (𝓞 K) (perp H U) ⊓ (M ⊔ rs (𝓞 K) X)) (M ⊓ rs (𝓞 K) (perp H U)) : ℝ) =
      del H (M ⊓ rs (𝓞 K) (perp H U)) := by
  subst eU eI
  have e := inf_sup_eq H (Λ := Λ) (X := X) (U := X ⊔ X') (I := X ⊓ X') inf_le_left
    (inf_le_left.trans le_sup_left) (fun x hx y hy => hX x hx y hy.1)
  rw [← eM] at e
  have hL := inner_unimod H hX hX' hr hr' hU
  rw [e] at hL
  have hM := isUnimodMod_quot H hU (I := X ⊓ X') fun x hx y hy => hX x hx.1 y hy.1
  rw [← eM] at hM
  have hIU : X ⊓ X' ≤ X ⊔ X' := inf_le_left.trans le_sup_left
  have hrad := rad_sup H hX hX' hr hr'
  have hIP : X ⊓ X' ≤ perp H (X ⊔ X') := fun x hx => (mem_perp_iff H _ x).2 ((hrad x (hIU hx)).2 hx)
  obtain ⟨-, h2, h3, -⟩ := DelScale.main K V H hK _ _ _ _ hIP (rad_perp H hIU hrad) hL.1
    (latMod_inf hM.1 hIP (perp_anti H hIU))
  have hle : M ⊓ rs (𝓞 K) (perp H (X ⊔ X')) ≤ rs (𝓞 K) (perp H (X ⊔ X')) ⊓ (M ⊔ rs (𝓞 K) X) :=
    le_inf inf_le_right (inf_le_left.trans le_sup_left)
  rw [gidx_of_le' hle] at h2 h3
  have h4 : del H (rs (𝓞 K) (perp H (X ⊔ X')) ⊓ (M ⊔ rs (𝓞 K) X)) = 1 := by
    simp [del, gidx, idx, hL.2]
  refine ⟨e, by exact_mod_cast h2.ne', by rw [h3, h4, mul_one]⟩

include hX hX' hr hr' in

theorem core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hU : IsUnimod H Λ) {Y : Submodule K V} (hY : X = Y ⊔ X ⊓ X')
    {M L L' Λ₁ A A' : Submodule (𝓞 K) V}
    (eM : M = (Λ ⊓ rs (𝓞 K) (perp H (X ⊓ X'))) ⊔ rs (𝓞 K) (X ⊓ X'))
    (eL : L = rs (𝓞 K) (perp H (X ⊔ X')) ⊓ (Λ ⊔ rs (𝓞 K) X))
    (eL' : L' = rs (𝓞 K) (perp H (X ⊔ X')) ⊓ (Λ ⊔ rs (𝓞 K) X'))
    (e1 : Λ₁ = M ⊓ rs (𝓞 K) (perp H (X ⊔ X')))
    (eA : A = (Λ ⊓ rs (𝓞 K) X) ⊔ rs (𝓞 K) (X ⊓ X')) (eA' : A' = (Λ ⊓ rs (𝓞 K) X') ⊔ rs (𝓞 K) (X ⊓ X')) :
    (idx L Λ₁ : ℝ) * idx (M ⊓ rs (𝓞 K) (X ⊔ X')) (A ⊔ A') = del H (A ⊔ A') ∧ idx L' Λ₁ = idx L Λ₁ ∧
      Λ₁ ≤ L ⊓ L' ∧ idx (L ⊓ L') Λ₁ ≤ idx (M ⊓ rs (𝓞 K) (X ⊔ X')) (A ⊔ A') ∧
      GenBy L Λ₁ (Module.finrank K Y) := by
  obtain ⟨a1, a2, a3⟩ := idx_eq_del H hX hX' hr hr' hK hU rfl rfl eM
  obtain ⟨b1, b2, b3⟩ := idx_eq_del H hX' hX hr' hr hK hU (sup_comm X X') (inf_comm X X') eM
  rw [a1] at eL
  rw [b1] at eL'
  rw [← eL, ← e1] at a2 a3
  rw [← eL', ← e1] at b2 b3
  have hXI : ∀ x ∈ X, ∀ y ∈ X ⊓ X', H.B x y = 0 := fun x hx y hy => hX x hx y hy.1
  have hXI' : ∀ x ∈ X', ∀ y ∈ X ⊓ X', H.B x y = 0 := fun x hx y hy => hX' x hx y hy.2
  rw [← quot_inf H inf_le_left hXI, ← eM] at eA
  rw [← quot_inf H inf_le_right hXI', ← eM] at eA'
  have hM := isUnimodMod_quot H hU (I := X ⊓ X') fun x hx y hy => hX x hx.1 y hy.1
  rw [← eM] at hM
  have hIM := (DelScale.le_of_latMod hM.1).1
  have hIU : X ⊓ X' ≤ X ⊔ X' := inf_le_left.trans le_sup_left
  have hrad := rad_sup H hX hX' hr hr'
  have hXP : X ≤ perp H (X ⊓ X') := fun x hx => (mem_perp_iff H _ x).2 (hXI x hx)
  have hXP' : X' ≤ perp H (X ⊓ X') := fun x hx => (mem_perp_iff H _ x).2 (hXI' x hx)
  have hA : IsLatMod A X (X ⊓ X') := eA ▸ latMod_inf hM.1 inf_le_left hXP
  have hA' : IsLatMod A' X' (X ⊓ X') := eA' ▸ latMod_inf hM.1 inf_le_right hXP'
  obtain ⟨-, c2, c3, -⟩ := DelScale.main K V H hK _ _ _ _ hIU hrad
    (latMod_inf hM.1 hIU (sup_le hXP hXP')) (latMod_sup hA hA')
  have hle : A ⊔ A' ≤ M ⊓ rs (𝓞 K) (X ⊔ X') := by
    rw [eA, eA']
    exact sup_le (inf_le_inf_left _ (show rs (𝓞 K) X ≤ rs (𝓞 K) (X ⊔ X') from le_sup_left (a := X)))
      (inf_le_inf_left _ (show rs (𝓞 K) X' ≤ rs (𝓞 K) (X ⊔ X') from le_sup_right (a := X)))
  rw [gidx_of_le' hle] at c2 c3
  have hradI : ∀ x ∈ perp H (X ⊓ X'), (∀ y ∈ perp H (X ⊓ X'), H.B x y = 0) ↔ x ∈ X ⊓ X' :=
    rad_perp H le_rfl fun x hx => ⟨fun _ => hx, fun _ => hXI x hx.1⟩
  have d := (Compl.main K V H hK M _ _ _ hIU (sup_le hXP hXP') hradI hrad hM).1
  rw [inf_eq_right.2 (perp_anti H hIU), ← e1] at d
  refine ⟨by rw [c3, d, a3, mul_comm], by exact_mod_cast b3.trans a3.symm, ?_, ?_, ?_⟩
  · rw [e1, eL, eL']
    exact le_inf (le_inf inf_le_right (inf_le_left.trans le_sup_left))
      (le_inf inf_le_right (inf_le_left.trans le_sup_left))
  · refine idx_le_of_rel (fun y z => ∃ x ∈ X, ∃ x' ∈ X', y - x ∈ M ∧ y - x' ∈ M ∧ z = x - x')
      (by exact_mod_cast c2.ne') ?_ ?_
    · rw [eL, eL']
      rintro y ⟨⟨-, h1⟩, -, h2⟩
      obtain ⟨m, hm, x, hx, e⟩ := Submodule.mem_sup.1 h1
      obtain ⟨m', hm', x', hx', e'⟩ := Submodule.mem_sup.1 h2
      have f : y - x ∈ M := by rw [← e]; simpa using hm
      have f' : y - x' ∈ M := by rw [← e']; simpa using hm'
      refine ⟨x - x', ⟨?_, sub_mem (Submodule.mem_sup_left (S := X) hx) (Submodule.mem_sup_right (T := X') hx')⟩,
        x, hx, x', hx', f, f', rfl⟩
      have := sub_mem f' f
      simpa using this
    · rw [eL, eL', e1, eA, eA']
      rintro y ⟨⟨hy, -⟩, -⟩ w ⟨⟨hw, -⟩, -⟩ _ _ ⟨x, hx, x', hx', f, -, rfl⟩ ⟨u, hu, u', hu', g, -, rfl⟩ h
      obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 h
      refine ⟨?_, add_mem (neg_mem hy) hw⟩
      have h1 : u - x - a ∈ X := sub_mem (sub_mem hu hx) ha.2
      have h2 : u - x - a ∈ X' := by
        have : u - x - a = b + (u' - x') := by
          calc u - x - a = (-(x - x') + (u - u')) - a + (u' - x') := by abel
            _ = _ := by rw [← e]; abel
        rw [this]
        exact add_mem hb.2 (sub_mem hu' hx')
      have h3 : -y + w = (w - u) - (y - x) + (u - x - a) + a := by abel
      rw [SetLike.mem_coe, h3]
      exact add_mem (add_mem (sub_mem g f) (hIM ⟨h1, h2⟩)) ha.1
  · obtain ⟨t, h1, h2⟩ := gens_of_torsion (D := rs (𝓞 K) X ⊓ (M ⊔ rs (𝓞 K) (perp H (X ⊔ X'))))
      (Y := Y) (I := X ⊓ X') (A := A) (by rw [← hY]; exact hA)
      (by rw [eA]; exact le_inf inf_le_right (inf_le_left.trans le_sup_left)) a2 (by
        rintro x ⟨hx, hx'⟩
        obtain ⟨m, hm, u, hu, e⟩ := Submodule.mem_sup.1 hx'
        have hL : u ∈ L := by
          rw [eL]
          refine ⟨hu, ?_⟩
          rw [eq_sub_of_add_eq' e]
          exact sub_mem (Submodule.mem_sup_right hx) (Submodule.mem_sup_left hm)
        have h3 := GlobalTheory.Mass.LatticeGens.idxN_smul_mem Λ₁ L hL
        rw [eA]
        refine ⟨?_, Submodule.smul_mem _ _ hx⟩
        rw [← e, smul_add]
        exact add_mem (M.smul_mem _ hm) ((e1.le.trans inf_le_left) h3))
    rw [eA] at h2
    obtain ⟨t', h3, h4⟩ := Compl.gen_glue M _ _ t h2
    exact ⟨t', h3.trans h1, by rw [eL, e1, h4]⟩

end Pair

section Flags
open GlobalTheory.DegCnt.Kill GlobalTheory.DegCnt.FrameCramer

variable {H : HermSpace K V} {r : ℕ}

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem flag_rad (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) (hD : Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0)
    (h : ∀ a : Fin r, j ≤ a.val → ∃ c : K, F.e a.castSucc = c • F'.e a.castSucc) :
    ∀ x ∈ F.X, (∀ y ∈ F'.X, H.B x y = 0) → x ∈ F'.X := by
  intro x hx h0
  obtain ⟨y, hy, i, -, hi, rfl⟩ := X_le F F' j h x hx
  obtain ⟨c, -, rfl⟩ := exists_coord F hj le_rfl hy
  have : c = 0 := by
    refine Matrix.eq_zero_of_vecMul_eq_zero hD (funext fun b => ?_)
    have hb := Xa_le F' j (e_mem F' hj b)
    have := h0 _ hb
    rw [map_add, LinearMap.add_apply, iso_Xa F' hi hb, add_zero] at this
    simpa [Matrix.vecMul, dotProduct, Zhat] using this
  simpa [this] using hi

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem finrank_Xa_le (F : FlagD H r) {j : ℕ} (hj : j ≤ r) : Module.finrank K (F.Xa j) ≤ j := by
  have : F.Xa j = Submodule.span K (Set.range fun b : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) := by
    refine le_antisymm (fun x hx => ?_) (Submodule.span_le.2 (by rintro _ ⟨b, rfl⟩; exact e_mem F hj b))
    obtain ⟨c, -, rfl⟩ := exists_coord F hj le_rfl hx
    exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  rw [this]
  exact (finrank_range_le_card (R := K) fun b : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)).trans
    (Fintype.card_fin j).le

end Flags

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → (idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) : ℝ) * cardB N.F N.F' Λ = delBar N.F N.F' Λ ∧ idx (latL N.F' N.F Λ) (lamOne N.F N.F' Λ) = idx (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) ∧ lamOne N.F N.F' Λ ≤ latL N.F N.F' Λ ⊓ latL N.F' N.F Λ ∧ idx (latL N.F N.F' Λ ⊓ latL N.F' N.F Λ) (lamOne N.F N.F' Λ) ≤ cardB N.F N.F' Λ ∧ GenBy (latL N.F N.F' Λ) (lamOne N.F N.F' Λ) N.j := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ _ hT
  have s' : ∀ a : Fin r, N.j ≤ a.val → ∃ c : K, N.F'.e a.castSucc = c • N.F.e a.castSucc :=
    fun a ha => ⟨N.c, N.same a.castSucc ha⟩
  have s : ∀ a : Fin r, N.j ≤ a.val → ∃ c : K, N.F.e a.castSucc = c • N.F'.e a.castSucc :=
    fun a ha => ⟨N.c⁻¹, by rw [N.same a.castSucc ha, smul_smul, inv_mul_cancel₀ (Kill.c_ne N), one_smul]⟩
  have hD' : Dl N.F' N.F N.j (N.j_le.trans (Nat.le_succ r)) ≠ 0 := by
    rw [FrameCramer.Dl_swap]
    exact star_ne_zero.2 (Kill.Dj_ne N)
  have hY : N.F.X = N.F.Xa N.j ⊔ N.F.X ⊓ N.F'.X := by
    refine le_antisymm (fun x hx => ?_) (sup_le (Kill.Xa_le _ _) inf_le_left)
    obtain ⟨y, hy, i, hi, hi', rfl⟩ := Kill.X_le N.F N.F' N.j s x hx
    exact Submodule.add_mem_sup hy ⟨hi, hi'⟩
  obtain ⟨h1, h2, h3, h4, t, h5, h6⟩ := core H (Λ := Λ) (fun _ hx _ hy => Kill.iso_Xa N.F hx hy)
    (fun _ hx _ hy => Kill.iso_Xa N.F' hx hy) (flag_rad N.F N.F' N.j_le (Kill.Dj_ne N) s)
    (flag_rad N.F' N.F N.j_le hD' s') hK hT.1.1 hY (M := lamI N.F N.F' Λ) (L := latL N.F N.F' Λ)
    (L' := latL N.F' N.F Λ) (Λ₁ := lamOne N.F N.F' Λ) (A := latA0 N.F N.F' Λ) (A' := latA0 N.F' N.F Λ)
    rfl rfl (by rw [latL, uPerp, sup_comm N.F'.X]; rfl) rfl rfl (by rw [latA0, II, inf_comm N.F'.X]; rfl)
  exact ⟨h1, h2, h3, h4, t, h5.trans (finrank_Xa_le N.F N.j_le), h6⟩

end GlobalTheory.DegCnt.InnerIndex
