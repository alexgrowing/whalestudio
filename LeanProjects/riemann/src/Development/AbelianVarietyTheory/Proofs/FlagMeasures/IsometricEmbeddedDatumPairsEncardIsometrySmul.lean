import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical

noncomputable section

namespace GlobalTheory.TripInv

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

abbrev lin (s : V ≃ₗ[K] V) : V →ₗ[𝓞 K] V := (s : V →ₗ[K] V).restrictScalars (𝓞 K)

def pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) : Submodule (𝓞 K) (V × V) :=
  Γ.map ((lin s).prodMap (lin s))

theorem gmap_eq (s : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) : Formalism.HermitianLatticesTheory.gmap s M = M.map (lin s) := rfl

theorem mem_gmap (s : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) :
    y ∈ Formalism.HermitianLatticesTheory.gmap s M ↔ s.symm y ∈ M := by
  rw [gmap_eq, Submodule.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨s.symm y, h, by simp⟩

theorem mem_pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) (p : V × V) :
    p ∈ pmap s Γ ↔ (s.symm p.1, s.symm p.2) ∈ Γ := by
  rw [pmap, Submodule.mem_map]
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa using hq
  · intro h
    exact ⟨_, h, by ext <;> simp⟩

theorem gmap_injective (s : V ≃ₗ[K] V) : Function.Injective (Formalism.HermitianLatticesTheory.gmap (R := 𝓞 K) s) := by
  intro M M' h
  ext x
  have := congrArg (s x ∈ ·) h
  simpa [mem_gmap] using this

theorem pmap_injective (s : V ≃ₗ[K] V) : Function.Injective (pmap s) := by
  intro Γ Γ' h
  ext p
  have := congrArg ((s p.1, s p.2) ∈ ·) h
  simpa [mem_pmap] using this

theorem smulLat_gmap (s : V ≃ₗ[K] V) (g : 𝓞 K) (M : Submodule (𝓞 K) V) :
    smulLat g (Formalism.HermitianLatticesTheory.gmap s M) = Formalism.HermitianLatticesTheory.gmap s (smulLat g M) := by
  rw [gmap_eq, gmap_eq, smulLat, smulLat, ← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
  rw [← algebraMap_smul K g x, ← algebraMap_smul K g (s x), map_smul]

theorem prod_gmap (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    (Formalism.HermitianLatticesTheory.gmap s A).prod (Formalism.HermitianLatticesTheory.gmap s B) = pmap s (A.prod B) := by
  ext p
  simp [mem_pmap, mem_gmap, Submodule.mem_prod]

theorem fixLat_pmap (s : V ≃ₗ[K] V) (Γ : Submodule (𝓞 K) (V × V)) :
    fixLat (pmap s Γ) = Formalism.HermitianLatticesTheory.gmap s (fixLat Γ) := by
  ext x
  simp [fixLat, mem_pmap, mem_gmap]

theorem toAddSubgroup_gmap (s : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    (Formalism.HermitianLatticesTheory.gmap s M).toAddSubgroup = M.toAddSubgroup.map (lin s).toAddMonoidHom := by
  ext x
  rfl

theorem idx_gmap (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    idx (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) = idx A B := by
  unfold idx
  rw [toAddSubgroup_gmap, toAddSubgroup_gmap]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ (by simpa using s.injective)

theorem idxN_gmap (s : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    GlobalTheory.Mass.idxN (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) = GlobalTheory.Mass.idxN A B :=
  idx_gmap s A B

variable {H : HermSpace K V}

theorem isom_symm {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (x y : V) :
    H.B (s.symm x) (s.symm y) = H.B x y := by
  rw [← hs]
  simp

theorem dual_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.dual H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) = Formalism.HermitianLatticesTheory.gmap s (Formalism.HermitianLatticesTheory.dual H.B.flip M) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, mem_gmap,
    LinearMap.restrictScalars_apply, LinearMap.flip_apply]
  constructor
  · intro h z hz
    have := h (s z) (by simpa using hz)
    rwa [← isom_symm hs, LinearEquiv.symm_apply_apply] at this
  · intro h y hy
    have := h _ hy
    rwa [isom_symm hs] at this

theorem isIntLat_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {M : Submodule (𝓞 K) V}
    (hM : GlobalTheory.Mass.IsIntLat H.B.flip M) : GlobalTheory.Mass.IsIntLat H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) := by
  obtain ⟨hL, hI⟩ := hM
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [gmap_eq]
    exact hL.fg.map _
  · rw [gmap_eq, Submodule.map_coe]
    change Submodule.span K ((s : V →ₗ[K] V) '' (M : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top]
    exact LinearEquiv.range s
  · intro x hx y hy
    rw [mem_gmap] at hx hy
    have := hI _ hx _ hy
    simp only [LinearMap.flip_apply] at this ⊢
    rwa [isom_symm hs] at this

theorem discN_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (M : Submodule (𝓞 K) V) :
    GlobalTheory.Mass.discN H.B.flip (Formalism.HermitianLatticesTheory.gmap s M) = GlobalTheory.Mass.discN H.B.flip M := by
  unfold GlobalTheory.Mass.discN
  rw [dual_gmap hs, idxN_gmap]

theorem genBy_gmap (s : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} {j : ℕ} (h : GenBy A B j) :
    GenBy (Formalism.HermitianLatticesTheory.gmap s A) (Formalism.HermitianLatticesTheory.gmap s B) j := by
  classical
  obtain ⟨t, ht, rfl⟩ := h
  refine ⟨t.image s, (Finset.card_image_le).trans ht, ?_⟩
  rw [gmap_eq, gmap_eq, Submodule.map_sup, Submodule.map_span, Finset.coe_image]
  rfl

theorem isModIso_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {g : 𝓞 K}
    {M L : Submodule (𝓞 K) V} {Γ : Submodule (𝓞 K) (V × V)} (h : IsModIso H g M L Γ) :
    IsModIso H g (Formalism.HermitianLatticesTheory.gmap s M) (Formalism.HermitianLatticesTheory.gmap s L) (pmap s Γ) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [prod_gmap]
    exact Submodule.map_mono h1
  · rw [smulLat_gmap, smulLat_gmap, prod_gmap]
    exact Submodule.map_mono h2
  · intro y' hy'
    rw [mem_gmap] at hy'
    obtain ⟨y, hy⟩ := h3 _ hy'
    exact ⟨s y, by simpa [mem_pmap] using hy⟩
  · intro y hy
    rw [mem_gmap] at hy
    obtain ⟨y', hy'⟩ := h4 _ hy
    exact ⟨s y', by simpa [mem_pmap] using hy'⟩
  · intro y hy
    rw [mem_pmap] at hy
    rw [smulLat_gmap, mem_gmap]
    exact h5 _ (by simpa using hy)
  · intro y' hy'
    rw [mem_pmap] at hy'
    rw [smulLat_gmap, mem_gmap]
    exact h6 _ (by simpa using hy')
  · intro p hp q hq
    rw [mem_pmap] at hp hq
    obtain ⟨t, ht⟩ := h7 _ hp _ hq
    exact ⟨t, by simpa only [isom_symm hs] using ht⟩

theorem isDat_gmap {s : V ≃ₗ[K] V} (hs : ∀ x y, H.B (s x) (s y) = H.B x y) {g : ℕ} {L : Submodule (𝓞 K) V}
    {j x : ℕ} {d : Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)} (h : IsDat H g L j x d) :
    IsDat H g (Formalism.HermitianLatticesTheory.gmap s L) j x (Formalism.HermitianLatticesTheory.gmap s d.1, pmap s d.2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨isIntLat_gmap hs h1, ?_, isModIso_gmap hs h3, ?_, ?_⟩
  · rw [discN_gmap hs, discN_gmap hs, h2]
  · rw [fixLat_pmap, idx_gmap, h4]
  · rw [fixLat_pmap]
    exact genBy_gmap s h5

def tr (s : V ≃ₗ[K] V)
    (p : (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V)) :
    (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (Submodule (𝓞 K) V × Submodule (𝓞 K) (V × V)) × (V ≃ₗ[K] V) :=
  ((Formalism.HermitianLatticesTheory.gmap s p.1.1, pmap s p.1.2), (Formalism.HermitianLatticesTheory.gmap s p.2.1.1, pmap s p.2.1.2), s * p.2.2 * s⁻¹)

theorem tr_injective (s : V ≃ₗ[K] V) : Function.Injective (tr (K := K) s) := by
  rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, η⟩ ⟨⟨a1', a2'⟩, ⟨b1', b2'⟩, η'⟩ h
  simp only [tr, Prod.mk.injEq] at h
  obtain ⟨⟨e1, e2⟩, ⟨e3, e4⟩, e5⟩ := h
  simp only [gmap_injective s e1, pmap_injective s e2, gmap_injective s e3, pmap_injective s e4,
    mul_left_cancel (mul_right_cancel e5)]

theorem tr_mapsTo {s : V ≃ₗ[K] V} (hs : s ∈ isomGrp H) (g : ℕ) (L : Submodule (𝓞 K) V) (j x x' : ℕ) :
    Set.MapsTo (tr s) (Trip H g L j x x') (Trip H g (Formalism.HermitianLatticesTheory.gmap s L) j x x') := by
  have hs' := (mem_isomGrp H s).1 hs
  rintro ⟨⟨a1, a2⟩, ⟨b1, b2⟩, η⟩ ⟨hA, hB, hη, him, hgr⟩
  refine ⟨isDat_gmap hs' hA, isDat_gmap hs' hB, ?_, ?_, ?_⟩
  · exact (isomGrp H).mul_mem ((isomGrp H).mul_mem hs hη) ((isomGrp H).inv_mem hs)
  · change Formalism.HermitianLatticesTheory.gmap (s * η * s⁻¹) (Formalism.HermitianLatticesTheory.gmap s b1) = Formalism.HermitianLatticesTheory.gmap s a1
    rw [Formalism.HermitianLatticesTheory.genusBasic_gmap_mul, Formalism.HermitianLatticesTheory.genusBasic_gmap_inv, Formalism.HermitianLatticesTheory.genusBasic_gmap_mul]
    exact congrArg _ him
  · intro y y'
    change (y, y') ∈ pmap s b2 ↔ (s (η (s.symm y)), y') ∈ pmap s a2
    rw [mem_pmap, mem_pmap]
    simpa using hgr (s.symm y) (s.symm y')

theorem encard_le (HW : HermSpace K V) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip) (L : Submodule (𝓞 K) V) :
    (Trip HW g L j x x').encard ≤ (Trip HW g (s • L) j x x').encard :=
  Set.encard_le_encard_of_injOn (tr_mapsTo s.2 g L j x x') (tr_injective _).injOn

theorem trip_encard_smul : ∀ (K W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (HW : HermSpace K W) (g j x x' : ℕ) (s : Formalism.HermitianLatticesTheory.isom HW.B.flip)
    (L : Submodule (𝓞 K) W), (Trip HW g (s • L) j x x').encard = (Trip HW g L j x x').encard := by
  intro K W _ _ _ _ _ _ _ HW g j x x' s L
  refine le_antisymm ?_ (encard_le HW g j x x' s L)
  have := encard_le HW g j x x' s⁻¹ (s • L)
  exact this.trans_eq (congrArg (fun M => (Trip HW g M j x x').encard)
    (Formalism.HermitianLatticesTheory.genusBasic_gmap_inv (s : W ≃ₗ[K] W) L))

end GlobalTheory.TripInv
