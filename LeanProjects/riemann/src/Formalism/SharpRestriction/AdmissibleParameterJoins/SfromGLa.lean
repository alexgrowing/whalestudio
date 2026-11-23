import Mathlib
import Formalism.HermitianLattices.StatementMass
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

section Transport

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

def latMap (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V' :=
  M.map ((φ : V →ₗ[K] V').restrictScalars (𝓞 K))

theorem mem_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) (y : V') : y ∈ latMap φ M ↔ φ.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨φ.symm y, h, by simp⟩

theorem tr_symm_tr (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V) : latMap φ.symm (latMap φ M) = M := by
  ext x; simp [mem_tr]

theorem tr_tr_symm (φ : V ≃ₗ[K] V') (M : Submodule (𝓞 K) V') : latMap φ (latMap φ.symm M) = M := by
  ext x; simp [mem_tr]

theorem tr_injective (φ : V ≃ₗ[K] V') : Function.Injective (latMap (K := K) φ) := fun a b h => by
  rw [← tr_symm_tr φ a, h, tr_symm_tr]

def cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : V' ≃ₗ[K] V' := (φ.symm.trans g).trans φ

theorem cj_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') : cj φ g y = φ (g (φ.symm y)) := rfl

theorem cj_symm_apply (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (y : V') :
    (cj φ g).symm y = φ (g.symm (φ.symm y)) := rfl

theorem cj_symm_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) : cj φ.symm (cj φ g) = g := by
  ext x; simp [cj_apply]

theorem cj_cj_symm (φ : V ≃ₗ[K] V') (g : V' ≃ₗ[K] V') : cj φ (cj φ.symm g) = g := by
  ext x; simp [cj_apply]

theorem mem_gmap (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) (y : V) : y ∈ gmap g M ↔ g.symm y ∈ M := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨g.symm y, h, by simp⟩

theorem gmap_cj (φ : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) (M : Submodule (𝓞 K) V) :
    gmap (cj φ g) (latMap φ M) = latMap φ (gmap g M) := by
  ext y
  simp [mem_gmap, mem_tr, cj_symm_apply]

theorem loc_tr (φ : V ≃ₗ[K] V') (p : Ideal (𝓞 K)) (M : Submodule (𝓞 K) V) :
    loc (K := K) p (latMap φ M) = latMap φ (loc (K := K) p M) := by
  ext y
  rw [mem_tr]
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr] at h
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e] at h
  · rintro ⟨s, hs, h⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_tr]
    have e : φ.symm (s • y) = s • φ.symm y := by
      rw [← algebraMap_smul K s y, map_smul, algebraMap_smul]
    rwa [e]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem isom_symm {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) :
    ∀ x y, h (φ.symm x) (φ.symm y) = h' x y := fun x y => by
  rw [← hφ]; simp

theorem cj_mem_isom {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {g : V ≃ₗ[K] V}
    (hg : g ∈ isom h) : cj φ g ∈ isom h' := by
  intro x y
  rw [cj_apply, cj_apply, hφ, hg, isom_symm hφ]

theorem isLattice_tr (φ : V ≃ₗ[K] V') {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (latMap φ M) where
  fg := hM.fg.map _
  span_eq_top := by
    have h1 : ((latMap φ M : Submodule (𝓞 K) V') : Set V') = (φ : V →ₗ[K] V') '' (M : Set V) := rfl
    rw [h1, Submodule.span_image, hM.span_eq_top, Submodule.map_top, LinearEquiv.range]

theorem genus_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L M : Submodule (𝓞 K) V}
    (hM : M ∈ genus h L) : latMap φ M ∈ genus h' (latMap φ L) := by
  refine ⟨isLattice_tr φ hM.1, fun p hp => ?_⟩
  obtain ⟨g, hg, e⟩ := hM.2 p hp
  exact ⟨cj φ g, cj_mem_isom hφ hg, by rw [loc_tr, gmap_cj, e, loc_tr]⟩

theorem classReps_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) {L : Submodule (𝓞 K) V}
    {s : Finset (Submodule (𝓞 K) V)} (hs : IsClassReps h L s) :
    IsClassReps h' (latMap φ L) (s.map ⟨latMap φ, tr_injective φ⟩) := by
  constructor
  · intro M hM
    obtain ⟨N, hN, rfl⟩ := Finset.mem_map.1 hM
    exact genus_tr hφ (hs.1 N hN)
  · intro M hM
    have hM' : latMap φ.symm M ∈ genus h L := by
      have := genus_tr (isom_symm hφ) hM
      rwa [tr_symm_tr] at this
    obtain ⟨N, ⟨hN, g, hg, e⟩, huniq⟩ := hs.2 _ hM'
    refine ⟨latMap φ N, ⟨Finset.mem_map.2 ⟨N, hN, rfl⟩, cj φ g, cj_mem_isom hφ hg, ?_⟩, ?_⟩
    · rw [gmap_cj, e, tr_tr_symm]
    · rintro N' ⟨hN', g', hg', e'⟩
      obtain ⟨N₀, hN₀, rfl⟩ := Finset.mem_map.1 hN'
      have : N₀ = N := by
        refine huniq N₀ ⟨hN₀, cj φ.symm g', cj_mem_isom (isom_symm hφ) hg', ?_⟩
        have h2 := gmap_cj φ.symm g' (latMap φ N₀)
        rw [tr_symm_tr] at h2
        change gmap g' (latMap φ N₀) = M at e'
        rw [h2, e']
      rw [this]; rfl

theorem card_autL_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (M : Submodule (𝓞 K) V) :
    Nat.card (autL h' (latMap φ M)) = Nat.card (autL h M) := by
  have a1 : ∀ g : autL h M, gmap (cj φ g.1) (latMap φ M) = latMap φ M := fun g => by
    rw [gmap_cj, g.2.2]
  have a2 : ∀ g : autL h' (latMap φ M), gmap (cj φ.symm g.1) M = M := fun g => by
    have h2 := gmap_cj φ.symm g.1 (latMap φ M)
    rw [tr_symm_tr] at h2
    rw [h2, g.2.2, tr_symm_tr]
  exact (Nat.card_congr ⟨fun g => ⟨cj φ g.1, cj_mem_isom hφ g.2.1, a1 g⟩,
    fun g => ⟨cj φ.symm g.1, cj_mem_isom (isom_symm hφ) g.2.1, a2 g⟩,
    fun g => Subtype.ext (cj_symm_cj φ g.1), fun g => Subtype.ext (cj_cj_symm φ g.1)⟩).symm

theorem mass_eq_sum (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    (s : Finset (Submodule (𝓞 K) V)) (hs : IsClassReps h L s) :
    mass h L = ∑ M ∈ s, ((Nat.card (autL h M) : ℕ) : ℝ)⁻¹ := by
  rw [massBasic_mass_eq h L ⟨s, hs⟩]
  apply Complex.ofReal_injective
  rw [massBasic_sum_cast, massBasic_sum_cast]
  exact latLiftIndep K V h L _ _ (fun _ _ _ => rfl) (fun _ _ _ => rfl) _ _
    (Exists.choose_spec (⟨s, hs⟩ : ∃ s, IsClassReps h L s)) hs

theorem mass_tr {φ : V ≃ₗ[K] V'} (hφ : ∀ x y, h' (φ x) (φ y) = h x y) (L : Submodule (𝓞 K) V) :
    mass h' (latMap φ L) = mass h L := by
  by_cases hs : ∃ s, IsClassReps h L s
  · obtain ⟨s, hs⟩ := hs
    rw [mass_eq_sum h L s hs, mass_eq_sum h' _ _ (classReps_tr hφ hs), Finset.sum_map]
    exact Finset.sum_congr rfl fun M _ => by
      rw [Function.Embedding.coeFn_mk, card_autL_tr hφ]
  · have hs' : ¬ ∃ s, IsClassReps h' (latMap φ L) s := by
      rintro ⟨s, hs'⟩
      apply hs
      have := classReps_tr (isom_symm hφ) hs'
      rw [tr_symm_tr] at this
      exact ⟨_, this⟩
    unfold mass
    rw [dif_neg hs, dif_neg hs']

theorem mass_ortho_eq {n : ℕ} {L : Submodule (𝓞 K) V} {L' : Submodule (𝓞 K) V'}
    (hL : IsOrthoLattice h L n) (hL' : IsOrthoLattice h' L' n) : mass h L = mass h' L' := by
  obtain ⟨e, he1, he2, rfl, he⟩ := hL
  obtain ⟨e', he1', he2', rfl, he'⟩ := hL'
  let b : Module.Basis (Fin n) K V := Module.Basis.mk he1 he2.ge
  let b' : Module.Basis (Fin n) K V' := Module.Basis.mk he1' he2'.ge
  let φ : V ≃ₗ[K] V' := b.equiv b' (Equiv.refl _)
  have hφe : ∀ i, φ (e i) = e' i := fun i => by
    have := b.equiv_apply i b' (Equiv.refl _)
    simpa [b, b', φ] using this
  have hφ : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    have hx := b.sum_repr x
    have hy := b.sum_repr y
    rw [← hx, ← hy]
    simp only [map_sum, map_smul, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, b,
      Module.Basis.mk_apply, hφe, he, he']
  rw [← mass_tr hφ]
  congr 1
  unfold latMap
  rw [Submodule.map_span, ← Set.range_comp]
  congr 2
  funext i
  exact hφe i

end Transport

end Formalism.MainNotions.J

end
