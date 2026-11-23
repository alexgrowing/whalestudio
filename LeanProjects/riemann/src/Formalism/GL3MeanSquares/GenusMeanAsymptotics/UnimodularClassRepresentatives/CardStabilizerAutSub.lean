import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomMapOfEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AdjoinMemGenusIff
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbitRepresentatives

theorem exists_orbit_reps {G X : Type*} [Group G] [MulAction G X] (A : Set X) (hfin : A.Finite)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let r := MulAction.orbitRel G X
  let f : X → X := fun x => (@Quotient.mk _ r x).out
  have hf1 : ∀ x, ∃ g : G, g • x = f x := fun x => MulAction.orbitRel_apply.mp (@Quotient.mk_out _ r x)
  have hf2 : ∀ x y (g : G), g • y = x → f x = f y := fun x y g hg =>
    congrArg Quotient.out (@Quotient.sound _ r x y (MulAction.orbitRel_apply.mpr ⟨g, hg⟩))
  refine ⟨hfin.toFinset.image f, ?_, ?_⟩
  · intro t ht
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨g, hg⟩ := hf1 x
    rw [← hg]
    exact hA g x (hfin.mem_toFinset.mp hx)
  · intro x hx
    obtain ⟨g, hg⟩ := hf1 x
    refine ⟨f x, ⟨Finset.mem_image_of_mem f (hfin.mem_toFinset.mpr hx), g⁻¹, ?_⟩, ?_⟩
    · rw [← hg, inv_smul_smul]
    · rintro y ⟨hy, g', hg'⟩
      obtain ⟨z, -, rfl⟩ := Finset.mem_image.mp hy
      obtain ⟨k, hk⟩ := hf1 z
      exact (hf2 x z (g' * k) (by rw [mul_smul, hk, hg'])).symm

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem card_stabilizer_autSub (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (t : V) :
    Nat.card (MulAction.stabilizer (autSub h L) t) =
      Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} :=
  Nat.card_congr
    { toFun := fun g => ⟨g.1.1, g.1.2, g.2⟩
      invFun := fun g => ⟨⟨g.1, g.2.1⟩, g.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem gmap_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) :
    Formalism.HermitianLatticesTheory.gmap g L ∈ Formalism.HermitianLatticesTheory.genus h I := by
  obtain ⟨hLat, hG⟩ := hL
  have hiso : ∀ x y, h (g x) (g y) = h x y := hg
  show Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap g L) ∧ Formalism.HermitianLatticesTheory.SameGenus h I (Formalism.HermitianLatticesTheory.gmap g L)
  refine ⟨?_, ?_⟩
  · constructor
    · unfold Formalism.HermitianLatticesTheory.gmap
      exact hLat.fg.map _
    · unfold Formalism.HermitianLatticesTheory.gmap
      rw [Submodule.map_coe]
      show Submodule.span K (⇑(g : V →ₗ[K] V) '' L) = ⊤
      rw [Submodule.span_image, hLat.span_eq_top, Submodule.map_top,
        LinearMap.range_eq_top.mpr g.surjective]
  · unfold Formalism.HermitianLatticesTheory.SameGenus
    intro p hp
    obtain ⟨g', hg', he⟩ := hG p hp
    refine ⟨g * g', mul_mem hg hg', ?_⟩
    rw [autSub_gmap_mul, he, Formalism.HermitianLattices.Ext.L3.loc_gmap]

theorem integral_of_mem_genus {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {I L : Submodule (𝓞 K) V}
    {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n) (hL : L ∈ Formalism.HermitianLatticesTheory.genus h I) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h L := by
  obtain ⟨-, -, hi⟩ := Formalism.HermitianLatticesTheory.genusBasic (𝓞 K) K V h hs Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range
  exact ((hi I L (isLattice_of_ortho hI).fg hL.1.fg hL.2).2).mp (isIntegralLat_of_ortho hI)

theorem exists_reps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    ∃ T : Finset V, (∀ t ∈ T, t ∈ L ∧ h t t = 1) ∧
      (∀ x, x ∈ L → h x x = 1 → ∃ t ∈ T, ∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t = x) ∧
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, (∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t₁ = t₂) → t₁ = t₂) ∧
      (repCount h L 1 : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h L) : ℕ) : ℝ) =
        ∑ t ∈ T, ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹ := by
  classical
  unfold Formalism.HermitianLattices.Ext.L3.repCount
  have hfin := finite_repSet_of_ortho hK hs hI hL 1
  haveI : Finite (autSub h L) := by
    have := (finite_autL_of_ortho hK hs hI hL).to_subtype
    exact this
  haveI : Finite ({x : V | x ∈ L ∧ h x x = 1} : Set V) := hfin.to_subtype
  have hA : ∀ g : autSub h L, ∀ x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V),
      g • x ∈ ({x : V | x ∈ L ∧ h x x = 1} : Set V) := by
    rintro ⟨g, hgI, hgL⟩ x ⟨hxL, hxx⟩
    have hgI' : ∀ x y, h (g x) (g y) = h x y := hgI
    refine ⟨?_, ?_⟩
    · show g x ∈ L
      rw [← hgL]
      unfold Formalism.HermitianLatticesTheory.gmap
      exact Submodule.mem_map_of_mem hxL
    · show h (g x) (g x) = 1
      rw [hgI' x x, hxx]
  obtain ⟨T, hTA, hT⟩ := exists_orbit_reps (G := autSub h L) _ hfin hA
  refine ⟨T, hTA, ?_, ?_, ?_⟩
  · intro x hxL hxx
    obtain ⟨t, ⟨htT, g, hg⟩, -⟩ := hT x ⟨hxL, hxx⟩
    exact ⟨t, htT, g.1, g.2, hg⟩
  · rintro t₁ h₁ t₂ h₂ ⟨a, ha, hat⟩
    obtain ⟨t, -, huniq⟩ := hT t₂ (hTA t₂ h₂)
    have e1 := huniq t₁ ⟨h₁, ⟨a, ha⟩, hat⟩
    have e2 := huniq t₂ ⟨h₂, 1, one_smul _ _⟩
    rw [e1, e2]
  · have key := sum_inv_card_stab (G := autSub h L) _ hA T hTA hT
    have e : ∀ t ∈ T, ((Nat.card (MulAction.stabilizer (autSub h L) t) : ℕ) : ℝ)⁻¹ =
        ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹ :=
      fun t _ => by rw [card_stabilizer_autSub]
    rw [← Finset.sum_congr rfl e]
    exact key

end OrbitRepresentatives

end Formalism.HermitianLattices.Ext.L3
