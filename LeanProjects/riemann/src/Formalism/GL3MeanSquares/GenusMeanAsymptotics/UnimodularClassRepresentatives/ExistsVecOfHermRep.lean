import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteDimensionalOfOrtho

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

def perpSpace (h : V →ₗ⋆[K] V →ₗ[K] K) (x₀ : V) : Submodule K V := LinearMap.ker (h x₀)

def perpForm (h : V →ₗ⋆[K] V →ₗ[K] K) (x₀ : V) :
    ↥(perpSpace h x₀) →ₗ⋆[K] ↥(perpSpace h x₀) →ₗ[K] K :=
  (h.comp (perpSpace h x₀).subtype).compl₂ (perpSpace h x₀).subtype

def vecSplitPerp (h : V →ₗ⋆[K] V →ₗ[K] K) {x₀ : V} (hx : h x₀ x₀ ≠ 0) :
    VecSplit h (perpForm h x₀) where
  x₀ := x₀
  ι := (perpSpace h x₀).subtype
  inj := Subtype.val_injective
  hx₀ := hx
  isom := fun _ _ => rfl
  orth := fun a => LinearMap.mem_ker.mp a.2
  cover := fun v => by
    refine ⟨h x₀ v / h x₀ x₀, ⟨v - (h x₀ v / h x₀ x₀) • x₀, ?_⟩, ?_⟩
    · change v - (h x₀ v / h x₀ x₀) • x₀ ∈ LinearMap.ker (h x₀)
      rw [LinearMap.mem_ker, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hx, sub_self]
    · simp

private theorem star_sesq_eq_swap_of_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (a b : V) :
    star (h a b) = h b a := by
  first | exact hs a b | exact hs.eq a b

theorem VecSplit.finrank_add_one {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') : finrank K V' + 1 = finrank K V := by
  let f : K × V' →ₗ[K] V := LinearMap.coprod (LinearMap.toSpanSingleton K V S.x₀) S.ι
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨c, a⟩ hca
      have h1 : c • S.x₀ + S.ι a = 0 := by simpa [f] using hca
      have h2 : h S.x₀ (c • S.x₀ + S.ι a) = 0 := by rw [h1, map_zero]
      rw [map_add, map_smul, S.orth, add_zero, smul_eq_mul] at h2
      have hc : c = 0 := (mul_eq_zero.mp h2).resolve_right S.hx₀
      subst hc
      have h3 : S.ι a = 0 := by simpa using h1
      have ha : a = 0 := S.inj (by rw [h3, map_zero])
      simp [ha]
    · intro v
      obtain ⟨c, a, hv⟩ := S.cover v
      exact ⟨(c, a), by simp [f, hv]⟩
  have := (LinearEquiv.ofBijective f hf).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at this
  omega

theorem finrank_perpSpace {h : V →ₗ⋆[K] V →ₗ[K] K} {x₀ : V} (hx : h x₀ x₀ ≠ 0) :
    finrank K (perpSpace h x₀) + 1 = finrank K V :=
  VecSplit.finrank_add_one (vecSplitPerp h hx)

theorem VecSplit.isTotPosDef {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') (hd : IsTotPosDef h) : IsTotPosDef h' := by
  intro a ha φ
  rw [← S.isom]
  exact hd _ (fun h0 => ha (S.inj (by rw [h0, map_zero]))) φ

theorem VecSplit.isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (S : VecSplit h h') (hs : h.IsSymm) : h'.IsSymm := by
  have H : ∀ a b : V', star (h' a b) = h' b a := by
    intro a b
    rw [← S.isom, ← S.isom]
    exact star_sesq_eq_swap_of_isSymm hs _ _
  first | exact H | exact ⟨H⟩

theorem exists_vec_of_hermRep (hH : HermRepUnram) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) (hV : 2 ≤ finrank K V)
    (n : K) (hn : star n = n) (hpos : TotPos n) : ∃ x : V, h x x = n := by
  have hne : ∀ x : V, x ≠ 0 → h x x ≠ 0 := by
    intro x hx h0
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x hx φ
    rw [h0, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by omega)
  have hfr := finrank_perpSpace (h := h) (hne x hx)
  obtain ⟨y', hy'⟩ : ∃ y : ↥(perpSpace h x), y ≠ 0 :=
    (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by omega)
  have hy0 : y'.1 ≠ 0 := fun h0 => hy' (Subtype.ext h0)
  have hxy : h x y'.1 = 0 := LinearMap.mem_ker.mp y'.2
  have hyx : h y'.1 x = 0 := by rw [← star_sesq_eq_swap_of_isSymm hs, hxy, star_zero]
  obtain ⟨s, t, hst⟩ := hH K hK (h x x) (h y'.1 y'.1) n (star_sesq_eq_swap_of_isSymm hs x x) (star_sesq_eq_swap_of_isSymm hs _ _) hn
    (fun φ => hd x hx φ) (fun φ => hd _ hy0 φ) hpos
  refine ⟨star s • x + star t • y'.1, ?_⟩
  simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, map_smul, smul_eq_mul,
    hxy, hyx, starRingEnd_apply, star_star]
  linear_combination hst

theorem VecSplit.le_dual_of_mem {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
    (hs : h.IsSymm) (S : VecSplit h h') {Λ : Submodule (𝓞 K) V}
    (hΛ : Formalism.HermitianLatticesTheory.IsIntegralLat h Λ) (hx : S.x₀ ∈ Λ) :
    S.adjoin (S.cut Λ) ≤ Λ ∧ Λ ≤ Formalism.HermitianLatticesTheory.dual h (S.adjoin (S.cut Λ)) := by
  have hle : S.adjoin (S.cut Λ) ≤ Λ :=
    sup_le (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) (Submodule.map_comap_le _ _)
  refine ⟨hle, fun x hx' => ?_⟩
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap]
  intro y hy
  exact hΛ y (hle hy) x hx'

end Formalism.HermitianLattices.Ext.L3
