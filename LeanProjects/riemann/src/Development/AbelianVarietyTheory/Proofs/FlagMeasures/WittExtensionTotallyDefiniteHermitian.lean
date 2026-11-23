import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Witt

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem mem_perp (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (v : V) :
    v ∈ perp h U ↔ ∀ x ∈ U, h x v = 0 := by
  simp [perp, Submodule.mem_iInf, LinearMap.mem_ker]

private lemma h_sub_smul_sub_smul_eq_of_hww (h : V →ₗ⋆[K] V →ₗ[K] K) (hsym : ∀ a b, star (h a b) = h b a)
    (w : V) (α : K) (hα : α ≠ 0) (hww : h w w = α + star α) (a b : V) :
    h (a - (α⁻¹ * h w a) • w) (b - (α⁻¹ * h w b) • w) = h a b := by
  have hα' : star α ≠ 0 := star_ne_zero.mpr hα
  simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
    starRingEnd_apply]
  rw [← hsym w a, hww, star_mul, star_inv₀]
  field_simp
  ring

theorem exists_isom_move [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) (x y : V) (hxy : h x x = h y y) :
    ∃ g ∈ isom h, g x = y ∧ ∀ v, h (x - y) v = 0 → g v = v := by
  have hsym : ∀ a b, star (h a b) = h b a := fun a b => by
    rw [← starRingEnd_apply]; exact hs.eq a b
  have hww : h (x - y) (x - y) = h (x - y) x + star (h (x - y) x) := by
    rw [hsym]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hxy]; ring
  by_cases hα : h (x - y) x = 0
  · have h0 : h (x - y) (x - y) = 0 := by rw [hww, hα, star_zero, add_zero]
    have hxy' : x = y := sub_eq_zero.mp (ha _ h0)
    exact ⟨1, (isom h).one_mem, by simp [hxy'], fun v _ => rfl⟩
  · let f : V →ₗ[K] V :=
      LinearMap.id - LinearMap.smulRight ((h (x - y) x)⁻¹ • h (x - y)) (x - y)
    have hf : ∀ v, f v = v - ((h (x - y) x)⁻¹ * h (x - y) v) • (x - y) := fun v => rfl
    have key : ∀ a b, h (f a) (f b) = h a b := fun a b => by
      rw [hf, hf]; exact h_sub_smul_sub_smul_eq_of_hww h hsym (x - y) _ hα hww a b
    have hinj : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro a ha0
      apply ha a
      rw [← key a a, ha0, map_zero]
    let g : V ≃ₗ[K] V := LinearEquiv.ofInjectiveEndo f hinj
    have hg : ∀ v, g v = f v := fun v => rfl
    refine ⟨g, fun a b => by rw [hg, hg, key], ?_, fun v hv => ?_⟩
    · rw [hg, hf, inv_mul_cancel₀ hα, one_smul, sub_sub_cancel]
    · rw [hg, hf, hv, mul_zero, zero_smul, sub_zero]

theorem exists_isom_finset [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) {ι : Type} (a b : ι → V)
    (hab : ∀ i j, h (b i) (b j) = h (a i) (a j)) (t : Finset ι) :
    ∃ g ∈ isom h, ∀ i ∈ t, g (a i) = b i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, (isom h).one_mem, by simp⟩
  | insert j s hj ih =>
    obtain ⟨g, hg, hgs⟩ := ih
    have hg' : ∀ u v, h (g u) (g v) = h u v := hg
    have hgx : h (g (a j)) (g (a j)) = h (b j) (b j) := by rw [hg', hab]
    obtain ⟨k, hk, hkx, hkfix⟩ := exists_isom_move h hs ha (g (a j)) (b j) hgx
    refine ⟨k * g, (isom h).mul_mem hk hg, fun i hi => ?_⟩
    show k (g (a i)) = b i
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hkx
    · rw [hgs i hi]
      apply hkfix
      have e1 : h (g (a j)) (b i) = h (b j) (b i) :=
        calc h (g (a j)) (b i) = h (g (a j)) (g (a i)) := by rw [hgs i hi]
          _ = h (a j) (a i) := hg' _ _
          _ = h (b j) (b i) := (hab j i).symm
      rw [map_sub, LinearMap.sub_apply, e1, sub_self]

theorem isCompl_perp [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (ha : ∀ x, h x x = 0 → x = 0) (U : Submodule K V) : IsCompl U (perp h U) := by
  have hdis : Disjoint U (perp h U) := by
    rw [Submodule.disjoint_def]
    intro x hxU hxP
    exact ha x (((mem_perp h U x).1 hxP) x hxU)
  let bU := Module.finBasis K U
  let T : V →ₗ[K] (Fin (Module.finrank K U) → K) := LinearMap.pi fun i => h (bU i : V)
  have hker : LinearMap.ker T ≤ perp h U := by
    intro v hv
    rw [mem_perp]
    intro x hx
    have hv' : ∀ i, h (bU i : V) v = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp hv) i
      simpa [T] using this
    have hx' : x = ∑ i, (bU.repr ⟨x, hx⟩ i) • (bU i : V) := by
      have e := congrArg Subtype.val (bU.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      exact e.symm
    rw [hx', map_sum, LinearMap.sum_apply]
    simp [hv']
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 : Module.finrank K (LinearMap.range T) ≤ Module.finrank K U := by
    simpa using Submodule.finrank_le (LinearMap.range T)
  have h3 := Submodule.finrank_mono hker
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq U (perp h U)
  rw [hdis.eq_bot, finrank_bot] at h4
  refine ⟨hdis, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have h5 := Submodule.finrank_le (U ⊔ perp h U)
  omega

theorem perp_perp [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) (U : Submodule K V) : perp h (perp h U) = U := by
  have hle : U ≤ perp h (perp h U) := by
    intro u hu
    rw [mem_perp]
    intro w hw
    have h0 : h u w = 0 := (mem_perp h U w).1 hw u hu
    rw [← hs.eq u w, h0, map_zero]
  have c1 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp h ha U)
  have c2 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp h ha (perp h U))
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem witt_definite : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ U U' : Submodule K V, ∀ e : U ≃ₗ[K] U', (∀ x y, h (e x : V) (e y : V) = h (x : V) (y : V)) → ∃ g ∈ isom h, ∀ x : U, g (x : V) = (e x : V)) ∧ ∀ U : Submodule K V, IsCompl U (perp h U) ∧ (hRes h U).IsSymm ∧ PD (hRes h U) ∧ perp h (perp h U) = U := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hpd
  have ha : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpd τ x hne
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨?_, fun U => ⟨isCompl_perp h ha U, ?_, ?_, perp_perp h hs ha U⟩⟩
  · intro U U' e he
    let bU := Module.finBasis K U
    obtain ⟨g, hg, hgb⟩ := exists_isom_finset h hs ha (fun i => (bU i : V))
      (fun i => (e (bU i) : V)) (fun i j => he _ _) Finset.univ
    refine ⟨g, hg, fun x => ?_⟩
    have hcomp : (g : V →ₗ[K] V).comp U.subtype = U'.subtype.comp (e : U →ₗ[K] U') := by
      apply bU.ext
      intro i
      simpa using hgb i (Finset.mem_univ i)
    exact LinearMap.congr_fun hcomp x
  · exact ⟨fun x y => hs.eq x y⟩
  · intro τ x hx
    show 0 < (τ (h x x)).re
    exact hpd τ x (fun h0 => hx (Subtype.ext h0))

end GlobalTheory.Mass.Witt
