import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace GlobalTheory.CxCoh

universe a b

theorem cocycle_two_isCoboundary_of_objectwiseQuasiIso {C : Type b} [Category.{0} C] {L K : Cx C}
    (a0 : ∀ T, L.M0.obj T →+ K.M0.obj T) (a1 : ∀ T, L.M1.obj T →+ K.M1.obj T)
    (a2 : ∀ T, L.M2.obj T →+ K.M2.obj T)
    (compDegreeZero_natural : ∀ {T T' : C} (φ : T ⟶ T') x, a0 T' (L.M0.map φ x) = K.M0.map φ (a0 T x))
    (compDegreeOne_natural : ∀ {T T' : C} (φ : T ⟶ T') x, a1 T' (L.M1.map φ x) = K.M1.map φ (a1 T x))
    (comp_commutes_diffZero : ∀ T x, a1 T (L.d0 T x) = K.d0 T (a0 T x))
    (comp_commutes_diffOne : ∀ T x, a2 T (L.d1 T x) = K.d1 T (a1 T x))
    (hq : ∀ T, IsQ (L.d0 T) (L.d1 T) (L.d2 T) (K.d0 T) (K.d1 T) (K.d2 T) (a0 T) (a1 T) (a2 T))
    (z : L.T2) (hz : z ∈ L.Z2) (c' : K.T1)
    (E0 : ∀ T T' T'' (φ : T ⟶ T') (ψ : T' ⟶ T''),
      K.M0.map ψ (c'.1 T T' φ) - c'.1 T T'' (φ ≫ ψ) + c'.1 T' T'' ψ = a0 T'' (z.1 T T' T'' φ ψ))
    (E1 : ∀ T T' (φ : T ⟶ T'),
      c'.2 T' - K.M1.map φ (c'.2 T) - K.d0 T' (c'.1 T T' φ) = a1 T' (z.2.1 T T' φ))
    (E2 : ∀ T, K.d1 T (c'.2 T) = a2 T (z.2.2 T)) :
    ∃ c, L.D1 c = z := by
  obtain ⟨Za, Zb, Zc, Zd⟩ := hz
  choose ω₁ hω₁ using fun T ↦ (hq T).inj2 (z.2.2 T) (c'.2 T) (Zd T) (E2 T).symm
  have h1 : ∀ T, K.d1 T (c'.2 T - a1 T (ω₁ T)) = 0 := fun T ↦ by
    rw [map_sub, E2, ← comp_commutes_diffOne, hω₁, sub_self]
  choose ω₂ w hω₂ hw using fun T ↦ (hq T).surj1 _ (h1 T)
  have hw' : ∀ T, a1 T (ω₂ T) = c'.2 T - a1 T (ω₁ T) - K.d0 T (w T) := fun T ↦ by
    rw [hw T]; abel
  obtain ⟨Ω, hΩ⟩ : ∃ Ω : ∀ T, L.M1.obj T, ∀ T, Ω T = ω₁ T + ω₂ T := ⟨_, fun _ ↦ rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : L.M1.c1, ∀ T T' (φ : T ⟶ T'),
      α T T' φ = z.2.1 T T' φ - (Ω T' - L.M1.map φ (Ω T)) := ⟨_, fun _ _ _ ↦ rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : K.M0.c1, ∀ T T' (φ : T ⟶ T'),
      f T T' φ = c'.1 T T' φ - (w T' - K.M0.map φ (w T)) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hα1 : ∀ T T' (φ : T ⟶ T'), L.d1 T' (α T T' φ) = 0 := fun T T' φ ↦ by
    have hc := Zc T T' φ
    simp only [hα, hΩ, map_sub, map_add, L.diffOne_natural, hω₁, hω₂, add_zero, map_zero]
    rw [hc]; abel
  have hα2 : ∀ T T' (φ : T ⟶ T'), a1 T' (α T T' φ) = K.d0 T' (-f T T' φ) := fun T T' φ ↦ by
    simp only [hα, hΩ, hf, map_sub, map_add, map_neg, compDegreeOne_natural, hw', ← E1, K.diffZero_natural]
    abel
  choose g hg using fun T T' (φ : T ⟶ T') ↦
    (hq T').inj1 (α T T' φ) (-f T T' φ) (hα1 T T' φ) (hα2 T T' φ)
  have h3 : ∀ T T' (φ : T ⟶ T'), K.d0 T' (f T T' φ + a0 T' (g T T' φ)) = 0 := fun T T' φ ↦ by
    rw [map_add, ← comp_commutes_diffZero, hg, hα2, map_neg, add_neg_cancel]
  choose f₂ hf₂ hf₂' using fun T T' (φ : T ⟶ T') ↦ (hq T').surj0 _ (h3 T T' φ)
  refine ⟨(fun T T' φ ↦ f₂ T T' φ - g T T' φ, Ω), Prod.ext (funext fun T ↦ funext fun T' ↦
    funext fun T'' ↦ funext fun φ ↦ funext fun ψ ↦ ?_) (Prod.ext (funext fun T ↦ funext fun T' ↦
    funext fun φ ↦ ?_) (funext fun T ↦ ?_))⟩
  · change L.M0.map ψ (f₂ T T' φ - g T T' φ) - (f₂ T T'' (φ ≫ ψ) - g T T'' (φ ≫ ψ))
      + (f₂ T' T'' ψ - g T' T'' ψ) = z.1 T T' T'' φ ψ
    have hZb : L.d0 T'' (z.1 T T' T'' φ ψ) =
        z.2.1 T T'' (φ ≫ ψ) - L.M1.map ψ (z.2.1 T T' φ) - z.2.1 T' T'' ψ := by
      rw [Zb T T' T'' φ ψ]; abel
    have hd : L.d0 T'' (z.1 T T' T'' φ ψ - (L.M0.map ψ (f₂ T T' φ - g T T' φ) -
        (f₂ T T'' (φ ≫ ψ) - g T T'' (φ ≫ ψ)) + (f₂ T' T'' ψ - g T' T'' ψ))) = 0 := by
      simp only [map_sub, map_add, L.diffZero_natural, hf₂, hg, hα, hZb, L.M1.map_comp, map_zero]
      abel
    have ha : a0 T'' (z.1 T T' T'' φ ψ - (L.M0.map ψ (f₂ T T' φ - g T T' φ) -
        (f₂ T T'' (φ ≫ ψ) - g T T'' (φ ≫ ψ)) + (f₂ T' T'' ψ - g T' T'' ψ))) = 0 := by
      simp only [map_sub, map_add, compDegreeZero_natural, hf₂', ← E0, hf, K.M0.map_comp]
      abel
    exact (sub_eq_zero.mp ((hq T'').inj0 _ hd ha)).symm
  · change Ω T' - L.M1.map φ (Ω T) - L.d0 T' (f₂ T T' φ - g T T' φ) = z.2.1 T T' φ
    rw [map_sub, hf₂, hg, hα]; abel
  · change L.d1 T (Ω T) = z.2.2 T
    rw [hΩ, map_add, hω₁, hω₂, add_zero]

theorem vertical_h2_injective : VertHas.{a, b} (fun m ↦ Function.Injective m.h2) := by
  intro C _ C' _ K K' m hq
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hx' : (QuotientAddGroup.mk (m.vert.z2 z) : K'.H2) = 0 := hx
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at hx' ⊢
  obtain ⟨c', hc'⟩ := hx'
  exact cocycle_two_isCoboundary_of_objectwiseQuasiIso (L := K.res m.G) (K := K') m.a0 m.a1 m.a2 m.compDegreeZero_natural m.compDegreeOne_natural
    m.comp_commutes_diffZero m.comp_commutes_diffOne hq z.1 z.2 c'
    (fun T T' T'' φ ψ ↦ congrArg (fun c ↦ c.1 T T' T'' φ ψ) hc')
    (fun T T' φ ↦ congrArg (fun c ↦ c.2.1 T T' φ) hc')
    (fun T ↦ congrArg (fun c ↦ c.2.2 T) hc')

theorem vertical_h2_injective_universes :
    VertHas.{1,1} (fun m ↦ Function.Injective m.h2) ∧ VertHas.{1,0} (fun m ↦ Function.Injective m.h2) ∧
      VertHas.{0,0} (fun m ↦ Function.Injective m.h2) :=
  ⟨vertical_h2_injective, vertical_h2_injective, vertical_h2_injective⟩

end GlobalTheory.CxCoh
