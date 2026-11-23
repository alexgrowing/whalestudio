import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

section Rep

variable {G : Type} [Group G] (Γ K : Subgroup G)

theorem mem_AMFK_iff {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρK : Representation k K W) (f : G → W) :
    f ∈ AMFK k Γ K ρK ↔ ∀ γ : Γ, ∀ g : G, ∀ κ : K, f ((γ : G) * g * κ) = ρK κ⁻¹ (f g) := Iff.rfl

theorem exists_rep (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c) (g : G) :
    ∃ p : Γ × K, g = (p.1 : G) * s (DoubleCoset.mk Γ K g) * (p.2 : G) := by
  have h := (DoubleCoset.eq Γ K (s (DoubleCoset.mk Γ K g)) g).1 (hs _)
  obtain ⟨a, ha, b, hb, hab⟩ := h
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩

theorem mk_of_eq (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (c : ClassSet Γ K) (g : G) (γ : Γ) (κ : K) (e : g = (γ : G) * s c * κ) :
    DoubleCoset.mk Γ K g = c := by
  conv_rhs => rw [← hs c]
  rw [DoubleCoset.eq]
  refine ⟨(γ : G)⁻¹, Γ.inv_mem γ.2, (κ : G)⁻¹, K.inv_mem κ.2, ?_⟩
  rw [e]
  group

theorem rho_eq_of_eq {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ W) (x : G) (w : W)
    (hw : ∀ γ ∈ stabAt Γ K x, ρ γ w = w) (γ γ' : Γ) (κ κ' : K)
    (e : (γ : G) * x * κ = (γ' : G) * x * κ') : ρ γ w = ρ γ' w := by
  have e' : (γ : G) = (γ' : G) * x * (κ' : G) * (κ : G)⁻¹ * x⁻¹ := by
    rw [← e]
    group
  have hmem : x⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * x ∈ K := by
    have h1 : x⁻¹ * ((γ'⁻¹ * γ : Γ) : G) * x = (κ' : G) * (κ : G)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, e']
      group
    rw [h1]
    exact K.mul_mem κ'.2 (K.inv_mem κ.2)
  have h := hw (γ'⁻¹ * γ) hmem
  calc ρ γ w = ρ (γ' * (γ'⁻¹ * γ)) w := by rw [mul_inv_cancel_left]
    _ = ρ γ' (ρ (γ'⁻¹ * γ) w) := by rw [map_mul]; rfl
    _ = ρ γ' w := by rw [h]

variable {k : Type} [CommRing k] {W : Type} [AddCommGroup W] [Module k W]

def extend (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (ρ : Representation k Γ W) (w : ClassSet Γ K → W) (g : G) : W :=
  ρ (Classical.choose (exists_rep Γ K s hs g)).1 (w (DoubleCoset.mk Γ K g))

theorem extend_eq (s : ClassSet Γ K → G) (hs : ∀ c, DoubleCoset.mk Γ K (s c) = c)
    (ρ : Representation k Γ W) (w : ClassSet Γ K → W)
    (hw : ∀ c, ∀ γ ∈ stabAt Γ K (s c), ρ γ (w c) = w c)
    (c : ClassSet Γ K) (g : G) (γ : Γ) (κ : K) (e : g = (γ : G) * s c * κ) :
    extend Γ K s hs ρ w g = ρ γ (w c) := by
  have hc : DoubleCoset.mk Γ K g = c := mk_of_eq Γ K s hs c g γ κ e
  have hp := Classical.choose_spec (exists_rep Γ K s hs g)
  unfold extend
  generalize Classical.choose (exists_rep Γ K s hs g) = p at hp ⊢
  rw [hc] at hp ⊢
  exact rho_eq_of_eq Γ K ρ (s c) (w c) (hw c) p.1 γ p.2 κ (hp.symm.trans e)

end Rep

theorem automorphic_forms_level_finite_holds : Formalism.UG.AMFKFinite := by
  intro G _ Γ K k _ _ W _ _ _ ρK hfin
  have hsurj : ∀ c : ClassSet Γ K, ∃ g : G, DoubleCoset.mk Γ K g = c := by
    intro c
    obtain ⟨g, hg⟩ := Quotient.exists_rep c
    exact ⟨g, hg⟩
  let s : ClassSet Γ K → G := fun c => (hsurj c).choose
  have hs : ∀ c, DoubleCoset.mk Γ K (s c) = c := fun c => (hsurj c).choose_spec
  let L : AMFK k Γ K ρK →ₗ[k] (ClassSet Γ K → W) :=
    LinearMap.pi fun c => (LinearMap.proj (s c)).comp (AMFK k Γ K ρK).subtype
  have hinj : Function.Injective L := by
    intro f g hfg
    apply Subtype.ext
    funext x
    obtain ⟨p, hp⟩ := exists_rep Γ K s hs x
    have hf := (mem_AMFK_iff Γ K ρK (f : G → W)).1 f.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hg := (mem_AMFK_iff Γ K ρK (g : G → W)).1 g.2 p.1 (s (DoubleCoset.mk Γ K x)) p.2
    have hfc := congrFun hfg (DoubleCoset.mk Γ K x)
    change (f : G → W) (s (DoubleCoset.mk Γ K x)) = (g : G → W) (s (DoubleCoset.mk Γ K x)) at hfc
    rw [← hp] at hf hg
    rw [hf, hg, hfc]
  exact Module.Finite.of_injective L hinj

end Formalism.UG.P
