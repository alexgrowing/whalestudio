import Mathlib

open Polynomial IsLocalRing

namespace GlobalTheory.CompanionTheory.Chevalley

variable {Ω L : Type*} [Field Ω] [Field L]

def Functional (G : Subring (Ω × L)) : Prop := ∀ l : L, ((0 : Ω), l) ∈ G → l = 0

theorem exists_maximal_functional (G₀ : Subring (Ω × L)) (h₀ : Functional G₀) :
    ∃ G, G₀ ≤ G ∧ Maximal Functional G := by
  have hub : ∀ c ⊆ {G : Subring (Ω × L) | Functional G}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {G : Subring (Ω × L) | Functional G}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hch y hy
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    show Functional (sSup c)
    intro l hl
    obtain ⟨s, hs, hls⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).mp hl
    exact (hc hs : Functional s) l hls
  obtain ⟨m, hm, hmax⟩ := zorn_le_nonempty₀ _ hub G₀ h₀
  exact ⟨m, hm, hmax⟩

def saturation (G : Subring (Ω × L)) (t : Ω × L) (ht : t ∈ G) : Subring (Ω × L) where
  carrier := {u | ∃ n : ℕ, t ^ n * u ∈ G}
  mul_mem' := by
    rintro u v ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := G.mul_mem hn hm
    convert this using 1
    ring
  one_mem' := ⟨0, by simpa using G.one_mem⟩
  add_mem' := by
    rintro u v ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := G.add_mem (G.mul_mem (G.pow_mem ht m) hn) (G.mul_mem (G.pow_mem ht n) hm)
    convert this using 1
    ring
  zero_mem' := ⟨0, by simp [G.zero_mem]⟩
  neg_mem' := by
    rintro u ⟨n, hn⟩
    exact ⟨n, by simpa using G.neg_mem hn⟩

theorem inv_mem {G : Subring (Ω × L)} (hG : Maximal Functional G) {b : Ω} {l : L}
    (hb : (b, l) ∈ G) (hl : l ≠ 0) : (b⁻¹, l⁻¹) ∈ G := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hl (hG.1 l hb)
  have hmem : ∀ u, u ∈ saturation G (b, l) hb ↔ ∃ n : ℕ, (b, l) ^ n * u ∈ G := fun u => Iff.rfl
  have hS : Functional (saturation G (b, l) hb) := by
    intro m hm
    obtain ⟨n, hn⟩ := (hmem _).mp hm
    rw [Prod.pow_mk, Prod.mk_mul_mk, mul_zero] at hn
    have h0 := hG.1 _ hn
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero n hl)
  have hle : G ≤ saturation G (b, l) hb := fun u hu => (hmem u).mpr ⟨0, by simpa using hu⟩
  apply hG.2 hS hle
  refine (hmem _).mpr ⟨1, ?_⟩
  rw [pow_one, Prod.mk_mul_mk, mul_inv_cancel₀ hb0, mul_inv_cancel₀ hl]
  exact G.one_mem

def p₁ (G : Subring (Ω × L)) : G →+* Ω := (RingHom.fst Ω L).comp G.subtype

def p₂ (G : Subring (Ω × L)) : G →+* L := (RingHom.snd Ω L).comp G.subtype

theorem isUnit_of_p₂_ne_zero {G : Subring (Ω × L)} (hG : Maximal Functional G) (r : G)
    (h : p₂ G r ≠ 0) : IsUnit r := by
  obtain ⟨⟨b, l⟩, hr⟩ := r
  have hl : l ≠ 0 := h
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hl (hG.1 l hr)
  have hinv := inv_mem hG hr hl
  have hprod : (⟨(b, l), hr⟩ : G) * ⟨(b⁻¹, l⁻¹), hinv⟩ = 1 := by
    apply Subtype.ext
    simp [hb0, hl]
  exact ⟨⟨_, _, hprod, by rw [mul_comm]; exact hprod⟩, rfl⟩

theorem isLocalRing_of_maximal {G : Subring (Ω × L)} (hG : Maximal Functional G) :
    IsLocalRing G := by
  have : Nontrivial G := (p₂ G).domain_nontrivial
  have key : ∀ r : G, r ∈ nonunits G ↔ p₂ G r = 0 := by
    intro r
    rw [mem_nonunits_iff]
    constructor
    · intro hr
      by_contra h
      exact hr (isUnit_of_p₂_ne_zero hG r h)
    · intro h hu
      have := hu.map (p₂ G)
      rw [h] at this
      exact not_isUnit_zero this
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [key] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

theorem exists_common_root [IsAlgClosed L] {k : Type*} [Field k] (ι : k →+* L) (I : Ideal k[X])
    (hI : I ≠ ⊤) : ∃ ξ : L, ∀ p ∈ I, eval₂ ι ξ p = 0 := by
  classical
  have hmem : ∀ p, p ∈ I ↔ Submodule.IsPrincipal.generator I ∣ p :=
    fun p => Submodule.IsPrincipal.mem_iff_generator_dvd I
  by_cases hf0 : Submodule.IsPrincipal.generator I = 0
  · refine ⟨0, fun p hp => ?_⟩
    rw [hmem, hf0, zero_dvd_iff] at hp
    rw [hp, eval₂_zero]
  · have hnu : ¬ IsUnit (Submodule.IsPrincipal.generator I) := by
      intro hu
      apply hI
      rw [Ideal.eq_top_iff_one, hmem]
      exact hu.dvd
    have hdeg : (Submodule.IsPrincipal.generator I).degree ≠ 0 := by
      intro h
      exact hnu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_eval₂_eq_zero ι _ hdeg
    refine ⟨ξ, fun p hp => ?_⟩
    obtain ⟨q, rfl⟩ := (hmem p).mp hp
    rw [eval₂_mul, hξ, zero_mul]

theorem mem_of_relations {G : Subring (Ω × L)} (hG : Maximal Functional G) (x : Ω) (ξ : L)
    (h : ∀ p : Polynomial G, eval₂ (p₁ G) x p = 0 → eval₂ (p₂ G) ξ p = 0) : (x, ξ) ∈ G := by
  have hfst : ∀ p : Polynomial G, (eval₂ G.subtype (x, ξ) p).1 = eval₂ (p₁ G) x p :=
    fun p => Polynomial.hom_eval₂ p G.subtype (RingHom.fst Ω L) (x, ξ)
  have hsnd : ∀ p : Polynomial G, (eval₂ G.subtype (x, ξ) p).2 = eval₂ (p₂ G) ξ p :=
    fun p => Polynomial.hom_eval₂ p G.subtype (RingHom.snd Ω L) (x, ξ)
  have hS : Functional (Polynomial.eval₂RingHom G.subtype (x, ξ)).range := by
    intro l hl
    obtain ⟨p, hp⟩ := RingHom.mem_range.mp hl
    have hp' : eval₂ G.subtype (x, ξ) p = (0, l) := hp
    have h1 : eval₂ (p₁ G) x p = 0 := by
      have := hfst p
      rw [hp'] at this
      exact this.symm
    have h2 := h p h1
    have := hsnd p
    rw [hp'] at this
    exact this.trans h2
  have hle : G ≤ (Polynomial.eval₂RingHom G.subtype (x, ξ)).range := by
    intro t ht
    exact RingHom.mem_range.mpr ⟨C ⟨t, ht⟩, by simp⟩
  exact hG.2 hS hle (RingHom.mem_range.mpr ⟨X, by simp⟩)

theorem exists_mem_of_dominates [IsAlgClosed L] {G : Subring (Ω × L)} (hG : Maximal Functional G)
    [IsLocalRing G] [IsLocalHom (p₂ G)] (V : ValuationSubring Ω) (g : G →+* V)
    (hg : ∀ r, (g r : Ω) = p₁ G r) [IsLocalHom g] (x : V) : ∃ ξ : L, ((x : Ω), ξ) ∈ G := by
  classical
  have hsurj : Function.Surjective (Polynomial.mapRingHom (IsLocalRing.residue G)) :=
    Polynomial.map_surjective _ IsLocalRing.residue_surjective
  have hJ : Ideal.map (Polynomial.mapRingHom (IsLocalRing.residue G))
      (RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω))) ≠ ⊤ := by
    intro hJ
    have h1 : (1 : Polynomial (IsLocalRing.ResidueField G)) ∈ Ideal.map (Polynomial.mapRingHom (IsLocalRing.residue G))
        (RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω))) := by
      rw [hJ]
      exact Submodule.mem_top
    obtain ⟨p, hpI, hp1'⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp h1
    have hp : eval₂ (p₁ G) (x : Ω) p = 0 := by
      rw [RingHom.mem_ker, Polynomial.coe_eval₂RingHom] at hpI
      exact hpI
    have hp1 : Polynomial.map (IsLocalRing.residue G) p = 1 := hp1'
    have hcomp : V.subtype.comp g = p₁ G := RingHom.ext hg
    have h0 : eval₂ g x p = 0 := by
      apply Subtype.val_injective
      have := Polynomial.hom_eval₂ p g V.subtype x
      rw [hcomp] at this
      exact this.trans hp
    have hc : (IsLocalRing.residue V).comp g
        = (IsLocalRing.ResidueField.map g).comp (IsLocalRing.residue G) := by
      ext r
      simp
    have h2 : IsLocalRing.residue V (eval₂ g x p) = 1 := by
      rw [Polynomial.hom_eval₂, hc, ← Polynomial.eval₂_map, hp1, eval₂_one]
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  obtain ⟨ξ, hξ⟩ := exists_common_root (IsLocalRing.ResidueField.lift (p₂ G)) _ hJ
  refine ⟨ξ, mem_of_relations hG (x : Ω) ξ fun p hp => ?_⟩
  have hpI : p ∈ RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω)) := by
    rw [RingHom.mem_ker, Polynomial.coe_eval₂RingHom]
    exact hp
  have := hξ _ (Ideal.mem_map_of_mem _ hpI)
  rw [Polynomial.coe_mapRingHom, Polynomial.eval₂_map, IsLocalRing.ResidueField.lift_comp_residue] at this
  exact this

theorem exists_valuationSubring_extension [IsAlgClosed L] (A : Subring Ω) (φ : A →+* L) :
    ∃ (V : ValuationSubring Ω) (hAV : ∀ a ∈ A, a ∈ V) (ψ : V →+* L),
      ∀ a : A, ψ ⟨a.1, hAV a.1 a.2⟩ = φ a := by
  classical
  have hG₀f : Functional (A.subtype.prod φ).range := by
    intro l hl
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp hl
    have h1 : (a : Ω) = 0 := congrArg Prod.fst ha
    have h2 : φ a = l := congrArg Prod.snd ha
    have ha0 : a = 0 := Subtype.ext h1
    rw [← h2, ha0, map_zero]
  obtain ⟨G, hG₀G, hG⟩ := exists_maximal_functional _ hG₀f
  have : IsLocalRing G := isLocalRing_of_maximal hG
  have : IsLocalHom (p₂ G) := ⟨fun r hr => isUnit_of_p₂_ne_zero hG r hr.ne_zero⟩
  have hinj : Function.Injective (p₁ G) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨b, l⟩, hr⟩ h0
    have hb : b = 0 := h0
    subst hb
    have hl := hG.1 l hr
    subst hl
    rfl
  let e : G ≃+* (p₁ G).range := RingEquiv.ofBijective (p₁ G).rangeRestrict
    ⟨fun r s h => hinj (congrArg Subtype.val h), (p₁ G).rangeRestrict_surjective⟩
  have : IsLocalRing (p₁ G).range :=
    IsLocalRing.of_surjective' (p₁ G).rangeRestrict (p₁ G).rangeRestrict_surjective
  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.mk (p₁ G).range)
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV
  have : IsLocalHom (p₁ G).rangeRestrict :=
    IsLocalHom.of_surjective _ (p₁ G).rangeRestrict_surjective
  let g : G →+* V := (Subring.inclusion hle).comp (p₁ G).rangeRestrict
  have : IsLocalHom g := ⟨fun r hr => IsLocalHom.map_nonunit (f := (p₁ G).rangeRestrict) r
    (IsLocalHom.map_nonunit (f := Subring.inclusion hle) (self := hloc) ((p₁ G).rangeRestrict r) hr)⟩
  have hVle : ∀ x ∈ V, x ∈ (p₁ G).range := by
    intro x hx
    obtain ⟨ξ, hξ⟩ := exists_mem_of_dominates hG V g (fun r => rfl) ⟨x, hx⟩
    exact RingHom.mem_range.mpr ⟨⟨(x, ξ), hξ⟩, rfl⟩
  have hVle' : V.toSubring ≤ (p₁ G).range := fun x hx => hVle x hx
  have hmem0 : ∀ a : A, ((a : Ω), φ a) ∈ G := fun a => hG₀G (RingHom.mem_range.mpr ⟨a, rfl⟩)
  have hAV : ∀ a ∈ A, a ∈ V := fun a ha =>
    hle (RingHom.mem_range.mpr ⟨⟨(a, φ ⟨a, ha⟩), hmem0 ⟨a, ha⟩⟩, rfl⟩)
  let ψ : V →+* L := (p₂ G).comp (e.symm.toRingHom.comp (Subring.inclusion hVle'))
  refine ⟨V, hAV, ψ, fun a => ?_⟩
  have key : e ⟨((a : Ω), φ a), hmem0 a⟩ = Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩ := Subtype.ext rfl
  have hpre : e.symm (Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩) = ⟨((a : Ω), φ a), hmem0 a⟩ := by
    rw [← key, RingEquiv.symm_apply_apply]
  show p₂ G (e.symm (Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩)) = φ a
  rw [hpre]
  rfl

theorem chevalley_extension : ∀ (Ω L : Type) [Field Ω] [Field L] [IsAlgClosed L] (A : Subring Ω)
    (φ : A →+* L), ∃ (V : ValuationSubring Ω) (hAV : ∀ a ∈ A, a ∈ V) (ψ : V →+* L),
      ∀ a : A, ψ ⟨a.1, hAV a.1 a.2⟩ = φ a := by
  intro Ω L _ _ _ A φ
  exact exists_valuationSubring_extension A φ

end GlobalTheory.CompanionTheory.Chevalley
