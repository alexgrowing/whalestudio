import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOfSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSummandGoodPlaceIndicator
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical

namespace GlobalTheory.OrbWeights

theorem mem_stabLat_iff_mulLat_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A]
    (t : Aˣ) (L : Submodule O A) :
    t ∈ GlobalTheory.UnitLemma.stabLat O L ↔ GlobalTheory.UnitLemma.mulLat O (t : A) L = L := by
  constructor
  · intro ht
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (ht y).1 hy
    · intro y hy
      have h1 : ((t⁻¹ : Aˣ) : A) * y ∈ L := by
        rw [ht]
        rw [← mul_assoc, Units.mul_inv, one_mul]
        exact hy
      refine ⟨((t⁻¹ : Aˣ) : A) * y, h1, ?_⟩
      change (t : A) * (((t⁻¹ : Aˣ) : A) * y) = y
      rw [← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    constructor
    · intro hy
      rw [← h]
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← h] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      change (t : A) * z = (t : A) * y at hzy
      have : z = y := by
        have := congrArg (fun w => ((t⁻¹ : Aˣ) : A) * w) hzy
        simpa [← mul_assoc] using this
      rw [← this]
      exact hz

theorem relIndex_stab_eq_relIndex_stabLat : ∀ {G : Type} [Group G] [TopologicalSpace G] (Kg : Subgroup G) (δ : G) {O A : Type} [CommRing O] [CommRing A] [Algebra O A] (Tb : Subgroup Aˣ) (M : G → Submodule O A) (τ : G → Aˣ), (∀ g k : G, k ∈ Kg → M (g * k) = M g) → (∀ g g' : G, M g = M g' → g⁻¹ * g' ∈ Kg) → (∀ h ∈ twCent (MonoidHom.id G) δ, τ h ∈ Tb ∧ ∀ g : G, M (h * g) = GlobalTheory.UnitLemma.mulLat O (τ h : A) (M g)) → (∀ s ∈ Tb, ∃ h ∈ twCent (MonoidHom.id G) δ, τ h = s) → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ (h * h') = τ h * τ h') → (∀ h ∈ twCent (MonoidHom.id G) δ, ∀ h' ∈ twCent (MonoidHom.id G) δ, τ h = τ h' → h = h') → (∀ h ∈ twCent (MonoidHom.id G) δ, h ∈ cptPart (twCent (MonoidHom.id G) δ) ↔ τ h ∈ GlobalTheory.UnitLemma.intUnits O A) → ∀ g : G, (twCent (MonoidHom.id G) δ ⊓ Kg.map (MulAut.conj g).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) δ)) = (GlobalTheory.UnitLemma.stabLat O (M g) ⊓ Tb).relIndex (GlobalTheory.UnitLemma.intUnits O A ⊓ Tb) := by
  intro G _ _ Kg δ O A _ _ _ Tb M τ hK hM hτ hsurj hmul hinj hcpt g
  set T := twCent (MonoidHom.id G) δ with hT
  have hone : τ 1 = 1 := by
    have := hmul 1 T.one_mem 1 T.one_mem
    rw [one_mul] at this
    exact (mul_eq_left.mp this.symm)
  let φ : T →* Aˣ :=
    { toFun := fun h => τ h
      map_one' := hone
      map_mul' := fun a b => hmul a a.2 b b.2 }
  have hφ : ∀ x : T, φ x = τ x := fun _ => rfl
  have hinjφ : Function.Injective φ := fun a b hab => Subtype.ext (hinj a a.2 b b.2 hab)
  have hCT : cptPart T ≤ T := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1
  rw [← Subgroup.relIndex_subgroupOf (H := T ⊓ Kg.map (MulAut.conj g).toMonoidHom) hCT,
    ← Subgroup.relIndex_map_map_of_injective _ _ hinjφ]
  congr 1
  · ext t
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, ⟨_, k, hk, hkx⟩, rfl⟩
      refine ⟨?_, (hτ x x.2).1⟩
      rw [hφ, mem_stabLat_iff_mulLat_eq, ← (hτ x x.2).2 g]
      have : (x : G) * g = g * k := by
        rw [← hkx]
        simp [mul_assoc]
      rw [this, hK g k hk]
    · rintro ⟨hs, hb⟩
      obtain ⟨h, hh, rfl⟩ := hsurj t hb
      refine ⟨⟨h, hh⟩, ⟨hh, g⁻¹ * (h * g), ?_, ?_⟩, rfl⟩
      · apply hM
        rw [mem_stabLat_iff_mulLat_eq, ← (hτ h hh).2 g] at hs
        exact hs.symm
      · simp [mul_assoc]
  · ext t
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(hcpt x x.2).1 hx, (hτ x x.2).1⟩
    · rintro ⟨hi, hb⟩
      obtain ⟨h, hh, rfl⟩ := hsurj t hb
      exact ⟨⟨h, hh⟩, (hcpt h hh).2 hi, rfl⟩

end GlobalTheory.OrbWeights
