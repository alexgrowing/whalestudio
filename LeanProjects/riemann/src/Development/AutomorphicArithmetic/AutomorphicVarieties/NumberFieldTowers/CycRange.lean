import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContTw
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.CycMemPrincIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.PrincGen

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Tower

theorem UpperTheory.V.Tower.cycRange :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime], HasMuQ l L → (cycZ L Ω l).range = KStar.TotallyRealRoots.princ l (cZero l L) := by
  intro L Ω _ _ _ _ _ l _ hq
  have hmu := muQ L Ω l
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed L
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  haveI : IsGalois L Ω := inferInstance
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hinj := (algebraMap L Ω).injective
  have key : ∀ (σ : G L Ω) (n : ℕ) (t : Ω), t ^ l ^ n = 1 →
      σ t = t ^ ((cycZ L Ω l σ : ℤ_[l]).toZModPow n).val := by
    intro σ n t ht
    exact cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G L Ω) Ω σ) t ht
  have hmem : ∀ (a : ℕ) (u : ℤ_[l]ˣ), u ∈ KStar.TotallyRealRoots.princ l a ↔ (u : ℤ_[l]).toZModPow a = 1 := by
    intro a u
    simp [KStar.TotallyRealRoots.princ, KStar.TotallyRealRoots.redPow, MonoidHom.mem_ker, Units.ext_iff]
  have hone : ∀ (n : ℕ) (t : Ω), IsPrimitiveRoot t (l ^ n) → t ^ ((1 : ZMod (l ^ n)).val) = t := by
    intro n t ht
    rw [ZMod.val_one_eq_one_mod, ht.eq_orderOf, pow_mod_orderOf, pow_one]
  have hfixed : ∀ (n : ℕ) (t : Ω) (a : ZMod (l ^ n)), IsPrimitiveRoot t (l ^ n) → t ^ a.val = t → a = 1 := by
    intro n t a ht h
    apply ZMod.val_injective
    apply ht.pow_inj (ZMod.val_lt a) (ZMod.val_lt 1)
    rw [h, hone n t ht]
  have hq' : qExp l ≤ cZero l L := hmu.2.2.1.mp hq
  have hle : (cycZ L Ω l).range ≤ KStar.TotallyRealRoots.princ l (cZero l L) := by
    rintro _ ⟨σ, rfl⟩
    obtain ⟨ζ, hζ⟩ := (hmu.1 (cZero l L)).2 le_rfl
    have hζ' : IsPrimitiveRoot (algebraMap L Ω ζ) (l ^ cZero l L) := hζ.map_of_injective hinj
    have hfix : σ (algebraMap L Ω ζ) = algebraMap L Ω ζ := σ.commutes ζ
    rw [key σ _ _ hζ'.pow_eq_one] at hfix
    exact (hmem _ _).2 (hfixed _ _ _ hζ' hfix)
  apply le_antisymm hle
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ (cZero l L + 1))
  have hnot : ξ ∉ Set.range (algebraMap L Ω) := by
    rintro ⟨x, rfl⟩
    have hx : IsPrimitiveRoot x (l ^ (cZero l L + 1)) := hξ.of_map_of_injective hinj
    have := (hmu.1 (cZero l L + 1)).1 ⟨x, hx⟩
    omega
  rw [InfiniteGalois.mem_range_algebraMap_iff_fixed] at hnot
  push_neg at hnot
  obtain ⟨σ, hσ⟩ := hnot
  have hu : cycZ L Ω l σ ∈ KStar.TotallyRealRoots.princ l (cZero l L) := hle ⟨σ, rfl⟩
  have hu' : cycZ L Ω l σ ∉ KStar.TotallyRealRoots.princ l (cZero l L + 1) := by
    intro hm
    apply hσ
    rw [key σ _ _ hξ.pow_eq_one, (hmem _ _).1 hm, hone _ _ hξ]
  have hgen := ((princGen l (cZero l L) hq').1 _ hu).2 hu'
  refine hgen.trans (Subgroup.topologicalClosure_minimal _ ?_ ?_)
  · rw [Subgroup.zpowers_le]
    exact ⟨σ, rfl⟩
  · rw [MonoidHom.coe_range]
    exact (isCompact_range (continuous_cycZ L Ω l)).isClosed
