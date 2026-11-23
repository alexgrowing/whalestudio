import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsExtraRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsMulMemAdjoinOfIsLocalization
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsAmpleBaseLocalizationEq
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts)

section Local

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

theorem not_mem_of_inv_mem_locIn (A : Subalgebra S Ω) (p : Ideal A) (hp : p.IsPrime) (b : A)
    (hb0 : (b : Ω) ≠ 0) (hb : (b : Ω)⁻¹ ∈ locIn A p) : b ∉ p := by
  have := hp
  obtain ⟨a, s, hs, e⟩ := (mem_locIn_iff A p _).mp hb
  intro hbp
  have hs0 : (s : Ω) ≠ 0 := fun h => hs (by rw [show s = 0 from Subtype.ext h]; exact p.zero_mem)
  have : s = a * b := Subtype.ext (by
    push_cast
    field_simp at e
    linear_combination e)
  exact hs (this ▸ p.mul_mem_left a hbp)

end Local

section Loc

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]
  {S' : Type} [CommRing S'] [Algebra S S'] [Algebra S' Ω] [IsScalarTower S S' Ω]
  (M : Submonoid S) [IsLocalization M S']

theorem algebraMap_mem_units {m : S} (hm : m ∈ M) (A' : Subalgebra S' Ω) :
    algebraMap S Ω m ≠ 0 ∧ algebraMap S Ω m ∈ A' ∧ (algebraMap S Ω m)⁻¹ ∈ A' := by
  obtain ⟨u, hu⟩ := IsLocalization.map_units S' (⟨m, hm⟩ : M)
  have hu' : (u : S') = algebraMap S S' m := hu
  have e : algebraMap S Ω m = algebraMap S' Ω u := by
    rw [IsScalarTower.algebraMap_apply S S' Ω, ← hu']
  have h1 : algebraMap S' Ω u * algebraMap S' Ω ↑u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hne : algebraMap S Ω m ≠ 0 := fun h => by
    rw [e] at h; rw [h, zero_mul] at h1; exact zero_ne_one h1
  refine ⟨hne, e ▸ Subalgebra.algebraMap_mem _ _, ?_⟩
  rw [e, inv_eq_of_mul_eq_one_right h1]
  exact Subalgebra.algebraMap_mem _ _

theorem algebraMap_not_mem_prime {m : S} (hm : m ∈ M) (A' : Subalgebra S' Ω) (p' : Ideal A')
    (hp' : p'.IsPrime) : (⟨algebraMap S Ω m, (algebraMap_mem_units M hm A').2.1⟩ : A') ∉ p' := by
  intro h
  obtain ⟨hne, hmem, hinv⟩ := algebraMap_mem_units M hm A'
  have h' := p'.mul_mem_left (⟨_, hinv⟩ : A') h
  rw [show (⟨_, hinv⟩ : A') * ⟨_, hmem⟩ = 1 from Subtype.ext (by simp [inv_mul_cancel₀ hne])] at h'
  exact hp'.ne_top ((Ideal.eq_top_iff_one _).mpr h')

def inclHom (A : Subalgebra S Ω) (A' : Subalgebra S' Ω) (hle : ∀ a ∈ A, a ∈ A') : A →+* A' where
  toFun a := ⟨a, hle a a.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem locIn_comap_inclHom (A : Subalgebra S Ω) (A' : Subalgebra S' Ω) (hle : ∀ a ∈ A, a ∈ A')
    (hden : ∀ a ∈ A', ∃ m ∈ M, algebraMap S Ω m * a ∈ A) (p' : Ideal A') (hp' : p'.IsPrime) :
    locIn A' p' = locIn A (p'.comap (inclHom A A' hle)) := by
  apply le_antisymm
  · refine Subring.closure_le.mpr ?_
    rintro u ⟨a', b', hb', rfl⟩
    obtain ⟨m₁, hm₁, h₁⟩ := hden a' a'.2
    obtain ⟨m₂, hm₂, h₂⟩ := hden b' b'.2
    have n₁ := (algebraMap_mem_units M hm₁ A').1
    have n₂ := (algebraMap_mem_units M hm₂ A').1
    have nb : (b' : Ω) ≠ 0 := fun h => hb' (by rw [show b' = 0 from Subtype.ext h]; exact p'.zero_mem)
    refine Subring.subset_closure ⟨⟨_, mul_mem (Subalgebra.algebraMap_mem A m₂) h₁⟩,
      ⟨_, mul_mem (Subalgebra.algebraMap_mem A m₁) h₂⟩, ?_, ?_⟩
    · rw [Ideal.mem_comap]
      intro h
      have e : inclHom A A' hle ⟨_, mul_mem (Subalgebra.algebraMap_mem A m₁) h₂⟩ =
          ⟨algebraMap S Ω m₁, (algebraMap_mem_units M hm₁ A').2.1⟩ *
            (⟨algebraMap S Ω m₂, (algebraMap_mem_units M hm₂ A').2.1⟩ * b') := Subtype.ext rfl
      rw [e] at h
      rcases hp'.mem_or_mem h with h | h
      · exact algebraMap_not_mem_prime M hm₁ A' p' hp' h
      rcases hp'.mem_or_mem h with h | h
      · exact algebraMap_not_mem_prime M hm₂ A' p' hp' h
      · exact hb' h
    · show (a' : Ω) / b' = algebraMap S Ω m₂ * (algebraMap S Ω m₁ * a') /
        (algebraMap S Ω m₁ * (algebraMap S Ω m₂ * b'))
      field_simp
  · refine Subring.closure_le.mpr ?_
    rintro u ⟨a, b, hb, rfl⟩
    exact Subring.subset_closure ⟨inclHom A A' hle a, inclHom A A' hle b, hb, rfl⟩

theorem isLocalization_inclHom (A : Subalgebra S Ω) (A' : Subalgebra S' Ω) (hle : ∀ a ∈ A, a ∈ A')
    (hden : ∀ a ∈ A', ∃ m ∈ M, algebraMap S Ω m * a ∈ A) :
    letI := (inclHom A A' hle).toAlgebra
    IsLocalization (M.map (algebraMap S A)) A' := by
  let _ := (inclHom A A' hle).toAlgebra
  refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, hm, rfl⟩
    obtain ⟨hne, hmem, hinv⟩ := algebraMap_mem_units M hm A'
    refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
    show algebraMap S Ω m * (algebraMap S Ω m)⁻¹ = 1
    exact mul_inv_cancel₀ hne
  · intro z
    obtain ⟨m, hm, h⟩ := hden z z.2
    refine ⟨(⟨_, h⟩, ⟨algebraMap S A m, Submonoid.mem_map_of_mem _ hm⟩), Subtype.ext ?_⟩
    show (z : Ω) * algebraMap S Ω m = algebraMap S Ω m * z
    ring
  · intro x y hxy
    refine ⟨1, ?_⟩
    have h' : ((algebraMap A A' x : A') : Ω) = (algebraMap A A' y : A') := congrArg Subtype.val hxy
    rw [show x = y from Subtype.ext h']

variable {K : Type} {ι : K → Type}

theorem chartRingOver_le (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    ∀ a ∈ chartRingOver S y c, a ∈ chartRingOver S' y c := by
  have hle : chartRingOver S y c ≤ (chartRingOver S' y c).restrictScalars S :=
    Algebra.adjoin_le fun x hx => (Algebra.subset_adjoin hx : x ∈ Algebra.adjoin S' _)
  exact fun a ha => hle ha

theorem modelPts_localization (y : (Σ k, ι k) → Ω) :
    modelPts S' y = {z | z ∈ modelPts S y ∧ ∀ m ∈ M, (algebraMap S Ω m)⁻¹ ∈ z} := by
  ext z
  have hden : ∀ c, ∀ a ∈ chartRingOver S' y c, ∃ m ∈ M, algebraMap S Ω m * a ∈ chartRingOver S y c :=
    fun c a ha => exists_mul_mem_adjoin_of_isLocalization (S' := S') M _ ha
  constructor
  · rintro ⟨c, hc, p', hp', rfl⟩
    refine ⟨⟨c, hc, p'.comap (inclHom _ _ (chartRingOver_le (S := S) (S' := S') y c)), by have := hp'; infer_instance,
      locIn_comap_inclHom M _ _ _ (hden c) p' hp'⟩, fun m hm => ?_⟩
    obtain ⟨hne, hmem, hinv⟩ := algebraMap_mem_units M hm (chartRingOver S' y c)
    exact Subring.subset_closure ⟨1, ⟨_, hmem⟩, algebraMap_not_mem_prime M hm _ p' hp', by simp⟩
  · rintro ⟨⟨c, hc, p, hp, rfl⟩, hM⟩
    let _ := (inclHom _ _ (chartRingOver_le (S := S) (S' := S') y c)).toAlgebra
    have := isLocalization_inclHom M _ _ (chartRingOver_le (S := S) (S' := S') y c) (hden c)
    have hd : Disjoint ((M.map (algebraMap S (chartRingOver S y c)) : Submonoid (chartRingOver S y c)) :
        Set (chartRingOver S y c)) (p : Set (chartRingOver S y c)) := by
      rw [Set.disjoint_left]
      rintro _ ⟨m, hm, rfl⟩ hmp
      exact not_mem_of_inv_mem_locIn _ p hp _ (algebraMap_mem_units M hm (chartRingOver S' y c)).1
        (hM m hm) hmp
    have hp' := IsLocalization.isPrime_of_isPrime_disjoint
      (M.map (algebraMap S (chartRingOver S y c))) (chartRingOver S' y c) p hp hd
    refine ⟨c, hc, _, hp', ?_⟩
    rw [locIn_comap_inclHom M _ _ _ (hden c) _ hp']
    congr 1
    exact (IsLocalization.under_map_of_isPrime_disjoint
      (M.map (algebraMap S (chartRingOver S y c))) (chartRingOver S' y c) hp hd).symm

end Loc

theorem ModelWithBaseLocalization.proof : ModelWithBaseLocalization.Statement := by
  intro S _ K ι Ω _ _ y k₀ S' _ _ _ _ M _ h
  refine ⟨h.1, ?_⟩
  have e : modelPts S y = modelPts S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)) := h.2
  show modelPts S' y = modelPts S' (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀))
  rw [modelPts_localization M y, modelPts_localization M (IndefiniteRowSideFullHecke.Kleiman2.oneBlock (IndefiniteRowSideFullHecke.Kleiman2.blockVec y k₀)), e]

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
