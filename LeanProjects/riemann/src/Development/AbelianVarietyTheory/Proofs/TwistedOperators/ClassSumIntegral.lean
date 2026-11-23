import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicFormsFiniteStabilisers

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory Formalism.L2.Theta
open Formalism.IndefR
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteClassSum

theorem invariant_sup {G X : Type} [Group G] {A B : Subgroup G} {Φ : G → X} (hA : ∀ k ∈ A, ∀ h, Φ (h * k) = Φ h)
    (hB : ∀ k ∈ B, ∀ h, Φ (h * k) = Φ h) : ∀ k ∈ A ⊔ B, ∀ h, Φ (h * k) = Φ h := by
  let S : Subgroup G :=
    { carrier := {k | ∀ h, Φ (h * k) = Φ h}
      mul_mem' := fun {a b} ha hb h => by rw [← mul_assoc, hb, ha]
      one_mem' := fun h => by rw [mul_one]
      inv_mem' := fun {a} ha h => by rw [← ha (h * a⁻¹), inv_mul_cancel_right] }
  exact fun k hk => (sup_le (show A ≤ S from hA) (show B ≤ S from hB) : A ⊔ B ≤ S) hk

theorem integral_eq_sum {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group H] (ν : Measure G) [ν.IsMulLeftInvariant] (π : G →* H) (Γ : Subgroup G) [Countable Γ] {𝓖 : Set G}
    (h𝓖 : IsFundamentalDomain Γ 𝓖 ν) (J : Subgroup H) (ho : IsOpen (J.comap π : Set G)) (h1 : ν (J.comap π) = 1)
    {I : Type} [Fintype I] (y : I → H) (hy : Bridge.IsReps (π.comp Γ.subtype) J y) (a : I → G) (ha : ∀ i, π (a i) = y i)
    (Φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ h, Φ (γ * h) = Φ h) (hr : ∀ k ∈ J.comap π, ∀ h, Φ (h * k) = Φ h) :
    (∀ i, Finite (Bridge.stab (π.comp Γ.subtype) J (y i))) ∧ IntegrableOn Φ 𝓖 ν ∧
      ∫ h in 𝓖, Φ h ∂ν = ∑ i, ((Nat.card (Bridge.stab (π.comp Γ.subtype) J (y i)) : ℂ))⁻¹ * Φ (a i) := by
  have hs : ∀ i, (Bridge.stab (π.comp Γ.subtype) J (y i) : Set Γ) = {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ J.comap π} := by
    intro i
    ext γ
    rw [SetLike.mem_coe, Bridge.mem_stab, Set.mem_setOf_eq, Subgroup.mem_comap, map_mul, map_mul, map_inv, ha]
    rfl
  have hfin : ∀ i, {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ J.comap π}.Finite := fun i =>
    GlobalTheory.InnerClassSum.finite_stab_of_measure ν Γ _ h𝓖 (h1 ▸ one_ne_zero) (h1 ▸ ENNReal.one_ne_top) (a i)
  have him : ∀ i, {γ : G | γ ∈ Γ ∧ (a i)⁻¹ * γ * a i ∈ J.comap π} =
      Subtype.val '' {γ : Γ | (a i)⁻¹ * (γ : G) * a i ∈ J.comap π} := by
    intro i
    ext γ
    simp only [Set.mem_setOf_eq, Set.mem_image, Subtype.exists, exists_and_right, exists_eq_right]
    exact ⟨fun h => ⟨h.1, h.2⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩
  have hu : ∀ x : G, ∃! i, ∃ γ ∈ Γ, ∃ k ∈ J.comap π, x = γ * a i * k := by
    intro x
    refine (existsUnique_congr fun i => ?_).1 (hy (π x))
    constructor
    · rintro ⟨γ, k, e⟩
      refine ⟨γ, γ.2, ((γ : G) * a i)⁻¹ * x, ?_, by group⟩
      rw [Subgroup.mem_comap, map_mul, map_inv, map_mul, ha, e]
      change (π γ * y i)⁻¹ * (π γ * y i * k) ∈ J
      rw [inv_mul_cancel_left]
      exact k.2
    · rintro ⟨γ, hγ, k, hk, rfl⟩
      exact ⟨⟨γ, hγ⟩, ⟨π k, hk⟩, by rw [map_mul, map_mul, ha]; rfl⟩
  obtain ⟨-, hi, he⟩ := GlobalTheory.Ker.integral_fundamentalDomain_eq_sum_doubleCoset G ν Γ (J.comap π) 𝓖 h𝓖 ho
    (h1 ▸ ENNReal.one_ne_top) I a hu (fun i => him i ▸ (hfin i).image _) Φ hl hr
  refine ⟨fun i => ?_, hi, ?_⟩
  · have := hfin i
    rw [← hs] at this
    exact this
  · rw [he, h1]
    simp only [ENNReal.toReal_one, Complex.ofReal_one, one_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [him, Set.ncard_image_of_injective _ Subtype.val_injective, ← hs, ← Nat.card_coe_set_eq]
    rfl

theorem classSumIntegral : GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.ClassSumIntegral := by
  intro D V _ K hK μ 𝓕 hμ I _ y hy z hz Φ hΦ
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  have hC := hT.2.2.2.2.2.2
  have := hμ.1.1
  have hr : ∀ k ∈ K.comap (Lev.finE V), ∀ h, Φ (h * k) = Φ h := by
    rw [GlobalTheory.Mass.Levels.comap_finE]
    exact invariant_sup hΦ.level hΦ.real
  have ho : IsOpen (((GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) : Set (GA D V)) := hK.1
  have h1 : μ ((GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K).comap (finHom V).rangeRestrict : Subgroup (GA D V)) = 1 :=
    GlobalTheory.Mass.Levels.measure_comap_finE hμ.1
  exact integral_eq_sum μ (finHom V).rangeRestrict (GQ V) hμ.2 (GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.levelFin V K) ho h1 y hy z hz Φ hΦ.left hr

end GlobalTheory.DefiniteClassSum
