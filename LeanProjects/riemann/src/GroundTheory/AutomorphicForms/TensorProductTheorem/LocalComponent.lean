import Mathlib
import GroundTheory.AutomorphicForms.TensorProductTheorem.Window

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module Set

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}

section General

variable (σ) in

def genSubrep (N : Submodule ℂ V) : Subrepresentation σ where
  toSubmodule := ⨆ g : L, N.map (σ g)
  apply_mem_toSubmodule g x hx := by
    have : (⨆ h : L, N.map (σ h)) ≤ (⨆ h : L, N.map (σ h)).comap (σ g) := by
      refine iSup_le fun h => ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact Submodule.mem_iSup_of_mem (g * h) ⟨n, hn, rfl⟩
    exact this hx

theorem mem_genSubrep_of_mem {N : Submodule ℂ V} {n : V} (hn : n ∈ N) (g : L) :
    σ g n ∈ (genSubrep σ N).toSubmodule :=
  Submodule.mem_iSup_of_mem g ⟨n, hn, rfl⟩

theorem le_genSubrep (N : Submodule ℂ V) : N ≤ (genSubrep σ N).toSubmodule := fun n hn => by
  simpa using mem_genSubrep_of_mem (σ := σ) hn 1

theorem genSubrep_le {N : Submodule ℂ V} {X : Subrepresentation σ} (h : N ≤ X.toSubmodule) :
    (genSubrep σ N).toSubmodule ≤ X.toSubmodule :=
  iSup_le fun g => by
    rintro _ ⟨n, hn, rfl⟩
    exact X.apply_mem_toSubmodule g (h hn)

end General

variable (hσ : IsSmooth σ) {K : Subgroup L} (hKc : IsCompact (K : Set L))
  (hKo : IsOpen (K : Set L)) (N : Submodule ℂ V)

def genKernel : Submodule ℂ (genSubrep σ N).toSubmodule where
  carrier := {u | ∀ g, fixedProj σ hσ hKc hKo (σ g u) = 0}
  add_mem' {a b} ha hb g := by
    simp only [mem_setOf_eq, Submodule.coe_add, map_add, ha g, hb g, add_zero]
  zero_mem' g := by simp
  smul_mem' c a ha g := by
    simp only [mem_setOf_eq, Submodule.coe_smul, map_smul, ha g, smul_zero]

theorem genKernel_le_comap (g : L) :
    genKernel hσ hKc hKo N ≤
      (genKernel hσ hKc hKo N).comap ((genSubrep σ N).toRepresentation g) := by
  intro u hu h
  show fixedProj σ hσ hKc hKo (σ h (σ g u)) = 0
  rw [← Module.End.mul_apply, ← map_mul]
  exact hu (h * g)

def genQuotRep : Representation ℂ L ((genSubrep σ N).toSubmodule ⧸ genKernel hσ hKc hKo N) :=
  (genSubrep σ N).toRepresentation.quotient _ (genKernel_le_comap hσ hKc hKo N)

def genQuotMk : N →ₗ[ℂ] (genSubrep σ N).toSubmodule ⧸ genKernel hσ hKc hKo N :=
  (genKernel hσ hKc hKo N).mkQ ∘ₗ Submodule.inclusion (le_genSubrep N)

theorem genQuotRep_mk (g : L) (u : (genSubrep σ N).toSubmodule) :
    genQuotRep hσ hKc hKo N g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ((genSubrep σ N).toRepresentation g u) :=
  rfl

def genQuotMap : Representation.IntertwiningMap (genSubrep σ N).toRepresentation
    (genQuotRep hσ hKc hKo N) where
  toLinearMap := (genKernel hσ hKc hKo N).mkQ
  isIntertwining' g := LinearMap.ext fun _ => rfl

include hσ in
theorem isSmooth_genSubrep : IsSmooth (genSubrep σ N).toRepresentation := by
  intro u
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf σ (u : V)) (fun g hg => ?_) (hσ u)
  exact Subtype.ext hg

theorem isSmooth_genQuotRep : IsSmooth (genQuotRep hσ hKc hKo N) := by
  intro q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf (genSubrep σ N).toRepresentation u)
    (fun g hg => ?_) (isSmooth_genSubrep hσ N u)
  show genQuotRep hσ hKc hKo N g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  rw [genQuotRep_mk, hg]

variable {N}

section Simple

variable (hNK : N ≤ fixedVectors σ K)
  (hNst : ∀ g, ∀ n ∈ N, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N)

include hNK hNst in

theorem mem_of_mem_genSubrep_fixed {u : V} (hu : u ∈ (genSubrep σ N).toSubmodule)
    (huK : u ∈ fixedVectors σ K) : u ∈ N := by
  have h1 : (fixedProj σ hσ hKc hKo u : V) = u := fixedProj_apply_of_mem hσ hKc hKo huK
  rw [← h1]
  have : (genSubrep σ N).toSubmodule ≤ N.comap ((fixedVectors σ K).subtype ∘ₗ
      fixedProj σ hσ hKc hKo) := by
    refine iSup_le fun g => ?_
    rintro _ ⟨n, hn, rfl⟩
    exact hNst g n hn
  exact this hu

include hNK in
theorem genQuotMk_injective : Function.Injective (genQuotMk hσ hKc hKo N) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro n hn
  rw [LinearMap.mem_ker, genQuotMk, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hn
  have := hn 1
  rw [map_one, Module.End.one_apply] at this
  have h2 : (fixedProj σ hσ hKc hKo (n : V) : V) = n := fixedProj_apply_of_mem hσ hKc hKo (hNK n.2)
  rw [Submodule.mem_bot]
  refine Subtype.ext ?_
  rw [← h2]
  simp only [Submodule.coe_inclusion] at this
  rw [this]
  rfl

include hNK in

theorem genQuotMk_mem_fixedVectors (n : N) :
    genQuotMk hσ hKc hKo N n ∈ fixedVectors (genQuotRep hσ hKc hKo N) K := by
  intro k hk
  show genQuotRep hσ hKc hKo N k (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
  rw [genQuotRep_mk]
  congr 1
  exact Subtype.ext (hNK n.2 k hk)

include hNK hNst in

theorem isIrreducible_genQuotRep (hN0 : N ≠ ⊥)
    (hNmin : ∀ N₁ : Submodule ℂ V, N₁ ≤ N → N₁ ≠ ⊥ →
      (∀ g, ∀ n ∈ N₁, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N₁) → N₁ = N) :
    (genQuotRep hσ hKc hKo N).IsIrreducible := by
  set U := genSubrep σ N
  set U₀ := genKernel hσ hKc hKo N
  set π := genQuotRep hσ hKc hKo N
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hmk0 : genQuotMk hσ hKc hKo N ⟨n, hn⟩ ≠ 0 := by
    intro h
    have := genQuotMk_injective hσ hKc hKo hNK (a₁ := ⟨n, hn⟩) (a₂ := 0) (by rw [h, map_zero])
    exact hn0 (congrArg Subtype.val this)
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro h0
    have : genQuotMk hσ hKc hKo N ⟨n, hn⟩ ∈ (⊤ : Subrepresentation π).toSubmodule :=
      Submodule.mem_top
    rw [← h0] at this
    exact hmk0 this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun X => ?_ }

  let Y : Subrepresentation σ :=
    { toSubmodule := (X.toSubmodule.comap U₀.mkQ).map U.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨u, hu, rfl⟩
        refine ⟨U.toRepresentation g u, ?_, rfl⟩
        have hu' : U₀.mkQ u ∈ X.toSubmodule := hu
        have := X.apply_mem_toSubmodule g hu'
        exact this }
  have hYU : ∀ {x : V}, x ∈ Y.toSubmodule → x ∈ U.toSubmodule := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2

  have hst : ∀ g, ∀ m ∈ Y.toSubmodule ⊓ N, (fixedProj σ hσ hKc hKo (σ g m) : V) ∈
      Y.toSubmodule ⊓ N := by
    rintro g m ⟨hmY, hmN⟩
    exact ⟨fixedProj_mem hσ hKc hKo Y (Y.apply_mem_toSubmodule g hmY), hNst g m hmN⟩
  by_cases hYN : Y.toSubmodule ⊓ N = ⊥
  ·
    left
    ext q
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      show Submodule.Quotient.mk u = (0 : U.toSubmodule ⧸ U₀)
      rw [Submodule.Quotient.mk_eq_zero]
      intro g
      have hY : (U.toRepresentation g u : V) ∈ Y.toSubmodule :=
        ⟨U.toRepresentation g u, X.apply_mem_toSubmodule g hq, rfl⟩
      have h1 := fixedProj_mem hσ hKc hKo Y hY
      have h2 : (fixedProj σ hσ hKc hKo (σ g u) : V) ∈ N :=
        mem_of_mem_genSubrep_fixed hσ hKc hKo hNK hNst (hYU h1) (fixedProj σ hσ hKc hKo _).2
      have h3 : (fixedProj σ hσ hKc hKo (σ g u) : V) ∈ Y.toSubmodule ⊓ N := ⟨h1, h2⟩
      rw [hYN, Submodule.mem_bot] at h3
      exact Subtype.ext h3
    · have : q = 0 := hq
      rw [this]
      exact X.toSubmodule.zero_mem
  ·
    right
    have hle : Y.toSubmodule ⊓ N ≤ N := inf_le_right
    have heq := hNmin _ hle hYN hst
    have hNY : N ≤ Y.toSubmodule := heq ▸ inf_le_left
    have hUY := genSubrep_le hNY
    ext q
    refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u', hu', hu'u⟩ := hUY u.2
    have : u' = u := Subtype.ext hu'u
    rw [← this]
    exact hu'

end Simple

theorem isAdmissible_genQuotRep
    (hfin : ∀ K' : Subgroup L, IsCompact (K' : Set L) → IsOpen (K' : Set L) →
      FiniteDimensional ℂ (fixedVectors (genSubrep σ N).toRepresentation K')) :
    IsAdmissible (genQuotRep hσ hKc hKo N) := by
  refine ⟨isSmooth_genQuotRep hσ hKc hKo N, fun K' hK'c hK'o => ?_⟩
  have := hfin K' hK'c hK'o
  have hsurj := fixedMap_surjective (isSmooth_genSubrep hσ N) (isSmooth_genQuotRep hσ hKc hKo N)
    hK'c hK'o (f := genQuotMap hσ hKc hKo N) (Submodule.mkQ_surjective _)
  exact Module.Finite.of_surjective _ hsurj

def genQuotForm (l : Dual ℂ (fixedVectors σ K)) :
    Dual ℂ ((genSubrep σ N).toSubmodule ⧸ genKernel hσ hKc hKo N) :=
  (genKernel hσ hKc hKo N).liftQ (l ∘ₗ fixedProj σ hσ hKc hKo ∘ₗ (genSubrep σ N).toSubmodule.subtype)
    fun u hu => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
      have := hu 1
      rw [map_one, Module.End.one_apply] at this
      simp only [Submodule.subtype_apply, this, map_zero]

theorem genQuotForm_apply (l : Dual ℂ (fixedVectors σ K)) (hNK : N ≤ fixedVectors σ K) (g : L)
    (n : N) :
    genQuotForm hσ hKc hKo l (genQuotRep hσ hKc hKo N g (genQuotMk hσ hKc hKo N n)) =
      l (fixedProj σ hσ hKc hKo (σ g n)) :=
  rfl

end RestrictedTensor

end GroundTheory.Automorphic
