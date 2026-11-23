import Mathlib
import GroundTheory.LocalFields.LubinTatePrimitive
import GroundTheory.LocalFields.LubinTateTowerMaps
import GroundTheory.LocalFields.LubinTateLimitGalois
import GroundTheory.LocalFields.LubinTateUnramified

noncomputable section

open IntermediateField Topology Filter

namespace GroundTheory.LocalField

open ValuativeRel GroundTheory.LocalField.Abstract

namespace FormalGroup

section UnramifiedTower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [Algebra K Ω] [IsSepClosed Ω]

variable (K Ω) in

def unramifiedTowerRoot (k : ℕ) : Ω :=
  Classical.choose (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))

theorem isPrimitiveRoot_unramifiedTowerRoot (k : ℕ) :
    IsPrimitiveRoot (unramifiedTowerRoot K Ω k) (Nat.card 𝓀[K] ^ (k + 1).factorial - 1) := by
  unfold unramifiedTowerRoot
  exact Classical.choose_spec (exists_isPrimitiveRoot_card_pow_sub_one (K := K) (Ksep := Ω)
    (Nat.factorial_ne_zero (k + 1)))

variable (K Ω) in

def unramifiedTower (k : ℕ) : IntermediateField K Ω := K⟮unramifiedTowerRoot K Ω k⟯

theorem isUnramifiedSubextension_unramifiedTower (k : ℕ) :
    IsUnramifiedSubextension (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).1

theorem finrank_unramifiedTower (k : ℕ) :
    Module.finrank K (unramifiedTower K Ω k) = (k + 1).factorial :=
  (isUnramifiedSubextension_adjoin (Nat.factorial_ne_zero _)
    (isPrimitiveRoot_unramifiedTowerRoot (K := K) (Ω := Ω) k)).2

theorem le_unramifiedTower_of_isUnramifiedSubextension {E : IntermediateField K Ω}
    (hE : IsUnramifiedSubextension E) {k : ℕ} (hk : Module.finrank K E ≤ k + 1) :
    E ≤ unramifiedTower K Ω k := by
  have := hE.1
  exact hE.le_adjoin (Nat.factorial_ne_zero _)
    (Nat.dvd_factorial Module.finrank_pos hk) (isPrimitiveRoot_unramifiedTowerRoot k)

theorem monotone_unramifiedTower : Monotone (unramifiedTower K Ω) := fun j k h => by
  have := (isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) j).1
  exact (isUnramifiedSubextension_unramifiedTower j).le_adjoin (Nat.factorial_ne_zero _)
    (by rw [finrank_unramifiedTower]; exact Nat.factorial_dvd_factorial (Nat.succ_le_succ h))
    (isPrimitiveRoot_unramifiedTowerRoot k)

theorem unramifiedTower_le_maximalUnramifiedExtension (k : ℕ) :
    unramifiedTower K Ω k ≤ maximalUnramifiedExtension K Ω :=
  (isUnramifiedSubextension_unramifiedTower k).le_maximalUnramifiedExtension

theorem exists_mem_unramifiedTower {x : Ω} (hx : x ∈ maximalUnramifiedExtension K Ω) :
    ∃ k, x ∈ unramifiedTower K Ω k := by
  obtain ⟨E, hE, hxE⟩ := mem_maximalUnramifiedExtension_iff.mp hx
  exact ⟨Module.finrank K E, le_unramifiedTower_of_isUnramifiedSubextension hE (Nat.le_succ _) hxE⟩

instance (k : ℕ) : IsGalois K (unramifiedTower K Ω k) :=
  (isUnramifiedSubextension_unramifiedTower k).isGalois

end UnramifiedTower

section MaxUnramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}

abbrev towerSup (hf : IsLubinTateSeries π f) (k : ℕ) : IntermediateField K Ω :=
  lubinTateField Ω hπ hf (k + 1) ⊔ unramifiedTower K Ω k

theorem monotone_towerSup (hf : IsLubinTateSeries π f) : Monotone (towerSup (Ω := Ω) hπ hf) :=
  fun _ _ h => sup_le_sup (lubinTateField_mono hπ hf (Nat.succ_le_succ h))
    (monotone_unramifiedTower h)

variable (Ω) in

abbrev lubinTateMaxUnramified (hπ : Irreducible π) : IntermediateField K Ω :=
  lubinTateLimit Ω hπ ⊔ maximalUnramifiedExtension K Ω

theorem towerSup_le (hf : IsLubinTateSeries π f) (k : ℕ) :
    towerSup (Ω := Ω) hπ hf k ≤ lubinTateMaxUnramified Ω hπ :=
  sup_le_sup (lubinTateField_le_lubinTateLimit hπ hf _) (unramifiedTower_le_maximalUnramifiedExtension k)

theorem exists_mem_towerSup (hf : IsLubinTateSeries π f) {x : Ω}
    (hx : x ∈ lubinTateMaxUnramified Ω hπ) : ∃ k, x ∈ towerSup hπ hf k := by
  have hle : lubinTateMaxUnramified Ω hπ ≤ ⨆ k, towerSup hπ hf k := by
    refine sup_le ?_ ?_
    · rw [lubinTateLimit_eq hπ hf]
      refine iSup_le fun n => ?_
      exact (lubinTateField_mono hπ hf n.le_succ).trans
        ((le_sup_left : _ ≤ towerSup hπ hf n).trans (le_iSup (towerSup hπ hf) n))
    · intro y hy
      obtain ⟨k, hk⟩ := exists_mem_unramifiedTower hy
      exact (le_iSup (towerSup hπ hf) k) ((le_sup_right : _ ≤ towerSup hπ hf k) hk)
  have := hle hx
  rw [← SetLike.mem_coe, IntermediateField.coe_iSup_of_directed
    (monotone_towerSup hπ hf).directed_le] at this
  simpa only [Set.mem_iUnion, SetLike.mem_coe] using this

def lubinTateMaxUnramifiedRestrict :
    (lubinTateMaxUnramified Ω hπ ≃ₐ[K] lubinTateMaxUnramified Ω hπ) →*
      (lubinTateLimit Ω hπ ≃ₐ[K] lubinTateLimit Ω hπ) ×
        (maximalUnramifiedExtension K Ω ≃ₐ[K] maximalUnramifiedExtension K Ω) :=
  (restrictAut le_sup_left).prod (restrictAut le_sup_right)

theorem lubinTateMaxUnramifiedRestrict_injective :
    Function.Injective (lubinTateMaxUnramifiedRestrict (Ω := Ω) hπ) := fun _ _ h =>
  algEquiv_ext_sup (congrArg Prod.fst h) (congrArg Prod.snd h)

theorem lubinTateMaxUnramifiedRestrict_surjective (hf : IsLubinTateSeries π f) :
    Function.Surjective (lubinTateMaxUnramifiedRestrict (Ω := Ω) hπ) := by
  rintro ⟨τ₁, τ₂⟩
  have hK : ∀ k, lubinTateField Ω hπ hf (k + 1) ≤ lubinTateLimit Ω hπ := fun k =>
    lubinTateField_le_lubinTateLimit hπ hf _
  have hE : ∀ k, unramifiedTower K Ω k ≤ maximalUnramifiedExtension K Ω :=
    unramifiedTower_le_maximalUnramifiedExtension
  have hσ := fun k => (bijective_restrictAut_prod hπ hf (Nat.succ_pos k)
    (isUnramifiedSubextension_unramifiedTower (K := K) (Ω := Ω) k)).2
      (restrictAut (hK k) τ₁, restrictAut (hE k) τ₂)
  choose σ hσ using hσ
  have hσ₁ : ∀ k, restrictAut le_sup_left (σ k) = restrictAut (hK k) τ₁ := fun k =>
    congrArg Prod.fst (hσ k)
  have hσ₂ : ∀ k, restrictAut le_sup_right (σ k) = restrictAut (hE k) τ₂ := fun k =>
    congrArg Prod.snd (hσ k)
  have hcompat : ∀ j k (h : j ≤ k), restrictAut (monotone_towerSup hπ hf h) (σ k) = σ j := by
    intro j k h
    apply algEquiv_ext_sup
    · rw [restrictAut_restrictAut, hσ₁ j,
        ← restrictAut_restrictAut (le_sup_left : _ ≤ towerSup hπ hf k)
          (lubinTateField_mono hπ hf (Nat.succ_le_succ h)),
        hσ₁ k, restrictAut_restrictAut]
    · rw [restrictAut_restrictAut, hσ₂ j,
        ← restrictAut_restrictAut (le_sup_right : _ ≤ towerSup hπ hf k)
          (monotone_unramifiedTower h), hσ₂ k, restrictAut_restrictAut]
  obtain ⟨ρ, hρ⟩ := exists_algEquiv_of_compatible (monotone_towerSup hπ hf) (towerSup_le hπ hf)
    (fun _ hx => exists_mem_towerSup hπ hf hx) σ hcompat
  refine ⟨ρ, Prod.ext ?_ ?_⟩
  · refine algEquiv_ext_of_restrictAut (F := fun k => lubinTateField Ω hπ hf (k + 1)) hK
      (fun x hx => ?_) fun k => ?_
    · obtain ⟨n, hn⟩ := (mem_lubinTateLimit_iff hπ hf).mp hx
      exact ⟨n, lubinTateField_mono hπ hf n.le_succ hn⟩
    · change restrictAut (hK k) (restrictAut le_sup_left ρ) = _
      rw [restrictAut_restrictAut,
        ← restrictAut_restrictAut (towerSup_le hπ hf k) (le_sup_left : _ ≤ towerSup hπ hf k),
        hρ k, hσ₁ k]
  · refine algEquiv_ext_of_restrictAut (F := unramifiedTower K Ω) hE
      (fun x hx => exists_mem_unramifiedTower hx) fun k => ?_
    change restrictAut (hE k) (restrictAut le_sup_right ρ) = _
    rw [restrictAut_restrictAut,
      ← restrictAut_restrictAut (towerSup_le hπ hf k) (le_sup_right : _ ≤ towerSup hπ hf k),
      hρ k, hσ₂ k]

variable [IsGalois K Ω]

def lubinTateMaxUnramifiedGalEquiv (hf : IsLubinTateSeries π f) :
    (lubinTateMaxUnramified Ω hπ ≃ₐ[K] lubinTateMaxUnramified Ω hπ) ≃ₜ*
      𝒪[K]ˣ × Multiplicative ℤ̂ :=
  let e := (MulEquiv.ofBijective (lubinTateMaxUnramifiedRestrict (Ω := Ω) hπ)
    ⟨lubinTateMaxUnramifiedRestrict_injective hπ, lubinTateMaxUnramifiedRestrict_surjective hπ hf⟩).trans
      (MulEquiv.prodCongr (lubinTateLimitGalEquiv hπ hf).symm.toMulEquiv
        (maximalUnramifiedExtensionGaloisEquiv K Ω).toMulEquiv)
  have hc : Continuous e :=
    (((lubinTateLimitGalEquiv hπ hf).symm.continuous.comp (continuous_restrictAut le_sup_left)).prodMk
      ((maximalUnramifiedExtensionGaloisEquiv K Ω).continuous.comp
        (continuous_restrictAut le_sup_right)))
  { e with
    continuous_toFun := hc
    continuous_invFun := (hc.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

end MaxUnramified

end FormalGroup

end GroundTheory.LocalField
