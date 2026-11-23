import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLiftDef
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftConst

namespace GlobalTheory.ThK.SplitInv

section Abstract

variable {H : Type} [Group H]

def rt (k : H) (φ : H → ℂ) : H → ℂ := fun g => φ (g * k)

theorem rt_rt (k k' : H) (φ : H → ℂ) : rt k (rt k' φ) = rt (k * k') φ := by
  funext g; simp only [rt, mul_assoc]

theorem rt_one (φ : H → ℂ) : rt 1 φ = φ := by
  funext g; simp only [rt, mul_one]

def RStable (G₀ : Subgroup H) (U : Submodule ℂ (H → ℂ)) : Prop := ∀ φ ∈ U, ∀ k ∈ G₀, rt k φ ∈ U

def fixIn (S : Submodule ℂ (H → ℂ)) (K : Subgroup H) : Submodule ℂ (H → ℂ) where
  carrier := {φ | φ ∈ S ∧ ∀ k ∈ K, rt k φ = φ}
  add_mem' := fun {φ ψ} hφ hψ => ⟨S.add_mem hφ.1 hψ.1, fun k hk => by
    show rt k φ + rt k ψ = φ + ψ
    rw [hφ.2 k hk, hψ.2 k hk]⟩
  zero_mem' := ⟨S.zero_mem, fun _ _ => rfl⟩
  smul_mem' := fun c φ hφ => ⟨S.smul_mem c hφ.1, fun k hk => by
    show c • rt k φ = c • φ
    rw [hφ.2 k hk]⟩

def SmAdm (G₀ : Subgroup H) (S : Submodule ℂ (H → ℂ)) (𝒦 : Set (Subgroup H)) : Prop :=
  (∀ K ∈ 𝒦, K ≤ G₀) ∧ (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ⊓ K' ∈ 𝒦 ∧ ((K ⊓ K').subgroupOf K).FiniteIndex) ∧
    (∀ φ ∈ S, ∃ K ∈ 𝒦, ∀ k ∈ K, rt k φ = φ) ∧ ∀ K ∈ 𝒦, FiniteDimensional ℂ (fixIn S K)

def Unitary (G₀ : Subgroup H) (S : Submodule ℂ (H → ℂ)) : Prop :=
  ∃ b : (H → ℂ) → (H → ℂ) → ℂ,
    (∀ φ ∈ S, ∀ ψ ∈ S, ∀ χ ∈ S, ∀ c : ℂ, b (c • φ + ψ) χ = c * b φ χ + b ψ χ) ∧
    (∀ φ ∈ S, ∀ ψ ∈ S, b φ ψ = starRingEnd ℂ (b ψ φ)) ∧
    (∀ φ ∈ S, φ ≠ 0 → 0 < (b φ φ).re) ∧
    ∀ φ ∈ S, ∀ ψ ∈ S, ∀ k ∈ G₀, b (rt k φ) (rt k ψ) = b φ ψ

def CompRed (G₀ : Subgroup H) (S : Submodule ℂ (H → ℂ)) : Prop :=
  ∀ C : Submodule ℂ (H → ℂ), C ≤ S → RStable G₀ C →
    ∃ C' : Submodule ℂ (H → ℂ), C' ≤ S ∧ RStable G₀ C' ∧ C ⊓ C' = ⊥ ∧ C ⊔ C' = S

def QuotTriv (G₀ : Subgroup H) (S : Submodule ℂ (H → ℂ)) : Prop :=
  ∀ N : Submodule ℂ (H → ℂ), N ≤ S → RStable G₀ N → N ≠ S →
    (∀ N' : Submodule ℂ (H → ℂ), RStable G₀ N' → N ≤ N' → N' ≤ S → N' = N ∨ N' = S) →
    ∀ φ ∈ S, ∀ k ∈ G₀, rt k φ - φ ∈ N

end Abstract

section Lift

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def datAt (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ) (v : Pl F) : Set ((Fin n × Fin d → AF F) → ℂ) :=
  {Ψ | ∃ k ∈ UAt σ X (evFin F v), ∃ h ∈ UAt σ W (evFin F v), ∃ Φ' : (Fin n × Fin d → AF F) → ℂ,
    (Φ' = Φ ∨ (Φ ≠ 0 ∧ ∃ (φ φ' : (Fin n × Fin d → Fv F v) → ℂ) (r : (Fin n × Fin d → AF F) → ℂ),
      Rest (evFin F v) φ r ∧ Φ = tens (evFin F v) φ r ∧ Rest (evFin F v) φ' r ∧ Φ' = tens (evFin F v) φ' r)) ∧
    Ψ = om (k, h) Φ'}

def funAt (f : UA σ W.J → ℂ) (v : Pl F) : Set (UA σ W.J → ℂ) :=
  {f' | ∃ h ∈ UAt σ W (evFin F v), f' = rt h f}

def liftSpace (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J))
    (f : UA σ W.J → ℂ) (v : Pl F) : Submodule ℂ (UA σ X.J → ℂ) :=
  Submodule.span ℂ {G | ∃ Ψ ∈ datAt om Φ v, ∃ f' ∈ funAt f v, G = thLift om Ψ μ 𝓕 f'}

theorem rStable_liftSpace (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ) (μ : Measure (UA σ W.J))
    (𝓕 : Set (UA σ W.J)) (f : UA σ W.J → ℂ) (v : Pl F) :
    RStable (UAtSub σ X (evFin F v)) (liftSpace om Φ μ 𝓕 f v) := by
  intro φ hφ k hk
  let L : (UA σ X.J → ℂ) →ₗ[ℂ] (UA σ X.J → ℂ) := LinearMap.funLeft ℂ ℂ (fun g => g * k)
  have hL : ∀ ψ, L ψ = rt k ψ := fun _ => rfl
  rw [← hL]
  refine (Submodule.span_le (p := (liftSpace om Φ μ 𝓕 f v).comap L)).2 ?_ hφ
  rintro _ ⟨Ψ, ⟨k₀, hk₀, h₀, hh₀, Φ', hΦ', rfl⟩, f', hf', rfl⟩
  refine Submodule.subset_span ⟨om (k * k₀, h₀) Φ', ⟨k * k₀, (UAtSub σ X (evFin F v)).mul_mem hk hk₀, h₀, hh₀, Φ', hΦ', rfl⟩,
    f', hf', ?_⟩
  have e : ∀ g h, om (g * k, h) (om (k₀, h₀) Φ') = om (g, h) (om (k * k₀, h₀) Φ') := by
    intro g h
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    ext1
    · exact mul_assoc _ _ _
    · rfl
  funext g
  simp only [hL, rt, thLift_def, theta, e]

theorem thLift_mem_liftSpace (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ) (μ : Measure (UA σ W.J))
    (𝓕 : Set (UA σ W.J)) (f : UA σ W.J → ℂ) (v : Pl F) : thLift om Φ μ 𝓕 f ∈ liftSpace om Φ μ 𝓕 f v := by
  refine Submodule.subset_span ⟨om (1, 1) Φ, ⟨1, (UAtSub σ X (evFin F v)).one_mem, 1, (UAtSub σ W (evFin F v)).one_mem, Φ,
    Or.inl rfl, rfl⟩, rt 1 f, ⟨1, (UAtSub σ W (evFin F v)).one_mem, rfl⟩, ?_⟩
  rw [rt_one, show ((1 : UA σ X.J), (1 : UA σ W.J)) = 1 from rfl, map_one, Module.End.one_apply]

end Lift

end GlobalTheory.ThK.SplitInv

end
