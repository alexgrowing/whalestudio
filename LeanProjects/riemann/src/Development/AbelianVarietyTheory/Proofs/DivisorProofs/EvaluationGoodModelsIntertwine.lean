import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.EvTame

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

def HasTameExp {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ))
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι)
    (P : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
    (g' : ι → (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), (∀ j, g' j ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, T (pureA F f g) = ∑ j, pureA F (P j f) (g' j)

theorem pureA_zero {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    pureA F f (0 : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) = 0 := by
  funext x; simp [pureA]

theorem pureA_add {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g₁ g₂ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f (g₁ + g₂) = pureA F f g₁ + pureA F f g₂ := by
  funext x; simp [pureA, mul_add]

theorem pureA_smul {κ : Type} (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (c : ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) : pureA F f (c • g) = c • pureA F f g := by
  funext x; simp only [pureA, Pi.smul_apply, smul_eq_mul]; ring

theorem hasTameExp_zero {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) :
    HasTameExp T 0 :=
  ⟨Empty, inferInstance, fun j => j.elim, fun j => j.elim, fun j => j.elim, fun f => by
    rw [pureA_zero, map_zero]; simp⟩

theorem HasTameExp.add {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    {g₁ g₂ : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (h₁ : HasTameExp T g₁) (h₂ : HasTameExp T g₂) :
    HasTameExp T (g₁ + g₂) := by
  obtain ⟨ι₁, _, P₁, k₁, hk₁, e₁⟩ := h₁
  obtain ⟨ι₂, _, P₂, k₂, hk₂, e₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim P₁ P₂, Sum.elim k₁ k₂, ?_, fun f => ?_⟩
  · rintro (j | j)
    · exact hk₁ j
    · exact hk₂ j
  · rw [pureA_add, map_add, e₁, e₂, Fintype.sum_sum_type]
    rfl

theorem HasTameExp.smul {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (c : ℂ) (h : HasTameExp T g) : HasTameExp T (c • g) := by
  obtain ⟨ι, _, P, k, hk, e⟩ := h
  refine ⟨ι, inferInstance, P, fun j => c • k j, fun j => Submodule.smul_mem _ c (hk j), fun f => ?_⟩
  rw [pureA_smul, map_smul, e, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => (pureA_smul _ c _).symm

theorem pure_eq_pureA {κ : Type} [Fintype κ] (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    pure f φ = pureA F f (fun y : κ → FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, φ v fun i => evalV F v (y i)) := rfl

end GlobalTheory.EvTame

namespace GlobalTheory.EvTame

open scoped Classical

theorem isTame_of_isEv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E)
    (I : Set (Matrix (Fin n) (Fin d) (AE F E))) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁),
    M.IsGood B.ψ → M₁.IsGood B.ψ → IsEv B M M₁ ι ι' I e → IsTame F e := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ ι ι' I e hM hM₁ hE g hg
  obtain ⟨ei, ev, -, hev, hloc⟩ := hE.loc
  have hs := GlobalTheory.SBSpan.mem_span_restrictedProd F (Fin n × Fin d) g hg
  clear hg
  change HasTameExp e g
  induction hs using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, hφ, hcof, rfl⟩ := hx
    have hvac : ∀ᶠ v in cofinite, φ v = M.vac v := by
      filter_upwards [hcof, hM.std] with v h1 h2
      rw [h1, h2]
    have hSB : ∀ v, ev v (φ v) ∈ SB (Fin n₁ × Fin d₁ → Fv F v) := fun v =>
      (hev v).2 ▸ Submodule.mem_map_of_mem (hφ v)
    have hcof' : ∀ᶠ v in cofinite,
        ev v (φ v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
      filter_upwards [hvac, hM₁.std] with v h1 h2
      rw [h1, (hev v).1, h2]
    refine ⟨Unit, inferInstance, fun _ => ei,
      fun _ y => ∏ᶠ v, ev v (φ v) fun i => evalV F v (y i),
      fun _ => GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ (fun v => ev v (φ v)) hSB hcof', fun f => ?_⟩
    rw [← pure_eq_pureA, hloc f φ hφ hvac, pure_eq_pureA, Fintype.sum_unique]
  | zero => exact hasTameExp_zero e
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.EvTame
