import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

def act {R κ : Type} [CommRing R] [Fintype κ] (a : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) : (κ → R) × (κ → R) :=
  ((a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl, (a *ᵥ Sum.elim w.1 w.2) ∘ Sum.inr)

theorem act_mul {R κ : Type} [CommRing R] [Fintype κ] (a b : Matrix (κ ⊕ κ) (κ ⊕ κ) R) (w : (κ → R) × (κ → R)) :
    act (a * b) w = act a (act b w) := by
  simp only [act, Matrix.mulVec_mulVec, Sum.elim_comp_inl_inr]

theorem act_fromBlocks {R κ : Type} [CommRing R] [Fintype κ] (A B C D : Matrix κ κ R) (w : (κ → R) × (κ → R)) :
    act (Matrix.fromBlocks A B C D) w = (A *ᵥ w.1 + B *ᵥ w.2, C *ᵥ w.1 + D *ᵥ w.2) := by
  simp only [act, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]

variable {F : Type} [Field F] [NumberField F]

def ind (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

def IsFam {κ : Type} (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) : Prop :=
  (∀ v, φ v ∈ SB (κ → Fv F v)) ∧ ∀ᶠ v in cofinite, φ v = ind κ v

def IsOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ) (c : ℂ) (ei : SInf F κ →L[ℂ] SInf F κ)
    (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ) : Prop :=
  c ≠ 0 ∧ Function.Surjective ei ∧
  (∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _)) ∧
  (∀ v (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), ev v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) =
    schr (GlobalTheory.LatVac.psiAt ψ v) (act (a.map (algebraMap F (Fv F v))) w) (ev v φ)) ∧
  (∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v) ∧
  ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
    e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) (fun v => ev v (φ v)) ∧
    (∀ w : (κ → AF F) × (κ → AF F), e (schr ψ w (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      schr ψ (act (a.map (algebraMap F (AF F))) w) (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ))) ∧
    thetaSum F (e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = c * thetaSum F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)

def HasOp {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) : Prop :=
  ∃ e c ei ev, IsOp ψ a e c ei ev

theorem IsOp.isFam {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e c ei ev}
    (h : IsOp ψ a e c ei ev) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : IsFam fun v => ev v (φ v) := by
  obtain ⟨-, -, hbij, -, hind, -⟩ := h
  refine ⟨fun v => (hbij v).mapsTo (hφ.1 v), ?_⟩
  filter_upwards [hφ.2, hind] with v h1 h2
  rw [h1, h2]

theorem HasOp.mul {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ} {a b : Matrix (κ ⊕ κ) (κ ⊕ κ) F}
    (ha : HasOp ψ a) (hb : HasOp ψ b) : HasOp ψ (a * b) := by
  obtain ⟨e₁, c₁, ei₁, ev₁, h₁⟩ := ha
  obtain ⟨e₂, c₂, ei₂, ev₂, h₂⟩ := hb
  have h₂' := h₂
  obtain ⟨hc₁, hs₁, hb₁, hw₁, hi₁, hp₁⟩ := h₁
  obtain ⟨hc₂, hs₂, hb₂, hw₂, hi₂, hp₂⟩ := h₂
  refine ⟨e₁ ∘ₗ e₂, c₁ * c₂, ei₁.comp ei₂, fun v => ev₁ v ∘ₗ ev₂ v, mul_ne_zero hc₁ hc₂, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs₁.comp hs₂
  · intro v
    exact (hb₁ v).comp (hb₂ v)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hw₂ v w φ hφ, hw₁ v _ _ ((hb₂ v).mapsTo hφ), Matrix.map_mul, act_mul]
  · filter_upwards [hi₁, hi₂] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ
    have hφ' : IsFam fun v => ev₂ v (φ v) := IsOp.isFam h₂' hφ
    obtain ⟨hq₂, hw₂', ht₂⟩ := hp₂ f φ hφ
    obtain ⟨hq₁, hw₁', ht₁⟩ := hp₁ (ei₂ f) (fun v => ev₂ v (φ v)) hφ'
    refine ⟨?_, ?_, ?_⟩
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply, hq₂, hq₁]
    · intro w
      simp only [LinearMap.comp_apply]
      rw [hw₂' w, hq₂, hw₁' _, Matrix.map_mul, act_mul]
    · simp only [LinearMap.comp_apply]
      rw [hq₂, ht₁, ← hq₂, ht₂, mul_assoc]

theorem hasOp_one {κ : Type} [Fintype κ] [DecidableEq κ] (ψ : AddChar (AF F) ℂ) : HasOp ψ (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) := by
  have h1 : ∀ {R : Type} [CommRing R] (w : (κ → R) × (κ → R)), act (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) R) w = w := by
    intro R _ w
    simp only [act, Matrix.one_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr]
  refine ⟨LinearMap.id, 1, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, one_ne_zero,
    Function.surjective_id, fun v => Set.bijOn_id _, ?_, ?_, ?_⟩
  · intro v w φ _
    simp only [LinearMap.id_apply, Matrix.map_one _ (map_zero _) (map_one _), h1]
  · exact Filter.Eventually.of_forall fun v => rfl
  · intro f φ _
    refine ⟨rfl, fun w => ?_, by simp⟩
    simp only [LinearMap.id_apply, Matrix.map_one _ (map_zero _) (map_one _), h1]

end GlobalTheory.RatWeilOp

end
