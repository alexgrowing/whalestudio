import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFullRankModuloTranslates
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantFormZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormFullRankBruhatVanishesStatement
open scoped Matrix
open GlobalTheory.WeilM GlobalTheory.FullRankCoinv

noncomputable section

namespace GlobalTheory.SBFormInv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lact_eq_omB {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ) :
    lact ν g Ψ = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ := by
  funext Y
  simp [lact, GlobalTheory.SplitFlip.omB]

theorem lact_mem_SB {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (h : Ψ ∈ SB (Matrix (Fin n) (Fin d) k)) : lact ν g Ψ ∈ SB (Matrix (Fin n) (Fin d) k) := by
  rw [lact_eq_omB]; exact GlobalTheory.SplitFlip.omB_mem_SB ν ν g 1 h

def lactL {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) :
    SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] SB (Matrix (Fin n) (Fin d) k) where
  toFun Ψ := ⟨lact ν g Ψ.1, lact_mem_SB ν g Ψ.2⟩
  map_add' _ _ := Subtype.ext (funext fun Y => by simp [lact, mul_add])
  map_smul' c _ := Subtype.ext (funext fun Y => by simp [lact]; ring)

theorem fullRk_le {n d : ℕ} : fullRk k n d ≤ SB (Matrix (Fin n) (Fin d) k) := fun _ h => h.1

theorem lact_mem_fullRk {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (h : Ψ ∈ fullRk k n d) : lact ν g Ψ ∈ fullRk k n d := by
  refine ⟨lact_mem_SB ν g h.1, fun Y hY => ?_⟩
  have hu : IsUnit (g.1ᵀ).det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  simp only [lact]
  rw [h.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]), mul_zero]

theorem form_lact_right : GlobalTheory.ThK.KP → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ) (ϖ : kˣ), n < d → GlobalTheory.SplitFlip.IsUnif ϖ → GlobalTheory.SmGL.IsSmoothChar ν → GlobalTheory.SmGL.IsUnitaryChar ν → (∀ m : ℕ, 0 < m → ∀ r : ℝ, ((ν ϖ : ℂ)) ^ m ≠ (r : ℂ)) →
    ∀ Bf : SB (Matrix (Fin n) (Fin d) k) →ₗ[ℂ] SB (Matrix (Fin n) (Fin d) k) →ₗ⋆[ℂ] ℂ,
      (∀ (g : GL (Fin n) k) (Ψ₁ Ψ₁' : SB (Matrix (Fin n) (Fin d) k)) (Ψ₂ : SB (Matrix (Fin n) (Fin d) k)), Ψ₁'.1 = lact ν g Ψ₁.1 → Bf Ψ₁' Ψ₂ = Bf Ψ₁ Ψ₂) →
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ (Ψ₁ Ψ₁' : SB (Matrix (Fin n) (Fin d) k)) (Ψ₂ Ψ₂' : SB (Matrix (Fin n) (Fin d) k)),
        Ψ₁'.1 = (fun Y => Ψ₁.1 (Y * h.1)) → Ψ₂'.1 = (fun Y => Ψ₂.1 (Y * h.1)) → (m : ℂ) * Bf Ψ₁' Ψ₂' = Bf Ψ₁ Ψ₂) →
      ∀ (g : GL (Fin n) k) (Ψ₁ Ψ₂ Ψ₂' : SB (Matrix (Fin n) (Fin d) k)), Ψ₂'.1 = lact ν g Ψ₂.1 → Bf Ψ₁ Ψ₂' = Bf Ψ₁ Ψ₂ := by
  intro hK k _ _ _ _ n d ν ϖ hnd hϖ hs hu hν Bf hA hQ g Ψ₁ Ψ₂ Ψ₂' e
  have hne : ν ≠ 1 := fun h => hν 1 one_pos 1 (by simp [h])
  let inc : fullRk k n d →ₗ[ℂ] SB (Matrix (Fin n) (Fin d) k) := Submodule.inclusion fullRk_le
  have hfull := GlobalTheory.T.full_rank_coinvariant_form_zero hK k n d ν hnd hs hu hne ((Bf.comp inc).compl₂ inc)
    (fun g Ψ₁ Ψ₁' Ψ₂ h => hA g (inc Ψ₁) (inc Ψ₁') (inc Ψ₂) h)
    (fun h => (hQ h).imp fun m hm => ⟨hm.1, fun Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2 => hm.2 (inc Ψ₁) (inc Ψ₁') (inc Ψ₂) (inc Ψ₂') h1 h2⟩)
  let D : fullRk k n d →ₗ[ℂ] SB (Matrix (Fin n) (Fin d) k) →ₗ⋆[ℂ] ℂ := (Bf.comp inc).compl₂ (lactL ν g - LinearMap.id)
  have hD : ∀ Ψ₁ Ψ₂, D Ψ₁ Ψ₂ = Bf (inc Ψ₁) (lactL ν g Ψ₂) - Bf (inc Ψ₁) Ψ₂ := fun Ψ₁ Ψ₂ => by
    simp [D]
  have hD0 := GlobalTheory.T.invariant_form_full_rank_bruhat_vanishes hK k n n d ν ϖ hnd hs hu hν D
    (fun g' Ψ₁ Ψ₁' Ψ₂ h => by rw [hD, hD, hA g' (inc Ψ₁) (inc Ψ₁') _ h, hA g' (inc Ψ₁) (inc Ψ₁') _ h])
    (fun h => (hQ h).imp fun m hm => ⟨hm.1, fun Ψ₁ Ψ₁' Ψ₂ Ψ₂' h1 h2 => by
      rw [hD, hD, mul_sub, hm.2 (inc Ψ₁) (inc Ψ₁') Ψ₂ Ψ₂' h1 h2, hm.2 (inc Ψ₁) (inc Ψ₁') (lactL ν g Ψ₂) (lactL ν g Ψ₂') h1 (by
        funext Y
        simp only [lactL, LinearMap.coe_mk, AddHom.coe_mk, lact, h2, Matrix.mul_assoc])]⟩)
    (fun Ψ₁ Ψ₂ h0 => by
      have hm : Ψ₂.1 ∈ fullRk k n d := ⟨Ψ₂.2, fun Y hY => h0 Y (lt_of_le_of_ne (by simpa using Matrix.rank_le_card_height Y) hY)⟩
      rw [hD, sub_eq_zero]
      exact hfull g Ψ₁ ⟨_, hm⟩ ⟨_, lact_mem_fullRk ν g hm⟩ rfl)
  obtain ⟨Ψ₀, h1, h2, h3⟩ := GlobalTheory.RankStrata.exists_fullRank_sub_mem_span k n d ν ϖ hϖ hν Ψ₁.1 Ψ₁.2
  have hker : ∀ Z ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k),
      Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'}, ∃ hZ : Z ∈ SB (Matrix (Fin n) (Fin d) k), Bf ⟨Z, hZ⟩ = 0 := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g', Ψ', hΨ', rfl⟩ := hZ
      rw [← lact_eq_omB]
      refine ⟨Submodule.sub_mem _ (lact_mem_SB ν g' hΨ') hΨ', ?_⟩
      ext Ψ
      have := hA g' ⟨Ψ', hΨ'⟩ (lactL ν g' ⟨Ψ', hΨ'⟩) Ψ rfl
      rw [← sub_eq_zero, ← LinearMap.sub_apply, ← map_sub] at this
      exact this
    | zero => exact ⟨Submodule.zero_mem _, map_zero Bf⟩
    | add x y _ _ hx hy =>
      obtain ⟨hx, ex⟩ := hx
      obtain ⟨hy, ey⟩ := hy
      refine ⟨Submodule.add_mem _ hx hy, ?_⟩
      have := map_add Bf ⟨x, hx⟩ ⟨y, hy⟩
      rw [ex, ey, add_zero] at this
      exact this
    | smul c x _ hx =>
      obtain ⟨hx, ex⟩ := hx
      refine ⟨Submodule.smul_mem _ c hx, ?_⟩
      have := map_smul Bf c ⟨x, hx⟩
      rw [ex, smul_zero] at this
      exact this
  obtain ⟨hZ, eZ⟩ := hker _ h3
  have e1 : Bf Ψ₁ = Bf (inc ⟨Ψ₀, h1, h2⟩) := by
    rw [← sub_eq_zero, ← map_sub]; exact eZ
  have e2 : Ψ₂' = lactL ν g Ψ₂ := Subtype.ext e
  rw [e1, e2, ← sub_eq_zero, ← hD]
  exact hD0 _ _

end GlobalTheory.SBFormInv
