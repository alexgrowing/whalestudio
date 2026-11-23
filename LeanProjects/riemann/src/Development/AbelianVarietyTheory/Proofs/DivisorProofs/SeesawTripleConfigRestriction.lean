import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSubmoduleSecondFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleSixthFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawTypeBTripleSeventhFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedSpanTranslateGeneratorsStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

namespace GlobalTheory.ConeLv1

theorem coneFin_ne_zero : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgB B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ K : Subgroup (UA σ G.V'.J), IsStab B K →
    ∀ (μKv : Measure (KAt K (evFin F B.v₁))) (μv : Measure (idelesAt E (evFin F B.v₁))),
    IsNormK K (evFin F B.v₁) μKv → IsNormE E B.v₁ μv →
    ∀ l : ((Fin b × Fin (a + b) → Fv F B.v₁) → ℂ) →ₗ[ℂ] ℂ,
    (∀ g ∈ UAt σ G₁.V' (evFin F B.v₁), ∀ ψ ∈ G₁.M'.SoLoc B.ψ B.τ₁, ∀ ψ' ∈ G₁.M'.SoLoc B.ψ B.τ₁,
      Acts (evFin F B.v₁) (om₁' (g, 1)) ψ ψ' → l ψ' = l ψ) →
    (∃ ψ ∈ G₁.M'.SoLoc B.ψ B.τ₁, l ψ ≠ 0) →
    ∃ φ ∈ G.M'.SoLoc B.ψ B.τ₁,
      coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ ∈ G₁.M'.SoLoc B.ψ B.τ₁ ∧
      l (coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) φ) ≠ 0 := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' ei ev hei hev hpure K hK μKv μv hμK hμ l hl hne
  set Λ := coneFin B G.M' om' B.v₁ (ev B.v₁) K μKv μv (shiftB σ H H') X.ν ((a - (b + 2)) / 2 + 1) with hΛ
  have hsupp : ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, Λ φ ∈ G₁.M'.SoLoc B.ψ B.τ₁ := fun φ hφ =>
    GlobalTheory.T.config_b_stabilizer_theta B G G₁ H H' hC e' he' K hK X om om' om₁ om₁' hT hT₁ ei ev hei hev hpure μKv μv hμK hμ φ hφ
  have hgood : X.Good B.v₁ := hT₁.chars.good
  have hroot := GlobalTheory.T.character_at_uniformizer_not_root_of_unity F E σ B a b G₁ X om₁ om₁' hT₁ B.v₁ hgood
  set N := Submodule.span ℂ (Λ '' G.M'.SoLoc B.ψ B.τ₁) ⊔ augAt om₁' B.v₁ with hN
  have haugSB : augAt om₁' B.v₁ ≤ SB _ := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨g, -, φ, hφ, φ₁, hφ₁, -, rfl⟩
    exact sub_mem hφ₁ hφ
  have hNSB : N ≤ SB _ := by
    refine sup_le (Submodule.span_le.2 ?_) haugSB
    rintro z ⟨φ, hφ, rfl⟩
    exact (hsupp φ hφ).1
  have hirr := GlobalTheory.T.augmentation_submodule_second_factor hKP.base F E σ B a b G₁ X om₁ om₁' hT₁ B.v₁ hgood hroot N le_sup_right hNSB
    (GlobalTheory.T.seesaw_type_b_triple_sixth_form hKP F E σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' ei ev hei hev hpure K hK μKv μv hμK hμ)
  have hNtop : N = SB _ := by
    rcases hirr with h | h
    · exfalso
      obtain ⟨φ, hφ, hn⟩ := GlobalTheory.T.seesaw_type_b_triple_seventh_form hKP F E σ B a b G G₁ H H' X om om' om₁ om₁' hC hT hT₁ e' he' ei ev hei hev hpure K hK μKv μv hμK hμ
      exact hn (h ▸ (le_sup_left : _ ≤ N) (Submodule.subset_span ⟨φ, hφ, rfl⟩))
    · exact h
  obtain ⟨ψ, hψ, hlψ⟩ := hne
  by_contra hall
  push_neg at hall
  have hkill : ∀ y ∈ Submodule.span ℂ (Λ '' G.M'.SoLoc B.ψ B.τ₁), l y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨φ, hφ, rfl⟩ := hx
      exact hall φ hφ (hsupp φ hφ)
    | zero => exact map_zero l
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hψN : ψ ∈ N := hNtop ▸ hψ.1
  obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 hψN
  have htspan : t ∈ Submodule.span ℂ (G₁.M'.SoLoc B.ψ B.τ₁) := by
    have : t = ψ - s := by rw [← hst]; abel
    rw [this]
    refine sub_mem (Submodule.subset_span hψ) ?_
    refine Submodule.span_mono ?_ hs
    rintro z ⟨φ, hφ, rfl⟩
    exact hsupp φ hφ
  have hkill2 : ∀ y ∈ Submodule.span ℂ {y | ∃ g ∈ UAt σ G₁.V' (evFin F B.v₁), ∃ ψ ∈ G₁.M'.SoLoc B.ψ B.τ₁,
      ∃ ψ' ∈ G₁.M'.SoLoc B.ψ B.τ₁, Acts (evFin F B.v₁) (om₁' (g, 1)) ψ ψ' ∧ y = ψ' - ψ}, l y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, ψ₀, hψ₀, ψ₁, hψ₁, hA, rfl⟩ := hx
      rw [map_sub, hl g hg ψ₀ hψ₀ ψ₁ hψ₁ hA, sub_self]
    | zero => exact map_zero l
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, hx, smul_zero]
  have hlt : l t = 0 := hkill2 t (GlobalTheory.T.augmented_span_translate_generators hKP F E σ B a b G₁ X om₁ om₁' hT₁ t ht htspan)
  apply hlψ
  rw [← hst, map_add, hkill s hs, hlt, add_zero]

end GlobalTheory.ConeLv1
