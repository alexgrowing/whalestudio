import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearBarModelTripleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenRelationContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleCompatibilityAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankInsertLeAddTwoStatement
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

namespace GlobalTheory.ConeSoB

theorem ev_shift_vanish_off_rank : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E) {a b : ℕ}
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (e' : Fn F (b + 2) (a + (b + 2)) →ₗ[ℂ] Fn F b (a + b)), IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
    ei ≠ 0 → (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) →
    (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) → e' (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∃ ι₁ : ((Fin b × Fin (a + b) → Fv F B.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁) → ℂ),
      G₁.M'.IsLinBar B.ψ B.τ₁ 1 1 ι₁ ∧ ∀ φ ∈ G.M'.SoLoc B.ψ B.τ₁, ∀ l : (AE F E)ˣ, ∀ Y : Matrix (Fin b) (Fin (a + b)) (Fv F B.v₁),
        Y.rank ≠ b → ι₁ (ev B.v₁ (locOp B.v₁ (G.M'.co.rho B.ψ (partFin B.v₁ (shiftB σ H H' l))) φ)) Y = 0 := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he X om om' om₁ om₁' hT hT₁ ei ev hei hvm hloc
  obtain ⟨ι₁, hι₁⟩ := GlobalTheory.T.exists_linear_bar_model_triple B G₁ X om₁ om₁' hT₁
  refine ⟨ι₁, hι₁, ?_⟩
  rintro φ ⟨hφ, ι, hι, hsupp⟩ l Y hY
  have hψ : Continuous B.ψ := hT.base.std.1
  have hSB : ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁), ev B.v₁ φ ∈ SB (Fin b × Fin (a + b) → Fv F B.v₁) :=
    fun φ hφ => (hvm B.v₁).2 ▸ Submodule.mem_map_of_mem hφ
  have hheis : ∀ z : Matrix (Fin b) (Fin (a + b)) (AE F E), At (evFin F B.v₁) z → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      ev B.v₁ (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (incM F H.ι * z * (incM F H'.ι)ᵀ)) φ) =
        schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G₁.M'.co B.v₁ z) (ev B.v₁ φ) := fun z hz φ hφ =>
    GlobalTheory.T.eigen_relation_continuous B G.M' G₁.M' H.ι H'.ι _ e' he hψ hT.geo.hM' hT₁.geo.hM' ei ev hei hvm hloc B.v₁ z hz φ hφ
  have hinv : ∀ u ∈ isoB H H', At (evFin F B.v₁) u → ∀ φ ∈ SB (Fin (b + 2) × Fin (a + (b + 2)) → Fv F B.v₁),
      ev B.v₁ (schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ u) φ) = ev B.v₁ φ := fun u hu hu' φ hφ =>
    GlobalTheory.ThK.EvLocInv.ev_schr_of_mem B G.M' G₁.M' H.ι H'.ι _ e' he hψ hT.geo.hM' hT₁.geo.hM' ei ev hei hvm hloc B.v₁ u hu hu' φ hφ
  obtain ⟨P, Q, A, A', g, x, hf⟩ := GlobalTheory.T.config_b_triple_compatibility_alt B G G₁ H H' hC X om om' om₁ om₁' hT hT₁ (ev B.v₁) hSB hheis hinv ι ι₁ hι hι₁ φ hφ l
  rw [hf Y]
  have hlt : Y.rank < b := lt_of_le_of_ne (Y.rank_le_card_height.trans (by simp)) hY
  have h0 : ∀ r c, ι φ (P * insS (A * Y * A') r c x * Q) = 0 := fun r c => by
    apply hsupp
    have h2 : (A * Y * A').rank ≤ Y.rank := (Matrix.rank_mul_le_left (A * Y) A').trans (Matrix.rank_mul_le_right A Y)
    have h1 : (P * insS (A * Y * A') r c x * Q).rank ≤ (insS (A * Y * A') r c x).rank :=
      (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
    have h3 := GlobalTheory.T.rank_insert_le_add_two (A * Y * A') r c x
    omega
  simp [h0]

end GlobalTheory.ConeSoB
