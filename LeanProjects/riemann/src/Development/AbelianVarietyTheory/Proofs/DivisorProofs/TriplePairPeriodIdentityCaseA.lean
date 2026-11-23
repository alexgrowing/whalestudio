import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtension
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical

noncomputable section

namespace GlobalTheory.ThK.HeisInvInf

variable {F : Type} [Field F] [NumberField F]

theorem pure_sub_arch {κ : Type} [Fintype κ] (f f' : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f - f') φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ := by
  funext x
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.sub_apply, Pi.sub_apply, sub_mul]

theorem arch_eq_of_pure_eq {κ : Type} [Fintype κ] {f f' : SInf F κ} {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ}
    (h0 : ∀ v, φ v ≠ 0) (hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f' φ) : f = f' := by
  by_contra hne
  exact GlobalTheory.ThK.EvNeZero.pure_ne_zero (f - f') (sub_ne_zero.2 hne) φ h0 hstd (by rw [pure_sub_arch, h, sub_self])

end GlobalTheory.ThK.HeisInvInf

open GlobalTheory.ThK.HeisInvInf GlobalTheory.ThK.EvUniqInf in

theorem GlobalTheory.ThK.HeisInvInf.ei_schr_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a'))
    (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
    CfgA B G G₁ H H' → IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (ei : SInf F (Fin (b + 2) × Fin (b + 2 + a')) →L[ℂ] SInf F (Fin b × Fin (b + a')))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (b + 2 + a') → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (b + a') → Fv F v) → ℂ),
      (∀ v, ev v (G.M.vac v) = G₁.M.vac v ∧ (SB _).map (ev v) = SB _) →
      (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) →
    ∀ (y : Fin (b + 2) → AE F E) (f g : SInf F (Fin (b + 2) × Fin (b + 2 + a'))),
      ⇑g = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F (Fin (b + 2) × Fin (b + 2 + a')))
        (GlobalTheory.ArchUniq.Coord.coordI G.M (Matrix.vecMulVec y (incV F H'.x))) ⇑f → ei g = ei f := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' X om om' om₁ om₁' _ hT hT₁ e he ei ev hev hpure y f g hg
  have hM := hT.geo.hM
  have hM₁ := hT₁.geo.hM
  set u := Matrix.vecMulVec y (incV F H'.x) with hu
  have hmem : partInf F u ∈ isoA H H' := Or.inl ⟨realAd F 1 • y, by
    show realAd F 1 • Matrix.vecMulVec y (incV F H'.x) = _
    rw [Matrix.smul_vecMulVec]⟩
  have hR := rest_pure f G.M.vac (fun v => (hM.vac v).1) hM.std
  have hΦ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f G.M.vac ∈ schA F _ := hR.2
  obtain ⟨hA, hloc⟩ := locOpInf_rho G.M.co hT.base.std u f
  have hgl : locOpInf (G.M.co.rho B.ψ (partInf F u)) f = g := DFunLike.coe_injective (by rw [hloc, hg]; rfl)
  have e1 : G.M.co.rho B.ψ (partInf F u) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f G.M.vac) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g G.M.vac := by
    have h := hA _ hR
    rw [hgl] at h
    exact h
  have h1 := he.inv _ hmem _ hΦ
  rw [e1, hpure g G.M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl),
    hpure f G.M.vac (fun v => (hM.vac v).1) (Eventually.of_forall fun _ => rfl)] at h1
  have hvac : (fun v => ev v (G.M.vac v)) = G₁.M.vac := funext fun v => (hev v).1
  rw [hvac] at h1
  exact arch_eq_of_pure_eq (fun v => (hM₁.vac v).2.1) hM₁.std h1

end
