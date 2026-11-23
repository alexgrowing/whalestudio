import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActsExistsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForLocOps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoatomOfFiniteLength

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.Published
open scoped TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HoweNonsplit

open GlobalTheory.HoweAdelic

theorem unique_maximal : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.Published.HoweDualityUnitary → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
      ∀ N N', Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N → Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) N' → N = N' := by
  intro hP hHD F E _ _ _ _ _ σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hηX hηW hHX hHW hWeil v hv N N' hN hN'
  obtain ⟨om', hom'⟩ := GlobalTheory.LocOpsW.locRep F E σ n d X W M ψ χX χW om hψ hWeil v
  have hHDv := GlobalTheory.HoweNonsplit.howeDualityFor_locOps hP hHD F E σ hCM n d X W M ψ χX χW om hψ hX hXd hW hWd hηX hηW hHX hHW hWeil v hv om' hom'
  have hpres : ∀ x, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), om' x φ ∈ SB (Fin n × Fin d → Fv F v) :=
    fun x φ hφ => (hom' x.1 x.2 φ hφ).1
  have key : ∀ (g : UAtGrp σ X (evFin F v)) (h : UAtGrp σ W (evFin F v)) (φ : (Fin n × Fin d → Fv F v) → ℂ),
      φ ∈ SB (Fin n × Fin d → Fv F v) → ∀ φ₁, φ₁ ∈ SB (Fin n × Fin d → Fv F v) →
      Acts (evFin F v) (om (g.1, h.1)) φ φ₁ → φ₁ = om' (g, h) φ := fun g h φ hφ φ₁ _ hA =>
    GlobalTheory.TensUniq.eq_of_tens_eq v φ φ₁ _ hφ fun r hr => (hA r hr).symm.trans ((hom' g h φ hφ).2 r hr)
  have haug : augAt om v = locAug om' := by
    apply le_antisymm
    · rw [augAt, Submodule.span_le]
      rintro z ⟨g, hg, φ, hφ, φ₁, hφ₁, hA, rfl⟩
      have e := key ⟨g, hg⟩ 1 φ hφ φ₁ hφ₁ hA
      exact Submodule.subset_span ⟨⟨g, hg⟩, φ, hφ, by rw [e]⟩
    · rw [locAug, Submodule.span_le]
      rintro z ⟨g, φ, hφ, rfl⟩
      exact Submodule.subset_span ⟨g.1, g.2, φ, hφ, om' (g, 1) φ, (hom' g 1 φ hφ).1, (hom' g 1 φ hφ).2, rfl⟩
  have hiff : ∀ P, ThetaSub om v P ↔ IsLocSub om' P := by
    intro P
    rw [ThetaSub, IsLocSub, haug]
    refine and_congr_right fun _ => and_congr_right fun hle => ⟨fun hs h φ hφ => ?_, fun hs h hh φ hφ φ₁ hφ₁ hA => ?_⟩
    · exact hs h.1 h.2 φ hφ _ (hom' 1 h φ (hle hφ)).1 (hom' 1 h φ (hle hφ)).2
    · rw [key 1 ⟨h, hh⟩ φ (hle hφ) φ₁ hφ₁ hA]
      exact hs _ φ hφ
  have hM : ∀ P, Maximal (fun P => ThetaSub om v P ∧ P ≠ SB _) P →
      Maximal (fun P => IsLocSub om' P ∧ P ≠ SB (Fin n × Fin d → Fv F v)) P := by
    intro P hP'
    simpa only [hiff] using hP'
  replace hN := hM N hN
  replace hN' := hM N' hN'
  have hsup : IsLocSub om' (N ⊔ N') := isLocSub_sup hN.1.1 hN'.1.1
  have hne : N ⊔ N' ≠ SB (Fin n × Fin d → Fv F v) :=
    GlobalTheory.HoweAdelic.sup_ne_SB_of_howeDuality om' hHDv hpres N N' hN.1.1 hN'.1.1 hN.1.2 hN'.1.2
  have h1 : N ⊔ N' ≤ N := hN.2 ⟨hsup, hne⟩ le_sup_left
  have h2 : N ⊔ N' ≤ N' := hN'.2 ⟨hsup, hne⟩ le_sup_right
  exact le_antisymm (le_sup_left.trans h2) (le_sup_right.trans h1)

end GlobalTheory.HoweNonsplit

end
