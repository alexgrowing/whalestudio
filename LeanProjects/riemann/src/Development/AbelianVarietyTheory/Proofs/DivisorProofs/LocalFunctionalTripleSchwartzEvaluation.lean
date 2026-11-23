import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelHeisenbergOperatorsTranslationCharStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruhStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupVStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogAbsEEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagFirstApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptQ
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped GlobalTheory.VacAny

namespace GlobalTheory.SoLocVanish

theorem soLoc_vanish : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v) (ι₀ : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a') ) (Fv F v) → ℂ)), G.M'.IsLinBar B.ψ t 1 1 ι₀ →
  ∀ φ ∈ G.M'.SoLoc B.ψ t, ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F v), Y.rank ≠ a' → ι₀ φ Y = 0 := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t ι hι φ hφSo Y hY
  have hcm : IsCMExt F E σ := hT.base.cm
  let B' : Base F E := { B with v₁ := v, τ₁ := t }
  have hT' : IsTriple B' G X om om' :=
    { base := { hT.base with }
      geo := { hT.geo with hV := { hT.geo.hV with }, hV' := { hT.geo.hV' with }, hW := { hT.geo.hW with } }
      chars := { hT.chars with good := hv }
      weil := hT.weil
      weil' := hT.weil' }
  have hι' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι := hι
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit (G.V'.J.map t).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J t (B.emb w).1 1 one_ne_zero (G.V'.θ w)
      (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have herm : ∀ i j, σ (G.V'.J j i) = algebraMap F E 1 * G.V'.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV'.herm i j
  let K := GlobalTheory.SplitUnitLift.liftU hcm t G.V'.J 1 herm hdet
  have hK : ∀ g, K g ∈ UAt σ G.V' (evFin F B'.v₁) ∧ (mat (K g)).map (piW B'.τ₁) = g.val ∧
      (mat (K g)).map (piW (B'.τ₁.comp σ)) = (G.V'.J.map B'.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map B'.τ₁ :=
    fun g => ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm t G.V' 1 herm hdet g, GlobalTheory.SplitUnitLift.liftU_piW hcm t G.V'.J 1 herm hdet g,
      GlobalTheory.SplitUnitLift.liftU_piW_comp hcm t G.V'.J 1 herm hdet g⟩
  choose S hS using fun g => GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hT v (K g) (hK g).1
  have h1 : ∀ g, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), S g φ ∈ SB _ := fun g φ hφ => (hS g φ hφ).1
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ →
      At (evFin F v) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have restS : ∀ g φ r, φ ∈ SB (Fin a' × Fin (a + a') → Fv F v) → Rest (evFin F v) φ r → Rest (evFin F v) (S g φ) r :=
    fun g φ r hφ hr => ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F v) γ → ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v)
            (GlobalTheory.LatVac.locCo G.M'.co v (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v (GlobalTheory.LatVac.locCo G.M'.co v γ) φ hφ
    refine GlobalTheory.T.eq_of_componentTensorAdelicFunction_eq v φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v γ hγ φ r hr
    have hRw : Rest (evFin F v) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo G.M'.co v γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.T.weil_representation_preserves_schwartz G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.T.adelicHeisenberg_acts_by_local_schrodinger G.M'.co B.ψ v _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.T.linearModel_heisenbergOperators_translation_char B' G X om om' hT' K hK S h1 h4
  obtain ⟨hTι, hMι, -, -⟩ := hA ι hι'
  obtain ⟨hφ, ι₂, hι₂, hvan⟩ := hφSo
  have hι₂' : G.M'.IsLinBar B'.ψ B'.τ₁ 1 1 ι₂ := hι₂
  obtain ⟨hT₂, hM₂, -, -⟩ := hA ι₂ hι₂'
  obtain ⟨c, hc⟩ := GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin a' × Fin (a + a') → Fv F v)) (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) hψc hψ1 ι₂ ι
    hι₂.bij (fun x _ y _ c => by rw [map_add, map_smul])
    (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wT C))
    (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B'.ψ B'.v₁) (wM l))
    (fun C x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hT₂ C x hx, hTι C x hx⟩)
    (fun l x hx => ⟨GlobalTheory.T.schrodinger_preserves_schwartz_bruhat B.ψ hT.base.std.1 v _ x hx, hM₂ l x hx, hMι l x hx⟩)
  rw [hc φ hφ, Pi.smul_apply, hvan Y hY, smul_zero]

end GlobalTheory.SoLocVanish
