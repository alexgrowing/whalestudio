import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

open GlobalTheory.FlipMatch

namespace GlobalTheory.SwapHeis

theorem heis_sliceT : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 → G.W.J.det ≠ 0 →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v)
    (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
    ∀ (u₁ u₂ : Matrix (Fin (a + a')) (Fin a') (AE F E)), At (evFin F v) u₁ → At (evFin F v) u₂ →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ) = 0 →
    GlobalTheory.FlipMatch.pairM (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ) (GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) = 0 →
    ∀ Φ ∈ SB ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v),
    ∀ Z : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Φ) Z =
        GlobalTheory.LatVac.psiAt B.ψ v (-GlobalTheory.FlipMatch.pairM Z.1 (GlobalTheory.FlipMatch.coX t 1 1 u₁ᵀ) +
                     GlobalTheory.FlipMatch.pairM Z.2 (GlobalTheory.FlipMatch.coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι Φ (Z.1 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₁ᵀ,
            Z.2 + GlobalTheory.FlipMatch.coY σ G.V' G.W t 1 1 u₂ᵀ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT hdV hdW v t ι hι d' hd' dd hdd u₁ u₂ hu₁ hu₂ hp₁ hp₂ Φ hΦ Z
  set ψv := GlobalTheory.LatVac.psiAt B.ψ v with hψv
  have hc : Continuous ψv := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 v
  have hstar : ∀ y, starRingEnd ℂ (ψv y) = ψv (-y) := fun y => GlobalTheory.DblVacLine.star_psiAt B.ψ hT.base.std.1 v y
  have hatT : ∀ u : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) u → At (evFin F v) uᵀ :=
    fun u hu r hr => by rw [← Matrix.transpose_smul, hu r hr, Matrix.transpose_zero]
  have Heisenberg₂ : ∀ u : Matrix (Fin (a + a')) (Fin a') (AE F E), At (evFin F v) u →
      pairM (coX t 1 1 uᵀ) (coY σ G.V' G.W t 1 1 uᵀ) = 0 →
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ Y,
        ι (schr ψv (GlobalTheory.LatVac.locCo G.M'.co v uᵀ) φ) Y =
          ψv (-pairM Y (coX t 1 1 uᵀ)) * ι φ (Y + coY σ G.V' G.W t 1 1 uᵀ) := by
    intro u hu hp φ hφ Y
    exact (GlobalTheory.HeisFlip.heis_trans_char hT.base.cm G.V' G.W hT.geo.hV'.herm hT.geo.hW.skew hdV hdW G.M' B.ψ
      hT.base.std t 1 1 uᵀ (hatT u hu) hp φ hφ _ (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 v _ φ hφ)
      (GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ v uᵀ (hatT u hu) φ)).2 ι hι Y
  have hloc : GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂) =
      (Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).1 (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).1,
        Sum.elim (GlobalTheory.LatVac.locCo G.M'.co v u₁ᵀ).2 (-(GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ).2)) := by
    have e1 := hd' u₁ᵀ
    have e2 := hd' u₂ᵀ
    rw [Matrix.transpose_transpose] at e1 e2
    have h := hdd u₁ u₂
    ext k <;> cases k <;> simp [GlobalTheory.LatVac.locCo, h, e1, e2]
  have hconjSB : ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), (fun x => starRingEnd ℂ (φ x)) ∈ SB _ :=
    fun φ hφ => ⟨hφ.1.comp _, hφ.2.comp_left (map_zero _)⟩
  have hconj : ∀ (w : (Fin a' × Fin (a + a') → Fv F v) × (Fin a' × Fin (a + a') → Fv F v))
      (φ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      (fun x => starRingEnd ℂ (schr ψv (w.1, -w.2) φ x)) = schr ψv w (fun x => starRingEnd ℂ (φ x)) := by
    intro w φ
    funext x
    simp only [GlobalTheory.WeilM.schr, map_mul, hstar]
    congr 2
    rw [dotProduct_neg, dotProduct_neg]
    ring
  have hbox : ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₂ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) (boxFun φ₁ φ₂)) Z =
        ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ)) *
          GlobalTheory.SwapSlice.sliceT ι (boxFun φ₁ φ₂) (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ) := by
    intro φ₁ h₁ φ₂ h₂
    rw [hloc, GlobalTheory.BoxSpan.schr_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun, GlobalTheory.SwapSlice.sliceT_boxFun]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Prod.mk.eta]
    rw [GlobalTheory.SwapSlice.barL_apply, GlobalTheory.SwapSlice.barL_apply, hconj (GlobalTheory.LatVac.locCo G.M'.co v u₂ᵀ),
      Heisenberg₂ u₁ hu₁ hp₁ φ₁ h₁, Heisenberg₂ u₂ hu₂ hp₂ _ (hconjSB φ₂ h₂), map_mul, hstar, neg_neg, AddChar.map_add_eq_mul]
    ring
  let Lw : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ]
      ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) :=
    { toFun := schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂))
      map_add' := fun f g => by funext x; simp [schr, mul_add]
      map_smul' := fun c f => by funext x; simp [schr]; ring }
  let Z' : Matrix (Fin a') (Fin (a + a')) (Fv F v) × Matrix (Fin a') (Fin (a + a')) (Fv F v) :=
    (Z.1 + coY σ G.V' G.W t 1 1 u₁ᵀ, Z.2 + coY σ G.V' G.W t 1 1 u₂ᵀ)
  let c : ℂ := ψv (-pairM Z.1 (coX t 1 1 u₁ᵀ) + pairM Z.2 (coX t 1 1 u₂ᵀ))
  let Λ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → Fv F v) → ℂ) →ₗ[ℂ] ℂ :=
    (LinearMap.proj Z).comp ((GlobalTheory.SwapSlice.sliceT ι).comp Lw) - c • (LinearMap.proj Z').comp (GlobalTheory.SwapSlice.sliceT ι)
  have hΛ : ∀ Ψ, Λ Ψ = GlobalTheory.SwapSlice.sliceT ι (schr ψv (GlobalTheory.LatVac.locCo dd v (Matrix.fromCols u₁ u₂)) Ψ) Z -
      c * GlobalTheory.SwapSlice.sliceT ι Ψ Z' := fun Ψ => rfl
  have h0 := GlobalTheory.BoxSpan.boxSpan_ker F v (Fin a' × Fin (a + a')) (Fin a' × Fin (a + a')) ψv hc
    (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hT.base.std v) Λ
    (fun φ₁ h₁ φ₂ h₂ => by rw [hΛ, hbox φ₁ h₁ φ₂ h₂, sub_self]) Φ hΦ
  rw [hΛ, sub_eq_zero] at h0
  exact h0

end GlobalTheory.SwapHeis
