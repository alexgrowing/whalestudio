import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelHeisenbergOperatorsTranslationChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open GlobalTheory.WeilM
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SoLocAnyIntertwiner

theorem soLoc_iff : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
    ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
      (φ ∈ G.M'.SoLoc B.ψ B.τ₁ ↔ ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁), Y.rank ≠ a' → ι φ Y = 0) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT ι hι φ hφ
  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit (G.V'.J.map B.τ₁).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J B.τ₁ (B.emb w).1 1 one_ne_zero (G.V'.θ w)
      (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have herm : ∀ i j, σ (G.V'.J j i) = algebraMap F E 1 * G.V'.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV'.herm i j
  let K := GlobalTheory.SplitUnitLift.liftU hcm B.τ₁ G.V'.J 1 herm hdet
  have hK : ∀ g, K g ∈ UAt σ G.V' (evFin F B.v₁) ∧ (mat (K g)).map (piW B.τ₁) = g.val ∧
      (mat (K g)).map (piW (B.τ₁.comp σ)) = (G.V'.J.map B.τ₁)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map B.τ₁ :=
    fun g => ⟨GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm B.τ₁ G.V' 1 herm hdet g, GlobalTheory.SplitUnitLift.liftU_piW hcm B.τ₁ G.V'.J 1 herm hdet g,
      GlobalTheory.SplitUnitLift.liftU_piW_comp hcm B.τ₁ G.V'.J 1 herm hdet g⟩
  choose S hS using fun g => GlobalTheory.WeilLocality.locality B G X om om' hT B.v₁ (K g) (hK g).1
  have h1 : ∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), S g φ ∈ GlobalTheory.WeilM.SB _ := fun g φ hφ => (hS g φ hφ).1
  have hSplit := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hT.weil'
  have atAct : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F B.v₁) γ →
      At (evFin F B.v₁) (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ) := by
    intro g γ hγ u hu
    simp only [GlobalTheory.WeilM.actAB]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hγ u hu, Matrix.mul_zero, Matrix.zero_mul]
  have restS : ∀ g φ r, φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁) → Rest (evFin F B.v₁) φ r → Rest (evFin F B.v₁) (S g φ) r :=
    fun g φ r hφ hr => ⟨hr.1, by rw [← (hS g φ hφ).2 r hr]; exact hSplit.pres _ _ hr.2⟩
  have h4 : ∀ g (γ : Matrix (Fin a') (Fin (a + a')) (AE F E)), At (evFin F B.v₁) γ → ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        S g (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ γ) φ) =
          GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁)
            (GlobalTheory.LatVac.locCo G.M'.co B.v₁ (GlobalTheory.WeilM.actAB (cA σ) (K g, (1 : UA σ G.W.J)) γ)) (S g φ) := by
    intro g γ hγ φ hφ
    have hw := GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 B.v₁ (GlobalTheory.LatVac.locCo G.M'.co B.v₁ γ) φ hφ
    refine GlobalTheory.TensUniq.eq_of_tens_eq B.v₁ φ _ _ hφ fun r hr => ?_
    have hb1 := GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ B.v₁ γ hγ φ r hr
    have hRw : Rest (evFin F B.v₁) (GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (GlobalTheory.LatVac.locCo G.M'.co B.v₁ γ) φ) r :=
      ⟨hr.1, by rw [← hb1]; exact GlobalTheory.HeisSchA.rho_mem_schA G.M' B.ψ hT.base.std γ _ hr.2⟩
    rw [← (hS g _ hw).2 r hRw, ← hb1, hSplit.impl _ _ _ hr.2, (hS g φ hφ).2 r hr,
      GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ B.v₁ _ (atAct g γ hγ) (S g φ) r (restS g φ r hφ hr)]
  obtain ⟨hψc, hψ1, wT, wM, hA⟩ := GlobalTheory.LinBarOps.heis_ops B G X om om' hT K hK S h1 h4
  obtain ⟨hTι, hMι, -, -⟩ := hA ι hι
  constructor
  · rintro ⟨-, ι₂, hι₂, hvan⟩ Y hY
    obtain ⟨hT₂, hM₂, -, -⟩ := hA ι₂ hι₂
    obtain ⟨c, hc⟩ := GlobalTheory.LinSchur.eq_smul_of_commute (GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁)) (GlobalTheory.LatVac.psiAt B.ψ B.v₁) hψc hψ1 ι₂ ι
      hι₂.bij (fun x _ y _ c => by rw [map_add, map_smul])
      (fun C => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wT C))
      (fun l => GlobalTheory.WeilM.schr (GlobalTheory.LatVac.psiAt B.ψ B.v₁) (wM l))
      (fun C x hx => ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 B.v₁ _ x hx, hT₂ C x hx, hTι C x hx⟩)
      (fun l x hx => ⟨GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 B.v₁ _ x hx, hM₂ l x hx, hMι l x hx⟩)
    rw [hc φ hφ, Pi.smul_apply, hvan Y hY, smul_zero]
  · intro h
    exact ⟨hφ, ι, hι, h⟩

end GlobalTheory.SoLocAnyIntertwiner
