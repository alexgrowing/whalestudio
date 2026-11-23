import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOfMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPairConverse
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmThetaSumRhoPure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThKPointCont

def schrLin {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' φ φ' := funext fun _ => mul_add _ _ _
  map_smul' c φ := funext fun _ => mul_left_comm _ _ _

theorem comp_schrLin_mem_adm {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] [Invertible (2 : AF F)]
    (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (w : (κ → AF F) × (κ → AF F)) :
    ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ schrLin ψ w ∈ (adeleClass F).adm κ := by
  intro l hl g hg
  obtain ⟨T, g', hg', hT⟩ := GlobalTheory.ThetaHeisCLM.exists_schr_pureA_eq ψ hψ w hg
  obtain ⟨L, hL⟩ := hl g' hg'
  exact ⟨L.comp T, fun f => (congrArg l (hT f)).trans (hL (T f))⟩

theorem continuous_ev_rho_weil : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), ∀ (w : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E)) (y : Fin b × Fin (b + a') → AF F),
      Continuous (fun g : UA σ G.V.J × UA σ G.W.J => e (G.M.co.rho B.ψ w (om g Ψ)) y) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' _ e he X om om' om₁ om₁' hT hT₁ Ψ hΨ w y
  have h1 := GlobalTheory.EvAdm.comp_mem_adm F E σ B _ _ _ _ _ _ _ _ G.M G₁.M _ _ _ e hT.geo.hM hT₁.geo.hM he _
    (GlobalTheory.EvPoint.proj_mem_adm F _ y)
  exact hT.weil.2.2 _ (comp_schrLin_mem_adm B.ψ hT.base.std (G.M.co.e w) _ h1) Ψ hΨ

end GlobalTheory.ThKPointCont

end
