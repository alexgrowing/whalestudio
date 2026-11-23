import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatFixLeRatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinSeriesMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeSmallTermMeas

theorem termW_mul_ht_aestronglyMeasurable : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure → ∀ γ, IsWitt (σ := σ) (J := G.W.J) H'.x γ →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∀ hf : UA σ G.V'.J → ℝ, GlobalTheory.ConeSmall.IsIwaHt K H.x hf → (∀ g, ∃ (p k : UA σ G.V'.J) (l : (AE F E)ˣ), k ∈ K ∧ mat p *ᵥ incV F H.x = l.1 • incV F H.x ∧ g = p * k) →
    ∀ (w : IsoV σ G.W.J) (h : UA σ G.W.J) (r : ℝ), AEStronglyMeasurable (fun g => ‖termW B G.M' H H' e' om' Φ' γ w g h‖ * hf g ^ r) G.M'.μ := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' _ e' hE K _ _ hK _ _ γ _ X om om' om₁ om₁' hT hT₁ Φ hΦ hf hiw hdec w h r
  have hM := hT.geo.hM'
  have hM₁ := hT₁.geo.hM'
  have hψ := hT.base.std
  have hW : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co X.α (X.α / X.β) om' :=
    hT.weil'
  obtain ⟨l₀, hl₀, hl₀eq⟩ := GlobalTheory.ThetaAdmitted.exists_admitted_form_eq_adelicThetaDistribution_alt F (Fin b × Fin (a + b))
  have hl := GlobalTheory.ConeMeasV.comp_schr_mem_adm hψ (G.M'.co.e (shiftB σ H H' 1))
    (GlobalTheory.ConeMeasV.comp_ev_mem_adm hM hM₁ hE hl₀)
  have hΦA := GlobalTheory.ConeMeasV.polData_le_schA hM hΦ.1
  have hc := hW.2.2 _ hl Φ hΦA
  have hsplit := hW.isUSplitting
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  have heq : (fun g => termW B G.M' H H' e' om' Φ γ w g h) =
      fun g => ((l₀ ∘ₗ e') ∘ₗ GlobalTheory.ConeMeasV.schrLin B.ψ (G.M'.co.e (shiftB σ H H' 1))) (om' (g, γ w * h) Φ) := by
    funext g
    have h1 : om' (g, γ w * h) Φ ∈ schA F _ := hsplit.pres (g, γ w * h) Φ hΦA
    have h2 := GlobalTheory.ConeMeasV.schr_mem_schA hψ (G.M'.co.e (shiftB σ H H' 1)) h1
    have h3 := hE.maps _ h2
    exact (hl₀eq _ h3).symm
  have hcT : Continuous fun g => termW B G.M' H H' e' om' Φ γ w g h := by
    rw [heq]
    exact hc.comp (continuous_id.prodMk continuous_const)
  obtain ⟨K', -, -, hK'stab, hK'cpt, -, -⟩ :=
    GlobalTheory.StabHaar.stabEx hKP.base F E σ B (b + 2) G.V' _ _ hT.base hT.geo.hV'
  have hKK : K = K' := Subgroup.ext fun g => (hK g).trans (hK'stab g).symm
  subst hKK
  have hcont : Continuous hf := GlobalTheory.ConeSmallMeas.continuous_ht K hK'cpt H.x hf hiw hdec
  exact (hcT.norm.measurable.mul (hcont.measurable.pow_const r)).aestronglyMeasurable

end GlobalTheory.ConeSmallTermMeas

end
