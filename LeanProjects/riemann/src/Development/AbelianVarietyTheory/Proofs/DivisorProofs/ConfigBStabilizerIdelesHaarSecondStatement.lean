import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIdelesHaarSecond
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_b_stabilizer_ideles_haar_second : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ → ∀ emb : UA σ G₁.W.J → UA σ G.W.J, (∀ h₁, IsLevi H' 1 h₁ (emb h₁)) →
    ∀ w : UA σ G.W.J, IsSwap H' H₂ w → ∀ nn : AE F E → UA σ G.W.J, IsShear H' H₂ nn →
    ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
      GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T →
      ∀ Gf : UA σ G.W.J → ℂ, (∀ g, IsCT H₂ (fun h₁ => (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (emb h₁ * g)) (fun h₁ => Gf (emb h₁ * g))) →
      ∃ (T₁ : Set (UA σ G₁.W.J)) (κ : ℂ) (ν : @Measure (AE F E) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν ∧
        IsCT H' (GlobalTheory.ConeSmallSer.partSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) (GlobalTheory.ConeSmallSer.midSet H'.x T))
          (fun h => κ * ∑' γ : T₁, ∫ c, Gf (w * nn c * emb γ.1 * h) ∂ν) ∧
        (∀ h, Summable fun γ : T₁ => ‖∫ c, Gf (w * nn c * emb γ.1 * h) ∂ν‖) ∧
        ∀ h (γ : T₁), Integrable (fun c => Gf (w * nn c * emb γ.1 * h)) ν := by
  first | exact @GlobalTheory.ConeSmallMidJB.ctMid_unfold | exact GlobalTheory.ConeSmallMidJB.ctMid_unfold | (intros; apply GlobalTheory.ConeSmallMidJB.ctMid_unfold <;> assumption)
