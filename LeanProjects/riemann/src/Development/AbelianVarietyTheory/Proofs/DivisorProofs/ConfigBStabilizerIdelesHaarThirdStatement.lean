import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBStabilizerIdelesHaarThird
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
theorem _root_.GlobalTheory.T.config_b_stabilizer_ideles_haar_third : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ (V : Spc F E a) (V' : Spc F E b) (W₁' : Spc F E (a + b)), IsTriple B (reG G₁ V V' W₁') X om₁ om₁' →
    ∀ (e : ℕ) (W₂ : Spc F E e) (H₂ : Plane E (a + b) e) (i₀ i₁ : ℕ), H₂.IsAdapted σ B (reG G₁ V V' W₁').W W₂ i₀ i₁ →
    ∃ s₁ : ℝ, ∀ s : ℂ, s₁ < s.re → ∀ g : UA σ G.W.J,
      (∀ (k : K) (l : (AE F E)ˣ), ∃ c : UA σ G₁.W.J → ℂ, IsCT H₂ (G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, g) Φ')))) c ∧
        GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.α (((b : ℕ) : ℂ) / 2) X.β (((a : ℕ) : ℂ) / 2) c ∧
        GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.β (((a : ℕ) : ℂ) / 2) X.α (((b : ℕ) : ℂ) / 2) c) →
      ∃ C : UA σ G₁.W.J → ℂ, IsCT H₂ (fun v => ∫ k, ∫ l, G₁.M'.I om₁' (e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' (k.1, g) Φ'))) v * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ (s + ((a : ℂ) + 1) / 2) ∂μ ∂μK) C ∧
        GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.α (((b : ℕ) : ℂ) / 2) X.β (((a : ℕ) : ℂ) / 2) C ∧
        GlobalTheory.ConeSmallMid.JRel W₂ H₂ X.β (((a : ℕ) : ℂ) / 2) X.α (((b : ℕ) : ℂ) / 2) C := by
  first | exact @GlobalTheory.ConeJBPass.pass | exact GlobalTheory.ConeJBPass.pass | (intros; apply GlobalTheory.ConeJBPass.pass <;> assumption)
