import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationBCompactSupport
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralImports
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.configuration_b_compact_support : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ X om om', IsTriple B G X om om' →
    ∀ Φ' ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), ∀ C : Set (UA σ G.V'.J × UA σ G.W.J), IsCompact C →
    ∃ U : Set (Fin (Module.finrank F E) → Af F), IsCompact U ∧ ∀ p ∈ C, ∀ l : (AE F E)ˣ,
      (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∉ U → e' (G.M'.co.rho B.ψ (shiftB σ H H' l) (om' p Φ')) = 0 := by
  first | exact @GlobalTheory.ConeFinSuppUnif.finsupp | exact GlobalTheory.ConeFinSuppUnif.finsupp | (intros; apply GlobalTheory.ConeFinSuppUnif.finsupp <;> assumption)
