import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEigenStabilizerIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_eigen_stabilizer_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      ∃ C : Set (Fin b × Fin (b + a') → FiniteAdeleRing (𝓞 F) F), IsCompact C ∧
        ∀ (k : K) (l : (AE F E)ˣ) (x : Fin b × Fin (b + a') → AF F), (fun i => (x i).2) ∉ C →
          e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) x = 0 := by
  first | exact @GlobalTheory.ConeSupp.supp | exact GlobalTheory.ConeSupp.supp | (intros; apply GlobalTheory.ConeSupp.supp <;> assumption)
