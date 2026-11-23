import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeMidsetIsotropicVector
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
theorem _root_.GlobalTheory.T.cone_midset_isotropic_vector : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ X om om', IsTriple B G X om om' →
    ∀ T : Set (UA σ G.W.J), T ⊆ ratU σ G.W.J → ∀ t ∈ GlobalTheory.ConeSmallSer.midSet H'.x T, ∃ z : Fin (a + b) → E, z ≠ 0 ∧ form σ G₁.W.J z z = 0 := by
  first | exact @GlobalTheory.ConeSmallMidJB.IsoMid.exists_isotropic_of_mid | exact GlobalTheory.ConeSmallMidJB.IsoMid.exists_isotropic_of_mid | (intros; apply GlobalTheory.ConeSmallMidJB.IsoMid.exists_isotropic_of_mid <;> assumption)
