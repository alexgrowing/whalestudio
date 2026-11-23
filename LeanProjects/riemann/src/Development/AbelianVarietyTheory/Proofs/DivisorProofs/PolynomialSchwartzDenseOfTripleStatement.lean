import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialSchwartzDenseOfTriple
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_schwartz_dense_of_triple : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    Dense ((G.M.Pol B.ψ B.emb : Submodule ℂ (SInf F (Fin a × Fin (a + a')))) : Set (SInf F (Fin a × Fin (a + a')))) := by
  first | exact @GlobalTheory.PolDenseTriple.pol_dense_triple | exact GlobalTheory.PolDenseTriple.pol_dense_triple | (intros; apply GlobalTheory.PolDenseTriple.pol_dense_triple <;> assumption)
