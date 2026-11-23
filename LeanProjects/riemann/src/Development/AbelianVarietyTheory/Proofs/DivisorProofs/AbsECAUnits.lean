import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory

theorem absE_cA_units {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (t : (AE F E)ˣ) : absE F E (Units.map (cA σ : AE F E →* AE F E) t) = absE F E t := by
  have hn : Algebra.norm (AF F) (Units.map (cA σ : AE F E →* AE F E) t).1 = Algebra.norm (AF F) t.1 :=
    Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R := AF F) (A₁ := AF F))
      (AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ))) t.1
  simp only [GlobalTheory.Doubling.absE_apply, GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]
  rw [hn]

end GlobalTheory
