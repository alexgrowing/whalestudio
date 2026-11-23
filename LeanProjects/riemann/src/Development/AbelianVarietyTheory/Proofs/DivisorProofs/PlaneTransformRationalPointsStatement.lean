import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneTransformRationalPoints
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_transform_rational_points : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (H : Plane E n n₁) (H' : Plane E d d₁) (x : Matrix (Fin n) (Fin d) E),
    (∃ y z : Kc F E d₁ n₁ → F, (planeT σ X W H H' (incM F x)).1 = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) ∧
    ∃ x₁ : Matrix (Fin n₁) (Fin d₁) E, (planeT σ X W H H' (incM F x)).2 = incM F x₁ := by
  first | exact @GlobalTheory.ThK.PlaneCo.Rat.planeT_incM | exact GlobalTheory.ThK.PlaneCo.Rat.planeT_incM | (intros; apply GlobalTheory.ThK.PlaneCo.Rat.planeT_incM <;> assumption)
