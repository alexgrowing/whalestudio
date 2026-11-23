import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOneParameterSubgroupUnitaryOfRealPlaceLieA
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oneParameterSubgroup_unitary_of_realPlace_lieAlg : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : InfinitePlace F → ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : ∀ w : InfinitePlace F, Mat (R w) (S w), (∀ w, Y w ∈ upq (R w) (S w)) → ∃ γ ∈ RLines σ J, IsGenD τ C γ Y := by
  first | exact @GlobalTheory.HoweD.exists_line_of_upqD | exact GlobalTheory.HoweD.exists_line_of_upqD | (intros; apply GlobalTheory.HoweD.exists_line_of_upqD <;> assumption)
