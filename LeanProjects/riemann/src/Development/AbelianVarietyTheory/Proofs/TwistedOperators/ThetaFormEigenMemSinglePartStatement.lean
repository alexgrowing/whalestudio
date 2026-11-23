import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFormEigenMemSinglePart
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ConjScalarThm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaForm_eigen_mem_single_part : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.models_HW → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) (b : Pl D.host.E → List ℤ → ℂ), ∃ ev, ∀ w : (R.HW i σ).H, (∀ P d, GlobalTheory.Hk3.Good R A.μ0 P → GlobalTheory.ConjScalar.RelLab (Wc D i) P d → postOn (R.MW i σ) (GlobalTheory.Hk3.hk (Wc D i) P (Finsupp.single d 1)) ((R.HW i σ).e w) = b P d • (R.HW i σ).e w) → w ∈ GlobalTheory.LiftLower.partH R i σ ev := by
  first | exact @GlobalTheory.ConjScalar.OnePart.mem_one_part | exact GlobalTheory.ConjScalar.OnePart.mem_one_part | (intros; apply GlobalTheory.ConjScalar.OnePart.mem_one_part <;> assumption)
