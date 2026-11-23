import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeImageOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_lattice_image_open : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) {n d : ℕ}
    (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)) (v : Pl F),
      IsOpen (((latAtV X W v).map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) :
        Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) ∧
      IsCompact (((latAtV X W v).map (GlobalTheory.LatVac.locCo co v) : AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) :
        Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) := by
  first | exact @GlobalTheory.LatOpenCptAny.main | exact GlobalTheory.LatOpenCptAny.main | (intros; apply GlobalTheory.LatOpenCptAny.main <;> assumption)
