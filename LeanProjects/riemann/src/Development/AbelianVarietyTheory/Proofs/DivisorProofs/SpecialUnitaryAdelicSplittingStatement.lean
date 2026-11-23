import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryAdelicSplitting
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_adelic_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ)
    (J : Matrix (Fin M) (Fin M) E),
    ∃ e : SUAdelic σ J ≃ₜ*
        ((Matrix.GeneralLinearGroup.det.comp (HR (Ainf F) σ J).subtype).ker : Subgroup (HA (Ainf F) σ J)) ×
          finSU σ J,
      ∀ h, ((HA.mat (Ainf F) σ J (e h).1.1 : GL (Fin M) (Ainf F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Ainf F ⊗[F] E)) =
          ((HA.mat (AF F) σ J h.1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map
            (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) ∧
        ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) σ J (e h).2.1 : GL (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)) =
          finMat σ J h.1 := by
  first | exact @GlobalTheory.TamUnf.exists_adelic_split_detOne | exact GlobalTheory.TamUnf.exists_adelic_split_detOne | (intros; apply GlobalTheory.TamUnf.exists_adelic_split_detOne <;> assumption)
