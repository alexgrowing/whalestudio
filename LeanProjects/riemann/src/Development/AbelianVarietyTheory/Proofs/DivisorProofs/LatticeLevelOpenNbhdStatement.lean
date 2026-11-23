import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelOpenNbhd
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_level_open_nbhd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d), W.L.IsLattice E → ∃ U : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J), IsOpen U ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J) ∈ U ∧ U ∩ GlobalTheory.ThKAdm.FinPt σ W ⊆ GlobalTheory.ThKLevel.latLevel σ W := by
  first | exact @GlobalTheory.ThKLevelOpen.exists_open_latLevel | exact GlobalTheory.ThKLevelOpen.exists_open_latLevel | (intros; apply GlobalTheory.ThKLevelOpen.exists_open_latLevel <;> assumption)
