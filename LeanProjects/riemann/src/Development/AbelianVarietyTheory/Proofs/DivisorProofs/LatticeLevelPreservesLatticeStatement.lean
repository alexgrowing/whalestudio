import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelPreservesLattice
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatLevel
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_level_preserves_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ W.J), k ∈ GlobalTheory.ThKLevel.latLevel σ W → ∀ (w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E)), γ * Matrix.transpose (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat k) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV V W w ↔ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV V W w := by
  first | exact @GlobalTheory.ThKLevelLat.mul_transpose_mem_iff | exact GlobalTheory.ThKLevelLat.mul_transpose_mem_iff | (intros; apply GlobalTheory.ThKLevelLat.mul_transpose_mem_iff <;> assumption)
