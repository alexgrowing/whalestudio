import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenSubgroupCompactInterFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_subgroup_compact_inter_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsCMExt F E σ → ∃ U : Subgroup (UA σ J), IsOpen (U : Set (UA σ J)) ∧ IsCompact ((U ⊓ finU σ J : Subgroup (UA σ J)) : Set (UA σ J)) := by
  first | exact @GlobalTheory.ThetaCplV.exists_isOpen_isCompact_finU | exact GlobalTheory.ThetaCplV.exists_isOpen_isCompact_finU | (intros; apply GlobalTheory.ThetaCplV.exists_isOpen_isCompact_finU <;> assumption)
