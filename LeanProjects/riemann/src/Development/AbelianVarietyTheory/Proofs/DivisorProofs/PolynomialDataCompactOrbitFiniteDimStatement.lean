import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDataCompactOrbitFiniteDim
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_data_compact_orbit_finite_dim : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ Kf : Subgroup (UA σ W.J), IsCompact (Kf : Set (UA σ W.J)) → Kf ≤ finU σ W.J → ∀ Φ ∈ GlobalTheory.ThK.PolData B M, FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : Subgroup.closure (KInf σ W B.emb ∪ (Kf : Set (UA σ W.J))) => om (1, (k : UA σ W.J)) Φ)) := by
  first | exact @GlobalTheory.PolLocFin.polData_locFin | exact GlobalTheory.PolLocFin.polData_locFin | (intros; apply GlobalTheory.PolLocFin.polData_locFin <;> assumption)
