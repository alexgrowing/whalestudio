import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeSelfDualHermitianExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_self_dual_hermitian_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ (cm : @Formalism.BasicNotions.CMData F E _ _ _ _ (GlobalTheory.HCFinU.starOf σ hσ) _) (hJ : ∀ i j, σ ((c • W.J.map σ) j i) = (c • W.J.map σ) i j) (hdet : (c • W.J.map σ).det ≠ 0) (L : Submodule (𝓞 E) (Fin d → E)) (hfg : L.FG) (hspan : Submodule.span E (L : Set (Fin d → E)) = ⊤) (hdual : ∀ x : Fin d → E, x ∈ L ↔ ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) (c • W.J.map σ) y x ∈ (algebraMap (𝓞 E) E).range) (ε : InfinitePlace F → Fin d → Bool) (hφ : ∀ v (a : F), (B.emb v).1 (algebraMap F E a) = v.embedding a) (P : InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) (hPu : ∀ v, IsUnit (P v)) (hP : ∀ v, (P v)ᴴ * (c • W.J.map σ).map (B.emb v).1 * P v = Formalism.REAL.Jm (ε v)), (∀ v, (P v)⁻¹ * W.θ v * P v = Formalism.REAL.Jm (ε v) ∨ (P v)⁻¹ * W.θ v * P v = -Formalism.REAL.Jm (ε v)) → ∀ (hs : σ = (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP).cm.sig) (k : GlobalTheory.Dec.Kinf (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP)), (toGAd hσ W.J hc).symm (GlobalTheory.HCFinU.bridgeS (GlobalTheory.HCFinU.mkI σ hσ cm (c • W.J.map σ) hJ hdet L hfg hspan hdual ε (fun v => (B.emb v).1) hφ P hPu hP) σ hs ((fun v => (k v).1), 1)) ∈ KInf σ W B.emb := by
  first | exact @GlobalTheory.HCFinU.KinfBridge.main | exact GlobalTheory.HCFinU.KinfBridge.main | (intros; apply GlobalTheory.HCFinU.KinfBridge.main <;> assumption)
