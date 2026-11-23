import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelFamOfNotMem
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem

namespace GlobalTheory

theorem idemOp_fix_span : ∀ (D : D7) (V : HSp D) (T : TypeDataG V) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (v : T.S) (x : W), x ∈ Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z, φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} → smoothOp (σ.comp (locFin V v)) (μf v) (T.idem μf v) x = x := by
  intro D V T μf hμ W _ _ σ hσ v x hx
  haveI := hμ v
  have hc : Continuous (locFin V v) := (continuous_emb _ _ _).subtype_mk _
  have hs : IsSmooth (σ.comp (locFin V v)) := fun y => (hσ y).preimage hc
  have hk : IsOpen (((T.frame v).red.ker : Subgroup (Kv V v)) : Set (Kv V v)) := by
    rw [show ((T.frame v).red.ker : Set (Kv V v)) =
        (↑) ⁻¹' (stabLocOne D.sp.cm.sig V.gram (T.frame v).emb (frameLat V) : Set (GLoc D.sp.cm.sig V.gram v)) from
      Set.ext (T.frame v).red_eq_one_iff]
    exact (isOpen_stabLocOne _ (T.frame v).emb _ (T.frame v).cm).preimage continuous_subtype_val
  obtain ⟨-, h2, h3, -⟩ := (typeIdem_projector (μf v) (isOpen_stabLoc _ _ _ v.1) (isCompact_stabLoc _ _ _ v.1)
    (T.frame v).red_surjective hk (T.irred v)).2.1 _ _ hs
  change smoothOp (σ.comp (locFin V v)) (μf v) (typeIdem (μf v) (T.frame v).red (T.τ v)) x = x
  have hle : Submodule.span ℂ {y | ∃ φ : T.W v →ₗ[ℂ] W, (∀ (k : Kv V v) z,
      φ (T.τ v ((T.frame v).red k) z) = σ (locFin V v k) (φ z)) ∧ y ∈ LinearMap.range φ} ≤
      LinearMap.range (smoothOp (σ.comp (locFin V v)) (μf v) (typeIdem (μf v) (T.frame v).red (T.τ v))) := by
    refine Submodule.span_le.2 ?_
    rintro y ⟨φ, hφ, z, rfl⟩
    rw [SetLike.mem_coe, h3]
    exact GlobalTheory.LocGL.apply_mem_isotypic ⟨φ, fun k => LinearMap.ext fun z => hφ k z⟩ z
  obtain ⟨w, rfl⟩ := hle hx
  exact LinearMap.congr_fun h2 w

end GlobalTheory
