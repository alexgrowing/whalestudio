import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.HCChar GlobalTheory.Published
open scoped ComplexConjugate TensorProduct

namespace GlobalTheory.EllipticOrb

theorem orbInt_elliptic : DiscreteSeriesCharacter → ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (ρ : D.what₂.Tau) (μ : Measure (GArch D.sp.cm.sig V.gram (placeOf D ρ))) [μ.IsHaarMeasure]
    (f : GArch D.sp.cm.sig V.gram (placeOf D ρ) → ℂ), Formalism.QuantumDeterminants.IsHCParam (M.lam ρ) →
    (haveI := (M.ds ρ).1; IsPseudoCoeff (matAt V ρ) μ (dsRep M ρ) f) →
    ∀ (s : GArch D.sp.cm.sig V.gram (placeOf D ρ)), IsRegSS (matAt V ρ s) →
    IsCompact (cent s : Set (GArch D.sp.cm.sig V.gram (placeOf D ρ))) →
    ∀ (y : GArch D.sp.cm.sig V.gram (placeOf D ρ)) (θ : Fin V.rank → ℝ),
    frameMat M ρ (y⁻¹ * s * y) = Matrix.diagonal (fun a => Complex.exp (θ a * Complex.I)) →
    ∀ (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant],
    HasOrbInt μ s dt f (conj (dsChar (M.ε ρ) (M.lam ρ) θ) / dt.real univ) := by
  intro hDS D V S M ρ μ _ f hl hf s hs hT y θ hy dt _ _
  haveI := (M.ds ρ).1
  haveI : (μ.map (frameEquiv M ρ)).IsHaarMeasure := (frameEquiv M ρ).isHaarMeasure_map μ
  obtain ⟨Θ', hΘ', hval⟩ :=
    hDS V.rank (M.ε ρ) (μ.map (frameEquiv M ρ)) (M.H ρ) (M.lam ρ) (M.σ ρ) hl (M.ds ρ) (M.ds ρ).2.2.1
  have hΘ : IsCharFn (matAt V ρ) μ (dsRep M ρ) (Θ' ∘ frameEquiv M ρ) := by
    rw [dsRep_eq_comp]
    exact IsCharFn.of_map (M.fr_unit ρ) (ujMat_frameEquiv_eq_conj M ρ) hΘ'.1
  have hι : Topology.IsInducing (matCoord (matAt V ρ)) :=
    (isEmbedding_archMat V.gram (isCMExt_host D) (embOverOf D ρ)).isInducing
  have h1 := hf.orb_of_isCharFn hι hΘ hs hT dt
  have hreg : IsRegSS (ujMat (M.ε ρ) (frameEquiv M ρ s)) :=
    (isRegSS_conj_iff (M.fr_unit ρ) (ujMat_frameEquiv_eq_conj M ρ) s).2 hs
  have h2 : frameEquiv M ρ (y⁻¹ * s * y) = torusPt (M.ε ρ) θ := by
    apply Subtype.ext
    apply Units.ext
    exact hy
  have hreg' : IsRegSS (ujMat (M.ε ρ) (torusPt (M.ε ρ) θ)) := by
    rw [← h2]
    exact (isRegSS_conj_iff (M.fr_unit ρ) (ujMat_frameEquiv_eq_conj M ρ) _).2 (by
      rw [IsRegSS, map_mul, Matrix.charpoly_mul_comm, ← map_mul, mul_inv_cancel_left]
      exact hs)
  have h3 : Θ' (frameEquiv M ρ s) = dsChar (M.ε ρ) (M.lam ρ) θ := by
    rw [← (hΘ'.2 _ hreg).2 (frameEquiv M ρ y), ← map_inv, ← map_mul, ← map_mul, h2]
    exact hval θ hreg'
  simpa [Function.comp, h3] using h1

end GlobalTheory.EllipticOrb
