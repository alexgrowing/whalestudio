import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHasCls
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TorusElementCharpolyRegularCentralizerStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormClassesIffConjUnitaryTorusEllipticElementsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryTorusNormClassesAtAllPlacesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryTorusEquivCentralizerWithMeasureStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ArchimedeanUnitaryGroupStabilisersUnimodular
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnitaryGroupStabilizersUnimodularFinitePlac
open MeasureTheory Set Filter Polynomial NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots GlobalTheory.TrEll
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (mapH diagH)
open scoped TensorProduct ComplexConjugate Matrix

noncomputable section
namespace GlobalTheory.TrPhiOK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {r n : ℕ}
  {P : PPol σ r} {J : Matrix (Fin n) (Fin n) E}

theorem phiOK_of (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (k : Type) [Field k] [Algebra F k] [TopologicalSpace k]
    [IsTopologicalRing k] [T2Space k] [LocallyCompactSpace (HA k σ J)] [SecondCountableTopology (HA k σ J)]
    [T2Space (HA k σ J)] (hfin : Finite (Cls P k))
    (hU : ∀ μ : Measure (HA k σ J), μ.IsHaarMeasure → μ.IsMulRightInvariant)
    (hpr : ∀ g : HA k σ J, IsRegSS (matHom k σ J g).1 → IsProperOrbit (cent g) g)
    (μ : Measure (HA k σ J)) (dt : Measure (Tor P k)) (f : HA k σ J → ℂ) [hμ : μ.IsHaarMeasure]
    [hdt : dt.IsHaarMeasure] (hf : Continuous f) (hc : HasCompactSupport f) : PhiOK (J := J) μ dt f := by
  refine ⟨Set.toFinite _, fun x φ h => ?_⟩
  haveI := hU μ hμ
  set q : XSet P k J := ⟨QuotientGroup.mk x, x, φ, rfl, h⟩ with hq
  obtain ⟨hx0, h0⟩ := q.2.choose_spec.choose_spec
  set x0 := q.2.choose
  set φ0 := q.2.choose_spec.choose
  change HasOrbInt μ (gam h) (centMeas h dt) f (orbInt μ (gam h0) (centMeas h0 dt) f)

  have halg0 := GlobalTheory.T.torusElement_charpoly_regular_centralizer F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e0, he0, hm0⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r n P J hJ k x0 φ0 h0
  obtain ⟨e, he, hm⟩ := GlobalTheory.T.unitaryTorus_equiv_centralizer_with_measure F E σ hσ r n P J hJ k x φ h
  haveI : (centMeas h0 dt).IsHaarMeasure := by rw [hm0]; exact e0.isHaarMeasure_map dt
  haveI : (centMeas h0 dt).IsMulRightInvariant :=
    isMulRightInvariant_cent (isMulCommutative_cent_HA halg0.2.1) _
  have H0 : HasOrbInt μ (gam h0) (centMeas h0 dt) f (orbInt μ (gam h0) (centMeas h0 dt) f) :=
    (hpr _ halg0.2.1).hasOrbInt hf hc

  obtain ⟨g, hg⟩ := (GlobalTheory.T.normClasses_iff_conj_unitaryTorusEllipticElements F E σ hσ r n P J hJ k x0 φ0 h0 x φ h).1 (by rw [hx0])
  have hgam : g * gam h0 * g⁻¹ = gam h := (hg _).symm
  have hmeas : centMeas h dt = (centMeas h0 dt).map (centEquiv (conjEquiv g) (gam h0) hgam) := by
    rw [hm, hm0, Measure.map_map (map_continuous _).measurable (map_continuous _).measurable]
    congr 1
    funext t
    apply Subtype.ext
    change (e t).1 = g * (e0 t).1 * g⁻¹
    rw [he, he0, hg]
  rw [hmeas]
  exact ((hasOrbInt_conj (dh := μ) (dt := centMeas h0 dt) g hgam f _).1).2 H0

end GlobalTheory.TrPhiOK

open GlobalTheory.TrPhiOK in

theorem GlobalTheory.TrPhiOK.phiOK_local : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (r n : ℕ) (P : PPol σ r) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → (∀ (v : HeightOneSpectrum (𝓞 F)) (μ : Measure (GLoc σ J v)) (dt : Measure (Tor P (Fv F v))) (f : GLoc σ J v → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f) ∧ ∀ (w : InfinitePlace F) (μ : Measure (GArch σ J w)) (dt : Measure (Tor P w.Completion)) (f : GArch σ J w → ℂ), μ.IsHaarMeasure → dt.IsHaarMeasure → Continuous f → HasCompactSupport f → PhiOK (J := J) μ dt f := by
  intro F E _ _ _ _ _ σ hσ r n P J hJ
  have hfin := GlobalTheory.T.finite_unitaryTorusNormClasses_at_all_places F E σ hσ r P
  refine ⟨fun v μ dt f hμ hdt hf hc => ?_, fun w μ dt f hμ hdt hf hc => ?_⟩
  · have hU := (GlobalTheory.LocalUnitaryUnimod.unimodularOver_adicCompletion F E σ hσ n J hJ v).1
    exact phiOK_of hσ hJ (Fv F v) (hfin.1 v) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GLoc hσ hJ hg) μ dt f hf hc
  · haveI : SecondCountableTopology w.Completion :=
      (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
    have hU := (GlobalTheory.ArchUnitaryUnimod.unimodularOver_of_artinian (σ := σ) w.Completion hσ hJ).1
    exact phiOK_of hσ hJ w.Completion (hfin.2 w) hU.2.2.2.2.2.2 (fun g hg => isProperOrbit_GArch hσ hJ hg) μ dt f hf hc
