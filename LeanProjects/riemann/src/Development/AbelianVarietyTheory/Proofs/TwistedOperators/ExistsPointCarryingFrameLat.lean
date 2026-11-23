import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsBaseFrameSelfDualHermitianFrameLatticeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CorrectionOfTransport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.FramePointMove

open scoped Matrix

theorem conj_maps_iff {A : Type} [CommRing A] {n : ℕ} (J x : GL (Fin n) A) {P Q : Set (Fin n → A)}
    (hJ : J.1.mulVec '' P = Q) :
    (∀ y ∈ Q, (J * x * J⁻¹).1 *ᵥ y ∈ Q) ↔ ∀ w ∈ P, x.1 *ᵥ w ∈ P := by
  have hinj : Function.Injective J.1.mulVec := fun a b h => by
    have := congrArg (fun z => (J⁻¹).1 *ᵥ z) h
    simpa [Matrix.mulVec_mulVec] using this
  have mem : ∀ z, J.1 *ᵥ z ∈ Q ↔ z ∈ P := fun z => by
    rw [← hJ, hinj.mem_set_image]
  have e : ∀ w, (J * x * J⁻¹).1 *ᵥ (J.1 *ᵥ w) = J.1 *ᵥ (x.1 *ᵥ w) := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp [Matrix.mul_assoc]
  constructor
  · intro h w hw
    have := h _ ((mem w).2 hw)
    rwa [e, mem] at this
  · intro h y hy
    rw [← hJ] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [e, mem]
    exact h w hw

theorem conj_maps_inv_iff {A : Type} [CommRing A] {n : ℕ} (J x : GL (Fin n) A) {P Q : Set (Fin n → A)}
    (hJ : J.1.mulVec '' P = Q) :
    (∀ y ∈ Q, ((J * x * J⁻¹)⁻¹).1 *ᵥ y ∈ Q) ↔ ∀ w ∈ P, (x⁻¹).1 *ᵥ w ∈ P := by
  have hinv : (J * x * J⁻¹)⁻¹ = J * x⁻¹ * J⁻¹ := by group
  rw [hinv]
  exact conj_maps_iff J x⁻¹ hJ

set_option maxHeartbeats 800000 in

theorem exists_point_carrying_frameLat : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsBaseFrame V β Λ N → ∃ a : GfC V, GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V (a : GA D V)).val ∧ ∀ g : GfC V, finE V ((a * g * a⁻¹ : GfC V) : GA D V) ∈ St β ↔ ∀ v, finLoc V v g ∈ Kv V v := by
  intro D V β Λ N hβ
  obtain ⟨β₀, -, hβ₀⟩ := GlobalTheory.T.exists_baseFrame_selfDual_hermitianFrameLattice D V
  obtain ⟨j, hj, -⟩ := GlobalTheory.FinAdIdent.exists_latIsom V V rfl (frameLat V) Λ β₀ β 1 N hβ₀ hβ ∅
    (fun _ h => absurd h (Set.notMem_empty _))
  obtain ⟨j', h1, h2⟩ := GlobalTheory.FinAdIdent.exists_inv hj.1.1
  let J : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) := ⟨j, j', h1, h2⟩
  have hJ : J ∈ Formalism.L2.DIV.UA D.sp.cm V.gram := hj.1.2
  obtain ⟨k, hk, e⟩ := GlobalTheory.AdIsomCorrection.exists_finE V J hJ
  refine ⟨⟨k, hk⟩, ?_, fun g => ?_⟩
  · show GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V k).val
    rw [e]
    exact hj
  · have hg : finE V ((⟨k, hk⟩ * g * ⟨k, hk⟩⁻¹ : GfC V) : GA D V) = J * finE V (g : GA D V) * J⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, e]
    have hJP : J.1.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) (frameLat V) : Set _) =
        (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) := hj.2
    rw [hg, GlobalTheory.LevSplit.mem_St_iff β Λ hβ.1]
    have hs := GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β₀ (frameLat V) hβ₀.1 (g : GA D V)
    rw [GlobalTheory.LevSplit.mem_St_iff β₀ (frameLat V) hβ₀.1] at hs
    refine Iff.trans ?_ hs
    exact and_congr (conj_maps_iff J _ hJP) (conj_maps_inv_iff J _ hJP)

end GlobalTheory.FramePointMove
