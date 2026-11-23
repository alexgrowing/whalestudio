import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.SplitPrincipalSets
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsPlacesSingleton
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsFinCombSingleZero
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsBesPosOfBesselTied
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeReductionEqOneOfCompletionCongruence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionTrivialOfConjugatePlaceSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulAntiOfUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists

noncomputable section

namespace GlobalTheory.Core.Rk.DownCompare

open scoped ComplexConjugate Matrix ComplexOrder Pointwise TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff)
open GlobalTheory.Core.Rk.IP (WRep up wcoef rcoef)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lattices

open Formalism.L2.DIV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

end Lattices

variable {D : D7}

def latIn (V : HSp D) (L : Lat V) : Submodule (𝓞 D.host.E) V.V :=
  L.map (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_latIn {V : HSp D} {L : Lat V} {x : V.V} : x ∈ latIn V L ↔ V.frame.equivFun x ∈ L :=
  ⟨by rintro ⟨y, hy, rfl⟩; exact (V.frame.equivFun.apply_symm_apply y).symm ▸ hy, fun h => ⟨_, h, V.frame.equivFun.symm_apply_apply x⟩⟩

theorem hT_eq (V : HSp D) (x y : V.V) :
    V.hT x y = ∑ i, ∑ j, star (V.frame.equivFun x i) * V.gram i j * V.frame.equivFun y j := by
  conv_lhs => rw [← V.frame.sum_equivFun x, ← V.frame.sum_equivFun y]
  simp only [map_sum, map_smulₛₗ, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, HSpace.gram,
    Finset.mul_sum, starRingEnd_apply, RingHom.id_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem latIn_lat {V : HSp D} {L : Lat V} (h : IsSelfDualC V L) : Submodule.IsLattice D.host.E (latIn V L) where
  fg := h.1.fg.map _
  span_eq_top := by
    have := congrArg (Submodule.map V.frame.equivFun.symm.toLinearMap) h.1.span_eq_top
    rwa [Submodule.map_span, Submodule.map_top, LinearEquiv.range] at this

theorem latIn_unimod {V : HSp D} {L : Lat V} (h : IsSelfDualC V L) : Formalism.HermitianLatticesTheory.IsUnimodular V.hT (latIn V L) := by
  ext y
  rw [mem_latIn, h.2]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
    LinearMap.restrictScalars_apply]
  constructor
  · intro hy x hx
    obtain ⟨b, hb⟩ := hy _ (mem_latIn.2 (by rwa [LinearEquiv.apply_symm_apply] : V.frame.equivFun (V.frame.equivFun.symm x) ∈ L))
    exact ⟨b, by rw [hT_eq, LinearEquiv.apply_symm_apply] at hb; exact hb⟩
  · intro hy x hx
    obtain ⟨b, hb⟩ := hy _ (mem_latIn.1 hx)
    exact ⟨b, by rw [hT_eq]; exact hb⟩

def reset (V : HSp D) (L : Lat V) (h : IsSelfDualC V L) (s : (D.host.E →+* ℂ) → ℕ × ℕ) : HSp D :=
  { V with sig := s, L0 := latIn V L, standardTuple_isLattice := latIn_lat h, baseLattice_isUnimodular := latIn_unimod h }

theorem frameLat_reset (V : HSp D) (L : Lat V) (h : IsSelfDualC V L) (s : (D.host.E →+* ℂ) → ℕ × ℕ) :
    frameLat (reset V L h s) = L := by
  ext x
  exact (mem_latIn (V := V) (L := L) (x := V.frame.equivFun.symm x)).trans (by rw [V.frame.equivFun.apply_symm_apply x]; rfl)

section Transport

variable {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {LA : Lat A} {LW : Lat W} (hA : IsSelfDualC A LA) (hW : IsSelfDualC W LW)
  (sA sW : (D.host.E →+* ℂ) → ℕ × ℕ)

end Transport

def OwnLat (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A W : HSp D) (t : ℕ), IsInfFam θ → A.SigOK → A.IsPosDef → W.SigOK →
    A.rank = W.rank + t → 1 ≤ W.rank → W.rank + 5 ≤ t →
  ∀ (χA χW : (AE D)ˣ →* Circle) (om : WRep A W), IsWeilDatumO ψ A W χA χW om →
  ∀ Z : Finset (IndefiniteRowSideFullHecke.SplitPrincipalSets.FinPlE D), IndefiniteRowSideFullHecke.SplitPrincipalSets.IsSplitSet Z →
    (∀ v : FinPl D, (2 : 𝓞 D.host.F) ∈ v.asIdeal → Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v) →
    LFun.UnrOff χW (IndefiniteRowSideFullHecke.SplitPrincipalSets.below Z : Set (FinPl D)) →
  ∀ u : GA D A → ℂ, IsAutFunDef A u → (∀ k ∈ IndefiniteRowSideFullHecke.SplitPrincipalSets.prin A (frameLat A) Z, ∀ g, u (g * k) = u g) →
  ∀ c : LFun.Fam D.host.E, IndefiniteRowSideFullHecke.SplitPrincipalSets.IsSmallFam (IndefiniteRowSideFullHecke.SplitPrincipalSets.below Z) W.rank c →
    LFun.IsParamFun D.sp.cm.sig A.gram (frameLat A) (IndefiniteRowSideFullHecke.SplitPrincipalSets.below Z : Set (FinPl D)) u (c + LFun.segFam (LFun.val χW) t) →
  ∀ (m : Measure (GA D A)) (mInf : Measure (GinfC A)), m.IsHaarMeasure → mInf.IsHaarMeasure →
  ∀ (ν : Measure (WO A W)) (𝓕 : Set (WO A W)), IsCovolOne (ratL W A) ν 𝓕 →
  ∀ sW : RealMat W, (∀ τ, IsCartanInv (gramAt D W τ) (sW τ)) →
  ∀ Φ : WO A W → ℂ, IsFockVec ψ θ A W (fun _ => 1) sW Φ →
    IsSphOff ψ A W (frameLat A) (frameLat W) (IndefiniteRowSideFullHecke.SplitPrincipalSets.below Z) Φ →
    (∀ k ∈ IndefiniteRowSideFullHecke.SplitPrincipalSets.prin A (frameLat A) Z, om (k, 1) Φ = Φ) →
    ∫ b : GinfC A, wcoef om ν 𝓕 Φ Φ b * rcoef m u u b ∂mInf ≠ 0 →
    ∃ f, IsThetaFunO ψ A W f ∧ ∃ h, up om m f u h ≠ 0

end GlobalTheory.Core.Rk.DownCompare

end
