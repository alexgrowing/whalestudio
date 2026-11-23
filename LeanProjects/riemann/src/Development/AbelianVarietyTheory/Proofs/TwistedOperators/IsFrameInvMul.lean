import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IsometryCarriesCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DegreeOnePrimeReductionSplitPlaceDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersUnramifiedOffLevelPlaces
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
open scoped TensorProduct

namespace GlobalTheory.SplitPlaceRed

theorem isFrame_inv_mul {D : D7} {n : ℕ} {L Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (β A : GL (Fin n) (Formalism.IndefR.Lev.EAf D)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (hA : A.1.mulVec '' (Formalism.L2.Herm.hatL (F := D.host.F) L : Set (Fin n → Formalism.IndefR.Lev.EAf D)) =
      (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set (Fin n → Formalism.IndefR.Lev.EAf D))) :
    Formalism.L2.DIV.IsFrame (A⁻¹ * β) L := by
  intro x
  have hAm : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) L ↔ A.1.mulVec z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
    intro z
    constructor
    · intro hz
      rw [← SetLike.mem_coe, ← hA]
      exact ⟨z, hz, rfl⟩
    · intro hz
      rw [← SetLike.mem_coe, ← hA] at hz
      obtain ⟨z', hz', e⟩ := hz
      have e2 := congrArg (A⁻¹).1.mulVec e
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Matrix.one_mulVec] at e2
      exact e2 ▸ hz'
  rw [hAm, hβ]
  have e : ((A⁻¹ * β)⁻¹).1 = (β⁻¹).1 * A.1 := by
    rw [mul_inv_rev, inv_inv]; rfl
  rw [e, ← Matrix.mulVec_mulVec]

set_option maxHeartbeats 1000000 in

theorem map_intGL_eq {D : D7} (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v)
    (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (A : GA D V) (g : Gv V v)
    (y : GL (Fin V.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E))
    (hy : Formalism.L2.DIV.frGL β y = finE V (A * embV V v g * A⁻¹)) :
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) (Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y) =
      (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V A)⁻¹ * β))⁻¹ * splitHom D.sp.cm.sig V.gram (GlobalTheory.SplitProjChart.emb φ) g *
        GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V A)⁻¹ * β) := by
  set Φ : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D) →* GL (Fin V.rank) (Fv D.host.F v) :=
    Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ) with hΦ
  have hfin : ∀ h : GA D V, Φ (finE V h) = Matrix.GeneralLinearGroup.map (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ) (Formalism.L2.Theta.matHom V h) := by
    intro h
    apply Units.ext
    apply Matrix.ext
    intro p q
    show GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdE φ ((finE V h).1 p q) = GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdA φ ((Formalism.L2.Theta.matHom V h).1 p q)
    rw [GlobalTheory.LevSplit.finE_val]
    exact GlobalTheory.SplitProjChart.rdE_toEAf φ _
  have hk : Φ (finE V (embV V v g)) = splitHom D.sp.cm.sig V.gram (GlobalTheory.SplitProjChart.emb φ) g := by
    rw [hfin]
    exact GlobalTheory.SplitChartLink.rdA_matHom_embV V φ _
  have hyv : Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y = β⁻¹ * Formalism.L2.DIV.frGL β y * β := by
    show _ = β⁻¹ * (β * _ * β⁻¹) * β
    group
  rw [hyv, hy]
  show _ = (Φ ((finE V A)⁻¹ * β))⁻¹ * _ * Φ ((finE V A)⁻¹ * β)
  simp only [map_mul, map_inv, hk]
  group

end GlobalTheory.SplitPlaceRed

namespace GlobalTheory.SplitPlaceRed

set_option maxHeartbeats 1000000 in

theorem splitRed_frame : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (a : GfC V), IsBaseFrame V β Λ N → GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter.IsLatIsom V V (frameLat V) Λ (finE V (a : GA D V)).val → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), PP.under (𝓞 D.host.F) = v → ¬ Formalism.IndefR.Lev.IsConjPl PP PP → (∀ k : Kv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β) → ∃ (s : SplitAt D.sp.cm.sig V.gram (frameLat V) v) (ρ : ResF v ≃+* kP PP), ∀ (k : Kv V v) (i j : Fin V.rank), (redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V))).1 i j = ρ ((s.red k).1 i j) := by
  intro D V β Λ N a hB hL v PP hv hc hst

  have hcc : Formalism.IndefR.Lev.IsConjPl PP (Formalism.L2.DIV.conjPl PP) := by
    intro c hc'
    refine ⟨Formalism.L2.DIV.starO c, ?_, Formalism.L2.DIV.starO_coe c⟩
    show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO c) ∈ PP.asIdeal
    rw [Formalism.L2.DIV.starO_starO]
    exact hc'
  have hne : PP ≠ Formalism.L2.DIV.conjPl PP := fun e => hc (by
    have := hcc
    rw [← e] at this
    exact this)
  have hv' : (Formalism.L2.DIV.conjPl PP).under (𝓞 D.host.F) = v :=
    (GlobalTheory.LevelPlaces.under_eq_of_isConjPl hcc).symm.trans hv
  obtain ⟨τ, hτ, -⟩ := existsUnique_splitPrime_eq (isCMExt_host D) hne hv hv'
  set φ : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.SplitProj D v := splitProj τ with hφ
  have hemb : GlobalTheory.SplitProjChart.emb φ = τ := by
    ext x; simp [hφ, GlobalTheory.SplitProjChart.emb, splitProj]

  have hfr := isFrame_inv_mul β (finE V (a : GA D V)) hB.1 hL.2
  have hsb := GlobalTheory.ChartStab.isSplitBasis_frCo hfr φ
  let s : SplitAt D.sp.cm.sig V.gram (frameLat V) v :=
    ⟨GlobalTheory.SplitProjChart.emb φ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.frCo φ ((finE V (a : GA D V))⁻¹ * β), isCMExt_host D,
      GlobalTheory.ChartStab.hermND D V, GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm V v, hsb⟩
  have hP : splitPrime (GlobalTheory.SplitProjChart.emb φ) = PP := hemb ▸ hτ
  let ρ : ResF v ≃+* kP PP :=
    (splitResidueEquiv (GlobalTheory.SplitProjChart.emb φ)).symm.trans (Ideal.quotEquivOfEq (congrArg HeightOneSpectrum.asIdeal hP))
  refine ⟨s, ρ, fun k i j => ?_⟩
  obtain ⟨y, hy⟩ := hst k
  have hg0 : ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) = (a : GA D V) * embV V v (k : Gv V v) * (a : GA D V)⁻¹ := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_locFin, Subgroup.coe_inv]
  rw [← hy, redFn_frGL]
  rw [hg0] at hy
  show resS D.host.F PP (y.1 i j) = ρ ((s.red k).1 i j)

  have hg : ∀ x : 𝓞 D.host.E, ((ρ : ResF v →+* kP PP).comp ((IsLocalRing.residue _).comp (GlobalTheory.PlaceRed.rdS φ)))
      (oToS D.host.F D.host.E x) = Ideal.Quotient.mk PP.asIdeal x := by
    intro x
    simp only [RingHom.comp_apply, GlobalTheory.PlaceRed.rdS_oToS]
    have e1 : GlobalTheory.PlaceRed.rdO φ x = splitInt (GlobalTheory.SplitProjChart.emb φ) x := Subtype.ext rfl
    rw [e1, ← splitResidueEquiv_mk]
    show Ideal.quotEquivOfEq (congrArg HeightOneSpectrum.asIdeal hP) ((splitResidueEquiv _).symm (splitResidueEquiv _ _)) = _
    rw [RingEquiv.symm_apply_apply, Ideal.quotEquivOfEq_mk]
  rw [← GlobalTheory.PlaceRed.eq_resS PP _ hg]
  show ρ (IsLocalRing.residue _ (GlobalTheory.PlaceRed.rdS φ (y.1 i j))) = ρ ((s.red k).1 i j)
  congr 1
  have hred : (s.red k).1 i j = IsLocalRing.residue _ ((stabLocEquiv (isCMExt_host D) (GlobalTheory.ChartStab.hermND D V)
      (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat_of_cm D.sp.cm V v) hsb k).1 i j) := by
    show (splitRed _ _ _ _ k).1 i j = _
    rw [splitRed_val]; rfl
  rw [hred]
  congr 1
  apply Subtype.ext
  rw [coe_stabLocEquiv, splitEquivIn_apply]
  exact congrArg (fun m : GL (Fin V.rank) (Fv D.host.F v) => m.1 i j) (map_intGL_eq V φ β (a : GA D V) (k : Gv V v) y hy)

end GlobalTheory.SplitPlaceRed
