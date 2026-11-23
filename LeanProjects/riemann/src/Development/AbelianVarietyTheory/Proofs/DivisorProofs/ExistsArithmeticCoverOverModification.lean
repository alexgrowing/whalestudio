import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleProductOfEach
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPointClosureDimBasicProjArithAmbient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointClosureDimLeAndResidueDegreeNeZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreimagePositiveResidueDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueDegreeOfIsOpenImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverLift

open Limits GlobalTheory.MixHt

theorem exists_cover_over_modification : ∀ (k : Type) [CommRing k] (X X' Y : Scheme.{0}) [IsIntegral X] [IsIntegral X']
    [IsIntegral Y] (p : X ⟶ Sp k) (D E : ℕ) (ρ : X' ⟶ X) (π : Y ⟶ X), IsArithVar p D → IsArithVar (ρ ≫ p) D →
    IsArithVar (π ≫ p) E → ρ (genericPoint X') = genericPoint X →
    ∃ (Y' : Scheme.{0}) (_ : IsIntegral Y') (g : Y' ⟶ Y) (π' : Y' ⟶ X'), π' ≫ ρ = g ≫ π ∧
      IsArithVar (g ≫ π ≫ p) E ∧ g (genericPoint Y') = genericPoint Y ∧
      g.residueDegree (genericPoint Y') ≠ 0 := by
  intro k _ X X' Y _ _ _ p D E ρ π hX hX' hY hρ

  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  obtain ⟨N', j', _, hj'⟩ := hX'.isProjOver
  have : IsProper (ρ ≫ p) := hj' ▸ inferInstance
  have : IsProper ρ := IsProper.of_comp ρ p
  have hs : Function.Surjective ρ := by
    rw [← Set.range_eq_univ]
    refine Set.eq_univ_of_univ_subset ?_
    rw [← (genericPoint_spec X).def, ← ρ.isClosedMap.isClosed_range.closure_eq]
    exact closure_mono (Set.singleton_subset_iff.2 ⟨_, hρ⟩)
  have : Surjective ρ := ⟨hs⟩

  obtain ⟨z, hz, hdeg⟩ := exists_residueDegree_pos_of_mem_range _ _ (pullback.fst π ρ) (genericPoint Y)
    ((inferInstance : Surjective (pullback.fst π ρ)).surj _)
  set g := cloι z ≫ pullback.fst π ρ with hgdef
  have hg : g (genericPoint (clo z)) = genericPoint Y := by
    rw [hgdef, Scheme.Hom.comp_apply, cloι_genericPoint, hz]
  have hdeg' : g.residueDegree (genericPoint (clo z)) ≠ 0 := by
    rw [hgdef, CurveDegreesCompare.residueDegree_comp, Published.residueDegree_of_isClosedImmersion (cloι z), mul_one,
      cloι_genericPoint]
    exact hdeg.ne'

  have hP : IsProjOver (pullback.fst π ρ ≫ π ≫ p) :=
    FlagFamily.isProjOver_pullback_over hX.isProjOver hY.isProjOver hX'.isProjOver
  have hA : IsAmb (g ≫ π ≫ p) := by
    have := (IsAmb.mk hX.1 hX.2 hP).sub (cloι z)
    rwa [← Category.assoc] at this
  have hAY : IsAmb (π ≫ p) := isAmb_of_isArithVar hY

  obtain ⟨⟨m, hm⟩, -, -, -, -, hgen⟩ := hasDim_basic k (clo z) (g ≫ π ≫ p) hA
  obtain ⟨d, -, hd⟩ := hm (genericPoint (clo z))
  have hdY : HasDim (g (genericPoint (clo z))) (E + 1) := by
    rw [hg]
    exact (DimBasic.hasDim_genericPoint_iff Y (E + 1)).2 hY.dim_eq
  have hcmp := DimDeg.dim_le_and_residueDegree_ne_zero_iff k Y (clo z) (π ≫ p) (g ≫ π ≫ p) hAY hA g rfl
    (genericPoint (clo z)) d (E + 1) hd hdY
  have hdim : topologicalKrullDim (clo z) = (E + 1 : ℕ) := (hgen (clo z) (E + 1)).1 (hcmp.2.1 hdeg' ▸ hd)

  have hcY : CharZero Γ(Y, ⊤) := hY.charZero
  have h₁ : CharZero Y.functionField :=
    charZero_of_injective_ringHom (fnOf_injective (⊤ : Y.Opens) (Opens.mem_top _))
  have h₂ : CharZero (Y.residueField (genericPoint Y)) := by
    let f : Y.functionField →+* Y.residueField (genericPoint Y) := (Y.residue _).hom
    exact charZero_of_injective_ringHom f.injective
  have h₃ : CharZero (Y.residueField (g (genericPoint (clo z)))) := hg ▸ h₂
  have h₄ : CharZero ((clo z).residueField (genericPoint (clo z))) :=
    charZero_of_injective_ringHom (g.residueFieldMap _).hom.injective
  have h₅ : CharZero (clo z).functionField := by
    let f : (clo z).functionField →+* (clo z).residueField (genericPoint (clo z)) := ((clo z).residue _).hom
    exact (RingHom.charZero_iff f.injective).2 h₄
  have h₆ : CharZero Γ(clo z, ⊤) :=
    (RingHom.charZero_iff (fnOf_injective (⊤ : (clo z).Opens) (Opens.mem_top _))).2 h₅
  refine ⟨clo z, inferInstance, g, cloι z ≫ pullback.snd π ρ, ?_,
    ⟨hX.1, hX.2, inferInstance, hA.isProjOver, (flat_int_iff_charZero _).2 h₆, hdim⟩, hg, hdeg'⟩
  rw [Category.assoc, ← pullback.condition, ← Category.assoc]

end GlobalTheory.CoverLift
