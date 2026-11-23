import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WFormsPartsOfDistinctTypesOrthogonalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalMultiplicityCarriersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeGoodProjectorBaseLevelTwistedModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftCarryingOfBaseTupleRowsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalOperatorsFormsOnRankSpaceNormalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupStableInfTypeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.SumW

theorem tw_sub_eq_map {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : Bool) (V : Submodule ℂ E) :
    Tw.sub c V = V.map (Tw.mkL c E) := by
  ext x
  constructor
  · intro hx; exact ⟨Tw.out x, hx, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact hy

theorem tw_sub_iSup {E ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : Bool) (U : ι → Submodule ℂ E) :
    Tw.sub c (⨆ p, U p) = ⨆ p, Tw.sub c (U p) := by
  simp only [tw_sub_eq_map, Submodule.map_iSup]

theorem inner_tw_eq_zero {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (c : Bool) (x y : Tw c E)
    (h : inner ℂ (Tw.out x) (Tw.out y) = 0) : inner ℂ x y = 0 := by
  rw [Tw.inner_eq, h, map_zero]

theorem iSup_inf_typeSp {G E C K : Type} [Group G] [Fintype G] [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ)
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) (U : C → Submodule ℂ E)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) :
    (⨆ c, U c) ⊓ (⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id)) =
      ⨆ c, U c ⊓ (⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id)) := by
  have := GlobalTheory.iSup_stable_inf_typeSpace ρ P ((Units.map σ.toMonoidHom).comp ψ) U (fun _ => True) hU
  simpa only [iSup_pos trivial, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] using this

theorem iSup_inf_inf_typeSp {G E C K : Type} [Group G] [Fintype G] [Field K] [AddCommGroup E] [Module ℂ E] (σ : K →+* ℂ)
    (ρ : Representation ℂ G E) (P : Subgroup G) (ψ : P →* Kˣ) (U : C → Submodule ℂ E) (R0 : Submodule ℂ E)
    (hU : ∀ c g, (U c).map (ρ g) ≤ U c) (hsum : (⨆ c, U c) = R0) :
    (⨆ c, U c ⊓ (R0 ⊓ ⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id))) =
      R0 ⊓ ⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id) := by
  have hle : ∀ c, U c ≤ R0 := fun c => hsum ▸ le_iSup U c
  have h1 := iSup_inf_typeSp σ ρ P ψ U hU
  set Kt := ⨅ h : P, LinearMap.ker (ρ (h : G) - (σ ((ψ h : Kˣ) : K)) • LinearMap.id) with hKt
  calc (⨆ c, U c ⊓ (R0 ⊓ Kt)) = ⨆ c, U c ⊓ Kt :=
        iSup_congr fun c => by rw [← inf_assoc, inf_of_le_left (hle c)]
    _ = (⨆ c, U c) ⊓ Kt := h1.symm
    _ = R0 ⊓ Kt := by rw [hsum]

theorem partsW_base : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → R.toRealDat.LUnif → (R.toCx3 F).PartsW false := by
  intro hCRD hHowe D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hW hEx hInert hGS hCD hME hOkH hPG hPos hkap hB hU
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R.toRealDat
  obtain ⟨hCore, hSF, -, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hcar := GlobalTheory.T.thetaLift_carrying_of_base_tuple_rows hCRD hHowe R F hLI hOk hW hEx hInert hPG hPos
  have hspan := GlobalTheory.T.cuspidal_multiplicity_carriers R F hOk hW hEx hS hGS hCD hME hcar
  have horth := GlobalTheory.T.W_forms_parts_of_distinct_types_orthogonal R F hOk hW hEx hS hOkH hkap hB
  intro j
  have htype := GlobalTheory.T.range_goodProjector_baseLevel_twistedModel R F hOk hW hEx hU j
  refine ⟨fun p q hpq w hw w' hw' => ?_, ?_⟩
  · exact inner_tw_eq_zero (E := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) w w' (horth j p q hpq _ hw.1 _ hw'.1)
  · obtain ⟨-, -, -, -, -, hst, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hS hirr R.SF hSF j
    have hstab : ∀ p g, (R.Wp3 j p).map (R.gW j (sg0 D A3.A) g) ≤ R.Wp3 j p := by
      intro p g
      unfold RealDat3.Wp3
      simp only [Submodule.map_iSup]
      exact iSup₂_mono fun c _ => by rw [hWc]; exact hst c g
    have hstabX : ∀ p g, ((R.toCx3 F).Wp j p).map (R.gWx F j g) ≤ (R.toCx3 F).Wp j p := by
      rintro p g _ ⟨y, hy, rfl⟩
      exact hstab p g (Submodule.mem_map_of_mem hy)
    have hsumX : (⨆ p, (R.toCx3 F).Wp j p) =
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat j)) :=
      (tw_sub_iSup (twAt D.what₂.embLL A3.A.v0) (R.Wp3 j)).symm.trans
        (congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) (hspan j))
    rw [htype]
    unfold typeSubspace
    exact iSup_inf_inf_typeSp _ (R.gWx F j) F.P0 F.ψ0⁻¹ ((R.toCx3 F).Wp j) _ hstabX hsumX

end GlobalTheory.SumW
