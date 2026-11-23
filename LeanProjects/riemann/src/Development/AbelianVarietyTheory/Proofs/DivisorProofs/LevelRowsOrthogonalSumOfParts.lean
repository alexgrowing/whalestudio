import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftCarryingOfBaseTupleRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthogonalRowPartsOfDistinctTypesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupRowsEigenpartsPrincipalLevelEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelRowsEqTypeVectorsOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowPartsFullSphericalAlgebraStableFiniteGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupStableInfTypeSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.RowsSum3

theorem rowTypePart_map_finiteGroup_le {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hE : R.toRealDat.ExAt) (p : A3.fam3.base3.Ix) (g : G) :
    (R.EEp3 p).map (R.gE g) ≤ R.EEp3 p := by
  obtain ⟨hcore, hSF, hEE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hC hE
  simp only [RealDat3.EEp3, Submodule.map_iSup]
  refine iSup_le fun c => iSup_le fun hc => ?_
  refine le_trans ?_ (le_iSup₂_of_le c hc le_rfl)
  rw [hEE]
  exact GlobalTheory.RowPartStable.map_gE_le (s := 0) R.toRealDat F.lv2 hcore _ hSF c g

theorem iSup_EEp_inf_typeSp3 {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hE : R.toRealDat.ExAt) (htop : (⨆ p, R.EEp3 p) = ⊤) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) :
    (⨆ p, (R.toCx3 F).EEp p ⊓ typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ) = typeSp3 A3 (R.toCx3 F) (R.gEx F) P ψ := by
  have hsup : (⨆ p, (R.toCx3 F).EEp p) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have hx : Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) x ∈ ⨆ p, R.EEp3 p := htop ▸ Submodule.mem_top
    exact Submodule.iSup_induction R.EEp3
      (motive := fun y => (Tw.mk (twAt D.what₂.embLL A3.A.v0) y : (R.toCx3 F).EE) ∈ ⨆ p, (R.toCx3 F).EEp p) hx
      (fun p y hy => Submodule.mem_iSup_of_mem (p := (R.toCx3 F).EEp) p hy) (Submodule.zero_mem _)
      fun y z hy hz => Submodule.add_mem _ hy hz
  have hst : ∀ p g, ((R.toCx3 F).EEp p).map (R.gEx F g) ≤ (R.toCx3 F).EEp p := by
    rintro p g _ ⟨x, hx, rfl⟩
    exact rowTypePart_map_finiteGroup_le R F hC hE p g ⟨_, hx, rfl⟩
  have h := GlobalTheory.iSup_stable_inf_typeSpace (R.gEx F) P ((Units.map (A3.A.fam.v0.embedding : D.what₂.LL →+* ℂ).toMonoidHom).comp ψ)
    (R.toCx3 F).EEp (fun _ => True) hst
  simp only [iSup_pos, hsup, top_inf_eq] at h
  exact h.symm

theorem partsE : GlobalTheory.Published.CuspRapidDecay → HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint) → R.PGEquiv F → (∀ b, (lv (F.fc (R.toCx3 F).zs) b).Pos) → (0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) → R.PThmB → ∀ b, (R.toCx3 F).PartsE b := by
  intro hCR hHU D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hLI hOk hC hE hJ hOkH hPG hPos hkl hB b
  have hcar := GlobalTheory.T.thetaLift_carrying_of_base_tuple_rows hCR hHU R F hLI hOk hC hE hJ hPG hPos
  have htop := GlobalTheory.T.iSup_eEp3_eq_whole_space_of_weakCharacterisation R F hC hE (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCR R.toRealDat) hcar
  have hor := GlobalTheory.T.orthogonal_rowParts_of_distinct_types R F hOk hC hOkH hkl hB
  refine ⟨fun p q hpq e he e' he' => ?_, ?_⟩
  · exact (congrArg (cj _) (hor p q hpq _ he.1 _ he'.1)).trans (map_zero _)
  · obtain ⟨h0, h1⟩ := GlobalTheory.LevelRows3.eel_eq_typeSp3 R F hC
    cases b
    · rw [h0]; exact iSup_EEp_inf_typeSp3 R F hC hE htop _ _
    · rw [h1]; exact iSup_EEp_inf_typeSp3 R F hC hE htop _ _

end GlobalTheory.RowsSum3

end
