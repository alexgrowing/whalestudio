import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AvgLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelCharacterSpaceCoordsIffLevelActsByCharStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemFaceLevelMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrincipalLevelFormOfFaceLevelMultiplicityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalLevelFormMemSpanAdelicRationalFormsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.TopSpan

theorem span_range_map_mem {M N ι : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (f : M →ₗ[ℂ] N)
    (g : ι → M) {y : M} (hy : y ∈ Submodule.span ℂ (Set.range g)) : f y ∈ Submodule.span ℂ (Set.range fun i => f (g i)) := by
  have h := Submodule.mem_map_of_mem (f := f) hy
  rwa [Submodule.map_span, ← Set.range_comp] at h

set_option maxHeartbeats 1000000 in

theorem topSpan : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Seed.PrIso R.MX R.cX R.prX → A.fam.Ok 1 → TopMultH R → ∀ (b : Bool) (t : T), Submodule.span ℂ (Set.range fun x => R.cX.toMap R.prX ((R.HX t).e (R.jX t (rowForm A (F.lvl b).P (F.lvl b).ψ t x)))) = Mult.MultT R.θ R.MX (levS _ R.βX (datXP R t (R.levR F b))) (levChi _ R.βX (datXP R t (R.levR F b))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hB hPr hOk hTop b t
  have hjX : ∀ x, (R.HX t).e (R.jX t x) = R.B.jR t x := hB.models.jX t
  simp only [hjX]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    have hmem : R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x) ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ
        (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ :=
      Bridge.ClassPres.extMem_holds (R.B.R t).pres _
    have hlv := (GlobalTheory.T.levelCharacterSpace_coords_iff_level_acts_by_char _ _ _ (A.fam.R t).r (F.lvl b).P (F.lvl b).ψ (rowForm A (F.lvl b).P (F.lvl b).ψ t x)).1 ⟨x, rfl⟩
    exact GlobalTheory.T.principalLevelForm_mem_faceLevelMultiplicity D G Pl0 T A Ks R F hB b t _ hmem (GlobalTheory.TopSpan.jR_level D G Pl0 T A Ks R F b t _ hlv)
  · intro Tm hT
    obtain ⟨Fn, hF, hQ, rfl⟩ := GlobalTheory.T.exists_principalLevelForm_of_faceLevelMultiplicity D G Pl0 T A Ks R F hB b t Tm hT
    exact span_range_map_mem (R.cX.toMap R.prX) (fun x => R.B.jR t (rowForm A (F.lvl b).P (F.lvl b).ψ t x))
      (GlobalTheory.T.principalLevelForm_mem_span_adelicRationalForms D G Pl0 T A Ks R F b t Fn hF hQ)

end GlobalTheory.TopSpan
