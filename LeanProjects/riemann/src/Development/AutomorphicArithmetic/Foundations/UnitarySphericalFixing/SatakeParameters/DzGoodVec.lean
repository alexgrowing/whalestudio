import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTypeVector
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodLem
import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.ClassMapD

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
open Formalism.MainNotions.ArithmeticCylinders Formalism.MainNotions.PrimeDegreeVariant GlobalTheory.TypeLeaf
namespace DiscreteGroups.sglob.DzType.Rt

theorem good_of_vector_row_m : ∀ (D : D7) (Rw : GlobalTheory.HeightCounting.RowSide D) (L : ∀ k, LabelDatum (D.host.g k)) (rc : GlobalTheory.SerSys.Corr D) (cp : GlobalTheory.GoodTypes.Comp D), LabTie D L → DiscreteGroups.sglob.DzType.Rt.LabParamLe D.R.nV D L rc → (∀ k v, GlobalTheory.SerSys.IsClassMapD D.naut.lpDim (rc k v)) → GlobalTheory.GoodTypes.SeriesConj D → (∀ σ k v, IrrSm (cp σ k v) ∧ Rw.locR σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v)) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (G0g D.nd) V) (W : Submodule ℂ V) (σ : D.what₂.FT), (∀ k v, GlobalTheory.GoodTypes.ConjIn ρ W (GlobalTheory.GoodTypes.facHom D k v) (cp σ k v).ρ) → ∀ x : V, x ≠ 0 → (∀ a, ρ.asAlgebraHom a x ∈ W) → ρ.asAlgebraHom D.ntypes.e0 x = x → D.nd.goodRow σ := by
  intro D Rw L rc cp hT hLP hCl hC hP V _ _ ρ W σ hW x hx hxW he
  obtain ⟨t, a, ht, h0, hfix⟩ := GlobalTheory.GoodTypes.exists_good D ρ hx he
  have key : ∀ k v, GlobalTheory.SeriesSupportTest.dualFun D k (t k v) = D.nd.lab k σ v := by
    intro k v
    have hl : IsLabel D k (t k v) := (ht k).1.1 v
    have h1 := hfix k v
    rw [GlobalTheory.GoodTypes.act_atPlace] at h1
    have h2 := (hW k v).act_ne _ (D.ntypes.eSer k (dualLab D k (t k v))) (fun y => by
      rw [← GlobalTheory.GoodTypes.labAct_conj D k hl, ← hC k _ hl, Finsupp.mapRange_apply]; rfl) (hxW a) h0 h1
    obtain ⟨p1, p3⟩ := hP σ k v
    have q1 := ((hCl k v) _ _ p1).1
    rw [(hT k).2] at h2
    have h3 := hLP k v D.R.r (DiscreteGroups.sglob.DzType.Rt.r_le_nV D) (cp σ k v) p1 _ h2
    rw [(hT k).1] at h3
    simp only [] at h3
    rw [← p3] at h3 q1
    rw [D.ntypes.inertiaCharpoly_type k v _ (by rw [← Rw.lab_eq, q1, (D.nd.lab_monic k σ v).2]), ← Rw.lab_eq] at h3
    rw [GlobalTheory.SeriesSupportTest.dualFun, if_pos hl]
    exact GlobalTheory.GoodTypes.eq_of_teich _ (GlobalTheory.Compare.TeichmullerRoots.teich_injective _ (D.ntypes.teichC_inj k))
      (GlobalTheory.SeriesSupportTest.label_dual D k hl).1 (D.nd.lab_monic k σ v).1 h3.symm
  have hd := GlobalTheory.SeriesSupportTest.good_dualFun D t ht
  simp only [key] at hd
  exact hd

end DiscreteGroups.sglob.DzType.Rt
end
