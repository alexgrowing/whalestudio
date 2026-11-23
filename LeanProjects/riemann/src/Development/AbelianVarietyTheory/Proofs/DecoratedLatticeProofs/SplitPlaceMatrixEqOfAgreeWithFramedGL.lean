import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOff

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.OffPlace

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_of_idOff (p : SplitPt D k) {a : Formalism.L2.Theta.AE D} (ha : a ∈ idOff D (· = p.v)) : p.pr a = 0 := by

  have hv : compAt D p.v a = 0 := by
    rw [idOff, Submodule.mem_iInf] at ha
    exact ha ⟨p.v, rfl⟩
  obtain ⟨ε, hε, hsum⟩ := p.above
  obtain ⟨hee, hec, -⟩ := p.split
  obtain ⟨α, hα, hαv, hαw⟩ := hε
  have hparts := placeIdempotent_infinite_and_finite_components D p.v ε α hα

  have hεa : algebraMap (AF D.host.F) (AE D) ε * a = 0 := by
    apply CMAdele_eq_zero_of_infinite_and_finite_components_zero
    · rw [map_mul, hparts.1, zero_mul]
    · intro w
      rw [map_mul, hparts.2 w]
      by_cases hw : w = p.v
      · subst hw
        rw [hv, mul_zero]
      · rw [hαw w hw, TensorProduct.zero_tmul, zero_mul]

  have hea : p.e * a = 0 := by
    have : p.e * algebraMap (AF D.host.F) (AE D) ε = p.e := by
      rw [← hsum, mul_add, hee, hec, add_zero]
    rw [← this, mul_assoc, hεa, mul_zero]
  rw [← p.pr_sec (p.pr a), p.sec_pr, hea, map_zero]

theorem map_pr_of_off : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S : HSp D) (n : Type) [Fintype n] [DecidableEq n] (β : Frame p S n) (κ : GA D S) (g : GL n k), κ * (β.gl g)⁻¹ ∈ grpOff S (· = p.v) → (mt S κ).map p.pr = β.b * g.val * β.b' := by
  intro D k _ _ _ _ p S n _ _ β κ g h
  set γ := κ * (β.gl g)⁻¹ with hγ

  have hq : (mt S γ).map (Ideal.Quotient.mk (idOff D (· = p.v))) = 1 := by
    rw [grpOff, congGrp, MonoidHom.mem_ker] at h
    have := congrArg (fun M : GL (Fin S.rank) (AE D ⧸ idOff D (· = p.v)) => M.val) h
    simpa [Formalism.L2.Theta.mt] using this

  have hγ1 : (mt S γ).map p.pr = 1 := by
    ext i j
    have hij := congrFun (congrFun hq i) j
    have hmem : mt S γ i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D (· = p.v) := by
      rw [← Ideal.Quotient.eq]
      rw [Matrix.map_apply] at hij
      rw [hij, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    have h0 := pr_of_idOff p hmem
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.map_apply, h0, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hκ : κ = γ * β.gl g := by rw [hγ, inv_mul_cancel_right]
  have hmt : mt S κ = mt S γ * mt S (β.gl g) := by
    rw [hκ]
    simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]
  rw [hmt, Matrix.map_mul, hγ1, one_mul, β.gl_mat g]

end GlobalTheory.AdForm.OffPlace
