import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitMulClauseOfGeneratesIffNonzero
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsExpandsAtOfIntegral
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenPf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.KeyEven.ThetaNorm

theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (IsLocalRing.maximalIdeal V) D A G), ∀ (σ : U.LG.L.Sec) (σ₁ : H0 U.LG.L 1) (f : ∀ α : D.toPre.X, D.toPre.SecB 1 α), NzFib σ → (∀ (i : U.LG.L.ι) (h : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i), σ₁.f (fun _ => i) = resG _ h (σ.f i)) → (∀ e, U.ExpandsAt e 1 σ₁ f) → ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∀ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN → ∀ (ϑ : Fam D.toPre C 1) (c : C), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre C α) (DegPre.famε 1) (ϑ.s α) (D.toPre.famφB α) (DegPre.famε 1) (f α) (DegPre.prB D.toPre C).left 1) → ν.FamV ϑ (c • N.vth) → ‖c‖ = 1 := by
  intro V _ _ _ _ hc D A G _ _ hG U σ σ₁ f hNz hch hE C _ _ _ _ _ _ hC N ν hI ϑ c hϑ hV
  have hL : Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hL4 : Laws4 := GlobalTheory.allSixLaws.2.2.2.1
  have hS : SecBaseChangeSt := hL.secBaseChange
  have h1 : ReciprocityTheory.ChartRestriction.G.DVR.NonzeroOnSpecial U σ₁ := by
    obtain ⟨z, hz, hzn⟩ := hNz (IsLocalRing.closedPoint V)
    refine GlobalTheory.ThetaUnit.nonzeroOnSpecial_of_mem U σ₁ z hz ?_
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hzn
    have hle : LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) ≤ U.LG.L.U i :=
      fun y hy => Set.mem_iInter.1 hy 0
    have hzi : z ∈ U.LG.L.U i := G.left.basicOpen_le _ hi
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, ?_⟩
    rw [hch i hle]
    change z ∈ G.left.basicOpen ((G.left.presheaf.map (homOfLE hle).op) (σ.f i))
    rw [Scheme.basicOpen_res]
    exact ⟨fun _ ⟨k, hk⟩ => hk ▸ hzi, hi⟩
  have hCL : CLND V := (GlobalTheory.ThetaCompare.clnd_iff_of_dvr V).2 hc
  obtain ⟨f', hf', hgen'⟩ := ReciprocityTheory.ChartRestriction.G.DVR.isTheta_of_nonzeroOnSpecial' hL hL4 hCL rfl U σ₁ h1 0
  have hgen := GlobalTheory.ThetaCompare.secBGenerates_of_expandsAt hS le_rfl U.toUnifPre hf' (hE 0) hgen'
  obtain ⟨g, hg⟩ := GlobalTheory.ThetaCompare.exists_corr_right D.toPre ν.th
  have hgg := (GlobalTheory.ThetaCompare.generates_iff_secBGenerates hS hg).1 (fun s => ν.th_gen s)
  have hgs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul (g : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgg
  have hfs := (GlobalTheory.ThetaCompare.secBGenerates_iff_smul ((f 0 : D.toPre.SecB 1 0) : GlobalTheory.ConstFam.SecBMod D.toPre 1 0)).1 hgen
  obtain ⟨u, hu⟩ := (GlobalTheory.ThetaCompare.generates_iff_unit_smul (fun s => (hgs s).exists) _).1 (fun s => (hfs s).exists)
  have hum : ReciprocityTheory.ChartRestriction.G.DVR.SecIsMul D.toPre.P.A.hom (u : V) (f 0) g :=
    (GlobalTheory.ThetaUnit.secIsMul_iff _ _ _ _).2 hu

  let z : Sp C := IsLocalRing.closedPoint C
  have hJ := GlobalTheory.Ex.FamVal.good ν z
  have hcst : ∀ a : C, cst (𝟙 (Sp C)) z a = toStk z a := fun a => by
    rw [cst, ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs_eq _ _ ⊤ trivial, toStk]
    rfl
  have hc0 : N.c 0 = 1 := by
    have h := N.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hx : ∀ x, c * N.th x * ν.rg = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) * (N.th x * ν.rg) := by
    intro x
    have H := (GlobalTheory.Ex.FamVal.famV_iff ν z ϑ _).1 hV 0 x
    have e1 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal (hϑ 0) (GlobalTheory.Ex.FamVal.pt ν x).left z hJ
    have e2 := GlobalTheory.IndivisibleSection.sval_of_secIsMul hum
      ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e3 := ReciprocityTheory.ChartRestriction.G.H1.sval_scal hg ((GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left) z hJ
    have e4 : toStk z (N.th x * ν.rg) = sval ν.th (ν.eA x).left z ν.J :=
      (congrArg (toStk z) (ν.th_eq x)).trans (GlobalTheory.Ex.FamVal.toStk_sF hJ _ _)
    have ep : (GlobalTheory.Ex.FamVal.pt ν x).left ≫ (DegPre.prB D.toPre C).left = (ν.eA x).left := by
      rw [← Over.comp_left, lift_snd]
    rw [map_zero] at H
    rw [Category.comp_id, ep, ← e4] at e3
    rw [ep] at e2
    rw [e1, ep, e2, ← e3] at H
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, pow_one] at H
    have ec : cst ((ν.eA x).left ≫ D.toPre.P.A.hom) z (u : V) =
        toStk z (algebraMap (FractionRing V) C (algebraMap V _ (u : V))) := by
      have ew : (ν.eA x).left ≫ D.toPre.P.A.hom =
          (𝟙 (Sp C) ≫ spMap (algebraMap (FractionRing V) C)) ≫ spMap (algebraMap V (FractionRing V)) := by
        rw [Category.id_comp]; exact Over.w (ν.eA x)
      rw [ew, cst_comp, cst_comp, hcst]
    have ev : N.vth 0 x = N.th x := by
      simp [NumD.vth, N.ψ_zero, hc0]
    rw [ev, ← GlobalTheory.Ex.FamVal.rg_eq, ec, ← map_mul, ← map_mul] at H
    exact (toStk z).injective H
  have hL2 : Laws2 := GlobalTheory.abelianSchemeLaws_all.2
  have hB := GlobalTheory.Ex.brFam hL hL2 V D.toPre D.psi_even D.tau_bimult C N ν 1 le_rfl
  obtain ⟨x, hx0⟩ : ∃ x, N.th x ≠ 0 := by
    by_contra hno
    push_neg at hno
    obtain ⟨s, f0, hf0, hne⟩ := hB.2.2.2.1
    obtain ⟨c', hc'⟩ := hB.2.2.2.2.1 s f0 hf0
    refine hne ?_
    rw [hc']
    funext α y
    simp [NumD.vth, hno]
  have hcu : c = algebraMap (FractionRing V) C (algebraMap V _ (u : V)) := by
    have h := hx x
    rw [_root_.mul_assoc] at h
    exact mul_right_cancel₀ (mul_ne_zero hx0 (GlobalTheory.Ex.FamVal.rg_ne ν)) h
  have n1 := hC.1 (u : V)
  have n2 := hC.1 ((u⁻¹ : Vˣ) : V)
  have hprod : ‖algebraMap (FractionRing V) C (algebraMap V _ (u : V))‖ *
      ‖algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  rw [hcu]
  nlinarith [norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ ((u⁻¹ : Vˣ) : V))),
    norm_nonneg (algebraMap (FractionRing V) C (algebraMap V _ (u : V)))]

end GlobalTheory.KeyEven.ThetaNorm
