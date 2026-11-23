import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNormPull
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricLiftActionGeometricFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

open GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

theorem exists_secsOver : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∃ rig e th s, SecsOver u x rig e th s := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u x hx
  obtain ⟨w, hw⟩ := u.lb
  have hp := u.cart
  have hL₀ := ρ.P.isLB
  have hL₁ := u.A.isLB
  have := u.A.isAb.comm
  have := ρ.P.isAb.comm
  let τ : (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have hτ : τ ≫ (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun q => spMap q) u.fac.symm
  have hx' : ∀ a, (x a).left ≫ u.φ = τ ≫ (ρ.pt a).left := hx
  obtain ⟨rig, hrig, Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec u.A.A) (φ := fun _ => eSec ρ.P.A)
    (ε := fun _ => 1) (h := spMap u.yK) hw hL₀ hL₁ (fun _ => PolBaseChange.eSec_comm hp) ρ.rig ρ.rig_gen
  choose e he He using fun a => exists_gen_through (φ' := fun _ : Fin 1 => (x a).left) (h := τ) hw hL₀ hL₁
    (fun _ => hx' a) (ρ.fr a) (ρ.fr_tors a).2.1
  have hfr : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) := fun a =>
    FrameMove.isTorsFrame_move hp hw
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx' a) (ρ.fr_tors a) (he a) (fun z J J' hJ hJ' => by
        have := He a _ (𝟙 _) z J J' hJ hJ'
        rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this)
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ ρ.th₁
  choose s hs using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (ρ.s i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have hpow : ∀ (n : ℕ) a, ρ.pt (n • a) = ρ.pt a ^ n := fun n a => by
    induction n with
    | zero =>
      have h := ρ.pt_add 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hN : ∀ a, x (S.r • a) ^ S.N = 1 := fun a => FrameMove.pow_eq_one_of hp (hx' _) (by
    rw [hpow, ← pow_mul]
    exact (ρ.fr_tors a).1)
  refine ⟨rig, e, th, s, hrig, hfr, fun a z J hJ => ?_, fun i a z J hJ => ?_,
    ⟨α, hα, ThetaGeom.norm_move hp τ hτ hL₀ hL₁ Hr vα ρ.α_norm,
      isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) hα vα hth (hs ρ.i₀) ρ.s_zero⟩, fun a => ?_⟩
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (He a) hth (ρ.th_val a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    rw [ThetaGeom.val_powFrame, Nat.cast_one, zpow_one]
    exact q
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (ThetaGeom.genThrough_pow τ (He a) S.N) (hs i)
      (ρ.ev_val i a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    exact q
  · obtain ⟨θ, hθ, H⟩ := ClassWeight.symLift_act_move hp τ hτ hw hL₀ hL₁ (hx' _).symm (hN a) (ρ.U_sym a)
      (fun l i => fn (algebraMap o S.R (S.ρ a l i))) (fun l i => cF u.V (y₀ (algebraMap o S.R (S.ρ a l i))))
      (fun l i => spMap_appTop_fn y₀ _) hs (ρ.U_act a)
    exact ⟨θ, hθ, fun i σ h => (ThetaGeom.comb_iff _ _ _).2 (H i σ h)⟩

end GlobalTheory.TestFibre
end
