import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtOntoDivisibleKernel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelValuationDataStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionPointsGroupPairingStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemOrthogonalLabelsAreTorusPointsStatement
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

open GlobalTheory.TorusExt

theorem torus_points_level_weights : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∀ t : S.perp l.yy.ker, ∃ (τ : Multiplicative u.D.toPre.X →* (PadicAlgCl p)ˣ) (q : QkPt u.D.toPre (PadicAlgCl p) S.N), q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU u.U.toUnifPre (PadicAlgCl p) S.N q (x (S.r • (t : S.Gam))) ∧ ∀ β, (τ (Multiplicative.ofAdd β) : PadicAlgCl p) = y₀ (algebraMap o S.R S.ζN) ^ (l.wt β t).val := by
  intro h₁ h₂ hT o Ω _ _ _ _ S ρ p _ y₀ u l hy x hx t
  obtain ⟨hc, -, hA, -, -, -⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy
  obtain ⟨hadd, -⟩ := (GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing h₁ o Ω S ρ p y₀ u).2 x hx
  obtain ⟨τ, q, hq0, hqτ, hq, hval⟩ := GlobalTheory.T.thetaSystem_orthogonal_labels_are_torus_points h₁ h₂ hT o Ω S ρ p y₀ u l hy x hx t
  have hL : LL := (laws_all h₁ h₂).1
  letI := gtGroup u.D.toPre (PadicAlgCl p)
  have hB := u.D.tau_bimult
  have hN : 1 ≤ S.N := le_trans (by norm_num) S.N_ge
  have hx0 : x 0 = 1 := by
    have e := hadd 0 0
    rw [add_zero] at e
    exact mul_eq_left.1 e.symm
  have hpow : ∀ (n : ℕ) (a : S.Gam), x (n • a) = x a ^ n := fun n a => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hx0]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hg : S.N • (S.r • q.g) = iota hB (PadicAlgCl p) q.y := by
    rw [← mul_nsmul, qk_nsmul hB q]
  refine ⟨τ ^ S.r, qkMk hB q.y (S.r • q.g) hg, hq0, ?_, ?_, fun β => ?_⟩
  · rw [isTor_iff, isTorusPtF_iff_eq] at hqτ ⊢
    show S.r • q.g = _
    rw [hqτ, ofMul_pow, map_nsmul]
  · rw [hpow]
    exact (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL u.V _ hA u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N S.r (S.r * S.N) hN S.r_pos
      (mul_comm _ _) (qkMk hB q.y (S.r • q.g) hg) q (x t)).2 rfl ((isNsmul_iff_eq _ _ _).2 rfl) hq
  · obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk β)
    haveI : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by have := S.r_pos; omega) (by omega)⟩
    have hζ : y₀ (algebraMap o S.R S.ζN) ^ S.N = 1 := by
      rw [← map_pow, ← map_pow, ThetaSys.ζN, ← pow_mul,
        show S.r ^ 2 * S.N * S.N = (S.r * S.N) ^ 2 by ring, S.prim.pow_eq_one, map_one, map_one]
    rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, hval a β ha, l.wt_eq a β ha t, ZMod.castHom_apply,
      ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ, ThetaSys.ζN, map_pow, map_pow, ← pow_mul, ← pow_mul]
    congr 1
    ring

end GlobalTheory.TestFibre
end
