import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.LocalComponentGL

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (WModel.nf WModel.norm_def WModel.abv_le_one_iff WModel.abv_le_pow_iff)

attribute [local instance] Formalism.InvariantFactorPaths.G7.WModel.nf

variable (p : ℕ) [hp : Fact p.Prime]

theorem sx_charZero : CharZero (K0 p) := inferInstance

attribute [local instance] sx_charZero

theorem sx_norm_le_one_iff (x : K0 p) : ‖x‖ ≤ 1 ↔ ∃ w : WW p, algebraMap (WW p) (K0 p) w = x := by
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  exact Formalism.InvariantFactorPaths.G7.WModel.abv_le_one_iff p x

theorem sx_norm_le_inv_iff (x : K0 p) :
    ‖x‖ ≤ (p : ℝ)⁻¹ ↔ ∃ w : WW p, x = (p : K0 p) * algebraMap (WW p) (K0 p) w := by
  have h := Formalism.InvariantFactorPaths.G7.WModel.abv_le_pow_iff p 1 x
  rw [pow_one, pow_one] at h
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  exact h

theorem sx_norm_p : ‖(p : K0 p)‖ = (p : ℝ)⁻¹ := by
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  exact Formalism.InvariantFactorPaths.G7.WModel.abv_p p

theorem sx_ultra : IsUltrametricDist (K0 p) := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def, Formalism.InvariantFactorPaths.G7.WModel.norm_def, Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  exact Formalism.InvariantFactorPaths.G7.WModel.abv_nonarch p x y

theorem sx_sigK_eq : (sigK p).toRingHom = Formalism.InvariantFactorPaths.G7.WModel.sig p := by
  apply IsLocalization.ringHom_ext (nonZeroDivisors (WW p))
  ext w
  simp [sigK, Formalism.InvariantFactorPaths.G7.WModel.sig, IsLocalization.map_eq]

theorem sx_sig_frob (a : K0 p) (ha : ‖a‖ ≤ 1) : ‖(sigK p).toRingHom a - a ^ p‖ ≤ (p : ℝ)⁻¹ := by
  rw [sx_sigK_eq, Formalism.InvariantFactorPaths.G7.WModel.norm_def]
  rw [Formalism.InvariantFactorPaths.G7.WModel.norm_def] at ha
  exact Formalism.InvariantFactorPaths.G7.WModel.abv_sig p a ha

theorem sx_integral_iff {ι : Type} (f : MvPowerSeries ι (K0 p)) : Integral f ↔ IntS p f := by
  constructor
  · intro h
    choose g hg using fun n => (sx_norm_le_one_iff p (MvPowerSeries.coeff n f)).mp (h n)
    refine ⟨fun n => g n, ?_⟩
    ext n
    exact (hg n).symm
  · rintro ⟨g, rfl⟩ n
    exact (sx_norm_le_one_iff p _).mpr ⟨_, rfl⟩

theorem sx_expS_eq {ι : Type} {f : MvPowerSeries ι (K0 p)} (hf : MvPowerSeries.constantCoeff f = 0) :
    expS p f = mvExp f := by
  ext n
  unfold mvExp
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hf)]
  have hord : (1 : ℕ∞) ≤ f.order := by
    apply MvPowerSeries.le_order
    intro d hd
    have hd0 : d = 0 := by
      have : Finsupp.degree d = 0 := by exact_mod_cast Nat.lt_one_iff.mp (by exact_mod_cast hd)
      exact (Finsupp.degree_eq_zero_iff d).mp this
    rw [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff]
    exact hf
  have hz : ∀ d : ℕ, Finsupp.degree n < d → MvPowerSeries.coeff n (f ^ d) = 0 := by
    intro d hd
    apply MvPowerSeries.coeff_of_lt_order
    calc ((Finsupp.degree n : ℕ) : ℕ∞) < d := by exact_mod_cast hd
      _ = d • (1 : ℕ∞) := by simp
      _ ≤ d • f.order := nsmul_le_nsmul_right hord d
      _ ≤ (f ^ d).order := MvPowerSeries.le_order_pow d
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (Finsupp.degree n + 1))]
  · show ∑ k ∈ Finset.range (n.degree + 1), ((k.factorial : K0 p))⁻¹ * MvPowerSeries.coeff n (f ^ k) = _
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_exp, smul_eq_mul]
    simp
  · intro d hd
    rw [Function.mem_support] at hd
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra h
    push_neg at h
    apply hd
    rw [hz d (by omega), smul_zero]

theorem sx_div_p_iff {ι : Type} (f : MvPowerSeries ι (K0 p)) :
    (∀ n, ‖MvPowerSeries.coeff n f‖ ≤ (p : ℝ)⁻¹) ↔
      ∃ Q : MvPowerSeries ι (WW p), f = (p : K0 p) • MvPowerSeries.map (algebraMap (WW p) (K0 p)) Q := by
  constructor
  · intro h
    choose g hg using fun n => (sx_norm_le_inv_iff p (MvPowerSeries.coeff n f)).mp (h n)
    refine ⟨fun n => g n, ?_⟩
    ext n
    simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, smul_eq_mul]
    exact hg n
  · rintro ⟨Q, rfl⟩ n
    simp only [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map, smul_eq_mul]
    exact (sx_norm_le_inv_iff p _).mpr ⟨_, rfl⟩

theorem sx_dwork : DworkLemma p := by
  intro _ n Ps h0
  have := sx_ultra p
  have h := Formalism.InvariantFactorPaths.G7.dwork_multivariable (K0 p) (Fin n) p (sigK p).toRingHom hp.out (sx_norm_p p) (sx_sig_frob p) Ps h0
  rw [sx_expS_eq p h0, ← sx_integral_iff, h, sx_div_p_iff]
  unfold Formalism.InvariantFactorPaths.G7.frobVar
  rw [MvPowerSeries.smul_eq_C_mul]

theorem positivity_condition_holds (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.FormalGroupSystem.adm1 D := fun p _ => sx_dwork p

end Formalism.MainNotions.FormalGroupSystem.Pf
