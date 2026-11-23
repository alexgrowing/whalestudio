import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.RegularClassTraces.RegClassFin
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointRadical
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KernelLocallyFiniteContinuous
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsIsoFrameFirstCols
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp
open Matrix
open scoped Pointwise
open GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.RegInt

namespace GlobalTheory.CompanionTheory.ConeInt

theorem setLIntegral_Ici_rpow_lt_top {a b : ℝ} (ha : a < -1) (hb : 0 < b) :
    ∫⁻ x in Ici b, ENNReal.ofReal (x ^ a) < ⊤ := by
  have h : IntegrableOn (fun x : ℝ => x ^ a) (Ici b) :=
    (integrableOn_Ici_iff_integrableOn_Ioi enorm_ne_top).2 (integrableOn_Ioi_rpow_of_lt ha hb)
  exact h.lintegral_lt_top

theorem le_of_mem_cone {r : ℕ} {c : ℝ} (hc : 0 < c) {t : Fin r → ℝ} (ht : t ∈ cone r c) (i : Fin r) :
    min c 1 ^ r ≤ t i := by
  obtain ⟨hpos, hstep, hlast⟩ := ht
  have hb0 : 0 < min c 1 := lt_min hc one_pos
  have hb1 : min c 1 ≤ 1 := min_le_right _ _
  have key : ∀ (k : ℕ) (i : Fin r), i.val + k + 1 = r → min c 1 ^ (k + 1) ≤ t i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      simpa using (min_le_left c 1).trans (hlast i (by omega))
    | succ k ih =>
      intro i hi
      have hj : i.val + 1 < r := by omega
      have h1 := ih ⟨i.val + 1, hj⟩ (by simp only; omega)
      have h2 := hstep i ⟨i.val + 1, hj⟩ rfl
      have h3 : min c 1 * t ⟨i.val + 1, hj⟩ ≤ c * t ⟨i.val + 1, hj⟩ :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (hpos _).le
      calc min c 1 ^ (k + 1 + 1) = min c 1 * min c 1 ^ (k + 1) := pow_succ' _ _
        _ ≤ min c 1 * t ⟨i.val + 1, hj⟩ := mul_le_mul_of_nonneg_left h1 hb0.le
        _ ≤ t i := h3.trans h2
  have hk : i.val + (r - i.val - 1) + 1 = r := by omega
  refine le_trans ?_ (key (r - i.val - 1) i hk)
  exact pow_le_pow_of_le_one hb0.le hb1 (by omega)

theorem integrand_eq (F : Type) [Field F] [NumberField F] (n : ℕ) {r : ℕ} (m : ℕ) {t : Fin r → ℝ} (ht : ∀ i, 0 < t i) :
    ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) =
      ∏ i, ENNReal.ofReal (t i ^ (-(m : ℝ) -
        ((2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1)) := by
  have hnn : (0 : ℝ) ≤ ∏ i, (t i)⁻¹ ^ m := Finset.prod_nonneg fun i _ => pow_nonneg (inv_pos.2 (ht i)).le _
  rw [← ENNReal.ofReal_mul hnn, ← ENNReal.ofReal_prod_of_nonneg fun i _ => Real.rpow_nonneg (ht i).le _]
  congr 1
  unfold modulus
  rw [← Finset.prod_mul_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h := ht i
  rw [Real.rpow_sub h, Real.rpow_sub h, Real.rpow_neg h.le, Real.rpow_natCast, Real.rpow_intCast, Real.rpow_one,
    inv_pow, mul_inv]
  field_simp

end GlobalTheory.CompanionTheory.ConeInt

namespace GlobalTheory.CompanionTheory.ConeInt

open GlobalTheory.SiegelSet in

theorem lintegral_cone_lt_top : ∀ (F : Type) [Field F] [NumberField F] (n r : ℕ) (c : ℝ), 0 < c → ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    ∫⁻ t in cone r c, ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  intro F _ _ n r c hc
  refine ⟨2 * Module.finrank ℚ F * (2 * r + 1) + 1, fun m hm => ?_⟩
  have hb : 0 < min c 1 ^ r := pow_pos (lt_min hc one_pos) _
  let a : Fin r → ℝ := fun i => -(m : ℝ) -
    ((2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1
  have ha : ∀ i, a i < -1 := by
    intro i
    have hz : (-(m : ℤ)) - 2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) < 0 := by
      have hi : (i.val : ℤ) + 1 ≤ r := by exact_mod_cast i.isLt
      have hm' : 2 * (Module.finrank ℚ F : ℤ) * (2 * r + 1) + 1 ≤ m := by exact_mod_cast hm
      have hd : (0 : ℤ) ≤ 2 * (Module.finrank ℚ F : ℤ) := by positivity
      have hn : (0 : ℤ) ≤ n := by positivity
      have : 2 * (Module.finrank ℚ F : ℤ) * (-(n : ℤ) + 2 * (i.val : ℤ) + 1) ≤
          2 * (Module.finrank ℚ F : ℤ) * (2 * r + 1) :=
        mul_le_mul_of_nonneg_left (by omega) hd
      nlinarith
    have hz' : ((-(m : ℤ) - 2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) < 0 := by
      exact_mod_cast hz
    have : a i = ((-(m : ℤ) - 2 * (Module.finrank ℚ F : ℤ) * ((n : ℤ) - 2 * (i.val : ℤ) - 1) : ℤ) : ℝ) - 1 := by
      simp only [a]; push_cast; ring
    rw [this]; linarith
  have hsub : cone r c ⊆ Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r) :=
    fun t ht i _ => le_of_mem_cone hc ht i
  have hmeas : MeasurableSet (Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r)) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Ici
  calc ∫⁻ t in cone r c, ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹)
      ≤ ∫⁻ t in Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r),
          ENNReal.ofReal (∏ i, (t i)⁻¹ ^ m) * ENNReal.ofReal ((modulus F n t * ∏ i, t i)⁻¹) :=
        lintegral_mono_set hsub
    _ = ∫⁻ t in Set.pi univ fun _ : Fin r => Ici (min c 1 ^ r), ∏ i, ENNReal.ofReal (t i ^ a i) :=
        setLIntegral_congr_fun hmeas fun t ht =>
          integrand_eq F n m fun i => hb.trans_le (ht i (mem_univ i))
    _ = ∏ i, ∫⁻ x in Ici (min c 1 ^ r), ENNReal.ofReal (x ^ a i) := by
        rw [volume_pi, Measure.restrict_pi_pi]
        exact GlobalTheory.RestrMeas.lintegral_fin_prod_eq_prod (E := fun _ => ℝ)
          (f := fun i x => ENNReal.ofReal (x ^ a i))
          fun i => ((measurable_id.pow_const (a i)).ennreal_ofReal).aemeasurable
    _ < ⊤ := ENNReal.prod_lt_top fun i _ => setLIntegral_Ici_rpow_lt_top (ha i) hb

end GlobalTheory.CompanionTheory.ConeInt
