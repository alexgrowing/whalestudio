import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTeichmullerLogUnitBcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltUniformizerPowEqMulUnitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKummerCocycleTiltUniformizerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTruncLogGalModFilStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KummerNotCoboundary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltOfTiltRootFlatAlgebraicAndGaloisFix
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.LogFlat

theorem rootT_cocycle_of_pow_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (g : GQ l) (y ϖ x : Per.Fl l) (n : ℕ) (a b : ℤ_[l]),
    y ^ n = ϖ * x → ϖ.untilt ≠ 0 →
    (∀ m, rootT (Per.σF g y) m = rootT C.ε m ^ (PadicInt.toZModPow m a).val * rootT y m) →
    (∀ m, rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m b).val * rootT ϖ m) →
    ∀ m, rootT (Per.σF g x) m = rootT C.ε m ^ (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val * rootT x m := by
  intro l _ C g y ϖ x n a b hyx hϖ ha hb m
  have hmul : ∀ u v : Per.Fl l, rootT (u * v) m = rootT u m * rootT v m := by
    intro u v; simp only [rootT, iterate_map_mul, map_mul]
  have hpow : ∀ u : Per.Fl l, rootT (u ^ n) m = rootT u m ^ n := by
    intro u; simp only [rootT, iterate_map_pow, map_pow]
  have hζ : rootT C.ε m ^ (l ^ m) = 1 := by
    rw [rootT_pow_eq_untilt]; exact (core_isEps l C).1
  have hϖm : rootT ϖ m ≠ 0 := by
    intro h0; apply hϖ; rw [← rootT_pow_eq_untilt, h0, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)]
  have hζ0 : ∀ k : ℕ, rootT C.ε m ^ k ≠ 0 := by
    intro k h0
    have : rootT C.ε m = 0 := pow_eq_zero_iff'.mp h0 |>.1
    rw [this, zero_pow (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)] at hζ
    exact zero_ne_one hζ
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  set A := (PadicInt.toZModPow m a).val
  set B := (PadicInt.toZModPow m b).val
  set Cc := (PadicInt.toZModPow m ((n : ℤ_[l]) * a - b)).val
  have hexp : rootT C.ε m ^ (n * A) = rootT C.ε m ^ (B + Cc) := by
    rw [pow_eq_pow_mod (n * A) hζ, pow_eq_pow_mod (B + Cc) hζ]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff']
    simp only [A, B, Cc, Nat.cast_mul, Nat.cast_add, ZMod.natCast_val, ZMod.cast_id', id, map_sub, map_mul,
      map_natCast]
    ring
  have h1 : rootT ((Per.σF g y) ^ n) m = rootT (Per.σF g ϖ * Per.σF g x) m := by
    rw [← map_pow, ← map_mul, hyx]
  rw [hpow, hmul, ha, hb, mul_pow, ← pow_mul, ← hpow y, hyx, hmul, mul_comm A n, hexp] at h1
  have h2 : rootT C.ε m ^ B * (rootT ϖ m * rootT ((Per.σF g) x) m) =
      rootT C.ε m ^ B * (rootT ϖ m * (rootT C.ε m ^ Cc * rootT x m)) := by
    rw [pow_add] at h1; linear_combination -h1
  have h3 := mul_left_cancel₀ (hζ0 B) h2
  exact mul_left_cancel₀ hϖm h3

theorem rootT_σF_tilt_l : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (C : Core l), C.ζ = P.ζQ → ∀ ϖ : Per.Fl l,
    (∀ m : ℕ, (rootT ϖ m : ℂ_[l]) = algebraMap (Om l) ℂ_[l] (lRoot l m)) → ∀ (g : GQ l) (m : ℕ),
    rootT (Per.σF g ϖ) m = rootT C.ε m ^ (PadicInt.toZModPow m (kummer P g)).val * rootT ϖ m := by
  intro l _ P C hζ ϖ hr g m
  have hit : ∀ k : ℕ, ((frobeniusEquiv (Per.Fl l) l).symm)^[k] (Per.σF g ϖ) =
      Per.σF g (((frobeniusEquiv (Per.Fl l) l).symm)^[k] ϖ) := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, RingHom.map_frobeniusEquiv_symm]
  have hsig : rootT (Per.σF g ϖ) m = Per.σO g (rootT ϖ m) := by
    rw [rootT, hit, GlobalTheory.RingBasics.untilt_σF]; rfl
  rw [hsig]
  apply Subtype.ext
  have h1 : ((Per.σO g (rootT ϖ m) : Per.OC l) : ℂ_[l]) = Per.σC g (rootT ϖ m : ℂ_[l]) :=
    GlobalTheory.RingIface.sigO_coe l g _
  have h2 : Per.σC g (algebraMap (Om l) ℂ_[l] (lRoot l m)) = algebraMap (Om l) ℂ_[l] (g (lRoot l m)) :=
    GlobalTheory.RingBasics.σC_coe g _
  push_cast
  rw [h1, hr, h2, isKummer_kummer P g m, map_mul, map_pow, C.ε_root, hζ]

theorem exists_log_flat_pow_Bst : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (_ : True), ∃ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) ∧ (∀ g, bk.FixFlat g → c g = 0) ∧ ∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m := by
  intro l _ K bk P AI T C hF _
  obtain ⟨ϖ, hr⟩ := GlobalTheory.Pst.NoLog.exists_tilt (lRoot l) (lRoot_succ l) l (lRoot_zero l)
  have hϖ : ϖ.untilt = ((l : ℕ) : Per.OC l) := Subtype.ext (by
    have := hr 0
    rw [lRoot_zero, map_natCast] at this
    exact this.trans (SubringClass.coe_natCast _ _).symm)
  obtain ⟨x, hxu, hx⟩ := GlobalTheory.T.tilt_uniformizer_pow_eq_mul_unit l K bk ϖ hϖ
  obtain ⟨cπ, hcπ, hfix⟩ := GlobalTheory.T.exists_kummer_cocycle_tilt_uniformizer l K bk C
  obtain ⟨bx, hφ, hgal⟩ := GlobalTheory.T.exists_teichmuller_log_unit_bcris l C x hxu
  have hϖ0 : ϖ.untilt ≠ 0 := by
    rw [hϖ]; exact_mod_cast (Fact.out : l.Prime).ne_zero
  refine ⟨T.eB.symm bx, fun g => (bk.Ep.natDegree : ℤ_[l]) * cπ g, ⟨fun g => ?_, ?_⟩,
    fun g hg => by simp [hfix g hg], GlobalTheory.T.exists_truncLog_gal_mod_filP l K bk C cπ hcπ⟩
  · have hx' := rootT_cocycle_of_pow_eq_mul l C (g : GQ l) bk.flat ϖ x bk.Ep.natDegree (cπ g) (kummer P g) hx hϖ0 (hcπ g)
      (rootT_σF_tilt_l l P C hF.ζ ϖ hr g)
    have h1 := hgal (g : GQ l) _ hx'
    have h2 : P.actQ (g : GQ l) (T.eB.symm bx) = T.eB.symm bx +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      apply T.eB.injective
      rw [T.actB, RingEquiv.apply_symm_apply, h1, map_add, RingEquiv.apply_symm_apply, Algebra.smul_def, map_mul,
        T.zB, hF.t]
    rw [map_add, actSt_X, actSt_C, h2, Polynomial.C_add]
    have key : ((kummer P (g : GQ l) : ℤ_[l]) : ℚ_[l]) • P.tB +
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g - kummer P g : ℤ_[l]) : ℚ_[l]) • P.tB =
        (((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB := by
      rw [← add_smul]; congr 1; push_cast; ring
    show _ = _ + Polynomial.C ((((bk.Ep.natDegree : ℤ_[l]) * cπ g : ℤ_[l]) : ℚ_[l]) • P.tB)
    rw [← key, Polynomial.C_add]; ring
  · have h2 : P.φB (T.eB.symm bx) = (l : P.R.B) * T.eB.symm bx := by
      apply T.eB.injective
      rw [T.frob, RingEquiv.apply_symm_apply, hφ, map_mul, map_natCast, RingEquiv.apply_symm_apply]
    rw [map_add, phiSt_X, phiSt_C, h2, mul_add, Polynomial.C_mul, map_natCast]

end GlobalTheory.LogFlat

end
