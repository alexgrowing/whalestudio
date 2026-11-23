import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteHeightBreuilKisinLatticeSemistableStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsGaloisFixingFlatStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPeriodIsUnitWittTiltAndNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiscMaps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscPeriodDataOfAcrisPeriods
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.WPre

theorem map_smul_hom {R S F : Type*} [CommRing R] [CommRing S] [FunLike F R S] [RingHomClass F R S] {m n : Type*}
    (f : F) (c : R) (M : Matrix m n R) : (c • M).map f = f c • M.map f :=
  Matrix.ext fun i j => by simp

theorem smul_cancel {R : Type*} [CommRing R] {m n : Type*} {c : R} (hc : IsUnit c) {M M' : Matrix m n R}
    (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact hc.mul_left_cancel this

end GlobalTheory.BKLim.WPre

namespace GlobalTheory.BKLim

open GlobalTheory.BKLim.WPre in

theorem exists_pre_of_wseed : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ), ∃ (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T ∧ IsUnit Z ∧ ∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap bk.ev i → s.W * Z.map i = Y.map bk.iA := by
  intro l _ K bk τ hτ d ρ hρ s
  classical
  obtain ⟨Y, Z, b, A, A', hYu, hZu, hWZ, hAA', hφY⟩ := GlobalTheory.T.exists_finiteHeight_breuilKisin_lattice_semistable l K bk τ hτ d ρ hρ s
  obtain ⟨htu, -, -, hστ⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  obtain ⟨hmaps, hgal, -, h0, -, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  obtain ⟨i0, hi0⟩ := hmaps bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 h0 (by rw [pow_one]) (by rw [pow_one])
  have hinj : Function.Injective bk.iA := GlobalTheory.BSP.SeedAsm.iA_injective bk
  obtain ⟨u, hu⟩ := htu
  set n := s.N with hn
  set t := inclW l τ with ht
  set e := bk.evW bk.E with he
  set T : Matrix (Fin d) (Fin d) (WCb l) := (u⁻¹ ^ n : (WCb l)ˣ) • Y.map (inclW l) with hT
  have hYT : Y.map (inclW l) = t ^ n • T := by
    rw [hT, Units.smul_def, smul_smul, ← hu, Units.val_pow_eq_pow_val, ← mul_pow, Units.mul_inv, one_pow, one_smul]
  have htn : IsUnit (t ^ n) := by rw [← hu]; exact (Units.isUnit u).pow n

  have hft : frobW l t = e * t := by
    rw [ht, GlobalTheory.Prism.frobW_inclW, hτ.1, map_mul]; rfl
  have hφT : e ^ n • T.map (frobW l) = T * A.map bk.evW := by
    have h1 := congrArg (fun M => Matrix.map M (inclW l)) hφY
    simp only [Matrix.map_mul] at h1
    have h2 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
      ext i j; simp [GlobalTheory.Prism.frobW_inclW]
    rw [h2, hYT, show (A.map bk.ev).map (inclW l) = A.map bk.evW from rfl] at h1
    apply smul_cancel htn
    calc t ^ n • e ^ n • T.map (frobW l) = (t ^ n • T).map (frobW l) := by
          rw [map_smul_hom, map_pow, hft, mul_pow, mul_comm, smul_smul]
      _ = t ^ n • (T * A.map bk.evW) := by rw [h1, Matrix.smul_mul]

  have hfix : ∀ g : ↥(GK K), bk.FixFlat g → zW (ρ g) * T.map (galW l (g : GQ l)) = T := by
    intro g hg
    obtain ⟨G, hG⟩ := hgal bk.ρ₀ h0 (g : GQ l)
    obtain ⟨hGfix, hGW⟩ := GlobalTheory.T.semistable_periods_galois_fixing_flat l K bk τ hτ d ρ hρ s g hg G hG
    set R := (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) with hR
    have hGZ : (Z.map i0).map G = Z.map i0 := by
      exact Matrix.ext fun i j => hGfix i0 hi0 _
    have hYG : (Y.map (Per.σA (g : GQ l))).map bk.iA = (Y.map bk.iA).map G := by
      exact Matrix.ext fun i j => (hG.ext _).symm
    have hA1 : (τ ^ n • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l)))).map bk.iA =
        (Per.σA (g : GQ l) τ ^ n • Y).map bk.iA := by
      rw [map_smul_hom, map_smul_hom, Matrix.map_mul, hYG, ← hWZ i0 hi0, Matrix.map_mul, hGZ, map_pow, map_pow,
        show ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA = R from Matrix.ext fun i j => rfl, ← Matrix.mul_assoc,
        ← Matrix.smul_mul, hGW, Matrix.smul_mul, ← hG.ext]
    have hA2 : τ ^ n • ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) =
        Per.σA (g : GQ l) τ ^ n • Y := by
      refine Matrix.ext fun i j => hinj ?_
      have := congrFun (congrFun hA1 i) j
      simpa only [Matrix.map_apply] using this
    have hA3 := congrArg (fun M => Matrix.map M (inclW l)) hA2
    simp only [map_smul_hom, Matrix.map_mul, map_pow] at hA3
    have hz : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = zW (ρ g) := by
      exact Matrix.ext fun i j => (inclWA l).commutes _
    have hg' : (Y.map (Per.σA (g : GQ l))).map (inclW l) = (Y.map (inclW l)).map (galW l (g : GQ l)) := by
      exact Matrix.ext fun i j => (GlobalTheory.Prism.galW_inclW _ _).symm
    rw [hz, hg', hYT, map_smul_hom, map_pow, ht, GlobalTheory.Prism.galW_inclW] at hA3
    have hsu : IsUnit (inclW l (Per.σA (g : GQ l) τ) ^ n) := (hστ _).pow n
    apply smul_cancel (htn.mul hsu)
    have e1 : (t ^ n * inclW l (Per.σA (g : GQ l) τ) ^ n) • (zW (ρ g) * T.map (galW l (g : GQ l))) =
        t ^ n • (zW (ρ g) * (inclW l (Per.σA (g : GQ l) τ) ^ n • T.map (galW l (g : GQ l)))) := by
      rw [Matrix.mul_smul, smul_smul]
    have e2 : (t ^ n * inclW l (Per.σA (g : GQ l) τ) ^ n) • T = inclW l (Per.σA (g : GQ l) τ) ^ n • t ^ n • T := by
      rw [smul_smul, mul_comm]
    rw [e1, e2]
    exact hA3
  refine ⟨n + b, Pre.mk T ?_ (bk.E ^ b • A) (bk.E ^ (2 * n) • A') ?_ ?_ hfix, Y, Z, hYT, hZu, hWZ⟩
  · rw [hT]; exact hYu.smul _
  · rw [Matrix.smul_mul, Matrix.mul_smul, hAA', smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2; ring
  · rw [map_smul_hom, Matrix.mul_smul, ← hφT, pow_add, mul_comm, ← smul_smul, map_pow]

end GlobalTheory.BKLim
