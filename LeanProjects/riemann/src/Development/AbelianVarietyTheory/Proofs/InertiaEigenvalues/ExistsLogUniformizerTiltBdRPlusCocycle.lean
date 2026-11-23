import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EcoefQNormLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantLogSemistableToDeRham
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConstOfInvariantMod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinImagePowIdealAinfProperties
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveTiltedRootOfUnityLocalPeriodRingsData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.LogFlatLam

variable {l : ℕ} [Fact l.Prime]

theorem eD_smul_tB {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l} (hF : Fits T C)
    (z : ℤ_[l]) :
    T.eD (P.ιB ((z : ℚ_[l]) • P.tB)) =
      algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (Per.zA l z) * C.j C.t) := by
  rw [map_smul, Algebra.smul_def, map_mul, T.zD, hF.ι, hF.t, Core.tB, C.ι_j, map_mul, GlobalTheory.RingIface.zD_eq_alg]
  simp only [aDp, RingHom.comp_apply]

theorem exists_mem_FilD_neg (C : Core l) (x : Per.BdR l) : ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ)) := by
  have he := GlobalTheory.T.isPrimitiveTiltedRootOfUnity_localPeriodRingsData l C
  obtain ⟨n, y, hy⟩ := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.2.2 C.ε he x
  refine ⟨n, (GlobalTheory.MemLoc.mem_FilD_iff_xi_pow l C.ε he _ x).2 ⟨y, ?_⟩⟩
  simpa using hy

theorem const_eq_zero_of_mem_Fil_one {P : LocPrime l} {AI : LocAinf l P} {T : LocTied l P AI} {C : Core l}
    (hF : Fits T C) (K : FinExt l) (c : ↥K.1) (hc : algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil 1) : c = 0 := by
  have h1 := (T.fil K 1 _).1 hc
  have e : algebraMap ↥K.1 P.R.BdR c = algebraMap (Om l) P.R.BdR (c : Om l) := rfl
  rw [e, hF.o] at h1
  obtain ⟨z, hz, hze⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).1 (by exact_mod_cast h1)
  have hz' : z = C.o (c : Om l) := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1 hze
  have h0 : Per.θD l z = 0 := by
    have := (GlobalTheory.MemLoc.thetaD_onto_ker l).2
    rw [← this] at hz
    exact hz
  rw [hz', C.o_sec.th] at h0
  have : (c : Om l) = 0 := (algebraMap (Om l) ℂ_[l]).injective (by simpa using h0)
  exact Subtype.ext this

end GlobalTheory.LogFlatLam

namespace GlobalTheory.LogFlatLam

variable {l : ℕ} [Fact l.Prime]

theorem σD_alg (g : GQ l) (x : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) x) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g x) :=
  GlobalTheory.RingIface.sigD_alg l g x

theorem σDp_alg (g : GQ l) (a : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) :=
  GlobalTheory.RingIface.sigDp_alg l g a

theorem σDp_aDp (g : GQ l) (a : Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply, σDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

end GlobalTheory.LogFlatLam

open GlobalTheory.LogFlatLam in

theorem GlobalTheory.LogFlatLam.exists_lam : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (b : P.R.B) (c : ↥(GK K) → ℤ_[l]), ((∀ g : ↥(GK K), actSt P (g : GQ l) (Polynomial.X + Polynomial.C b) = Polynomial.X + Polynomial.C b + Polynomial.C ((c g : ℚ_[l]) • P.tB)) ∧ phiSt P (Polynomial.X + Polynomial.C b) = (l : Bst P) * (Polynomial.X + Polynomial.C b)) → (∀ g, bk.FixFlat g → c g = 0) → (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ ∀ g : ↥(GK K), aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) - (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) ∈ Per.FilP l m) → ∃ lam : Per.BdRp l, (∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t) ∧ (∀ m : ℕ, ∃ (k : ℕ) (s : bk.S), bk.E ∣ s ∧ aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam ∈ Per.FilP l m) := by
  rintro l _ K bk P AI T C hF b c ⟨hact, -⟩ - happrox
  obtain ⟨ι, hιC, hιg⟩ := GlobalTheory.BstLog.iota_exists l P AI T
  have hinj := (GlobalTheory.MemLoc.BdRField.bdR_isField l).2.1
  set yA := ι (Polynomial.X + Polynomial.C b) with hyA
  have hy : ∀ g : ↥(GK K), P.actQdR (g : GQ l) yA = yA + P.ιB ((c g : ℚ_[l]) • P.tB) := by
    intro g
    rw [hyA, ← hιg, hact g, map_add, hιC]
  have hKc : ∀ (g : ↥(GK K)) (d : ↥K.1), P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR d) =
      algebraMap ↥K.1 P.R.BdR d := by
    intro g d
    rw [← P.PD_actdR K g, AlgEquiv.commutes]
  obtain ⟨n, hn⟩ := exists_mem_FilD_neg C (T.eD yA)
  have hn' : yA ∈ (P.PD K).Fil (-(n : ℤ)) := (T.fil K _ _).2 hn
  have hg1 : ∀ g : ↥(GK K), (P.PD K).actdR g yA - yA ∈ (P.PD K).Fil 1 := by
    intro g
    rw [P.PD_actdR, hy, add_sub_cancel_left]
    refine (T.fil K 1 _).2 ?_
    rw [eD_smul_tB hF]
    exact_mod_cast (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).2
      ⟨_, Ideal.mul_mem_left _ _ (GlobalTheory.MemLoc.core_t_unit_fil l C).2.1, rfl⟩
  obtain ⟨c0, -, hc0⟩ := GlobalTheory.FilInv.const_of_invariant_mod l P AI T K (-(n : ℤ)) 1 yA hn' hg1
  set lamA := yA - algebraMap ↥K.1 P.R.BdR c0 with hlamA
  obtain ⟨lam, hlam1, hlamE⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).1 (by exact_mod_cast (T.fil K 1 lamA).1 hc0)
  have hequiv : ∀ g : ↥(GK K), Per.σDp (g : GQ l) lam = lam + aDp l (Per.zA l (c g)) * C.j C.t := by
    intro g
    apply hinj
    rw [map_add, ← σD_alg, hlamE, ← T.actD, hlamA, map_sub, hKc, hy]
    simp only [map_sub, map_add, eD_smul_tB hF]
    ring
  refine ⟨lam, hequiv, fun m => ?_⟩
  obtain ⟨k, s, hEs, hs⟩ := happrox m
  refine ⟨k, s, hEs, ?_⟩
  set x := aDp l (bk.ev s) - (l : Per.BdRp l) ^ k * lam with hx
  set xA := T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) x) with hxA
  have hxA' : T.eD xA = algebraMap (Per.BdRp l) (Per.BdR l) x := by rw [hxA, RingEquiv.apply_symm_apply]
  have hx1 : xA ∈ (P.PD K).Fil 1 := by
    refine (T.fil K 1 _).2 ?_
    rw [hxA']
    refine (GlobalTheory.BdRQuot.mem_FilD_nat 1 _).2 ⟨x, ?_, rfl⟩
    refine Ideal.sub_mem _ (((GlobalTheory.AinfEPow.ePow_facts l K bk 1).2.2.1 _).2 ?_) (Ideal.mul_mem_left _ _ hlam1)
    rw [pow_one]
    exact map_dvd _ hEs
  have hxg : ∀ g : ↥(GK K), (P.PD K).actdR g xA - xA ∈ (P.PD K).Fil (m : ℤ) := by
    intro g
    refine (T.fil K _ _).2 ?_
    rw [map_sub, P.PD_actdR, T.actD, hxA', σD_alg, ← map_sub]
    refine (GlobalTheory.BdRQuot.mem_FilD_nat m _).2 ⟨_, ?_, rfl⟩
    have e : Per.σDp (g : GQ l) x - x = aDp l (Per.σA (g : GQ l) (bk.ev s) - bk.ev s) -
        (l : Per.BdRp l) ^ k * (aDp l (Per.zA l (c g)) * C.j C.t) := by
      rw [hx, map_sub, map_mul, map_pow, map_natCast, σDp_aDp, hequiv, map_sub]
      ring
    rw [e]
    exact hs g
  obtain ⟨c', hc'1, hc'm⟩ := GlobalTheory.FilInv.const_of_invariant_mod l P AI T K 1 (m : ℤ) xA hx1 hxg
  have hc'0 : c' = 0 := const_eq_zero_of_mem_Fil_one hF K c' hc'1
  rw [hc'0, map_zero, sub_zero] at hc'm
  have h := (T.fil K _ _).1 hc'm
  rw [hxA'] at h
  obtain ⟨z, hz, hze⟩ := (GlobalTheory.BdRQuot.mem_FilD_nat m _).1 h
  rw [← hinj hze]
  exact hz
