import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusFiltrationEqFontaineXiPowStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BdRPlusIsDomainBdRIsFieldStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemDeRhamFiltrationIffXiPowStatement
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

noncomputable section
namespace GlobalTheory.ThetaTie
open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.MemLoc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime]

theorem zeta_pow {P : LocPrime l} (AI : LocAinf l P) (m n : ℕ) : AI.ζ (m + n) ^ l ^ n = AI.ζ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, ← add_assoc, AI.ζ_succ, ih]

theorem isEps {P : LocPrime l} (AI : LocAinf l P) : IsEps (l := l) AI.ε := by
  constructor
  · refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
    refine ⟨AI.ζ n, (AI.ε_coeff n).symm, ?_⟩
    have := zeta_pow AI 0 n
    rw [zero_add, AI.ζ_zero] at this
    rw [this]
  · have : ((frobeniusEquiv (Per.Fl l) l).symm AI.ε).untilt = AI.ζ 1 := by
      refine Perfection.teichmuller_spec (I := Ideal.span {(l : Per.OC l)}) fun n => ?_
      refine ⟨AI.ζ (1 + n), ?_, ?_⟩
      · rw [add_comm]
        exact (AI.ε_coeff (n + 1)).symm.trans (PreTilt.coeff_frobeniusEquiv_symm n _).symm
      · rw [zeta_pow AI 1 n]
    rw [this]
    exact AI.ζ_one

theorem ev_alg (n : ℕ) (a : Per.AinfP l) :
    Per.ev l n (algebraMap (Per.AinfP l) (Per.BdRp l) a) = Ideal.Quotient.mk _ a :=
  GlobalTheory.RingIface.ev_alg l n a

theorem mem_filtration_zero' (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  have : Subsingleton (Per.AinfP l ⧸ Per.kerP l ^ 0) := by
    rw [pow_zero, Ideal.one_eq_top]; infer_instance
  exact (GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow l 0 y).2 (Subsingleton.elim _ _)

theorem mem_filD_nat (n : ℕ) (x : Per.BdR l) :
    x ∈ Per.FilD l n ↔ ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = x := by
  constructor
  · exact GlobalTheory.RingIface.exists_of_mem_FilD_nat l
  · rintro ⟨z, hz, rfl⟩
    exact GlobalTheory.RingIface.alg_mem_FilD_nat l hz

theorem alg_inj {e : Per.Fl l} (he : IsEps e) :
    Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := by
  have _ := he
  exact (GlobalTheory.T.bdRPlus_isDomain_bdR_isField l).2.1

theorem actC_eq {P : LocPrime l} (AI : LocAinf l P) (g : GQ l) (x : ℂ_[l]) :
    AI.actC g x = Per.σC g x := by
  have hc : Continuous (AI.actC g) :=
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hc (GlobalTheory.RingIface.sigC_cont l g)
  | ih a => exact (AI.actC_ext g a).trans (GlobalTheory.RingBasics.σC_coe g a).symm

theorem log_mu {e : Per.Fl l} (he : IsEps e) {y : Per.BdRp l} (hy : Per.IsLog l e y) :
    aDp l (mu e) - y ∈ Per.FilP l 2 := by
  have hm : algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
    refine GlobalTheory.RingIface.alg_mem_kerP l ?_
    rw [map_sub, WittVector.fontaineTheta_teichmuller, he.1, map_one, sub_self]
  have h := GlobalTheory.CrisIncl.factorial_mul_ev l e y he.1 hy 2
  rw [GlobalTheory.RingIface.mem_filtration_iff_mem_kerTheta_pow]
  change Per.ev l 2 (algebraMap (Per.AinfP l) (Per.BdRp l)
    (algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1)) - y) = 0
  rw [map_sub, ev_alg]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = m at hm h ⊢
  have h2 : Ideal.Quotient.mk (Per.kerP l ^ 2) (m ^ 2) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hm 2)
  have hu : IsUnit ((2 : ℕ) : Per.AinfP l ⧸ Per.kerP l ^ 2) := by
    have := (GlobalTheory.RingBasics.isUnit_nat l 2 two_ne_zero).map (Ideal.Quotient.mk (Per.kerP l ^ 2))
    rwa [map_natCast] at this
  have hs : (∑ k ∈ Finset.range 2, (-1) ^ k * (((2 : ℕ).factorial / (k + 1) : ℕ) : Per.AinfP l) *
      m ^ (k + 1)) = ((2 : ℕ) : Per.AinfP l) * m - m ^ 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    ring
  rw [hs, map_sub, h2, sub_zero, map_mul, map_natCast] at h
  rw [sub_eq_zero]
  exact (hu.mul_left_cancel h).symm

variable {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

theorem eD_ιA (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
  have h := GlobalTheory.CrisIncl.incl_aB l _ T.incl a
  rw [← T.ιA] at h
  refine Eq.trans ?_ h
  simp

theorem fil_nat (n : ℕ) (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil n ↔
    ∃ z ∈ Per.FilP l n, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (T.fil _ _ _).trans (mem_filD_nat n _)

theorem fil_zero (x : P.R.BdR) : x ∈ (P.PD (botExt l)).Fil 0 ↔
    ∃ z, algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x :=
  (fil_nat T 0 x).trans ⟨fun ⟨z, _, h⟩ => ⟨z, h⟩, fun ⟨z, h⟩ => ⟨z, mem_filtration_zero' z, h⟩⟩

def th (x : P.R.BdR) : ℂ_[l] :=
  Per.θD l (Function.invFun (algebraMap (Per.BdRp l) (Per.BdR l)) (T.eD x))

theorem th_eq {x : P.R.BdR} {z : Per.BdRp l}
    (h : algebraMap (Per.BdRp l) (Per.BdR l) z = T.eD x) : th T x = Per.θD l z := by
  rw [th, ← h, Function.leftInverse_invFun (alg_inj (isEps AI))]

include T in
theorem exists_inverse_fontaineElement_mem_fil_neg_one : ∃ s ∈ (P.PD (botExt l)).Fil (-1), P.ιB P.tB * s = 1 := by
  obtain ⟨h1, -, -, -⟩ := GlobalTheory.T.bdRPlus_filtration_eq_fontaineXi_pow l _ (isEps AI)
  obtain ⟨-, hk, hun, -, -⟩ := GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l
  have hu := (P.PD (botExt l)).t_unit
  have t1 := (P.PD (botExt l)).mem_filtration_one
  have t2 := (P.PD (botExt l)).not_mem_filtration_two
  rw [P.PD_ι, P.period_datum_t_eq] at t1 t2
  rw [P.period_datum_t_eq] at hu
  obtain ⟨s, hs⟩ := (hu.map P.ιB).exists_right_inv
  refine ⟨s, ?_, hs⟩
  obtain ⟨z, hz, ez⟩ := (fil_nat T 1 _).1 t1
  obtain ⟨u, rfl⟩ := (h1 1 z).1 hz
  have huu : IsUnit u := hun u fun h0 => by
    obtain ⟨w, rfl⟩ := (h1 1 u).1 ((hk u).1 h0)
    exact t2 ((fil_nat T 2 _).2 ⟨_, (h1 2 _).2 ⟨w, by ring⟩, ez⟩)
  obtain ⟨v, hv⟩ := huu.exists_right_inv
  rw [T.fil, GlobalTheory.T.mem_deRhamFiltration_iff_xi_pow l _ (isEps AI)]
  refine ⟨v, ?_⟩
  have e1 : T.eD (P.ιB P.tB) * T.eD s = 1 := by rw [← map_mul, hs, map_one]
  have e2 := congrArg (algebraMap (Per.BdRp l) (Per.BdR l)) hv
  rw [← ez] at e1
  rw [show (- (-1 : ℤ)).toNat = 1 from rfl, show (-1 : ℤ).toNat = 0 from rfl]
  simp only [map_mul, map_one, pow_one, pow_zero, one_mul] at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) (aDp l (xi AI.ε)) = X at e1 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) u = U at e1 e2 ⊢
  generalize algebraMap (Per.BdRp l) (Per.BdR l) v = V at e2 ⊢
  linear_combination V * e1 - (T.eD s * X) * e2

def thetaL : ThetaL P AI where
  θ := th T
  θ_one := by rw [th_eq T (z := 1) (by simp), map_one]
  θ_add x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a + b) (by rw [map_add, map_add, ha, hb]), map_add]
  θ_mul x hx y hy := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    obtain ⟨b, hb⟩ := (fil_zero T y).1 hy
    rw [th_eq T ha, th_eq T hb, th_eq T (z := a * b) (by rw [map_mul, map_mul, ha, hb]), map_mul]
  θ_onto c := by
    obtain ⟨z, hz⟩ := (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).1 c
    have e : algebraMap (Per.BdRp l) (Per.BdR l) z =
        T.eD (T.eD.symm (algebraMap (Per.BdRp l) (Per.BdR l) z)) := (T.eD.apply_symm_apply _).symm
    exact ⟨_, (fil_zero T _).2 ⟨z, e⟩, (th_eq T e).trans hz⟩
  θ_ker x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    rw [th_eq T ha, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.1]
    refine ⟨fun h => (fil_nat T 1 x).2 ⟨a, h, ha⟩, fun h => ?_⟩
    obtain ⟨z, hz, e⟩ := (fil_nat T 1 x).1 h
    rwa [← alg_inj (isEps AI) (e.trans ha.symm)]
  θ_act g x hx := by
    obtain ⟨a, ha⟩ := (fil_zero T x).1 hx
    have e : algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g a) = T.eD (P.actQdR g x) := by
      rw [T.actD, ← ha]
      exact (GlobalTheory.RingIface.sigD_alg l g a).symm
    rw [th_eq T ha, th_eq T e, actC_eq, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.2]
  θ_Om x := by
    obtain ⟨y, h1, h2⟩ := T.om x
    rw [th_eq T h1.symm, h2]
  θ_int a := by
    rw [th_eq T (eD_ιA T a).symm, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1]
    exact (GlobalTheory.RingBasics.mem_OC _).1 (Per.θ l a).2
  θ_teich x y h := by
    rw [th_eq T (eD_ιA T _).symm, (GlobalTheory.T.thetaBdRPlus_surjective_ker_units_equivariant l).2.2.2.1, WittVector.fontaineTheta_teichmuller]
    have h1 := Ideal.Quotient.eq.1 ((PreTilt.mk_untilt_eq_coeff_zero x).trans h)
    have h2 := (GlobalTheory.RingBasics.mem_span_pow_OC 1 (x.untilt - y)).1 (by rwa [pow_one])
    simpa using h2
  fil_succ_iff_mul_t a x := by
    have t1 := (P.PD (botExt l)).mem_filtration_one
    rw [P.PD_ι, P.period_datum_t_eq] at t1
    constructor
    · intro hx
      obtain ⟨s, hs, e⟩ := exists_inverse_fontaineElement_mem_fil_neg_one T
      refine ⟨s * x, ?_, by rw [← mul_assoc, e, one_mul]⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ hs hx
      rwa [show -1 + (a + 1) = a by ring] at this
    · rintro ⟨y, hy, rfl⟩
      have := (P.PD (botExt l)).Fil_mul _ _ _ _ t1 hy
      rwa [add_comm] at this
  t_μ := by
    obtain ⟨y, hy, e⟩ := T.t
    refine (fil_nat T 2 _).2 ⟨_, log_mu (isEps AI) hy, ?_⟩
    rw [map_sub, map_sub, e, eD_ιA]
    rfl

theorem nonempty_thetaL (D : Formalism.BasicNotions.D7) (l : ℕ) [Fact l.Prime] :
    Nonempty (ThetaL (D.loc l) (D.locA l)) :=
  ⟨thetaL (D.locT l)⟩

end GlobalTheory.ThetaTie
