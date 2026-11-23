import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelOperatorsAtPrimeOffLevelDatumStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainInnerStepIntertwinesMatchedHeckeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHeckeStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.ChainE

variable {D : D7}

theorem mult_level {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (U : MMap M) (hU : U ∈ Mult θ M J χ) (v : M.Vec) : ∀ k ∈ J, ∀ g, U v (g * k) = χ k * U v g := by
  intro k hk g
  induction hU using Submodule.span_induction with
  | mem x hx => exact hx.lev v k hk g
  | zero => simp
  | add x y _ _ hx hy => simp only [MultilinearMap.add_apply, Pi.add_apply, hx, hy, mul_add]
  | smul a x _ hx => simp only [MultilinearMap.smul_apply, Pi.smul_apply, hx, smul_eq_mul, mul_left_comm]

theorem natCast_pow_notMem (P : Pl D.host.E) {n : ℕ} (h : ((n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (c : ℕ) :
    ((n ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h' =>
  h (P.isPrime.mem_of_pow_mem c (by rwa [Nat.cast_pow] at h'))

theorem gaL_comm {G : Type} [Group G] [Fintype G] (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (H : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (Φ : GA D V → ℂ)
    (h : ∀ g0 : G0 L.Pg L.r, actG0 V β L g0 (H Φ) = H (actG0 V β L g0 Φ)) :
    gaL V β L eG c (H Φ) = H (gaL V β L eG c Φ) := by
  unfold gaL
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  exact congrArg (c g • ·) (h (eG g))

section Chain

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
  [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem dnFrom_hk (t : T) (P : Pl D.host.E) (cs : ℕ → List ℤ →₀ ℂ)
    (hs : ∀ k, k + 1 < D.R.m → ∀ U U' : R.CC t (k + 1), (∀ v, U'.1 v = hk _ P (cs (k + 1)) (U.1 v)) →
      ∀ v, (R.ioY t k U').1 v = hk _ P (cs k) ((R.ioY t k U).1 v))
    (n : ℕ) (hn : n < D.R.m) (U U' : R.CC t n) (hU : ∀ v, U'.1 v = hk _ P (cs n) (U.1 v)) :
    ∀ v, (Lift.dnFrom (R.CC t) (R.ioY t) n U').1 v = hk _ P (cs 0) ((Lift.dnFrom (R.CC t) (R.ioY t) n U).1 v) := by
  induction n with
  | zero => exact hU
  | succ k ih => exact ih (by omega) (R.ioY t k U) (R.ioY t k U') (hs k hn U U' hU)

noncomputable def liftCC (t : T) (y : (R.HX t).H) : R.CC t 0 :=
  Lift.dnFrom (R.CC t) (R.ioY t) (D.R.m - 1) (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y))

theorem thDn_eq (t : T) (y : (R.HX t).H) : R.thDn t y = (liftCC t y).1 := rfl

theorem e_Th (hT : R.chain_Th) (t : T) (x : (R.HX t).H) (v : (R.MY 0).Vec) : R.HE.e (R.Th t x) v =
    R.e0 ((liftCC t x).1 (PiTensorProduct.tprod ℂ v)) := by
  rw [hT t x, postOn_apply, thDn_eq t x]
  rfl

theorem compositeLift_relation_passes_to_rows (F : Face D A) (hl : R.toLevCh.Is A.μ0) (t : T) (P : Pl D.host.E) (hP : Good R t P) (c : List ℤ →₀ ℂ) (U : R.CC t 0)
    (v : (R.MY 0).Vec) :
    R.e0 (hk _ P c (U.1 (PiTensorProduct.tprod ℂ v))) = hk _ P c (R.e0 (U.1 (PiTensorProduct.tprod ℂ v))) := by
  obtain ⟨n, hn⟩ := hl.βY 0 (by have := D.R.two_le_m; omega)
  have hN := natCast_pow_notMem P ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hl).2.1 t P hP).1 n
  have h1 := (GlobalTheory.T.level_operators_at_prime_off_level_datum _ _ _ _ (R.datYt t 0 R.triv) hn P hN hP).1
  have h2 := (GlobalTheory.T.level_operators_at_prime_off_level_datum _ _ _ _ (R.dat0 R.triv) hn P hN fun PP h =>
    hP PP (Or.inl (h.resolve_right (Finset.notMem_empty PP)))).2.2.2.1
  have h3 := mult_level _ _ _ _ _ ((mem_multT R.θ (R.MY 0) _ _ _).1 U.2) v
  refine gaL_comm _ _ _ _ _ _ _ fun g0 => h2 c g0 _ fun k hk h => ?_
  have h4 := h3 k (h1 k hk).1 h
  rw [(h1 k hk).2, one_mul] at h4
  exact h4

theorem e_Th_hk (F : Face D A) (hl : R.toLevCh.Is A.μ0) (hT : R.chain_Th) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (c : List ℤ →₀ ℂ) (y y' : (R.HX t).H) (h : ∀ v, (liftCC t y').1 v = hk _ P c ((liftCC t y).1 v)) :
    R.HE.e (R.Th t y') = postOn (R.MY 0) (hk (Yc D 0) P c) (R.HE.e (R.Th t y)) := by
  refine MultilinearMap.ext fun v => ?_
  exact ((e_Th hT t y' v).trans ((congrArg R.e0 (h _)).trans (compositeLift_relation_passes_to_rows F hl t P hP c (liftCC t y) v))).trans
    ((postOn_apply _ _ _ v).trans (congrArg (hk (Yc D 0) P c) (e_Th hT t y v))).symm

end Chain

theorem matchE_of_chain : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Chain.LiftInteg D → Core R F → SchurAll R → ∀ t P, Good R t P → FixAll R t P → ∀ (cX : List ℤ →₀ ℂ) (cs : ℕ → List ℤ →₀ ℂ), Match R.ψ (R.ωX t) P (cs (D.R.m - 1)) (dualC cX) → (∀ k, k + 1 < D.R.m → Match R.ψ (R.ωY t k) P (cs k) (dualC (cs (k + 1)))) → MatchE R t P cX (cs 0) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hI hC hS t P hP hF cX cs hX hY y y' hy
  refine e_Th_hk F hC.lev hC.chain.Th t P hP (cs 0) y y' ?_
  exact dnFrom_hk t P cs (fun k hk => GlobalTheory.T.chainInnerStep_intertwines_matchedHecke R F hI hC hS t P k hP hk (hF.1 k hk) _ _ (hY k hk))
    (D.R.m - 1) (by have := D.R.two_le_m; omega) _ _ (GlobalTheory.T.theta_chain_last_step_intertwines_matched_hecke R F hC hS t P hP hF.2.1 _ _ hX y y' hy)

end GlobalTheory.Hk3.ChainE
