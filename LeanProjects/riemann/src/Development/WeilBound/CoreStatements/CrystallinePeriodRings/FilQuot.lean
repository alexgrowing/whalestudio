import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT

noncomputable section

namespace PositivityTheory.LocInh

open Formalism Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

section SlopeTestRemainingChoices

open GroundTheory.PAdicHodge

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem filq_ker_eq : RingHom.ker (Per6.θD l) = IsLocalRing.maximalIdeal (Per6.BdRp l) :=
  (IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l)).symm

theorem filq_exists_aD (y : Per6.BdRp l) (n : ℕ) : ∃ (k : ℕ) (a : Ainf l),
    (l : Per6.BdRp l) ^ k * y - Per6.aD l a ∈ RingHom.ker (Per6.θD l) ^ n := by
  obtain ⟨b, hb⟩ := IsPerfectoidField.exists_toBDeRhamPlus_sub_mem (K := ℂ_[l]) (p := l) y n
  obtain ⟨k, c, hc⟩ := away_exists (toBDeRhamPlus ↥(normInteger ℂ_[l]) l)
    (wittToBDeRhamPlus ↥(normInteger ℂ_[l]) l) (fun _ => rfl) b
  obtain ⟨a, rfl⟩ := ainfMap_surjective c
  refine ⟨k, a, ?_⟩
  rw [map_natCast] at hc
  have e : Per6.aD l a = (l : Per6.BdRp l) ^ k * toBDeRhamPlus ↥(normInteger ℂ_[l]) l b := hc
  rw [e, ← mul_sub, filq_ker_eq]
  exact Ideal.mul_mem_left _ _ hb

theorem filq_tiltMap_ε1 (AI : LocAinf l P) : Per6.tiltMap l AI.ε1 =
    (frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).symm (Per6.tiltMap l AI.ε) := by
  apply (frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).injective
  rw [RingEquiv.apply_symm_apply, frobeniusEquiv_apply, frobenius_def, ← map_pow, LocAinf.ε1,
    frobeniusEquiv_symm_pow_p]

theorem filq_ainfMap_ξ (AI : LocAinf l P) :
    Per6.ainfMap l AI.ξ = AInf.xi (K := ℂ_[l]) (Per6.tiltMap l AI.ε) := by
  rw [LocAinf.ξ, map_sum, AInf.xi]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow, frob_ainfMap_teich, filq_tiltMap_ε1]

theorem filq_aD_mem_iff (AI : LocAinf l P) (a : Ainf l) (n : ℕ) :
    Per6.aD l a ∈ RingHom.ker (Per6.θD l) ^ n ↔ AI.ξ ^ n ∣ a := by
  have hξ := AInf.ker_fontaineTheta_eq_span_xi (untilt_ε AI) (untilt_ε_root_ne_one AI)
  have h1 : Per6.aD l a ∈ RingHom.ker (Per6.θD l) ^ n ↔
      Per6.ainfMap l a ∈ Ideal.span {ACris.xiGen ℂ_[l] l ^ n} := by
    rw [filq_ker_eq, IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span ACris.ker_eq_span_xiGen,
      Ideal.span_singleton_pow, ← ACris.algebraMap_dvd_iff, map_pow,
      ← toBDeRhamPlus_mem_span_pow_iff ACris.ker_eq_span_xiGen]
    exact Iff.rfl
  rw [h1, ← Ideal.span_singleton_pow, ← ACris.ker_eq_span_xiGen, hξ, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← filq_ainfMap_ξ, ← map_pow]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b, rfl⟩ := ainfMap_surjective c
    exact ⟨b, ainfMap_injective (hc.trans (map_mul _ _ _).symm)⟩
  · rintro ⟨b, rfl⟩
    exact ⟨Per6.ainfMap l b, map_mul _ _ _⟩

theorem filq_θD_π₁ (AI : LocAinf l P) :
    Per6.θD l (Per6.aD l AI.π₁) = ((AI.ζ 1 : OC l) : ℂ_[l]) - 1 := by
  rw [LocAinf.π₁, map_sub, map_sub, map_one, map_one, θD_aD, frob_ainfMap_teich,
    WittVector.fontaineTheta_teichmuller, filq_tiltMap_ε1, untilt_ε_root]
  rfl

theorem filq_t_eq (AI : LocAinf l P) : ∃ w : Per6.BdRp l,
    fontaineT (Per6.tiltMap l AI.ε) (untilt_ε AI) = Per6.aD l AI.ξ * w ∧
      Per6.θD l w = ((AI.ζ 1 : OC l) : ℂ_[l]) - 1 := by
  obtain ⟨u, hu, h⟩ := logOnePlus_eq_mul (muBdR_mem (untilt_ε AI))
  have e : muBdR l (Per6.tiltMap l AI.ε) = Per6.aD l AI.μ := by
    rw [muBdR_eq, ← frob_ainfMap_teich, LocAinf.μ, map_sub, map_one]
    rfl
  have hu1 : Per6.θD l u = 1 := by
    rw [← filq_ker_eq, RingHom.mem_ker, map_sub, map_one, sub_eq_zero] at hu
    exact hu
  refine ⟨Per6.aD l AI.π₁ * u, ?_, ?_⟩
  · refine h.trans ?_
    rw [e, LocAinf.μ_eq, map_mul, mul_comm (Per6.aD l AI.π₁), mul_assoc]
  · rw [map_mul, hu1, mul_one, filq_θD_π₁]

theorem filq_tie_fil (T : LocTied6 l P AI) (K : FinExt l) (n : ℕ) {x : P.R.BdR} {y : Per6.BdRp l}
    (h : T.eD x = algebraMap (Per6.BdRp l) (Per6.BdR l) y) :
    x ∈ (P.PD K).Fil (n : ℤ) ↔ y ∈ RingHom.ker (Per6.θD l) ^ n := by
  rw [T.fil, h, fil_nat]

theorem filq_θ_eq (T : LocTied6 l P AI) (J : ThetaL P AI) {x : P.R.BdR} {y : Per6.BdRp l}
    (h : T.eD x = algebraMap (Per6.BdRp l) (Per6.BdR l) y) {z : Om l}
    (hz : Per6.θD l y = (z : ℂ_[l])) : J.θ x = (z : ℂ_[l]) := by
  obtain ⟨v, hv, hθ⟩ := T.om z
  have hd : T.eD (x - algebraMap (Om l) P.R.BdR z) =
      algebraMap (Per6.BdRp l) (Per6.BdR l) (y - v) := by
    rw [map_sub, map_sub, h, hv]
  have h0 := (tie_fil_zero T (botExt l) _).2 ⟨_, hd⟩
  have h0' := (tie_fil_zero T (botExt l) _).2 ⟨_, hv⟩
  have h1 : x - algebraMap (Om l) P.R.BdR z ∈ (P.PD (botExt l)).Fil 1 :=
    (filq_tie_fil T (botExt l) 1 hd).2 (by
      rw [pow_one, RingHom.mem_ker, map_sub, hz, hθ, sub_self])
  have h2 := J.θ_add _ h0 _ h0'
  rwa [sub_add_cancel, (J.θ_ker _ h0).2 h1, zero_add, J.θ_Om] at h2

end SlopeTestRemainingChoices

theorem fil_quotient : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied6 l P AI → ∀ (J : ThetaL P AI) (n : ℕ),
    (∀ x ∈ (P.PD (botExt l)).Fil 0, ∃ (k : ℕ) (a : Ainf l),
      (l : P.R.BdR) ^ k * x - P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ)) ∧
    (∀ a : Ainf l, P.ιB (AI.ιA a) ∈ (P.PD (botExt l)).Fil (n : ℤ) ↔ AI.ξ ^ n ∣ a) ∧
    (∃ w ∈ (P.PD (botExt l)).Fil 0, P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w ∧
      J.θ w = ((AI.ζ 1 : OC l) : PadicComplex l) - 1) := by
  intro l _ P AI T J n
  refine ⟨fun x hx => ?_, fun a => ?_, ?_⟩
  · obtain ⟨y, hy⟩ := (tie_fil_zero T _ x).1 hx
    obtain ⟨k, a, h⟩ := filq_exists_aD y n
    refine ⟨k, a, (filq_tie_fil T _ n ?_).2 h⟩
    rw [map_sub, map_sub, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, hy, tie_a]
  · exact (filq_tie_fil T _ n (tie_a T a)).trans (filq_aD_mem_iff AI a n)
  · obtain ⟨w, hw, hθ⟩ := filq_t_eq AI
    have h := T.eD.apply_symm_apply (algebraMap (Per6.BdRp l) (Per6.BdR l) w)
    refine ⟨_, (tie_fil_zero T _ _).2 ⟨w, h⟩, T.eD.injective ?_, ?_⟩
    · rw [map_mul, h, tie_t, tie_a, hw, map_mul]
    · have e : ((AI.ζ 1 : OC l) : PadicComplex l) - 1 = ((P.ζQ 1 - 1 : Om l) : PadicComplex l) := by
        rw [AI.ζ_eq, UniformSpace.Completion.coe_sub, UniformSpace.Completion.coe_one]
      rw [e] at hθ ⊢
      exact filq_θ_eq T J h hθ

end PositivityTheory.LocInh
