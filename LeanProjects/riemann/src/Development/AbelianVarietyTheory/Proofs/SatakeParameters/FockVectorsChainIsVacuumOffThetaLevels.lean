import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOrientedFiniteFixesFockPolynomialVectoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.VacGood

variable {D : D7}

theorem infPart_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {u : WO S T}
    (hu : u ∈ latO S T LS LT fun _ => True) : u.map (infPart D) = 0 := by
  ext i j
  rw [Matrix.map_apply, Matrix.zero_apply]
  unfold latO at hu
  refine AddSubgroup.closure_induction (p := fun u _ => infPart D (u i j) = 0) ?_ ?_ ?_ ?_ hu
  · rintro w ⟨α, -, -, a, -, s, -, t, -, rfl⟩
    rw [Matrix.of_apply]
    exact (show infPart D (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) =
      (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) from rfl).trans (TensorProduct.zero_tmul _ _)
  · simp
  · intro x y _ _ hx hy; rw [Matrix.add_apply, RingHom.map_add, hx, hy, add_zero]
  · intro x _ hx; rw [Matrix.neg_apply, RingHom.map_neg, hx, neg_zero]

theorem prime_idem_absorb (S : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    f * e = e := by
  have hff := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S).2.2.1 P e f h).1
  rcases h with ⟨he, hf⟩ | ⟨hf, -, -⟩
  · rw [hf, add_mul, he.1.1, mul_comm (cA D e) e, he.1.2.1, add_zero]
  · subst hf; exact hff

theorem prime_idem_absorb_conj (S : HSp D) {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f) :
    f * cA D e = cA D e := by
  have hcf := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S).2.2.1 P e f h).2.1
  have := congrArg (cA D) (prime_idem_absorb S h)
  rwa [map_mul, hcf] at this

theorem half_absorb (S : HSp D) {T : HSp D} {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} (h : IsPrimeIdem P e f)
    {u : WO S T} (hu : IsHalf e u ∨ IsHalf (cA D e) u) (i : Fin T.rank) (j : Fin S.rank) : f * u i j = u i j := by
  rcases hu with hu | hu
  · rw [← hu i j, ← mul_assoc, prime_idem_absorb S h]
  · rw [← hu i j, ← mul_assoc, prime_idem_absorb_conj S h]

theorem idemSum_mul_zero (S : HSp D) {E0 : AE D} {Q : Finset (Pl D.host.E)} (hE : IsIdemSum E0 Q)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hQ : ∀ PP ∈ Q, PP ≠ P ∧ ¬ IsConjPl PP P)
    {e f : AE D} (hP : IsPrimeIdem P e f) (x : AE D) (hx : f * x = x) : E0 * x = 0 ∧ cA D E0 * x = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
  have hI := GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents S
  have key : ∀ PP ∈ Q, es PP * x = 0 ∧ cA D (es PP) * x = 0 := by
    intro PP hPP
    have hPPi : IsPrimeIdem PP (es PP) (es PP + cA D (es PP)) := Or.inl ⟨hes PP hPP, rfl⟩
    have h4 := (hI.2.2.1 PP _ _ hPPi).2.2.2.2 P e f hP
    have hff : (es PP + cA D (es PP)) * f = 0 := by
      rcases h4 with h | ⟨-, h | h⟩
      · exact h
      · exact absurd h.symm (hQ PP hPP).1
      · exact absurd h (hQ PP hPP).2
    have ha := prime_idem_absorb S hPPi
    have hb := prime_idem_absorb_conj S hPPi
    constructor
    · calc es PP * x = ((es PP + cA D (es PP)) * es PP) * (f * x) := by rw [ha, hx]
        _ = es PP * (((es PP + cA D (es PP)) * f) * x) := by ring
        _ = 0 := by rw [hff]; ring
    · calc cA D (es PP) * x = ((es PP + cA D (es PP)) * cA D (es PP)) * (f * x) := by rw [hb, hx]
        _ = cA D (es PP) * (((es PP + cA D (es PP)) * f) * x) := by ring
        _ = 0 := by rw [hff]; ring
  constructor
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP h => (key PP h).1
  · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP h => (key PP h).2

theorem vac_of_frames {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)} {NS NT : ℕ}
    (hS : IsSDFrame S βS ΛS NS) (hT : IsSDFrame T βT ΛT NT) {P : Pl D.host.E}
    (hNS : ((NS : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hNT : ((NT : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    {f₀ : WO S T → ℂ} (hv : IsVacO ψ θ S T sS sT ΛS ΛT f₀) : IsVacAt ψ S T P f₀ := by
  obtain ⟨cS, hS⟩ := hS
  obtain ⟨cT, hT⟩ := hT
  refine GlobalTheory.T.isLocalVacuum_of_isLatticeVacuum_coprime_level ψ S T βS βT ΛS ΛT (NS ^ cS) (NT ^ cT) hS hT P ?_ f₀ hv.2.theta hv.2.lat
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow]
  intro h
  rcases P.isPrime.mem_or_mem h with h | h
  · exact hNS (P.isPrime.mem_of_pow_mem _ h)
  · exact hNT (P.isPrime.mem_of_pow_mem _ h)

theorem vac_pt {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {P : Pl D.host.E}
    {f₀ Φ f : WO S T → ℂ} {E1 : AE D} {Λ : AddSubgroup (WO S T)}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hv : IsVacAt ψ S T P f₀) (ht : IsThetaAt ψ (symplO S T) (heisO ψ S T) E1 Λ 1 f₀ Φ f)
    (hE : ∀ e' f', IsPrimeIdem P e' f' → ∀ x : AE D, f' * x = x → E1 * x = 0 ∧ cA D E1 * x = 0)
    (hth : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) :
    ∀ φ, IsVacAt ψ S T P (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  intro φ
  refine ⟨hth φ, fun e' f' hP u hu hh => ?_⟩
  refine GlobalTheory.T.heisenbergOriented_finite_fixes_fockPolynomialVectors ψ θ S T hθ sS sT BS BT f hth u (infPart_latO hu) ?_ φ
  exact GlobalTheory.T.heisenbergOperator_fix_thetaDatum_away_splitPlaces ψ S T E1 Λ 1 f₀ Φ f ht u (fun i j => hE e' f' hP _ (half_absorb S hP hh i j))
    (hv.2 e' f' hP u hu hh)

theorem fock_vacua_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F →
    ∀ t P, Good R t P → (∀ k, k + 1 < D.R.m → ∀ φ, IsVacAt R.ψ _ _ P (R.ptY t k φ)) ∧ (∀ φ, IsVacAt R.ψ _ _ P (R.ptX t φ)) ∧
      ∀ i φ, IsVacAt R.ψ _ _ P (R.ptP i t φ) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t P hG
  classical
  have hN := ((GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev).2.1 t P hG).1
  have hθ : IsInfFam R.θ := hC.models.inf
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [Nat.cast_one]; exact fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hm := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · obtain ⟨hvac, e, he, ht⟩ := hC.chain.vY t k hk
    have hv := vac_of_frames (hC.lev.βY k (by omega)) (hC.lev.βY (k + 1) hk) hN hN hvac
    exact vac_pt hθ hv ht (fun e' f' hP x hx => idemSum_mul_zero (Yc D k) he (fun PP h => hG PP (Finset.mem_union.1 h)) hP x hx) (hC.chain.ptY t k hk)
  · obtain ⟨hvac, e, he, ht⟩ := hC.chain.vX t
    have hv := vac_of_frames (hC.lev.βY (D.R.m - 1) (by omega)) hC.lev.βX hN h1 hvac
    exact vac_pt hθ hv ht (fun e' f' hP x hx => idemSum_mul_zero (Yc D (D.R.m - 1)) he (fun PP h => hG PP (Finset.mem_union.1 h)) hP x hx) (hC.chain.ptX t)
  · obtain ⟨hvac, e, he, ht⟩ := hC.thP.vP i t
    have hv := vac_of_frames (hC.lev.βV i) (hC.lev.βW i) h1 h1 hvac
    refine vac_pt hθ hv ht (fun e' f' hP x hx => ?_) (hC.thP.pt_theta i t)
    obtain ⟨a, b⟩ := idemSum_mul_zero (Vc D i) he (fun PP h => hG PP (Finset.mem_union.1 h)) hP x hx
    exact ⟨b, by rw [cA_cA]; exact a⟩

end GlobalTheory.VacGood

end
