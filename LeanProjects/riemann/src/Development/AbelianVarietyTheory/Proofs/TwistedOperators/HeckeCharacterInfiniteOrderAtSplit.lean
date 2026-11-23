import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.IteratedLiftChains
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NonemptyEquivOfMem
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

namespace GlobalTheory.SplitValue

open WithZero GlobalTheory.CharVal GlobalTheory.Formalism.L2.Col.HostOk

theorem val_map_eq_one {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime) {w : HeightOneSpectrum (𝓞 E)}
    (hN : Ideal.absNorm w.asIdeal = p) (hsq : ((p : ℕ) : 𝓞 E) ∉ w.asIdeal ^ 2) {z : E}
    (hz : ∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ w → Q.valuation E z = 1) (φ : E →+* E) (hφ : φ ≠ RingHom.id E) :
    w.valuation E (φ z) = 1 := by
  obtain ⟨Q, hQ⟩ := exists_pull φ w
  refine val_emb_eq_one hQ (hz Q fun e => hφ ?_)
  subst e
  exact GlobalTheory.ringHom_eq_of_comap_eq_unramified_degree_one E E φ (RingHom.id E) Q Q p hp hN hsq hQ (fun r => Iff.rfl)

theorem not_isOfFinOrder_val : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E) (n : D.R.Psi → ℤ) (p : ℕ), (∀ v, χ.TameAt v) → χ.HasInf (Formalism.L2.Host.embPsi D.host) n → (∀ g, n g ≠ 0) → SplitsCompletely D p → ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal → ¬ IsOfFinOrder (χ.val w) := by
  intro D χ n p ht hinf hn hp w hw hfin
  classical
  obtain ⟨hN, hsq⟩ := hp.2 w hw
  obtain ⟨M, z, hM, h1, h2, h3⟩ := GlobalTheory.TamePow.exists_pow_locK_mul_inf D.host.E χ
    (GlobalTheory.Mem.UnrAe.unr_ae_and_level _ χ).1.toFinset (GlobalTheory.HeckeProduct.hchar_productRule _ χ)
    (fun v hv => by simpa using hv) ht w (Formalism.L2.Host.unif w)
  obtain ⟨a, ha, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 hfin
  have h4 : χ.inf z ^ a = 1 := by
    have := congrArg (· ^ a) h3
    simp only [mul_pow, one_pow] at this
    rw [← pow_mul, mul_comm M a, pow_mul] at this
    change χ.val w ^ a = 1 at hpow
    unfold Formalism.L2.Host.HChar.val at hpow
    rwa [hpow, one_pow, one_mul] at this
  have h5 : ((χ.inf z : ℂˣ) : ℂ) ^ 2 =
      D.host.φ₀ (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) := by
    rw [hinf z, map_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun g _ => ?_
    rw [map_zpow₀, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    congr 1
    have e : D.host.φ₀ (D.host.sigmaOf g (D.host.conj z)) = starRingEnd ℂ (D.host.φ₀ (D.host.sigmaOf g z)) := by
      rw [sigma_conj]
      exact D.host.conjE_apply D.host.φ₀ _
    have e' : Formalism.L2.Host.embPsi D.host g z = D.host.φ₀ (D.host.sigmaOf g z) := rfl
    have h0 : D.host.φ₀ (D.host.sigmaOf g z) ≠ 0 := by simp
    rw [map_div₀, e, e', div_pow, div_eq_div_iff (pow_ne_zero _ (by simpa using h0)) (by simpa using h0), sq, mul_assoc,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have h6 : (∏ g : D.R.Psi, (D.host.sigmaOf g z / D.host.sigmaOf g (D.host.conj z)) ^ n g) ^ a = 1 := by
    apply D.host.φ₀.injective
    rw [map_pow, ← h5, ← pow_mul, mul_comm, pow_mul, ← Units.val_pow_eq_pow_val, h4, map_one]
    simp
  have h7 := unit_of_pow (w := w) ha (by rw [h6, map_one])
  have hc : ∀ g : D.R.Psi, w.valuation _ (D.host.sigmaOf g (D.host.conj z)) = 1 := by
    intro g
    refine val_map_eq_one hp.1 hN hsq h2
      ((D.host.sigmaOf g : D.host.E →+* D.host.E).comp (D.host.conj : D.host.E →+* D.host.E)) fun e => ?_
    have := RingHom.congr_fun e D.host.sqrtMinusD
    change D.host.sigmaOf g (D.host.conj D.host.sqrtMinusD) = D.host.sqrtMinusD at this
    rw [conj_b, map_neg, sigmaOf_b] at this
    exact b_ne D.host this.symm
  have hone : D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) = 1 :=
    map_one (D.host.gal).symm
  have hg : ∀ g : D.R.Psi, g ≠ 1 → w.valuation _ (D.host.sigmaOf g z) = 1 := by
    intro g hg
    refine val_map_eq_one hp.1 hN hsq h2 (D.host.sigmaOf g : D.host.E →+* D.host.E) fun e => hg ?_
    have e1 : D.host.sigmaOf g = D.host.sigmaOf ((1 : D.R.Psi) : D.R.GG) := by
      rw [hone]
      exact AlgEquiv.ext fun x => RingHom.congr_fun e x
    exact Subtype.ext ((D.host.gal).symm.injective e1)
  rw [map_prod, Finset.prod_eq_single 1 (fun g _ h => by rw [map_zpow₀, map_div₀, hg g h, hc g, div_one, one_zpow])
    (by simp), map_zpow₀, map_div₀, hc, div_one, hone, AlgEquiv.one_apply, h1, val_unif, ← exp_nsmul, ← exp_zsmul,
    ← exp_zero, exp_inj] at h7
  simp only [nsmul_eq_mul, smul_eq_mul, mul_eq_zero] at h7
  rcases h7 with h | h | h
  · exact hn 1 h
  · omega
  · omega

end GlobalTheory.SplitValue
