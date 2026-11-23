import Formalism.LocalToGlobal.InertKernelTheory.DefsMMInv
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.AdditionIdentityOfSigmaFormulaUnit
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.OkpDict

noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace ThetaInverseLemmas

open Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext Formalism.MainNotions.Ext.CutA IntegralOrthonormalChange

section Okp

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem okp_range (a : 𝓞 D.host.K) :
    (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K)) ∈ OKp D lam :=
  subset_closure ⟨a, rfl⟩

theorem okp_closed : IsClosed (OKp D lam) := isClosed_closure

theorem tauK_int (n : ℤ) : tauK D lam (n : D.host.K) = n := by
  unfold tauK
  have : (((n : D.host.K)) : D.host.E) = (n : D.host.E) := by simp
  rw [this, lamPhi_int]

theorem tauKc_int (n : ℤ) : tauKc D lam (n : D.host.K) = n := by
  unfold tauKc
  have : (((n : D.host.K)) : D.host.E) = (n : D.host.E) := by simp
  rw [this, map_intCast, lamPhi_int]

theorem okp_intPair (n : ℤ) : ((n : ℂ_[p]), (n : ℂ_[p])) ∈ OKp D lam := by
  have h := okp_range D lam (n : 𝓞 D.host.K)
  have e : (((n : 𝓞 D.host.K)) : D.host.K) = (n : D.host.K) := by simp
  rwa [e, tauK_int, tauKc_int] at h

theorem okp_zp (u : ℤ_[p]) : (zc u, zc u) ∈ OKp D lam := by
  have hf : Continuous (fun z : ℤ_[p] => (zc z, zc z)) := zc_continuous.prodMk zc_continuous
  have hu : u ∈ closure (Set.range (Int.cast : ℤ → ℤ_[p])) := PadicInt.denseRange_intCast u
  have h := map_mem_closure hf hu (t := OKp D lam) (by
    rintro _ ⟨n, rfl⟩
    simpa [zc_int] using okp_intPair D lam n)
  rwa [(okp_closed D lam).closure_eq] at h

theorem norm_p_cp : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
  have h := norm_int_cp (p := p) (p : ℤ)
  push_cast at h
  rw [h]
  exact PadicInt.norm_p

theorem pow_dvd_of_norm (t : ℤ) (e : ℕ) (h : ‖(t : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ e) : ((p : ℤ) ^ e) ∣ t := by
  rw [norm_int_cp, norm_p_cp] at h
  apply PadicInt.norm_int_le_pow_iff_dvd.1
  rw [zpow_neg, zpow_natCast, ← inv_pow]
  exact h

theorem isAlg (k : D.host.K) : IsAlgebraic ℤ k :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ D.host.K).2 (Algebra.IsAlgebraic.isAlgebraic k)

end Okp

section Key

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

theorem tauK_nat (n : ℕ) : tauK D lam (n : D.host.K) = n := by
  have h := tauK_int D lam (n : ℤ)
  push_cast at h
  exact h

theorem tauKc_nat (n : ℕ) : tauKc D lam (n : D.host.K) = n := by
  have h := tauKc_int D lam (n : ℤ)
  push_cast at h
  exact h

theorem zc_mul' (a b : ℤ_[p]) : zc (a * b) = zc a * zc b := by simp [zc]

theorem keyInt (k : D.host.K) (h1 : ‖tauK D lam k‖ ≤ 1) (h2 : ‖tauKc D lam k‖ ≤ 1) :
    (tauK D lam k, tauKc D lam k) ∈ OKp D lam := by
  have hp : p.Prime := Fact.out
  obtain ⟨y, hy0, hyI⟩ := (isAlg D k).exists_integral_multiple
  obtain ⟨m, hm⟩ : ∃ m : ℕ, y = m ∨ y = -m := ⟨y.natAbs, Int.natAbs_eq y⟩
  have hm0 : m ≠ 0 := by
    rintro rfl
    rcases hm with h | h <;> simp [h] at hy0
  have hy : IsIntegral ℤ ((y : D.host.K) * k) := by rwa [zsmul_eq_mul] at hyI
  have hmI : IsIntegral ℤ ((m : D.host.K) * k) := by
    rcases hm with h | h
    · subst h
      simpa using hy
    · subst h
      have e : ((m : D.host.K)) * k = -((((-(m : ℤ)) : ℤ) : D.host.K) * k) := by push_cast; ring
      rw [e]
      exact hy.neg
  obtain ⟨e, n', hn', hmn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
  let c : 𝓞 D.host.K := ⟨(m : D.host.K) * k, hmI⟩
  have hcK : ((c : 𝓞 D.host.K) : D.host.K) = (m : D.host.K) * k := rfl
  have ht := tau_trace D lam c
  have hn := tau_norm D lam c
  rw [hcK, tauK_mul, tauKc_mul, tauK_nat, tauKc_nat] at ht hn
  generalize (Algebra.norm ℤ (1 + c) - Algebra.norm ℤ c - 1 : ℤ) = T at ht
  generalize (Algebra.norm ℤ c : ℤ) = Nn at hn
  have hn'1 : ‖(n' : ℂ_[p])‖ = 1 := by
    have := norm_int_cp_eq_one (p := p) (n' : ℤ) (by exact_mod_cast hn')
    simpa using this
  have hmc : (m : ℂ_[p]) = (p : ℂ_[p]) ^ e * n' := by rw [hmn]; push_cast; ring
  have hnorm_m : ‖(m : ℂ_[p])‖ = ‖(p : ℂ_[p])‖ ^ e := by
    rw [hmc, norm_mul, norm_pow, hn'1, mul_one]
  have hA : ‖(m : ℂ_[p]) * tauK D lam k‖ ≤ ‖(p : ℂ_[p])‖ ^ e := by
    rw [norm_mul, hnorm_m]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) h1
  have hB : ‖(m : ℂ_[p]) * tauKc D lam k‖ ≤ ‖(p : ℂ_[p])‖ ^ e := by
    rw [norm_mul, hnorm_m]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) h2
  have hT : ‖(T : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ e := by
    rw [← ht]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hA hB)
  have hN : ‖(Nn : ℂ_[p])‖ ≤ ‖(p : ℂ_[p])‖ ^ (2 * e) := by
    rw [← hn, norm_mul, two_mul, pow_add]
    exact mul_le_mul hA hB (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
  obtain ⟨t', rfl⟩ := pow_dvd_of_norm T e hT
  obtain ⟨n'', rfl⟩ := pow_dvd_of_norm Nn (2 * e) hN
  have hp0 : (p : ℂ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hpe : (p : ℂ_[p]) ^ e ≠ 0 := pow_ne_zero _ hp0
  have hpe2 : (p : ℂ_[p]) ^ (2 * e) ≠ 0 := pow_ne_zero _ hp0
  have hsum : (n' : ℂ_[p]) * tauK D lam k + n' * tauKc D lam k = t' := by
    apply mul_left_cancel₀ hpe
    rw [hmc] at ht
    push_cast at ht
    linear_combination ht
  have hprod : ((n' : ℂ_[p]) * tauK D lam k) * (n' * tauKc D lam k) = n'' := by
    apply mul_left_cancel₀ hpe2
    rw [hmc] at hn
    push_cast at hn
    linear_combination hn
  let c' : D.host.K := (n' : D.host.K) * k
  have htc' : tauKp D lam c' = (n' : ℂ_[p]) * tauK D lam k := by
    rw [tauKp_apply]
    show tauK D lam ((n' : D.host.K) * k) = _
    rw [tauK_mul, tauK_nat]
  have hK : c' ^ 2 - (t' : D.host.K) * c' + (n'' : D.host.K) = 0 := by
    apply (tauKp D lam).injective
    rw [map_zero, map_add, map_sub, map_mul, map_pow, map_intCast, map_intCast, htc']
    linear_combination (↑n' * tauK D lam k) * hsum - hprod
  have hc'I : IsIntegral ℤ c' := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t' * Polynomial.X + Polynomial.C n'', ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      simp only [eq_intCast]
      exact hK
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[p], zc u * (n' : ℂ_[p]) = 1 := by
    have h1 : ‖(n' : ℤ_[p])‖ = 1 := by
      simpa using norm_int_zp_eq_one (p := p) (n' : ℤ) (by exact_mod_cast hn')
    obtain ⟨w, hw⟩ := PadicInt.isUnit_iff.2 h1
    refine ⟨((w⁻¹ : ℤ_[p]ˣ) : ℤ_[p]), ?_⟩
    have h4 : zc ((n' : ℤ_[p])) = (n' : ℂ_[p]) := by simpa using zc_int (p := p) (n' : ℤ)
    rw [← h4, ← zc_mul', ← hw, Units.inv_mul]
    simp [zc]
  let c'' : 𝓞 D.host.K := ⟨c', hc'I⟩
  have e1 : tauK D lam (c'' : D.host.K) = (n' : ℂ_[p]) * tauK D lam k := by
    show tauK D lam ((n' : D.host.K) * k) = _
    rw [tauK_mul, tauK_nat]
  have e2 : tauKc D lam (c'' : D.host.K) = (n' : ℂ_[p]) * tauKc D lam k := by
    show tauKc D lam ((n' : D.host.K) * k) = _
    rw [tauKc_mul, tauKc_nat]
  have hm' := okp_mul D lam _ _ (okp_zp D lam u) (okp_range D lam c'')
  rw [Prod.mk_mul_mk, e1, e2, ← mul_assoc, ← mul_assoc, hu, one_mul, one_mul] at hm'
  exact hm'

theorem conv (σ : ℂ_[p] →+* ℂ_[p]) (hσ : IsConjP D lam σ) (x : ℂ_[p])
    (hx : x ∈ closure (Set.range fun k : D.host.K => lamC lam (D.host.φ₀ (k : D.host.E)))) (hx1 : ‖x‖ ≤ 1) :
    (x, σ x) ∈ OKp D lam := by
  have hσc : Continuous σ := by
    refine AddMonoidHomClass.continuous_of_bound σ 1 (fun y => ?_)
    rw [hσ.2 y, one_mul]
  have hU : IsOpen (Metric.closedBall (0 : ℂ_[p]) 1) := IsUltrametricDist.isOpen_closedBall 0 one_ne_zero
  have hx' : x ∈ closure (Metric.closedBall (0 : ℂ_[p]) 1 ∩
      Set.range fun k : D.host.K => lamC lam (D.host.φ₀ (k : D.host.E))) :=
    hU.inter_closure ⟨by simpa using hx1, hx⟩
  have h := map_mem_closure (continuous_id.prodMk hσc) hx' (t := OKp D lam) (by
    rintro _ ⟨hy1, k, rfl⟩
    have hy1' : ‖tauK D lam k‖ ≤ 1 := by simpa [tauK] using hy1
    have hc : σ (tauK D lam k) = tauKc D lam k := hσ.1 k
    have hk := keyInt D lam k hy1' (by rw [← hc, hσ.2]; exact hy1')
    rw [← hc] at hk
    exact hk)
  rwa [(okp_closed D lam).closure_eq] at h

end Key

section Lin

open scoped Matrix

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

def tauE : D.host.E →+* ℂ_[p] :=
  lam.comp (D.host.φ₀.codRestrict Qbar.toSubring (fun z => test_vector_mem_schwartz_bruhat D z))

theorem tauE_apply (x : D.host.E) : tauE D lam x = lamC lam (D.host.φ₀ x) := by
  rw [lamC_mem' lam (test_vector_mem_schwartz_bruhat D x)]
  rfl

theorem gram_change (σ : ℂ_[p] →+* ℂ_[p]) (hσ : IsConjP D lam σ) {N N' r : ℕ}
    (b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E) (Q : Fin r → Fin r → D.host.E)
    (hQK : ∀ i j, Q i j ∈ D.host.K) (hb' : ∀ j, b' j = ∑ i, Q i j • b i) :
    (Matrix.of fun m n => lamC lam (D.host.φ₀ ((hYY D (b' m) (b' n) : D.host.K) : D.host.E))) =
      (Matrix.of fun m n => lamC lam (D.host.φ₀ (Q n m))) *
        (Matrix.of fun m n => lamC lam (D.host.φ₀ ((hYY D (b m) (b n) : D.host.K) : D.host.E))) *
        ((Matrix.of fun m n => lamC lam (D.host.φ₀ (Q n m))).map σ)ᵀ := by
  have hσQ : ∀ a c, σ (lamC lam (D.host.φ₀ (Q a c))) = tauE D lam (D.host.conj (Q a c)) := by
    intro a c
    rw [tauE_apply]
    exact hσ.1 ⟨Q a c, hQK a c⟩
  ext m n
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hσQ]
  simp only [← tauE_apply]
  rw [hb' m, hb' n, hYY_comb D b (fun i => Q i m) (fun i => Q i n) (fun i => hQK i m) (fun i => hQK i n)]
  simp only [map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem unitary_mat {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [CommRing F] (σ : F →+* F)
    (A G : Matrix n n F) (h : ∀ i j, ∑ m, ∑ k, A i m * G m k * σ (A j k) = if i = j then 1 else 0) :
    A * G * (A.map σ)ᵀ = 1 := by
  ext i j
  rw [Matrix.one_apply, ← h i j]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem unitary_P {n : Type*} [Fintype n] [DecidableEq n] {F : Type*} [Field F] (σ : F →+* F)
    (A A' G Qt : Matrix n n F) (hA : A * G * (A.map σ)ᵀ = 1)
    (hA' : A' * (Qt * G * (Qt.map σ)ᵀ) * (A'.map σ)ᵀ = 1) (hdet : A.det ≠ 0) :
    (A' * Qt * A⁻¹) * ((A' * Qt * A⁻¹).map σ)ᵀ = 1 := by
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hdet)
  have hBs : A⁻¹.map σ * A.map σ = 1 := by
    rw [← Matrix.map_mul, hBA, Matrix.map_one _ (map_zero σ) (map_one σ)]
  have hG : A⁻¹ * (A⁻¹.map σ)ᵀ = G := by
    calc A⁻¹ * (A⁻¹.map σ)ᵀ = A⁻¹ * (A * G * (A.map σ)ᵀ) * (A⁻¹.map σ)ᵀ := by rw [hA, Matrix.mul_one]
      _ = (A⁻¹ * A) * G * (A⁻¹.map σ * A.map σ)ᵀ := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hBA, hBs]; simp
  calc (A' * Qt * A⁻¹) * ((A' * Qt * A⁻¹).map σ)ᵀ
      = A' * (Qt * (A⁻¹ * (A⁻¹.map σ)ᵀ) * (Qt.map σ)ᵀ) * (A'.map σ)ᵀ := by
        simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    _ = 1 := by rw [hG]; exact hA'

theorem lamb_change {N N' r : ℕ} (b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E) (Q : Fin r → Fin r → D.host.E)
    (hQK : ∀ i j, Q i j ∈ D.host.K) (hb' : ∀ j, b' j = ∑ i, Q i j • b i) (m : Fin r)
    (k : D.what₂.Tau × Fin N' × Fin N) :
    lamC lam (embT D k.1 (b' m k.2.1 k.2.2)) =
      ∑ n, lamC lam (D.host.φ₀ (Q n m)) * lamC lam (embT D k.1 (b n k.2.1 k.2.2)) := by
  rw [IntegralOrthonormalChange.lamC_embT, hb' m, Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← IntegralOrthonormalChange.embT_K D k.1 _ (hQK n m), IntegralOrthonormalChange.lamC_embT, IntegralOrthonormalChange.lamC_embT]

theorem v_change {N N' r : ℕ} (b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E) (Q : Fin r → Fin r → D.host.E)
    (hQK : ∀ i j, Q i j ∈ D.host.K) (hb' : ∀ j, b' j = ∑ i, Q i j • b i)
    (A A' : Matrix (Fin r) (Fin r) ℂ_[p]) (hdet : A.det ≠ 0)
    (v v' : Fin r → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p]))
    (hv : ∀ i k, v i k = ∑ m, A i m * lamC lam (embT D k.1 (b m k.2.1 k.2.2)))
    (hv' : ∀ i k, v' i k = ∑ m, A' i m * lamC lam (embT D k.1 (b' m k.2.1 k.2.2))) :
    ∀ i k, v' i k = ∑ j, (A' * (Matrix.of fun m n => lamC lam (D.host.φ₀ (Q n m))) * A⁻¹) i j * v j k := by
  intro i k
  set Qt : Matrix (Fin r) (Fin r) ℂ_[p] := Matrix.of fun m n => lamC lam (D.host.φ₀ (Q n m)) with hQt
  set w : Fin r → ℂ_[p] := fun n => lamC lam (embT D k.1 (b n k.2.1 k.2.2)) with hw
  have h1 : (fun j => v j k) = A *ᵥ w := by
    funext j
    rw [hv j k]
    rfl
  have h2 : (fun j => v' j k) = (A' * Qt) *ᵥ w := by
    funext j
    rw [hv' j k, ← Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [lamb_change D lam b b' Q hQK hb' m k]
    rfl
  have hBA : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.2 hdet)
  have h3 : (fun j => v' j k) = (A' * Qt * A⁻¹) *ᵥ (fun j => v j k) := by
    rw [h1, h2, Matrix.mulVec_mulVec, Matrix.mul_assoc (A' * Qt), hBA, Matrix.mul_one]
  exact congrFun h3 i

theorem lift_mem {n : Type*} [Fintype n] [DecidableEq n] (R' : Subring ℂ_[p]) (X : Matrix n n ℂ_[p])
    (hX : ∀ i j, X i j ∈ R') : X.det ∈ R' ∧ ∀ i j, X.adjugate i j ∈ R' := by
  let Xl : Matrix n n R' := Matrix.of fun i j => ⟨X i j, hX i j⟩
  have hX' : R'.subtype.mapMatrix Xl = X := by
    ext i j
    rfl
  constructor
  · rw [← hX', ← RingHom.map_det]
    exact (Xl.det).2
  · intro i j
    rw [← hX', ← RingHom.map_adjugate]
    exact (Xl.adjugate i j).2

theorem entries {r : ℕ} (A A' : Matrix (Fin r) (Fin r) ℂ_[p])
    (Q : Fin r → Fin r → D.host.E) (hQK : ∀ i j, Q i j ∈ D.host.K)
    (hQp : ∀ i j, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : 𝓞 D.host.K, (s : D.host.E) * Q i j = ((c : D.host.K) : D.host.E))
    (hA : ∀ i j, IsIntP (A i j) ∧
      A i j ∈ closure (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))))
    (hA' : ∀ i j, IsIntP (A' i j) ∧
      A' i j ∈ closure (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))))
    (hdet : ‖A.det‖ = 1) :
    ∀ i j, (A' * (Matrix.of fun m n => lamC lam (D.host.φ₀ (Q n m))) * A⁻¹) i j ∈
        closure (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))) ∧
      ‖(A' * (Matrix.of fun m n => lamC lam (D.host.φ₀ (Q n m))) * A⁻¹) i j‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  set S := Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E)) with hS
  let Kc : Subfield ℂ_[p] := (tauKp D lam).fieldRange.topologicalClosure
  have hKc : (Kc : Set ℂ_[p]) = closure S := by
    show closure ((tauKp D lam).fieldRange : Set ℂ_[p]) = closure S
    rw [RingHom.coe_fieldRange]
    congr 1
    ext x
    simp only [S, Set.mem_range, tauKp_apply]
  let R' : Subring ℂ_[p] := Kc.toSubring ⊓ intRing p
  have memR : ∀ x, x ∈ R' ↔ x ∈ closure S ∧ ‖x‖ ≤ 1 := fun x => by
    rw [← hKc]
    exact Iff.rfl
  have mulR : ∀ X Y : Matrix (Fin r) (Fin r) ℂ_[p], (∀ i j, X i j ∈ R') → (∀ i j, Y i j ∈ R') →
      ∀ i j, (X * Y) i j ∈ R' := fun X Y hX hY i j => by
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => mul_mem (hX i k) (hY k j)
  have hAR : ∀ i j, A i j ∈ R' := fun i j => (memR _).2 ⟨(hA i j).2, (hA i j).1⟩
  have hA'R : ∀ i j, A' i j ∈ R' := fun i j => (memR _).2 ⟨(hA' i j).2, (hA' i j).1⟩
  have hQR : ∀ m n, (Matrix.of fun m n => lamC lam (D.host.φ₀ (Q n m)) : Matrix (Fin r) (Fin r) ℂ_[p]) m n ∈ R' := by
    intro m n
    refine (memR _).2 ⟨subset_closure ⟨⟨Q n m, hQK n m⟩, rfl⟩, ?_⟩
    obtain ⟨s, hs, c, hc⟩ := hQp n m
    have h1 := congrArg (tauE D lam) hc
    rw [map_mul, map_natCast] at h1
    have hc1 : ‖tauE D lam ((c : D.host.K) : D.host.E)‖ ≤ 1 := by
      have := (okp_norm_le D lam _ (okp_range D lam c)).1
      rw [tauE_apply]
      exact this
    have hs1 : ‖(s : ℂ_[p])‖ = 1 := by
      have hnd : ¬ (p : ℤ) ∣ (s : ℤ) := by
        intro h
        have h' : p ∣ s := by exact_mod_cast h
        exact (hp.coprime_iff_not_dvd.1 hs.symm) h'
      simpa using norm_int_cp_eq_one (p := p) (s : ℤ) hnd
    show ‖lamC lam (D.host.φ₀ (Q n m))‖ ≤ 1
    rw [← tauE_apply]
    have h2 : ‖(s : ℂ_[p]) * tauE D lam (Q n m)‖ ≤ 1 := by rw [h1]; exact hc1
    rwa [norm_mul, hs1, one_mul] at h2
  obtain ⟨hdR, hadjR⟩ := lift_mem R' A hAR
  have hdinv : A.det⁻¹ ∈ R' := by
    refine (memR _).2 ⟨?_, ?_⟩
    · have hd : A.det ∈ (Kc : Set ℂ_[p]) := by rw [hKc]; exact ((memR _).1 hdR).1
      rw [← hKc]
      exact Kc.inv_mem hd
    · rw [norm_inv, hdet, inv_one]
  have hBR : ∀ i j, A⁻¹ i j ∈ R' := by
    intro i j
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
    exact mul_mem hdinv (hadjR i j)
  intro i j
  exact (memR _).1 (mulR _ _ (mulR _ _ hA'R hQR) hBR i j)

theorem atLogV_change {N N' r : ℕ} (Λ : AddSubgroup ℂ) (C : WeierstrassCurve.VariableChange ℂ_[p])
    (wq : PowerSeries ℂ_[p]) (v v' : Fin r → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p]))
    (P : Matrix (Fin r) (Fin r) ℂ_[p]) (hvP : ∀ i k, v' i k = ∑ j, P i j * v j k)
    (S : Fin r → MvPowerSeries (Fin r) ℂ_[p]) (hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0)
    (hSl : ∀ j, PowerSeries.subst (S j) (flog (C • wModel lam Λ) wq) =
      ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (P i j) *
        PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) :
    atLogV D lam Λ C wq v' F = MvPowerSeries.subst S (atLogV D lam Λ C wq v F) := by
  have hl0 := flog_constantCoeff (C • wModel lam Λ) wq
  have hX : ∀ i, MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) = 0 :=
    fun i => PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) _ hl0
  have hY : MvPowerSeries.HasSubst (fun k : D.what₂.Tau × Fin N' × Fin N =>
      ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i k) *
        PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin r) ℂ_[p]) (flog (C • wModel lam Λ) wq)) := by
    apply MvPowerSeries.hasSubst_of_constantCoeff_zero
    intro k
    simp [map_sum, hX]
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  unfold atLogV
  simp only []
  rw [MvPowerSeries.subst_comp_subst_apply hY hSs]
  congr 1
  funext k
  rw [← MvPowerSeries.coe_substAlgHom hSs, map_sum]
  simp only [map_mul, AlgHom.commutes, MvPowerSeries.coe_substAlgHom, subst_subst_X S hSs, hSl, hvP]
  simp only [Finset.mul_sum, Finset.sum_mul, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem locInv_core (hU : UnitSubstLoc) (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hcc : IsCurveIdeal D cc)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (hin : jacobiSym (-(D.host.d : ℤ)) p = -1)
    (lam : Qbar →+* ℂ_[p]) (σ : ℂ_[p] →+* ℂ_[p]) (hσ : IsConjP D lam σ) {N N' r : ℕ}
    (b b' : Fin r → Matrix (Fin N') (Fin N) D.host.E) (A A' : Matrix (Fin r) (Fin r) ℂ_[p])
    (Q : Fin r → Fin r → D.host.E) (hQK : ∀ i j, Q i j ∈ D.host.K)
    (hQp : ∀ i j, ∃ s : ℕ, Nat.Coprime s p ∧ ∃ c : 𝓞 D.host.K, (s : D.host.E) * Q i j = ((c : D.host.K) : D.host.E))
    (hb' : ∀ j, b' j = ∑ i, Q i j • b i)
    (hA : ∀ i j, IsIntP (A i j) ∧
      A i j ∈ closure (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))))
    (hA' : ∀ i j, IsIntP (A' i j) ∧
      A' i j ∈ closure (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))))
    (hdet : ‖A.det‖ = 1)
    (hAu : ∀ i j, ∑ m, ∑ n, A i m * lamC lam (D.host.φ₀ ((hYY D (b m) (b n) : D.host.K) : D.host.E)) * σ (A j n) =
      if i = j then 1 else 0)
    (hA'u : ∀ i j, ∑ m, ∑ n, A' i m * lamC lam (D.host.φ₀ ((hYY D (b' m) (b' n) : D.host.K) : D.host.E)) * σ (A' j n) =
      if i = j then 1 else 0)
    (v v' : Fin r → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p]))
    (hv : ∀ i k, v i k = ∑ m, A i m * lamC lam (embT D k.1 (b m k.2.1 k.2.2)))
    (hv' : ∀ i k, v' i k = ∑ m, A' i m * lamC lam (embT D k.1 (b' m k.2.1 k.2.2)))
    (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]) (hI : IntLocV D (tor0 D cc δ) p lam v F) :
    IntLocV D (tor0 D cc δ) p lam v' F := by
  set G : Matrix (Fin r) (Fin r) ℂ_[p] :=
    Matrix.of fun m n => lamC lam (D.host.φ₀ ((hYY D (b m) (b n) : D.host.K) : D.host.E)) with hGd
  set Qt : Matrix (Fin r) (Fin r) ℂ_[p] := Matrix.of fun m n => lamC lam (D.host.φ₀ (Q n m)) with hQt
  have hG' := gram_change D lam σ hσ b b' Q hQK hb'
  have hAm : A * G * (A.map σ)ᵀ = 1 := unitary_mat σ A G hAu
  have hA'm : A' * (Matrix.of fun m n => lamC lam (D.host.φ₀ ((hYY D (b' m) (b' n) : D.host.K) : D.host.E))) *
      (A'.map σ)ᵀ = 1 := unitary_mat σ A' _ hA'u
  rw [hG'] at hA'm
  have hdet0 : A.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  have hPu := unitary_P σ A A' G Qt hAm hA'm hdet0
  set P : Matrix (Fin r) (Fin r) ℂ_[p] := A' * Qt * A⁻¹ with hP
  have hvP : ∀ i k, v' i k = ∑ j, P i j * v j k := v_change D lam b b' Q hQK hb' A A' hdet0 v v' hv hv'
  have hPe := entries D lam A A' Q hQK hQp hA hA' hdet
  let M : Fin r → Fin r → ℂ_[p] × ℂ_[p] := fun i j => (P j i, σ (P j i))
  have hM : ∀ i j, M i j ∈ OKp D lam := fun i j => conv D lam σ hσ _ (hPe j i).1 (hPe j i).2
  have hrow : ∀ j j', ∑ i, P j i * σ (P j' i) = if j = j' then 1 else 0 := by
    intro j j'
    have h := congrFun (congrFun hPu j) j'
    simpa [Matrix.mul_apply, Matrix.one_apply] using h
  have hMu : ∀ j j', ∑ i, M i j * (M i j').swap = if j = j' then 1 else 0 := by
    intro j j'
    have e1 : (∑ i, M i j * (M i j').swap).1 = ∑ i, P j i * σ (P j' i) := by
      simp [M, Prod.fst_sum]
    have e2 : (∑ i, M i j * (M i j').swap).2 = ∑ i, P j' i * σ (P j i) := by
      simp only [M, Prod.snd_sum, Prod.snd_mul, Prod.snd_swap]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    refine Prod.ext ?_ ?_
    · rw [e1, hrow]
      by_cases h : j = j' <;> simp [h]
    · rw [e2, hrow]
      by_cases h : j = j' <;> simp [h, eq_comm]
  intro C wq hC hW
  obtain ⟨S, hS0, hSI, hSl, V, hV, hPV⟩ := hU D cc δ hcc hδ p hp5 hin lam C wq hC hW r M hM hMu
  have hSs : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero hS0
  have key := atLogV_change D lam (lamOf D cc δ) C wq v v' P hvP S hS0 (fun j => hSl j) F
  show IntegralMv (atLogV D lam (lamOf D cc δ) C wq v' F * ePh lam (lamOf D cc δ) C wq r)
  rw [key, hPV, ← mul_assoc, ← MvPowerSeries.subst_mul hSs]
  exact integral_mul (integral_subst S hS0 hSI (hI C wq hC hW)) hV

end Lin

end ThetaInverseLemmas

open ThetaInverseLemmas in

theorem locInv_of (hU : UnitSubstLoc) : LocInv := by
  intro D cc δ hcc hδ p _ hp5 hin lam σ hσ N N' Y r r' v v' F hv hv' hI
  obtain ⟨b, A, hbL, hA, hdet, hAu, hvA⟩ := hv
  obtain ⟨b', A', hb'L, hA', hdet', hA'u, hvA'⟩ := hv'
  have hp : p.Prime := Fact.out
  obtain ⟨Q, hQK, hQp, hb'⟩ := IntegralOrthonormalChange.exists_coeffs D hp hbL hb'L
  obtain ⟨Q', hQK', -, hbb⟩ := IntegralOrthonormalChange.exists_coeffs D hp hb'L hbL
  have hrr : r' = r :=
    le_antisymm (IntegralOrthonormalChange.card_le D Q hQK hb'L.1 hb') (IntegralOrthonormalChange.card_le D Q' hQK' hbL.1 hbb)
  subst hrr
  exact locInv_core hU D cc δ hcc hδ p hp5 hin lam σ hσ b b' A A' Q hQK hQp hb' hA hA' hdet hAu hA'u v v'
    hvA hvA' F hI

open ThetaInverseLemmas in

theorem unitSubst_of_loc (hU : UnitSubstLoc) : UnitSubst := by
  intro D cc δ hcc hδ p _ hp5 hin lam C wq hC hW r A hAK hAp hAu
  have hp : p.Prime := Fact.out
  let M : Fin r → Fin r → ℂ_[p] × ℂ_[p] := fun i j =>
    (Formalism.MainNotions.GL3Theta.tauK D lam ⟨A i j, hAK i j⟩, Formalism.MainNotions.GL3Theta.tauKc D lam ⟨A i j, hAK i j⟩)
  have hM : ∀ i j, M i j ∈ Formalism.MainNotions.GL3Theta.OKp D lam := by
    intro i j
    obtain ⟨s, hs, c, hc⟩ := hAp i j
    have hs1 : ‖(s : ℂ_[p])‖ = 1 := by
      have hnd : ¬ (p : ℤ) ∣ (s : ℤ) := by
        intro h
        have h' : p ∣ s := by exact_mod_cast h
        exact (hp.coprime_iff_not_dvd.1 hs.symm) h'
      simpa using Formalism.MainNotions.Ext.CutA.norm_int_cp_eq_one (p := p) (s : ℤ) hnd
    have hc2 := Formalism.MainNotions.Ext.CutA.okp_norm_le D lam _ (okp_range D lam c)
    have h1 := congrArg (tauE D lam) hc
    have h2 := congrArg (fun x => tauE D lam (D.host.conj x)) hc
    simp only [map_mul, map_natCast] at h1 h2
    refine keyInt D lam _ ?_ ?_
    · show ‖lamC lam (D.host.φ₀ (A i j))‖ ≤ 1
      rw [← tauE_apply]
      have h3 : ‖(s : ℂ_[p]) * tauE D lam (A i j)‖ ≤ 1 := by
        rw [h1, tauE_apply]
        exact hc2.1
      rwa [norm_mul, hs1, one_mul] at h3
    · show ‖lamC lam (D.host.φ₀ (D.host.conj (A i j)))‖ ≤ 1
      rw [← tauE_apply]
      have h3 : ‖(s : ℂ_[p]) * tauE D lam (D.host.conj (A i j))‖ ≤ 1 := by
        rw [h2, tauE_apply]
        exact hc2.2
      rwa [norm_mul, hs1, one_mul] at h3
  have hE : ∀ j j', ∑ i, tauE D lam (A i j) * tauE D lam (D.host.conj (A i j')) = if j = j' then 1 else 0 := by
    intro j j'
    simp only [← map_mul, ← map_sum]
    rw [hAu j j']
    split_ifs <;> simp
  have hMu : ∀ j j', ∑ i, M i j * (M i j').swap = if j = j' then 1 else 0 := by
    intro j j'
    have e1 : (∑ i, M i j * (M i j').swap).1 = ∑ i, tauE D lam (A i j) * tauE D lam (D.host.conj (A i j')) := by
      simp only [M, Prod.fst_sum, Prod.fst_mul, Prod.fst_swap, tauE_apply]
      rfl
    have e2 : (∑ i, M i j * (M i j').swap).2 = ∑ i, tauE D lam (A i j') * tauE D lam (D.host.conj (A i j)) := by
      simp only [M, Prod.snd_sum, Prod.snd_mul, Prod.snd_swap, tauE_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    refine Prod.ext ?_ ?_
    · rw [e1, hE]
      by_cases h : j = j' <;> simp [h]
    · rw [e2, hE]
      by_cases h : j = j' <;> simp [h, eq_comm]
  obtain ⟨S, hS0, hSI, hSl, V, hV, hPV⟩ := hU D cc δ hcc hδ p hp5 hin lam C wq hC hW r M hM hMu
  exact ⟨S, hS0, hSI, fun i => hSl i, V, hV, hPV⟩

theorem basisInv_of_loc (hU : UnitSubstLoc) : BasisInv := basisInv_of_unitSubst (unitSubst_of_loc hU)

end Formalism.L2.KerInert
