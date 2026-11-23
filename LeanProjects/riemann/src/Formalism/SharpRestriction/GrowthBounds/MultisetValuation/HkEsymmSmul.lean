import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.CoupledSumOfEntries

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

theorem hk_scal {K : Type} [Field K] (P a a' e : K) (hP : P ≠ 0) (ha : a ≠ 0) (h vm N g i l : ℤ) :
    P ^ (-(h * i * ((N + g) - i))) * (P ^ (vm * i) * (a' ^ (-i) * P ^ (h * N * i))) *
        (P ^ (2 * h * ((i - l) * (g - l))) * (P ^ (h * (l * (g - l))) * e)) *
        (P ^ (vm * (i - l)) * (a ^ (i - l) * P ^ (h * (N + g) * (i - l))))⁻¹ =
      ((a * a')⁻¹) ^ i * ((a * P ^ vm) ^ l * e) * P ^ (-(h * (i - l) * (N - (i - l)))) := by
  have e1 : P ^ (-(h * i * ((N + g) - i))) * P ^ (vm * i) * P ^ (h * N * i) * P ^ (2 * h * ((i - l) * (g - l))) *
      P ^ (h * (l * (g - l))) * (P ^ (vm * (i - l)))⁻¹ * (P ^ (h * (N + g) * (i - l)))⁻¹ =
      P ^ (vm * l) * P ^ (-(h * (i - l) * (N - (i - l)))) := by
    rw [← zpow_neg, ← zpow_neg]
    simp only [← zpow_add₀ hP]
    congr 1
    ring
  have e2 : (a ^ (i - l))⁻¹ = (a ^ i)⁻¹ * a ^ l := by
    rw [zpow_sub₀ ha, inv_div, div_eq_mul_inv, mul_comm]
  calc _ = (P ^ (-(h * i * ((N + g) - i))) * P ^ (vm * i) * P ^ (h * N * i) * P ^ (2 * h * ((i - l) * (g - l))) *
      P ^ (h * (l * (g - l))) * (P ^ (vm * (i - l)))⁻¹ * (P ^ (h * (N + g) * (i - l)))⁻¹) *
        (a ^ (i - l))⁻¹ * a' ^ (-i) * e := by ring
    _ = (P ^ (vm * l) * P ^ (-(h * (i - l) * (N - (i - l))))) * ((a ^ i)⁻¹ * a ^ l) * a' ^ (-i) * e := by
      rw [e1, e2]
    _ = _ := by
      rw [inv_zpow, mul_zpow, mul_zpow, ← zpow_mul, mul_inv, zpow_neg a' i]
      ring

theorem hk_esymm_smul {K σ : Type} [Field K] [Fintype σ] (c : K) (f : σ → K) (l : ℕ) :
    MvPolynomial.eval (fun x => c * f x) (MvPolynomial.esymm σ K l) =
      c ^ l * MvPolynomial.eval f (MvPolynomial.esymm σ K l) := by
  simp only [MvPolynomial.esymm, map_sum, map_prod, MvPolynomial.eval_X, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, (Finset.mem_powersetCard.1 ht).2]

theorem hk_esymm_zero {K σ : Type} [Field K] [Fintype σ] (l : ℕ) (h : Fintype.card σ < l) :
    MvPolynomial.esymm σ K l = 0 := by
  rw [MvPolynomial.esymm, Finset.powersetCard_eq_empty.2 (by rwa [Finset.card_univ]), Finset.sum_empty]

variable {p : ℕ} [Fact p.Prime] (X : Sys p)

def eBe (v : X.Pl) (l : ℕ) : X.G.Kf :=
  MvPolynomial.eval (fun x : Fin (X.t + 1) => X.qh v x.val) (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)

theorem nC_cast (hp : (p : X.G.Kf) ≠ 0) (v : X.Pl) (i l : ℕ) :
    (nC X v i l : X.G.Kf) = (p : X.G.Kf) ^ (2 * hv X v * (((i - l : ℕ) : ℤ) * ((X.t + 1 - l : ℕ) : ℤ))) *
      ((p : X.G.Kf) ^ (hv X v * ((l : ℤ) * ((X.t + 1 - l : ℕ) : ℤ))) * eBe X v l) := by
  obtain ⟨k, hk⟩ := (X.std v).even
  have h1 : X.G.P.n' v / 2 = k := by omega
  have h2 : p ^ X.G.P.n' v = (p ^ k) ^ 2 := by rw [← pow_mul]; congr 1; omega
  have hQ : (((p ^ k : ℕ) : ℕ) : X.G.Kf) ≠ 0 := by push_cast; exact pow_ne_zero _ hp
  have hG := Formalism.InvariantFactorPaths.G7.gauss_elementary_symmetric X.G.Kf (p ^ k) (X.t + 1) l hQ
  have hf : Formalism.InvariantFactorPaths.G7.beFam ((p : X.G.Kf) ^ k) (X.t + 1) = fun x => X.qh v x.val := funext fun x => by
    have := beFam_eq X v x
    rwa [h1] at this
  have hb : Formalism.InvariantFactorPaths.G7.eF (Formalism.InvariantFactorPaths.G7.beFam ((p : X.G.Kf) ^ k) (X.t + 1)) l = eBe X v l := by
    unfold Formalism.InvariantFactorPaths.G7.eF eBe
    rw [hf]
  unfold nC
  rw [h2]
  push_cast at hG ⊢
  rw [hG, hb]
  unfold hv
  rw [h1]
  congr 1
  · rw [← pow_mul, ← pow_mul, ← zpow_natCast]
    congr 1
    push_cast
    ring
  · congr 1
    rw [← pow_mul, ← zpow_natCast]
    congr 1

theorem NN_succ (k1 t j : ℕ) : (NN k1 t (j + 1) : ℤ) = (NN k1 t j : ℤ) + ((t + 1 : ℕ) : ℤ) := by
  unfold NN
  push_cast
  ring

theorem hk_coef (hp : (p : X.G.Kf) ≠ 0) (a a' : X.G.Kf) (ha : a ≠ 0) (v : X.Pl) (j i l : ℕ) (hl : l ≤ i) :
    (p : X.G.Kf) ^ (-(hv X v * i * ((NN X.G.P.m X.t (j + 1) : ℤ) - i))) * cA X a' v j i * (nC X v i l : X.G.Kf) *
        (cC X a v j (i - l))⁻¹ =
      ((a * a')⁻¹) ^ i * (MvPolynomial.eval (fun x : Fin (X.t + 1) => (a * (p : X.G.Kf) ^ (X.vm v (j + 1))) * X.qh v x.val)
          (MvPolynomial.esymm (Fin (X.t + 1)) X.G.Kf l)) *
        (p : X.G.Kf) ^ (-(hv X v * ((i - l : ℕ) : ℤ) * ((NN X.G.P.m X.t j : ℤ) - ((i - l : ℕ) : ℤ)))) := by
  rw [hk_esymm_smul, nC_cast X hp]
  show _ = ((a * a')⁻¹) ^ i * ((a * (p : X.G.Kf) ^ (X.vm v (j + 1))) ^ l * eBe X v l) * _
  by_cases hg : l ≤ X.t + 1
  · have := hk_scal (p : X.G.Kf) a a' (eBe X v l) hp ha (hv X v) (X.vm v (j + 1)) (NN X.G.P.m X.t j : ℤ)
      ((X.t + 1 : ℕ) : ℤ) i l
    unfold cA cC
    rw [NN_succ, Nat.cast_sub hl, Nat.cast_sub hg, ← zpow_natCast ((a * a')⁻¹) i,
      ← zpow_natCast (a * (p : X.G.Kf) ^ (X.vm v (j + 1))) l]
    exact this
  · have h0 : eBe X v l = 0 := by
      unfold eBe
      rw [hk_esymm_zero l (by simpa using not_le.1 hg), map_zero]
    rw [h0]
    simp

end Formalism.MainNotions.FormalGroupSystem.Pf
