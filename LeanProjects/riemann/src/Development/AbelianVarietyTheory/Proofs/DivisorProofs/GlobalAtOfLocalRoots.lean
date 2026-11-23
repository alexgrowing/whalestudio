import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHomogeneousAevalOfWeighted

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open Finset GlobalTheory.HodgeTateGlobal

namespace GlobalTheory.MixedGlobalChern

section Model

variable {D : D7} {p : ℕ} [Fact p.Prime] {N j : ℕ} {jc : KW p →+* ℂ}

theorem lie_pow_eq (M : DV.Mdl D p N (rkOf (PsiOf D jc) N j)) (rt : Bool × Rt D.what₂.Tau N → M.Z.LB)
    (hj : j ≤ N) (hR : Roots jc M rt) (τ : Emb D p) (σ : EmbC D) (h : jc.comp τ = D.host.emb (toGG D σ)) (k : ℕ) :
    ∑ l, M.Z.c1 ((M.lie τ).x l) ^ k = evC M rt (liePow j k σ) := by
  rcases σ with τ₀ | τ₀
  · rw [evC_liePow_inl]
    refine sum_low (rkOf_eq _ τ τ₀ h _ _) hj _ _ fun l i hi => ?_
    rw [((hR τ₀ τ h).1 l i hi).1]
  · obtain ⟨τ', h', rfl⟩ := exists_cEmb _ τ τ₀ h
    obtain ⟨e, he⟩ := M.om_dual τ'
    rw [evC_liePow_inr, ← e.sum_comp]
    refine sum_high (by rw [rkOf_eq _ τ' τ₀ h']) _ _ fun l i hi => ?_
    rw [((hR τ₀ τ' h').2 l i hi).1, he, neg_neg]

theorem chDiv_eq_chern {rk : Emb D p → ℕ} {chern : MvPolynomial (Rt D.what₂.Tau N) ℝ →ₗ[ℝ] ℝ} (M : DV.Mdl D p N rk)
    (rt : Bool × Rt D.what₂.Tau N → M.Z.LB) (h5 : Cons M rt chern) {r : ℕ} (x : Fin r → M.Z.LB) {k m : ℕ}
    (hm : k + m = dimFl D.what₂.Tau N) {H G : MvPolynomial (Vm D.what₂.Tau N) ℚ}
    (hH : H.IsWeightedHomogeneous (wt D.what₂.Tau N) k) (hG : G.IsWeightedHomogeneous (wt D.what₂.Tau N) m)
    (h : ∀ Q, M.Z.capDeg M.Z.divP ((∑ l, M.Z.c1 (x l) ^ k) * Q) = M.Z.capDeg M.Z.divP (evC M rt H * Q)) :
    chDiv x k (evC M rt G) / (M.cov : ℝ) =
      chern (C ((Nat.factorial k : ℝ)⁻¹) * collapse D _ (toR H) * collapse D _ (toR G)) := by
  have := h5 (H * G) (hm ▸ hH.mul hG)
  rw [chDiv, h, ← evC_mul, div_right_comm, this, mul_assoc, ← smul_eq_C_mul, map_smul, ← map_mul, smul_eq_mul,
    div_eq_inv_mul]
  simp only [toR, map_mul]

end Model

theorem mean_one {ι : Type} [Fintype ι] (w : ι → ℝ) (hw : ∑ la, w la = 1) (F f : ι → ℝ) (c : ℝ)
    (hF : ∀ la, F la = w la * f la) (h : ∀ la, f la = c) : ∑ la, F la = c := by
  simp only [hF, h]
  rw [← Finset.sum_mul, hw, one_mul]

end GlobalTheory.MixedGlobalChern

namespace GlobalTheory.MixedGlobalChern

theorem globAt_of_local : ∀ (D : D7) (Y : ShimX D.what₂.Tau) (p : ℕ) [Fact p.Prime] (ι : Type) [Fintype ι] (w : ι → ℝ)
    (jc : ι → (KW p →+* ℂ)) (M : ∀ la, DV.Mdl D p Y.N (rkOf (PsiOf D (jc la)) Y.N Y.j))
    (rt : ∀ la, Bool × Rt D.what₂.Tau Y.N → (M la).Z.LB), UnramE D p → Term Y p w jc M rt →
    (∀ la, Roots (jc la) (M la) (rt la) ∧ Comm (M la) ∧ Cons (M la) (rt la) Y.chern ∧ Local (M la)) → GlobAt Y p := by
  intro D Y p _ ι _ w jc M rt hu hT hA Sx R τ k hk m hm
  have hp : p.Prime := Fact.out
  refine real_of_rat (ι := EmbC D) _ m
    ((Y.arMix Sx R p).comp (LinearMap.mulLeft ℝ _))
    (fun σ => Y.chern.comp ((LinearMap.mulLeft ℝ (chLie Y.j (k - 1) σ)).comp (collapse D _).toLinearMap))
    (fun n => frobEmb D p (n + 1) (Sum.inl τ)) (Sum.inl τ) _ _ _ (by positivity) (inv_pow_lt_one hp hk) fun G hG => ?_
  choose τ' hτ' using fun la : ι => GlobalTheory.UnramEmb.exists_emb_comp_eq D p hu (jc la) (toGG D (Sum.inl τ))
  have hrk : ∀ la, rkOf (PsiOf D (jc la)) Y.N Y.j (τ' la) = Y.j := fun la => rkOf_eq _ _ τ (hτ' la) _ _
  have hrk' : ∀ la, Y.N - rkOf (PsiOf D (jc la)) Y.N Y.j (τ' la) = Y.N - Y.j := fun la => by rw [hrk]
  have hj := Y.j_lt
  have hD : ∀ i, (divDiff k (τ, i) * G).IsWeightedHomogeneous (wt D.what₂.Tau Y.N) (dimFl D.what₂.Tau Y.N) := fun i => by
    have := (homog_divDiff k (τ, i)).mul hG
    rwa [show k - 1 + m = dimFl D.what₂.Tau Y.N by omega] at this
  have hlow : ∑ i ∈ univ.filter (fun i : Fin Y.N => (i : ℕ) < Y.j),
      Y.arMix Sx R p (dRt D.what₂.Tau _ (τ, i) * toR (divDiff k (τ, i) * G)) =
      Real.log p * ∑ la, w la * ((ck ((M la).lie (τ' la)) k (evC (M la) (rt la) G) : ℝ) / ((M la).cov : ℝ)) := by
    rw [← sum_low rfl hj.le (fun l : Fin Y.j => Real.log p * ∑ la, w la *
      ((((M la).Z.capDeg (((M la).lie (τ' la)).Dv (Fin.cast (hrk la).symm l))
        (evC (M la) (rt la) (divDiff k (τ, Fin.castLE hj.le l) * G)) : ℚ) : ℝ) / ((M la).cov : ℝ))) _
      fun l i hi => by
        obtain rfl : i = Fin.castLE hj.le l := Fin.ext hi
        exact (hT.lie Sx R τ τ' hτ' (fun la => Fin.cast (hrk la).symm l) _ (fun _ => rfl) _ (hD _)).symm,
      ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [← Finset.mul_sum, ck, Rat.cast_sum, Finset.sum_div, ← (finCongr (hrk la).symm).sum_comp]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    have := ((hA la).1 τ (τ' la) (hτ' la)).1 (Fin.cast (hrk la).symm l) (Fin.castLE hj.le l) rfl
    rw [evC_mul, evC_divDiff, this.1, this.2]
    rfl
  have hhigh : ∑ i ∈ univ.filter (fun i : Fin Y.N => Y.j ≤ (i : ℕ)),
      Y.arMix Sx R p (dRt D.what₂.Tau _ (τ, i) * toR (divDiff k (τ, i) * G)) =
      Real.log p * ∑ la, w la * ((ck ((M la).om (τ' la)) k (evC (M la) (rt la) G) : ℝ) / ((M la).cov : ℝ)) := by
    rw [← sum_high rfl (fun l : Fin (Y.N - Y.j) => Real.log p * ∑ la, w la *
      ((((M la).Z.capDeg (((M la).om (τ' la)).Dv (Fin.cast (hrk' la).symm l))
        (evC (M la) (rt la) (divDiff k (τ, ⟨Y.j + l, by omega⟩) * G)) : ℚ) : ℝ) / ((M la).cov : ℝ))) _
      fun l i hi => by
        obtain rfl : i = ⟨Y.j + l, Nat.add_lt_of_lt_sub' l.2⟩ := Fin.ext hi
        exact (hT.om Sx R τ τ' hτ' (fun la => Fin.cast (hrk' la).symm l) _ (fun _ => rfl) _ (hD _)).symm,
      ← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [← Finset.mul_sum, ck, Rat.cast_sum, Finset.sum_div, ← (finCongr (hrk' la).symm).sum_comp]
    congr 1
    refine Finset.sum_congr rfl fun l _ => ?_
    have := ((hA la).1 τ (τ' la) (hτ' la)).2 (Fin.cast (hrk' la).symm l) ⟨Y.j + l, by omega⟩ rfl
    rw [evC_mul, evC_divDiff, this.1, this.2]
    rfl
  rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, tag_sub, map_smul, map_sum, sum_split Y.j, hlow, hhigh,
    ← mul_add, smul_eq_mul, mul_left_comm, ← Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  refine mean_one w hT.sum_w _ _ _ (fun la => by rw [← mul_add, mul_left_comm]) fun la => ?_
  have hL := (hA la).2.2.2 (τ' la) k hk m hm _ (homog_evV _ (rt la) hG)
  have hL' := congrArg (fun x : ℝ => x / ((M la).cov : ℝ)) hL
  refine Eq.trans ?_ (hL'.trans ?_)
  · simp only [chk, evC]
    ring
  have key : ∀ (t : Emb D p) (σ : EmbC D), (jc la).comp t = D.host.emb (toGG D σ) →
      chDiv ((M la).lie t).x (k - 1) (evC (M la) (rt la) G) / ((M la).cov : ℝ) =
      Y.chern (chLie Y.j (k - 1) σ * collapse D _ (toR G)) := fun t σ h => by
    rw [chLie_eq]
    exact chDiv_eq_chern (M la) (rt la) (hA la).2.2.1 _ (by omega) (homog_liePow _ _ σ) hG fun Q => by
      rw [lie_pow_eq (M la) (rt la) Y.j_lt.le (hA la).1 t σ h]
  refine tsum_div_sub _ _ _ _ _ _ _ _ (fun n => key _ _ ?_) (key _ _ (hτ' la))
  rw [frobEmb, toGG_ofGG]
  exact comp_phiPow hu _ _ _ (hτ' la) _

end GlobalTheory.MixedGlobalChern
