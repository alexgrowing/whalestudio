import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.KernelExpansionOfRestrictions

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem sSA_const (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (e : Fin (X.G.P.n' v)) (a : Fin (NN X.G.P.m X.t j))
    (b : Fin (NN X.G.P.m X.t (j + 1))) : MvPowerSeries.constantCoeff (X.sSA K' j v e a b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ l ∈ range ((0 : X.ZA j →₀ ℕ).degree + 1),
    if (0 : X.ZA j →₀ ℕ) = Finsupp.single (⟨v, (posSub e (2 * l), a, b)⟩ : X.ZA j) (p ^ (2 * l))
      then ((-1 : K') ^ l) else 0) = 0
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  exact pow_ne_zero (2 * l) hp.out.ne_zero (Finsupp.single_eq_zero.1 h.symm)

theorem hhA_const (K' : Type) [Field K'] (j : ℕ) (v : X.Pl) (u : Fin (X.G.P.n' v) → K') :
    MvPowerSeries.constantCoeff (X.hhA K' j v u) = 0 := by
  unfold Sys.hhA
  simp only [map_sum, map_mul, sSA_const, mul_zero, Finset.sum_const_zero]

theorem coordZA_const (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (x : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K' j x) = 0 := by
  rcases x with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;>
  simp only [Sys.coordZA, map_sum, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem ThZA_mul (K' : Type) [Field K'] [Algebra (K0 p) K'] (j : ℕ) (f g : MvPowerSeries (X.EA j ⊕ X.EA j) K') :
    X.ThZA K' j (f * g) = X.ThZA K' j f * X.ThZA K' j g :=
  MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZA_const X K' j)) f g

theorem all_places_of_restrictions (D : Formalism.BasicNotions.D7) (Y : Pend X) (hA : admitted D X Y)
    (hE : RestSExpA X) (hI : RestSIntA X) : ExpansionsMultiply D X Y := by
  intro j hj La La' h1 h2 φ K' _ _ _ _ R' vp hvp hRp hR1
  obtain ⟨Ph, U, hTh, hU, _, hbe, hPh⟩ := hA.2.2.1 j hj La La' h1 h2 φ
  obtain ⟨u, hu, V, hV, hEq⟩ := hE (hA.1 p) Y.be hbe j Ph hPh Y.Kc K' vp hvp
  refine ⟨u, fun v s => hRp (hu v s), fun h' hh' => ?_⟩
  choose h0' G hG hGE using hh'
  have hW := hI j Y.Kc Y.Oc U hU K' R' vp hvp hRp hR1
  have hc : ∀ k : ℕ, (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ R' := fun k => hRp (piFact p K' vp hvp k)
  have e1 : atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j (Y.ThA j La La' φ))) =
      (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * h' v))) *
        ((∏ v, expK (MvPowerSeries.C (vp ^ (p + 1)) * G v)) * V *
          atPi vp (MvPowerSeries.map (algebraMap Y.Kc K') (X.ThZA Y.Kc j U))) := by
    rw [hTh, ThZA_mul, map_mul, atPi_mul, hEq,
      Finset.prod_congr rfl fun v _ => exp_change K' (vp ^ (p + 1)) (X.hhA K' j v (u v)) (h' v) (G v)
        (hhA_const X K' j v (u v)) (h0' v) (hGE v), Finset.prod_mul_distrib]
    ring
  rw [e1]
  exact inProd_of_exp (pK'_ne p K') hc h' h0'
    (IntR_mul (IntR_mul (IntR_prod _ _ fun v _ => IntR_expK hc (hG v)) (IntR_mono hRp hV)) hW)

end Formalism.MainNotions.FormalGroupSystem.Pf
