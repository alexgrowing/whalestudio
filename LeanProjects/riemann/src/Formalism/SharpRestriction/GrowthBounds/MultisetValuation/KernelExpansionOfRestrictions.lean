import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NatCastInvMemRp

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def RestSExp (p : ℕ) [Fact p.Prime] : Prop :=
  5 ≤ p → DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (n' r0 r1 : ℕ), 2 ≤ n' → Even n' → ∀ (B : OmBasis p n')
    (Ph : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) (K0 p)),
    Simeq p Ph (∑ e : Eidx n' r0 r1, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : Fin n' → K', (∀ s, u s ∈ Rp p K' vp) ∧ ∃ V : MvPowerSeries (Zidx n' r0 r1) K', IntR (Rp p K' vp) V ∧
      ThZ B K' vp (MvPowerSeries.map (algebraMap (K0 p) K') (expS p (-Ph))) =
        expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u)) * V

def RestSInt (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n' r0 r1 : ℕ) (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U))

def RestSExpA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  DworkLemma p → ∀ be : MvPowerSeries (Fin 2) (K0 p), BeProp p be →
  ∀ (j : ℕ) (Ph : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)),
    Simeq p Ph (∑ e : X.EA j, sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))) →
  ∀ (K1 : Type) [Field K1] [Algebra (K0 p) K1] (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K']
    [IsScalarTower (K0 p) K1 K'] (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') →
    ∃ u : ∀ v : X.Pl, Fin (X.G.P.n' v) → K', (∀ v s, u v s ∈ Rp p K' vp) ∧
      ∃ V : MvPowerSeries (X.ZA j) K', IntR (Rp p K' vp) V ∧
        atPi vp (MvPowerSeries.map (algebraMap K1 K')
          (X.ThZA K1 j (MvPowerSeries.map (algebraMap (K0 p) K1) (expS p (-Ph))))) =
          (∏ v, expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * X.hhA K' j v (u v)))) * V

def RestSIntA {p : ℕ} [Fact p.Prime] (X : Sys p) : Prop :=
  ∀ (j : ℕ) (K1 : Type) [Field K1] [Algebra (K0 p) K1] (R1 : Subring K1)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) K1), IntR R1 (inParamK p K1 U) →
  ∀ (K' : Type) [Field K'] [Algebra (K0 p) K'] [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (R' : Subring K')
    (vp : K'), vp ^ (p ^ 2 - 1) = (p : K') → Rp p K' vp ≤ R' → (∀ x ∈ R1, algebraMap K1 K' x ∈ R') →
    IntR R' (atPi vp (MvPowerSeries.map (algebraMap K1 K') (X.ThZA K1 j U)))

section Formal

variable {p : ℕ} [hp : Fact p.Prime]

theorem sSer_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (e : Fin n') (a : Fin r0) (b : Fin r1) :
    MvPowerSeries.constantCoeff (sSer p K' e a b) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ l ∈ range ((0 : Zidx n' r0 r1 →₀ ℕ).degree + 1),
    if (0 : Zidx n' r0 r1 →₀ ℕ) = Finsupp.single (posSub e (2 * l), a, b) (p ^ (2 * l)) then ((-1 : K') ^ l) else 0) = 0
  refine Finset.sum_eq_zero fun l _ => if_neg fun h => ?_
  exact pow_ne_zero (2 * l) hp.out.ne_zero (Finsupp.single_eq_zero.1 h.symm)

theorem hhS_const {n' r0 r1 : ℕ} (K' : Type) [Field K'] (u : Fin n' → K') :
    MvPowerSeries.constantCoeff (hhS (r0 := r0) (r1 := r1) p K' u) = 0 := by
  unfold hhS
  simp only [map_sum, map_mul, sSer_const, mul_zero, Finset.sum_const_zero]

theorem coordZ_const {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (x : Eidx n' r0 r1 ⊕ Eidx n' r0 r1) : MvPowerSeries.constantCoeff (coordZ B K' vp x) = 0 := by
  rcases x with ⟨r, a, b⟩ | ⟨r, a, b⟩ <;>
  simp only [coordZ, map_sum, map_mul, MvPowerSeries.constantCoeff_X, mul_zero, Finset.sum_const_zero]

theorem ThZ_mul {n' r0 r1 : ℕ} (B : OmBasis p n') (K' : Type) [Field K'] [Algebra (K0 p) K'] (vp : K')
    (f g : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K') :
    ThZ B K' vp (f * g) = ThZ B K' vp f * ThZ B K' vp g :=
  MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero (coordZ_const B K' vp)) f g

theorem map_map_tower {ι : Type} (K1 K' : Type) [Field K1] [Algebra (K0 p) K1] [Field K'] [Algebra (K0 p) K']
    [Algebra K1 K'] [IsScalarTower (K0 p) K1 K'] (f : MvPowerSeries ι (K0 p)) :
    MvPowerSeries.map (algebraMap K1 K') (MvPowerSeries.map (algebraMap (K0 p) K1) f) =
      MvPowerSeries.map (algebraMap (K0 p) K') f := by
  rw [IsScalarTower.algebraMap_eq (K0 p) K1 K', MvPowerSeries.map_comp]
  rfl

theorem atPi_mul {σ R : Type} [CommRing R] (vp : R) (f g : MvPowerSeries σ R) :
    atPi vp (f * g) = atPi vp f * atPi vp g := by
  classical
  ext n
  show vp ^ n.degree * MvPowerSeries.coeff n (f * g) = MvPowerSeries.coeff n (atPi vp f * atPi vp g)
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hx' : x.1 + x.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  show _ = (vp ^ x.1.degree * MvPowerSeries.coeff x.1 f) * (vp ^ x.2.degree * MvPowerSeries.coeff x.2 g)
  rw [← hx', map_add, pow_add]
  ring

theorem exp_change {ι : Type} (K' : Type) [Field K'] [Algebra (K0 p) K'] (c : K') (hh hh' G : MvPowerSeries ι K')
    (h0 : MvPowerSeries.constantCoeff hh = 0) (h0' : MvPowerSeries.constantCoeff hh' = 0)
    (hE : hh' = hh + MvPowerSeries.C (p : K') * G) :
    expK (-(MvPowerSeries.C (c / (p : K')) * hh)) =
      expK (-(MvPowerSeries.C (c / (p : K')) * hh')) * expK (MvPowerSeries.C c * G) := by
  have := charZero_K' p K'
  have hp0 := pK'_ne p K'
  have hG : MvPowerSeries.constantCoeff G = 0 := by
    have := congrArg MvPowerSeries.constantCoeff hE
    rw [map_add, map_mul, h0, h0', zero_add, MvPowerSeries.constantCoeff_C] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact absurd h hp0
    · exact h
  rw [← expK_add (by rw [map_neg, map_mul, h0', mul_zero, neg_zero]) (by rw [map_mul, hG, mul_zero])]
  congr 1
  have e : (MvPowerSeries.C (c / (p : K')) : MvPowerSeries ι K') * MvPowerSeries.C (p : K') = MvPowerSeries.C c := by
    rw [← map_mul, div_mul_cancel₀ _ hp0]
  rw [hE, mul_add, ← mul_assoc, e]
  ring

end Formal

theorem SConcl_of {p : ℕ} [Fact p.Prime] (h5 : 5 ≤ p) (hD : DworkLemma p) (hE : RestSExp p) (hI : RestSInt p)
    {n' r0 r1 : ℕ} (h2 : 2 ≤ n') (hev : Even n') (B : OmBasis p n') (K1 : Type) [Field K1] [Algebra (K0 p) K1]
    (R1 : Subring K1) (be : MvPowerSeries (Fin 2) (K0 p)) (Th : MvPowerSeries (Eidx n' r0 r1 ⊕ Eidx n' r0 r1) K1)
    (hK : ExtensionLocalCondition p K1 R1 be Th) : SConcl B K1 R1 Th := by
  obtain ⟨Ph, U, hTh, hU, _, hbe, hPh⟩ := hK
  intro K' _ _ _ _ R' vp hvp hRp hR1
  obtain ⟨u, hu, V, hV, hEq⟩ := hE h5 hD be hbe n' r0 r1 h2 hev B Ph hPh K' vp hvp
  refine ⟨u, fun s => hRp (hu s), fun hh' h0' hG => ?_⟩
  obtain ⟨G, hG, hhE⟩ := hG
  have hW := hI n' r0 r1 B K1 R1 U hU K' R' vp hvp hRp hR1
  have hc : ∀ k : ℕ, (vp ^ (p + 1)) ^ k * ((k.factorial : K'))⁻¹ ∈ R' := fun k => hRp (piFact p K' vp hvp k)
  have e1 : ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') Th) =
      expK (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hh')) *
        (expK (MvPowerSeries.C (vp ^ (p + 1)) * G) * V * ThZ B K' vp (MvPowerSeries.map (algebraMap K1 K') U)) := by
    rw [hTh, map_mul, map_map_tower, ThZ_mul, hEq,
      exp_change K' (vp ^ (p + 1)) (hhS p K' u) hh' G (hhS_const K' u) h0' hhE]
    ring
  rw [e1]
  exact inClass_of_exp (pK'_ne p K') hc hh' h0' (IntR_mul (IntR_mul (IntR_expK hc hG) (IntR_mono hRp hV)) hW)

theorem kernel_expansion_of_restrictions (D : Formalism.BasicNotions.D7) {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X) (hA : admitted D X Y)
    (hE : RestSExp p) (hI : RestSInt p) : Conclusion1 D X Y := by
  intro v j hj La La' h1 h2 φ
  exact SConcl_of (X.std v).five_le (hA.1 p) hE hI (X.std v).two_le (X.std v).even (X.om v) Y.Kc Y.Oc Y.be _
    (hA.2.1 v j hj La La' h1 h2 φ)

end Formalism.MainNotions.FormalGroupSystem.Pf
