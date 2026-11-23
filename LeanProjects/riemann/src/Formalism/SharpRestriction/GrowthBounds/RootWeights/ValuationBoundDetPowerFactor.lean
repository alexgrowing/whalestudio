import Formalism.SharpRestriction.GrowthBounds.RootWeights.IdentityEvaluationGenericMatrix

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

private theorem sDegs_eq_support_mul_Phi_twistSub {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι)
    (j : Fin n) (H : MvPolynomial (ι × Fin n) R) :
    sDegs LL S j H = (mul_Phi _ _ (twistSub LL S j H)).coeff.support := by
  ext k
  simp only [sDegs, Finset.mem_biUnion, Finsupp.mem_support_iff, MvPolynomial.mem_support_iff]
  constructor
  · rintro ⟨m, -, hk⟩ h0
    apply hk
    rw [← mul_Phi_coeff, h0, MvPolynomial.coeff_zero]
  · intro hk
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hk
    rw [mul_Phi_coeff] at hm
    refine ⟨m, fun h => hm ?_, hm⟩
    rw [h]
    rfl

theorem mul_valS_eq {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (H : MvPolynomial (ι × Fin n) R) : valS LL S H =
      ((mul_Phi _ _ (twistSub LL S (lastIdx n) H)).coeff.support.inf fun k => (k : WithTop ℤ)) := by
  rw [valS, sDegs_eq_support_mul_Phi_twistSub]

theorem mul_lam1S_eq {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (H : MvPolynomial (ι × Fin n) R) : lam1S LL S H =
      ((mul_Phi _ _ (twistSub LL S (0 : Fin n) H)).coeff.support.sup fun k => (k : WithBot ℤ)) := by
  rw [lam1S, sDegs_eq_support_mul_Phi_twistSub]

theorem mul_valS_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : min (valS LL S F) (valS LL S G) ≤ valS LL S (F + G) := by
  rw [mul_valS_eq LL S F, mul_valS_eq LL S G, mul_valS_eq LL S (F + G), map_add, map_add]
  refine le_trans ?_ (Finset.inf_mono Finsupp.support_add)
  rw [Finset.inf_union]
  exact le_rfl

theorem mul_lam1S_add {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (F G : MvPolynomial (ι × Fin n) R) : lam1S LL S (F + G) ≤ max (lam1S LL S F) (lam1S LL S G) := by
  rw [mul_lam1S_eq LL S F, mul_lam1S_eq LL S G, mul_lam1S_eq LL S (F + G), map_add, map_add]
  refine le_trans (Finset.sup_mono Finsupp.support_add) ?_
  rw [Finset.sup_union]
  exact le_rfl

theorem valuation_bound_det_power_factor (R : Type) [Field R] (ι : Type) (LL : Letters ι) (r : ℕ) [NeZero r]
    (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, LL.vec (A l) = true)
    (G H : MvPolynomial (ι × Fin r) R) (m : ℕ) (hG : G = (detA (R := R) A) ^ m * H) (S' : Set ι) :
    valS LL S' G ≤ valS LL S' H + ((m : ℤ) : WithTop ℤ) := by
  have hd := mul_valS_detA_le (R := R) LL A hA hv S'
  have hpow : ∀ k : ℕ, valS LL S' ((detA (R := R) A) ^ (k + 1)) ≤ (((k + 1 : ℕ) : ℤ) : WithTop ℤ) := by
    intro k
    induction k with
    | zero => simpa using hd
    | succ k ih =>
      rw [pow_succ, mul_valS_mul]
      calc valS LL S' ((detA (R := R) A) ^ (k + 1)) + valS LL S' (detA (R := R) A)
          ≤ (((k + 1 : ℕ) : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ) := add_le_add ih hd
        _ = (((k + 1 + 1 : ℕ) : ℤ) : WithTop ℤ) := by
          rw [← WithTop.coe_add]
          congr 1
  subst hG
  rcases m with _ | k
  · simp
  · rw [mul_valS_mul, add_comm (valS LL S' _) (valS LL S' H)]
    exact add_le_add (le_refl _) (hpow k)

def GlOperatorsFormRepresentation : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι)
    (A : Fin r → ι), Function.Injective A → (∀ l, A l ∈ S ∧ LL.vec (A l) = true) →
    (∀ (d : ι → ℕ) (G : MvPolynomial (ι × Fin r) R), G ∈ Pol R r d →
      ∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → (degOther LL S A d : ℤ) < th →
        (detA (R := R) A) ^ (th - degOther LL S A d).toNat ∣ G)

theorem prvE_of_gl_operators_form_representation (D : Formalism.BasicNotions.D7) (h : GlOperatorsFormRepresentation) : ConclusionE D := by
  intro R _ ι _ LL r _ S A hA hAS
  exact ⟨h R ι LL r S A hA hAS,
    fun G H m hG S' => valuation_bound_det_power_factor R ι LL r A hA (fun l => (hAS l).2) G H m hG S'⟩

def GeneratedModuleWeightDescription : Prop :=
  ∀ (R : Type) [Field R] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι),
    (∀ (G : MvPolynomial (ι × Fin n) R) (th : ℤ), ((th : WithTop ℤ) ≤ valS LL S G ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), th ≤ mu (lastIdx n))) ∧
    (∀ (G : MvPolynomial (ι × Fin n) R) (M : ℤ), (lam1S LL S G ≤ (M : WithBot ℤ) ↔
      ∀ mu ∈ polWts LL S (polGenSub R LL S G), mu 0 ≤ M))

theorem valuations_additive_of_generated_weight_description (D : Formalism.BasicNotions.D7) (h : GeneratedModuleWeightDescription) : ValuationsAdditive D := by
  intro R _ ι _ LL n _ S
  exact ⟨mul_valS_mul LL S, mul_valS_add LL S, mul_lam1S_mul LL S, mul_lam1S_add LL S,
    (h R ι LL n S).1, (h R ι LL n S).2⟩

end Formalism.MainNotions.G.GLWeightTheory
