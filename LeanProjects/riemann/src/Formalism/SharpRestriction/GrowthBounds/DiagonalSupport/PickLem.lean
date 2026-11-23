import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickDefs
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.Proposition5OfThreeParts

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

section Co

variable {σ τ : Type} {Kf : Type} [Field Kf]

theorem coeff_planeCoeff (nu : τ →₀ ℕ) (F : MvPolynomial σ (MvPolynomial τ Kf)) (bp : σ →₀ ℕ) :
    (planeCoeff nu F).coeff bp = (F.coeff bp).coeff nu := by
  unfold planeCoeff
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, coeff_zero]

theorem coeff_oneT (e : Module.End Kf (MvPolynomial τ Kf)) (F : MvPolynomial σ (MvPolynomial τ Kf)) (bp : σ →₀ ℕ) :
    (oneT e F).coeff bp = e (F.coeff bp) := by
  unfold oneT
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, map_zero]

theorem coeff_diagK (g : (σ →₀ ℕ) → Kf) (F : MvPolynomial σ Kf) (mo : σ →₀ ℕ) :
    (diagK g F).coeff mo = g mo * F.coeff mo := by
  unfold diagK
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.1 h, mul_zero]

theorem diagK_mem_pol {ι : Type} {n : ℕ} (d : ι → ℕ) (g : (ι × Fin n →₀ ℕ) → Kf) {F : MvPolynomial (ι × Fin n) Kf}
    (hF : F ∈ Pol Kf n d) : diagK g F ∈ Pol Kf n d := by
  rw [Pol, mem_restrictSupport_iff] at hF ⊢
  intro mo hmo
  apply hF
  rw [Finset.mem_coe, mem_support_iff] at hmo ⊢
  rw [coeff_diagK] at hmo
  exact right_ne_zero_of_mul hmo

theorem fock_eq_sum (F G : MvPolynomial σ Kf) (s : Finset (σ →₀ ℕ)) (hs : G.support ⊆ s) :
    fock F G = ∑ m ∈ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) := by
  unfold fock
  have h1 : ∑ m ∈ F.support, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) =
      ∑ m ∈ F.support ∪ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) := by
    refine Finset.sum_subset Finset.subset_union_left fun m _ hm => ?_
    rw [notMem_support_iff.1 hm, zero_mul, zero_mul]
  have h2 : ∑ m ∈ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) =
      ∑ m ∈ F.support ∪ s, F.coeff m * G.coeff m * ((expFact m : ℕ) : Kf) := by
    refine Finset.sum_subset Finset.subset_union_right fun m _ hm => ?_
    have : m ∉ G.support := fun h => hm (hs h)
    rw [notMem_support_iff.1 this, mul_zero, zero_mul]
  rw [h1, h2]

theorem fock_monomial_right (F : MvPolynomial σ Kf) (nu : σ →₀ ℕ) :
    fock F (monomial nu 1) = F.coeff nu * ((expFact nu : ℕ) : Kf) := by
  rw [fock_eq_sum F _ {nu} (by
    intro m hm
    rw [mem_support_iff, coeff_monomial] at hm
    by_contra h
    rw [Finset.mem_singleton] at h
    exact hm (if_neg fun h' => h h'.symm))]
  rw [Finset.sum_singleton, coeff_monomial, if_pos rfl, mul_one]

theorem fock_smul_left (c : Kf) (F G : MvPolynomial σ Kf) : fock (c • F) G = c * fock F G := by
  rw [fock_eq_sum _ _ _ (Finset.Subset.refl _), fock_eq_sum F _ _ (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring

theorem fock_smul_right (c : Kf) (F G : MvPolynomial σ Kf) : fock F (c • G) = c * fock F G := by
  unfold fock
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]; ring

end Co

section VB

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem vBB_le_coeff (F : MvPolynomial σ (KK O)) (m : σ →₀ ℕ) :
    vBB (O := O) p F ≤ vK p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  by_cases h : m ∈ F.support
  · exact Finset.inf_le h
  · rw [notMem_support_iff.1 h, valuation_zero_alt, WithTop.top_add]
    exact le_top

theorem vBB_attained (F : MvPolynomial σ (KK O)) (hF : vBB (O := O) p F ≠ ⊤) :
    ∃ m ∈ F.support, vBB (O := O) p F = vK p (F.coeff m) + (((padicValNat p (expFact m) : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  have hne : F.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hF
    unfold vBB
    rw [h, Finset.inf_empty]
  exact Finset.exists_mem_eq_inf _ hne _

theorem vBB_smul (c : KK O) (hc : c ≠ 0) (F : MvPolynomial σ (KK O)) :
    vBB (O := O) p (c • F) = vK p c + vBB (O := O) p F := by
  unfold vBB
  have hs : (c • F).support = F.support := by
    ext m
    simp [MvPolynomial.mem_support_iff, hc]
  rw [hs]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, valuation_mul_alt, add_assoc]
  by_cases hne : F.support.Nonempty
  · exact (Finset.apply_inf_eq_inf_comp_of_linearOrder (fun y : WithTop ℚ => vK p c + y)
      (fun a b hab => add_le_add_right hab _) (by simp)).symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

theorem vK_inv (x : KK O) (q : ℚ) (hx : vK p x = (q : WithTop ℚ)) : vK p x⁻¹ = ((-q : ℚ) : WithTop ℚ) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [valuation_zero_alt] at hx
    exact WithTop.top_ne_coe hx
  have h := valuation_mul_alt p x x⁻¹
  rw [mul_inv_cancel₀ hx0, valuation_one_eq_zero_alt, hx] at h
  obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 (h.symm.trans (by rfl : (0 : WithTop ℚ) = ((0 : ℚ) : WithTop ℚ)))
  have h1 : a = q := by exact_mod_cast ha
  rw [← hb]
  congr 1
  linarith

theorem vK_w_pow (hp : p.Prime) (S : UniformizedDVR p O) (w : O) (hw : w ^ 2 = (p : O)) (n : ℕ) :
    vK p ((algebraMap O (KK O) w) ^ n) = (((n : ℚ) / 2 : ℚ) : WithTop ℚ) := by
  have h1 : vK p (algebraMap O (KK O) w) = (((1 : ℚ) / 2 : ℚ) : WithTop ℚ) := by
    have h2 : (algebraMap O (KK O) w) * (algebraMap O (KK O) w) = ((p : ℕ) : KK O) := by
      rw [← map_mul, ← pow_two, hw, map_natCast]
    have h3 := congrArg (vK p) h2
    rw [valuation_mul_alt, valuation_natCast_padicVal hp S p hp.ne_zero, padicValNat.self hp.one_lt] at h3
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 h3
    have hab' : a = b := by
      have : (a : WithTop ℚ) = (b : WithTop ℚ) := by rw [ha, hb]
      exact_mod_cast this
    rw [← ha]
    congr 1
    push_cast at hab
    linarith
  induction n with
  | zero => rw [pow_zero, valuation_one_eq_zero_alt]; simp
  | succ n ih =>
    rw [pow_succ, valuation_mul_alt, ih, h1, ← WithTop.coe_add]
    congr 1
    push_cast
    ring

end VB

end Formalism.MainNotions.Proposition5Numerics
