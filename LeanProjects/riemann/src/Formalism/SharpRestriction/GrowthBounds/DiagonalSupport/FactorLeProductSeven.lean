import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PickVal
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.DigAbs
import Formalism.SharpRestriction.GrowthBounds.ProjectionOfIsotypicDecomposition

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem lowest_weight_le_of_isotypic (D : Formalism.BasicNotions.D7) {R : Type} [Field R] [CharZero R] {ι : Type} [Fintype ι] (LL : Letters ι)
    {n : ℕ} [NeZero n] (S : Set ι) (lam : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) R)
    (hF : F ∈ isoSub (glOps R n LL S) lam) : lam1S LL S F ≤ ((lam 0 : ℤ) : WithBot ℤ) := by
  obtain ⟨ee, hee, _⟩ := Formalism.MainNotions.G.Joints.polIsoDecompB_of D (weight_condition_from_integral_form D) R ι LL n S
  refine (((valuation_field D).2 R ι LL n S ee hee).2 F (lam 0)).2 fun mu hmu => ?_
  by_cases h : lam = mu
  · rw [h]
  · exact absurd ((hee mu).2 lam h F hF) hmu

section DD

variable {σ Kf : Type} [Field Kf]

theorem coeff_mon_divDer (m a : σ →₀ ℕ) (F : MvPolynomial σ Kf) :
    (monomial m (1 : Kf) * divDer m F).coeff a = (∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : Kf)) * F.coeff a := by
  rw [coeff_monomial_mul']
  split_ifs with hma
  · rw [one_mul]
    unfold divDer
    rw [coeff_sum]
    have hsingle : ∀ b ∈ F.support, b ≠ a →
        coeff (a - m) (if m ≤ b then monomial (b - m) (F.coeff b * ((m.prod fun k j => (b k).choose j : ℕ) : Kf))
          else 0) = 0 := by
      intro b _ hb
      split_ifs with hmb
      · rw [coeff_monomial, if_neg]
        intro h
        apply hb
        have h1 : b - m + m = a - m + m := by rw [h]
        rwa [tsub_add_cancel_of_le hmb, tsub_add_cancel_of_le hma] at h1
      · rw [coeff_zero]
    by_cases ha : a ∈ F.support
    · rw [Finset.sum_eq_single a hsingle (fun h => absurd ha h), if_pos hma, coeff_monomial, if_pos rfl]
      unfold Finsupp.prod
      push_cast
      ring
    · rw [Finset.sum_eq_zero (fun b hb => hsingle b hb (fun h => ha (h ▸ hb))), notMem_support_iff.1 ha, mul_zero]
  · have : ∃ v, a v < m v := by
      by_contra hcon
      push Not at hcon
      exact hma hcon
    obtain ⟨v, hv⟩ := this
    have hvs : v ∈ m.support := by
      rw [Finsupp.mem_support_iff]
      omega
    rw [Finset.prod_eq_zero hvs (by rw [Nat.choose_eq_zero_of_lt hv, Nat.cast_zero]), zero_mul]

end DD

section BC

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem diagK_binomCombF (lam : (σ →₀ ℕ) →₀ O) (F : MvPolynomial σ (KK O)) :
    diagK (fun a => binomCombF (K := KK O) lam a) F =
      ∑ m ∈ lam.support, (algebraMap O (KK O) (lam m)) • (monomial m (1 : KK O) * divDer m F) := by
  ext a
  rw [coeff_diagK, coeff_sum]
  unfold binomCombF
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, coeff_mon_divDer, smul_eq_mul]
  ring

theorem geQ_binomCombF (S : UniformizedDVR p O) (lam : (σ →₀ ℕ) →₀ O) (a : σ →₀ ℕ) :
    geQ (vK p (binomCombF (K := KK O) lam a)) 0 := by
  unfold binomCombF
  refine geQ_sum _ _ fun m _ => ?_
  have h : algebraMap O (KK O) (lam m) * ∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : KK O) =
      algebraMap O (KK O) (lam m * ∏ v ∈ m.support, (((a v).choose (m v) : ℕ) : O)) := by
    rw [map_mul, map_prod]
    simp
  rw [h]
  exact geQ_alg S _

end BC

theorem padicVal_expFact_le' (p : ℕ) [hp : Fact p.Prime] {ι : Type} [Fintype ι] {k : ℕ} (d : ι → ℕ)
    (α : ι × Fin k →₀ ℕ) (hα : ∀ s, multideg α s = d s) :
    padicValNat p (expFact α) ≤ padicValNat p (∏ s, (d s).factorial) := by
  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : ι, ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  have h3 : (∏ s, (d s).factorial) = (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) * expFact α := by
    rw [h2, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : (∏ s : ι, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c))) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have hE0 : expFact α ≠ 0 := by
    rw [h2]
    exact Finset.prod_ne_zero_iff.2 fun s _ => Finset.prod_ne_zero_iff.2 fun c _ => Nat.factorial_ne_zero _
  rw [h3, padicValNat.mul hMn0 hE0]
  omega

section St

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem coefGe_of_inBB [hp : Fact p.Prime] (S : UniformizedDVR p O) (w : O) (hw2 : w ^ 2 = (p : O)) {ι : Type} [Fintype ι]
    {k : ℕ} (d : ι → ℕ) (Z : MvPolynomial (ι × Fin k) (KK O)) (hZ : Z ∈ Pol (KK O) k d) (hBB : InBB (O := O) p Z) :
    CoefGe p (((algebraMap O (KK O) w) ^ (padicValNat p (∏ s, (d s).factorial))) • Z) 0 := by
  intro bn
  rw [coeff_smul, smul_eq_mul]
  by_cases hbn : bn ∈ Z.support
  · have hdeg : ∀ s, multideg bn s = d s := ((mem_restrictSupport_iff (KK O)).1 hZ) hbn
    have h1 := padicVal_expFact_le' p d bn hdeg
    have h2 : (0 : WithTop ℚ) ≤ vK p (Z.coeff bn) + (((padicValNat p (expFact bn) : ℚ) / 2 : ℚ) : WithTop ℚ) :=
      le_trans hBB (vBB_le_coeff Z bn)
    intro q hq
    rw [valuation_mul_alt, vK_w_pow hp.out S w hw2] at hq
    obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 hq
    rw [← hb, ← WithTop.coe_add] at h2
    have h3 : (0 : ℚ) ≤ b + (padicValNat p (expFact bn) : ℚ) / 2 := by exact_mod_cast h2
    have h4 : a = ((padicValNat p (∏ s, (d s).factorial) : ℕ) : ℚ) / 2 := by exact_mod_cast ha
    have h5 : ((padicValNat p (expFact bn) : ℕ) : ℚ) ≤ ((padicValNat p (∏ s, (d s).factorial) : ℕ) : ℚ) := by
      exact_mod_cast h1
    have h6 : (0 : ℚ) ≤ q := by rw [← hab, h4]; linarith
    exact_mod_cast h6
  · rw [notMem_support_iff.1 hbn, mul_zero]
    exact geQ_zero 0

end St

end Formalism.MainNotions.Proposition5Numerics
