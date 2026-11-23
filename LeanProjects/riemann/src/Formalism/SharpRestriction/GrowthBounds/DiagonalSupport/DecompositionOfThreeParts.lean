import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.TwiceValuationFactorialProduct
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.ValLeOfVK
import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FockRLinDual
import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

section V

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem geQ_mono {x : WithTop ℚ} {s t : ℝ} (h : s ≤ t) (hx : geQ x t) : geQ x s :=
  fun q hq => le_trans h (hx q hq)

theorem leQ_mono {x : WithTop ℚ} {s t : ℝ} (h : s ≤ t) (hx : leQ x s) : leQ x t := by
  obtain ⟨q, hq, h1⟩ := hx
  exact ⟨q, hq, le_trans h1 h⟩

theorem geQ_top (t : ℝ) : geQ ⊤ t := fun q hq => absurd hq (by simp)

theorem geQ_of_le {x y : WithTop ℚ} {t : ℝ} (h : x ≤ y) (hx : geQ x t) : geQ y t := by
  intro q hq
  rw [hq] at h
  obtain ⟨q', hq', h1⟩ := WithTop.le_coe_iff.1 h
  have := hx q' hq'
  have h2 : (q' : ℝ) ≤ (q : ℝ) := by exact_mod_cast h1
  linarith

theorem geQ_add (x y : KK O) {t : ℝ} (hx : geQ (vK p x) t) (hy : geQ (vK p y) t) : geQ (vK p (x + y)) t := by
  have h := valuation_add_ge_min p x y
  exact geQ_of_le h (by
      rcases le_total (vK p x) (vK p y) with h2 | h2
      · rw [min_eq_left h2]; exact hx
      · rw [min_eq_right h2]; exact hy)

theorem geQ_neg (x : KK O) {t : ℝ} (hx : geQ (vK p x) t) : geQ (vK p (-x)) t := by
  rw [valuation_neg]; exact hx

theorem geQ_sub (x y : KK O) {t : ℝ} (hx : geQ (vK p x) t) (hy : geQ (vK p y) t) : geQ (vK p (x - y)) t := by
  rw [sub_eq_add_neg]; exact geQ_add _ _ hx (geQ_neg _ hy)

theorem geQ_mul (x y : KK O) {s t : ℝ} (hx : geQ (vK p x) s) (hy : geQ (vK p y) t) : geQ (vK p (x * y)) (s + t) := by
  intro q hq
  rw [valuation_mul_alt] at hq
  obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 hq
  have h1 := hx a ha.symm
  have h2 := hy b hb.symm
  rw [← hab]
  push_cast
  linarith

theorem leQ_mul (x y : KK O) {s t : ℝ} (hx : leQ (vK p x) s) (hy : leQ (vK p y) t) : leQ (vK p (x * y)) (s + t) := by
  obtain ⟨a, ha, h1⟩ := hx
  obtain ⟨b, hb, h2⟩ := hy
  refine ⟨a + b, ?_, ?_⟩
  · rw [valuation_mul_alt, ha, hb]; rfl
  · push_cast; linarith

theorem geQ_zero (t : ℝ) : geQ (vK p (0 : KK O)) t := by
  rw [valuation_zero_alt]; exact geQ_top t

theorem geQ_sum {ι : Type*} (s : Finset ι) (f : ι → KK O) {t : ℝ} (h : ∀ i ∈ s, geQ (vK p (f i)) t) :
    geQ (vK p (∑ i ∈ s, f i)) t := by
  induction s using Finset.induction_on with
  | empty => simpa using geQ_zero t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact geQ_add _ _ (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem valuation_one_eq_zero_alt : vK p (1 : KK O) = 0 := by
  have h := valuation_mul_alt p (1 : KK O) 1
  rw [mul_one] at h
  have hne : vK p (1 : KK O) ≠ ⊤ := by
    have h1 := valuation_algebraMap_eq_alt (O := O) p 1 one_ne_zero
    rw [map_one] at h1
    rw [h1]; exact WithTop.coe_ne_top
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.1 hne
  rw [← hq, ← WithTop.coe_add, WithTop.coe_inj] at h
  rw [← hq]
  have : q = 0 := by linarith
  rw [this]; rfl

theorem geQ_one : geQ (vK p (1 : KK O)) 0 := by
  intro q hq
  rw [valuation_one_eq_zero_alt] at hq
  have : q = 0 := by exact_mod_cast hq.symm
  rw [this]; simp

theorem leQ_add_of_lt (x e : KK O) {s t : ℝ} (hx : leQ (vK p x) t) (he : geQ (vK p e) s) (hst : t < s) :
    leQ (vK p (x + e)) t := by
  obtain ⟨a, ha, h1⟩ := hx
  by_contra hcon

  have h2 : geQ (vK p (x + e)) (min s ((a : ℝ) + (s - t) / 2)) ∨ True := Or.inr trivial
  have hlt : ((a : ℚ) : WithTop ℚ) < vK p (x + e) := by
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨b, hb, hba⟩ := WithTop.le_coe_iff.1 hle
    apply hcon
    refine ⟨b, hb, ?_⟩
    have : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    linarith
  have hlt2 : ((a : ℚ) : WithTop ℚ) < vK p (-e) := by
    rw [valuation_neg]
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨b, hb, hba⟩ := WithTop.le_coe_iff.1 hle
    have h3 := he b hb
    have : (b : ℝ) ≤ (a : ℝ) := by exact_mod_cast hba
    linarith
  have h4 := valuation_add_ge_min p (x + e) (-e)
  rw [add_neg_cancel_right, ha] at h4
  exact absurd h4 (not_le.2 (lt_min hlt hlt2))

theorem geQ_scale (hp : p.Prime) (S : UniformizedDVR p O) (x : KK O) (κ Dn : ℕ) (hD : Dn ≠ 0) {t : ℝ}
    (hx : geQ (vK p x) t) :
    geQ (vK p ((p : KK O) ^ κ * x / (Dn : KK O))) (t + κ - (padicValNat p Dn : ℝ)) := by
  have := dvr_fraction_field_char_zero hp S
  have hD' : (Dn : KK O) ≠ 0 := by exact_mod_cast hD
  intro q hq
  have h1 : (p : KK O) ^ κ * x / (Dn : KK O) * (Dn : KK O) = (p : KK O) ^ κ * x := by field_simp
  have h2 := congrArg (vK p) h1
  rw [valuation_mul_alt, Formalism.MainNotions.G.Joints.vK_pow_mul S, valuation_natCast_padicVal hp S Dn hD, hq, ← WithTop.coe_add] at h2
  obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 h2.symm
  have h3 := hx b hb.symm
  have h4 : a = (κ : ℚ) := by exact_mod_cast ha
  have h5 : ((a + b : ℚ) : ℝ) = ((q + (padicValNat p Dn : ℚ) : ℚ) : ℝ) := by rw [hab]
  push_cast at h5
  rw [h4] at h5
  push_cast at h5
  linarith

theorem leQ_scale (hp : p.Prime) (S : UniformizedDVR p O) (x : KK O) (κ Dn : ℕ) (hD : Dn ≠ 0) {t : ℝ}
    (hx : leQ (vK p x) t) :
    leQ (vK p ((p : KK O) ^ κ * x / (Dn : KK O))) (t + κ - (padicValNat p Dn : ℝ)) := by
  have := dvr_fraction_field_char_zero hp S
  have hD' : (Dn : KK O) ≠ 0 := by exact_mod_cast hD
  obtain ⟨b, hb, h3⟩ := hx
  have h1 : (p : KK O) ^ κ * x / (Dn : KK O) * (Dn : KK O) = (p : KK O) ^ κ * x := by field_simp
  have h2 := congrArg (vK p) h1
  rw [valuation_mul_alt, Formalism.MainNotions.G.Joints.vK_pow_mul S, valuation_natCast_padicVal hp S Dn hD, hb, ← WithTop.coe_add] at h2
  obtain ⟨q, c, hq, hc, hqc⟩ := WithTop.add_eq_coe.1 h2
  refine ⟨q, hq.symm, ?_⟩
  have h4 : c = (padicValNat p Dn : ℚ) := by exact_mod_cast hc
  have h5 : ((q + c : ℚ) : ℝ) = (((κ : ℚ) + b : ℚ) : ℝ) := by rw [hqc]
  push_cast at h5
  rw [h4] at h5
  push_cast at h5
  linarith

theorem geQ_alg (S : UniformizedDVR p O) (o : O) : geQ (vK p (algebraMap O (KK O) o)) 0 := by
  have h : (0 : WithTop ℚ) ≤ vK p (algebraMap O (KK O) o) := (valuation_nonneg_iff_integral S _).2 ⟨o, rfl⟩
  intro q hq
  rw [hq] at h
  have : (0 : ℚ) ≤ q := by exact_mod_cast h
  exact_mod_cast this

theorem exists_alg_of_geQ (S : UniformizedDVR p O) (x : KK O) (h : geQ (vK p x) 0) :
    ∃ o : O, x = algebraMap O (KK O) o := by
  apply (valuation_nonneg_iff_integral S x).1
  induction hx : vK p x using WithTop.recTopCoe with
  | top => exact le_top
  | coe q =>
    have := h q hx
    have h2 : (0 : ℚ) ≤ q := by exact_mod_cast this
    exact_mod_cast h2

end V

section C

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ τ : Type}

theorem CoefGe.mono {F : MvPolynomial σ (KK O)} {s t : ℝ} (h : s ≤ t) (hF : CoefGe p F t) : CoefGe p F s :=
  fun mo => geQ_mono h (hF mo)

theorem CoefGe.add {F G : MvPolynomial σ (KK O)} {t : ℝ} (hF : CoefGe p F t) (hG : CoefGe p G t) :
    CoefGe p (F + G) t := by
  intro mo
  rw [coeff_add]
  exact geQ_add _ _ (hF mo) (hG mo)

theorem CoefGe.zero (t : ℝ) : CoefGe p (0 : MvPolynomial σ (KK O)) t := by
  intro mo
  rw [coeff_zero]
  exact geQ_zero t

theorem CoefGe.sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ (KK O)) {t : ℝ}
    (h : ∀ i ∈ s, CoefGe p (f i) t) : CoefGe p (∑ i ∈ s, f i) t := by
  intro mo
  rw [coeff_sum]
  exact geQ_sum _ _ fun i hi => h i hi mo

theorem CoefGe.mul {F G : MvPolynomial σ (KK O)} {s t : ℝ} (hF : CoefGe p F s) (hG : CoefGe p G t) :
    CoefGe p (F * G) (s + t) := by
  intro mo
  rw [coeff_mul]
  exact geQ_sum _ _ fun x _ => geQ_mul _ _ (hF x.1) (hG x.2)

theorem CoefGe.monomial (mo : σ →₀ ℕ) {c : KK O} {t : ℝ} (hc : geQ (vK p c) t) :
    CoefGe p (MvPolynomial.monomial mo c) t := by
  intro mo'
  rw [coeff_monomial]
  split_ifs
  · exact hc
  · exact geQ_zero t

theorem CoefGe.one : CoefGe p (1 : MvPolynomial σ (KK O)) 0 := by
  have : (1 : MvPolynomial σ (KK O)) = MvPolynomial.monomial 0 1 := rfl
  rw [this]
  exact CoefGe.monomial _ geQ_one

theorem CoefGe.pow {F : MvPolynomial σ (KK O)} (hF : CoefGe p F 0) (n : ℕ) : CoefGe p (F ^ n) 0 := by
  induction n with
  | zero => rw [pow_zero]; exact CoefGe.one
  | succ n ih =>
    rw [pow_succ]
    have := CoefGe.mul ih hF
    rwa [add_zero] at this

theorem CoefGe.prod {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ (KK O))
    (h : ∀ i ∈ s, CoefGe p (f i) 0) : CoefGe p (∏ i ∈ s, f i) 0 := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact CoefGe.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have := CoefGe.mul (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    rwa [add_zero] at this

theorem CoefGe.X_pow (v : σ) (n : ℕ) : CoefGe p ((X v : MvPolynomial σ (KK O)) ^ n) 0 := by
  rw [X_pow_eq_monomial]
  exact CoefGe.monomial _ geQ_one

theorem CoefGe.aeval (f : σ → MvPolynomial τ (KK O)) (hf : ∀ v, CoefGe p (f v) 0) {F : MvPolynomial σ (KK O)} {t : ℝ}
    (hF : CoefGe p F t) : CoefGe p (MvPolynomial.aeval f F) t := by
  rw [aeval_def, eval₂_eq]
  refine CoefGe.sum _ _ fun d _ => ?_
  have h1 : CoefGe p (algebraMap (KK O) (MvPolynomial τ (KK O)) (F.coeff d)) t := by
    rw [algebraMap_eq, C_apply]
    exact CoefGe.monomial _ (hF d)
  have h2 := CoefGe.mul h1 (CoefGe.prod d.support (fun i => f i ^ d i) fun i _ => CoefGe.pow (hf i) _)
  rwa [add_zero] at h2

end C

section F

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem fock_add_right {σ : Type} (G T₁ T₂ : MvPolynomial σ (KK O)) : fock G (T₁ + T₂) = fock G T₁ + fock G T₂ := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

theorem geQ_expFact [hp : Fact p.Prime] (S : UniformizedDVR p O) {n' k : ℕ} (d : Fin n' → ℕ) (α : Fin n' × Fin k →₀ ℕ)
    (hα : ∀ s, multideg α s = d s) :
    geQ (vK p ((expFact α : ℕ) : KK O)) (twiceValuationFactorialProduct p d - (kapFl p k d : ℝ)) := by
  obtain ⟨c, hc⟩ := multDiv_kapFl O p S.p_mem (k := k) d α hα
  have hD : (∏ s, (d s).factorial) ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => Nat.factorial_ne_zero _
  have h1 : (p : KK O) ^ (kapFl p k d) * ((expFact α : ℕ) : KK O) =
      (((∏ s, (d s).factorial : ℕ) : ℕ) : KK O) * algebraMap O (KK O) c := by
    have := congrArg (algebraMap O (KK O)) hc
    simpa [map_mul, map_pow, map_natCast] using this
  intro q hq
  have h2 := congrArg (vK p) h1
  rw [Formalism.MainNotions.G.Joints.vK_pow_mul S, hq, valuation_mul_alt, valuation_natCast_padicVal hp.out S _ hD, ← WithTop.coe_add] at h2
  obtain ⟨a, b, ha, hb, hab⟩ := WithTop.add_eq_coe.1 h2.symm
  have h3 := geQ_alg S c b hb.symm
  have h4 : a = (padicValNat p (∏ s, (d s).factorial) : ℚ) := by exact_mod_cast ha
  have h5 : ((a + b : ℚ) : ℝ) = ((((kapFl p k d : ℕ) : ℚ) + q : ℚ) : ℝ) := by rw [hab]
  push_cast at h5
  rw [h4] at h5
  push_cast at h5
  unfold twiceValuationFactorialProduct
  linarith

theorem geQ_fock [hp : Fact p.Prime] (S : UniformizedDVR p O) {n' k : ℕ} (d : Fin n' → ℕ)
    (G T : MvPolynomial (TV n' k) (KK O)) {t : ℝ} (hd : HasMultideg G d) (hG : CoefGe p G 0) (hT : CoefGe p T t) :
    geQ (vK p (fock G T)) (t + twiceValuationFactorialProduct p d - (kapFl p k d : ℝ)) := by
  unfold fock
  refine geQ_sum _ _ fun m hm => ?_
  have hm' : ∀ s, multideg m s = d s := by
    have := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 hd
    exact this hm
  have h1 := geQ_mul _ _ (geQ_mul _ _ (hG m) (hT m)) (geQ_expFact S d m hm')
  refine geQ_mono ?_ h1
  linarith

end F

end Formalism.MainNotions.Proposition5Numerics
