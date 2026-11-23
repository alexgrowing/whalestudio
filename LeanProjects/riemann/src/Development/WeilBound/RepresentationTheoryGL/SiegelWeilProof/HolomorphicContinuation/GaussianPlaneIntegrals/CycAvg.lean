import Mathlib
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.CycAvgA

noncomputable section

open MeasureTheory MvPolynomial
open scoped Matrix

namespace PositivityTheory.Rg.Sw.FFTSteps.CA

variable {m n : ℕ}

def D (m n d : ℕ) : Finset ((Fin m × Fin n × Bool) →₀ ℕ) :=
  Finset.univ.image (fun f : Fin m × Fin n × Bool → Fin (d + 1) => Finsupp.equivFunOnFinite.symm (fun v => (f v : ℕ)))

theorem mem_D {d : ℕ} {t : (Fin m × Fin n × Bool) →₀ ℕ} (h : ∀ v, t v ≤ d) : t ∈ D m n d := by
  refine Finset.mem_image.2 ⟨fun v => ⟨t v, Nat.lt_succ_of_le (h v)⟩, Finset.mem_univ _, ?_⟩
  ext v; simp

theorem le_sum_fs (t : (Fin m × Fin n × Bool) →₀ ℕ) (v : Fin m × Fin n × Bool) : t v ≤ t.sum fun _ e => e := by
  by_cases hv : v ∈ t.support
  · exact Finset.single_le_sum (f := fun v => t v) (fun _ _ => Nat.zero_le _) hv
  · rw [Finsupp.notMem_support_iff.1 hv]; exact Nat.zero_le _

theorem totalDegree_var (u : Matrix (Fin m) (Fin m) ℂ) (k : Fin m × Fin n × Bool) :
    (subR u (X k : PX m n)).totalDegree ≤ 1 := by
  rcases k with ⟨a, i, _ | _⟩
  · rw [subR_X_false]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun b _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_C, totalDegree_X]
  · rw [subR_X_true]
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun b _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    simp [totalDegree_C, totalDegree_X]

theorem totalDegree_subR (u : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : (subR u P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun s hs => ?_)
  rw [subR, aeval_monomial, algebraMap_eq]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans ?_ (le_totalDegree hs)
  refine Finset.sum_le_sum fun v _ => ?_
  refine (totalDegree_pow _ _).trans ?_
  have := totalDegree_var (n := n) u v
  simp only [subR, aeval_X] at this
  nlinarith

theorem support_subR (u : Matrix (Fin m) (Fin m) ℂ) (P : PX m n) : (subR u P).support ⊆ D m n P.totalDegree := by
  intro t ht
  refine mem_D fun v => (le_sum_fs t v).trans ((le_totalDegree ht).trans (totalDegree_subR u P))

theorem expand (Q : PX m n) (d : ℕ) (h : Q.support ⊆ D m n d) : Q = ∑ s ∈ D m n d, monomial s (coeff s Q) := by
  conv_lhs => rw [Q.as_sum]
  refine Finset.sum_subset h fun s _ hs => ?_
  rw [notMem_support_iff.1 hs, monomial_zero]

def CC {K : Type*} [TopologicalSpace K] (F : K → PX m n) : Prop := ∀ t, Continuous fun k => coeff t (F k)

theorem CC.add {K : Type*} [TopologicalSpace K] {F G : K → PX m n} (hF : CC F) (hG : CC G) : CC fun k => F k + G k :=
  fun t => by simp only [coeff_add]; exact (hF t).add (hG t)

theorem CC.mul {K : Type*} [TopologicalSpace K] {F G : K → PX m n} (hF : CC F) (hG : CC G) : CC fun k => F k * G k :=
  fun t => by
    simp only [coeff_mul]
    exact continuous_finsetSum _ fun x _ => (hF x.1).mul (hG x.2)

theorem CC.const {K : Type*} [TopologicalSpace K] (Q : PX m n) : CC fun _ : K => Q := fun _ => continuous_const

theorem CC.ofC {K : Type*} [TopologicalSpace K] {f : K → ℂ} (hf : Continuous f) : CC fun k => (C (f k) : PX m n) :=
  fun t => by
    simp only [coeff_C]
    by_cases h : (0 : (Fin m × Fin n × Bool) →₀ ℕ) = t
    · simp only [h, if_true]; exact hf
    · simp only [h, if_false]; exact continuous_const

theorem CC.sum {K : Type*} [TopologicalSpace K] {ι : Type*} (s : Finset ι) {F : ι → K → PX m n} (hF : ∀ i, CC (F i)) :
    CC fun k => ∑ i ∈ s, F i k := fun t => by
  simp only [coeff_sum]
  exact continuous_finsetSum _ fun i _ => hF i t

theorem CC.subR {K : Type*} [TopologicalSpace K] {g : K → Matrix (Fin m) (Fin m) ℂ} (hg : Continuous g) (P : PX m n) :
    CC fun k => subR (g k) P := by
  induction P using MvPolynomial.induction_on
  next c => simpa [subR_C] using CC.const (K := K) (MvPolynomial.C c : PX m n)
  next p q hp hq => simpa [map_add] using hp.add hq
  next p v hp =>
    simp only [map_mul]
    refine hp.mul ?_
    rcases v with ⟨a, i, _ | _⟩
    · simp only [subR_X_false]
      exact CC.sum _ fun b => (CC.ofC (((continuous_apply b).comp (continuous_apply a)).comp hg)).mul (CC.const _)
    · simp only [subR_X_true]
      exact CC.sum _ fun b =>
        (CC.ofC (continuous_star.comp (((continuous_apply b).comp (continuous_apply a)).comp hg))).mul (CC.const _)

variable (ε : Fin m → Bool)

def gK (k : Formalism.REAL.KG ε) : Matrix (Fin m) (Fin m) ℂ := Formalism.REAL.toMK k⁻¹

theorem continuous_gK : Continuous (gK ε) := by
  have h : gK ε = fun k : Formalism.REAL.KG ε => ((((k : Formalism.REAL.UJ ε) : (Matrix (Fin m) (Fin m) ℂ)ˣ))⁻¹ : (Matrix (Fin m) (Fin m) ℂ)ˣ).val := by
    funext k; rfl
  rw [h]
  exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)

theorem toMK_mul (a b : Formalism.REAL.KG ε) : Formalism.REAL.toMK (a * b) = Formalism.REAL.toMK a * Formalism.REAL.toMK b := rfl

theorem gK_mem (k : Formalism.REAL.KG ε) : gK ε k ∈ Formalism.REAL.Kset ε := (k⁻¹).2

theorem unitary_of_mem {w : Matrix (Fin m) (Fin m) ℂ} (h : w ∈ Formalism.REAL.Kset ε) : wᴴ * w = 1 := by
  have := h.1
  rw [Matrix.mem_unitaryGroup_iff'] at this
  simpa [Matrix.star_eq_conjTranspose] using this

theorem evX_Qp (i j : Fin n) (x : Fin m → Fin n → ℂ) :
    evX (Qp ε i j) x = star (fun b => x b i) ⬝ᵥ (Matrix.diagonal (sgn ε) *ᵥ fun b => x b j) := by
  simp only [Qp, Qb, evX_eq, map_sub, map_sum, map_mul, eval_X, pt, if_true, Bool.false_eq_true, if_false,
    Finset.sum_filter, dotProduct, Matrix.mulVec_diagonal, Pi.star_apply]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  cases h : ε a <;> simp [sgn, h, pt]

theorem evX_Qp_act {w : Matrix (Fin m) (Fin m) ℂ} (hw : w ∈ Formalism.REAL.Kset ε) (i j : Fin n) (x : Fin m → Fin n → ℂ) :
    evX (Qp ε i j) (act w x) = evX (Qp ε i j) x := by
  have hJ : wᴴ * Matrix.diagonal (sgn ε) * w = Matrix.diagonal (sgn ε) := by
    have h2 : w * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * w := hw.2
    have hd : Formalism.REAL.Jm ε = Matrix.diagonal (sgn ε) := rfl
    rw [hd] at h2
    rw [Matrix.mul_assoc, ← h2, ← Matrix.mul_assoc, unitary_of_mem ε hw, Matrix.one_mul]
  have hcol : ∀ l, (fun b => act w x b l) = w *ᵥ fun b => x b l := fun l => rfl
  rw [evX_Qp, evX_Qp, hcol, hcol, Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, ← Matrix.mul_assoc, hJ]

theorem evX_inv_act {w : Matrix (Fin m) (Fin m) ℂ} (hw : w ∈ Formalism.REAL.Kset ε) {R : PX m n}
    (hR : R ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))) (x : Fin m → Fin n → ℂ) :
    evX R (act w x) = evX R x := by
  let S : Subalgebra ℂ (PX m n) :=
    { carrier := {R | ∀ x, evX R (act w x) = evX R x}
      mul_mem' := fun {a b} ha hb x => by simp only [evX_eq, map_mul] at *; rw [ha, hb]
      add_mem' := fun {a b} ha hb x => by simp only [evX_eq, map_add] at *; rw [ha, hb]
      algebraMap_mem' := fun c x => by simp [evX_eq, algebraMap_eq] }
  have hle : Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n)) ≤ S := by
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨ij, rfl⟩ x
    exact evX_Qp_act ε hw ij.1 ij.2 x
  exact hle hR x

def avg (P : PX m n) : PX m n :=
  ∑ t ∈ D m n P.totalDegree, monomial t (∫ k, coeff t (subR (gK ε k) P) ∂(Formalism.REAL.muK ε))

theorem integrable_coeff (P : PX m n) (t) : Integrable (fun k => coeff t (subR (gK ε k) P)) (Formalism.REAL.muK ε) :=
  (CC.subR (continuous_gK ε) P t).integrable_of_hasCompactSupport
    (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport _) (Set.subset_univ _))

theorem muK_univ : (Formalism.REAL.muK ε) Set.univ = 1 := by
  unfold Formalism.REAL.muK
  have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (Formalism.REAL.KG ε)))
  simpa using this

theorem coeff_avg (P : PX m n) (t) : coeff t (avg ε P) = ∫ k, coeff t (subR (gK ε k) P) ∂(Formalism.REAL.muK ε) := by
  unfold avg
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases ht : t ∈ D m n P.totalDegree
  · rw [Finset.sum_eq_single t (fun b _ hb => if_neg hb) (fun h => absurd ht h), if_pos rfl]
  · rw [Finset.sum_eq_zero (fun b hb => if_neg (fun h : b = t => ht (h ▸ hb)))]
    have : ∀ k, coeff t (subR (gK ε k) P) = 0 := fun k =>
      notMem_support_iff.1 (fun h => ht (support_subR _ P h))
    simp [this]

theorem mono_eq (s : (Fin m × Fin n × Bool) →₀ ℕ) (a : ℂ) :
    (monomial s a : PX m n) = MvPolynomial.C a * monomial s 1 := by
  rw [C_mul_monomial, mul_one]

theorem subR_mono (v : Matrix (Fin m) (Fin m) ℂ) (s : (Fin m × Fin n × Bool) →₀ ℕ) (a : ℂ) :
    subR v (monomial s a : PX m n) = MvPolynomial.C a * subR v (monomial s 1) := by
  rw [mono_eq s a, map_mul, subR_C]

theorem coeff_subR_sum (v : Matrix (Fin m) (Fin m) ℂ) (S : Finset ((Fin m × Fin n × Bool) →₀ ℕ))
    (a : ((Fin m × Fin n × Bool) →₀ ℕ) → ℂ) (t : (Fin m × Fin n × Bool) →₀ ℕ) :
    coeff t (subR v (∑ s ∈ S, monomial s (a s) : PX m n)) = ∑ s ∈ S, a s * coeff t (subR v (monomial s 1 : PX m n)) := by
  rw [map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [subR_mono, coeff_C_mul]

theorem avg_inv (P : PX m n) (kv : Formalism.REAL.KG ε) : subR (Formalism.REAL.toMK kv) (avg ε P) = avg ε P := by
  ext t
  have h1 : coeff t (subR (Formalism.REAL.toMK kv) (avg ε P)) = ∫ k, coeff t (subR (Formalism.REAL.toMK kv)
      (subR (gK ε k) P)) ∂(Formalism.REAL.muK ε) := by
    unfold avg
    rw [coeff_subR_sum]
    simp_rw [← integral_mul_const]
    rw [← integral_finsetSum _ fun s _ => (integrable_coeff ε P s).mul_const _]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    conv_rhs => rw [expand (subR (gK ε k) P) P.totalDegree (support_subR _ P)]
    rw [coeff_subR_sum]
  rw [h1, coeff_avg]
  simp_rw [subR_subR]
  have h2 : ∀ k : Formalism.REAL.KG ε, gK ε k * Formalism.REAL.toMK kv = gK ε (kv⁻¹ * k) := by
    intro k
    simp only [gK]
    rw [mul_inv_rev, inv_inv, toMK_mul]
  simp_rw [h2]
  exact integral_mul_left_eq_self (fun k => coeff t (subR (gK ε k) P)) kv⁻¹

theorem mom_sum_smul {c : ℝ} (hc : 0 < c) (S : Finset ((Fin m × Fin n × Bool) →₀ ℕ)) (a : _ → ℂ)
    (M : ((Fin m × Fin n × Bool) →₀ ℕ) → PX m n) :
    mom c (∑ s ∈ S, a s • M s) = ∑ s ∈ S, a s * mom c (M s) := by
  unfold mom
  have e : ∀ x, evX (∑ s ∈ S, a s • M s) x * gs c x = ∑ s ∈ S, a s * (evX (M s) x * gs c x) := by
    intro x
    simp only [evX_eq, map_sum, smul_eq_C_mul, map_mul, eval_C, Finset.sum_mul, mul_assoc]
  simp_rw [e]
  rw [integral_finsetSum _ fun s _ => (integrable_evX_gs hc (M s)).const_mul (a s)]
  simp_rw [integral_const_mul]

theorem mom_sub {c : ℝ} (hc : 0 < c) (p q : PX m n) : mom c (p - q) = mom c p - mom c q := by
  unfold mom
  have e : ∀ x, evX (p - q) x * gs c x = evX p x * gs c x - evX q x * gs c x := by
    intro x; simp only [evX_eq, map_sub, sub_mul]
  simp_rw [e]
  exact integral_sub (integrable_evX_gs hc p) (integrable_evX_gs hc q)

theorem mom_R_subR {c : ℝ} {w : Matrix (Fin m) (Fin m) ℂ} (hw : w ∈ Formalism.REAL.Kset ε) {R : PX m n}
    (hR : R ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))) (P : PX m n) :
    mom c (R * subR w P) = mom c (R * P) := by
  have h : mom c (R * subR w P) = mom c (subR w (R * P)) := by
    unfold mom
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [evX_subR]
    have : evX (R * subR w P) x = evX (R * P) (act w x) := by
      simp only [evX_eq, map_mul] at *
      rw [← evX_eq, ← evX_eq, ← evX_eq, ← evX_eq, evX_subR, evX_inv_act ε hw hR]
    rw [this]
  rw [h, mom_subR w (unitary_of_mem ε hw)]

theorem mom_avg {c : ℝ} (hc : 0 < c) {R : PX m n}
    (hR : R ∈ Algebra.adjoin ℂ (Set.range fun ij : Fin n × Fin n => (Qp ε ij.1 ij.2 : PX m n))) (P : PX m n) :
    mom c (R * avg ε P) = mom c (R * P) := by
  have e1 : R * avg ε P = ∑ s ∈ D m n P.totalDegree,
      (∫ k, coeff s (subR (gK ε k) P) ∂(Formalism.REAL.muK ε)) • (R * monomial s 1) := by
    unfold avg
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_C_mul, mono_eq s]; ring
  rw [e1, mom_sum_smul hc]
  simp_rw [← integral_mul_const]
  rw [← integral_finsetSum _ fun s _ => (integrable_coeff ε P s).mul_const _]
  have e2 : ∀ k : Formalism.REAL.KG ε, ∑ s ∈ D m n P.totalDegree, coeff s (subR (gK ε k) P) * mom c (R * monomial s 1) =
      mom c (R * P) := by
    intro k
    rw [← mom_sum_smul hc, ← mom_R_subR ε (gK_mem ε k) hR P]
    congr 1
    conv_rhs => rw [expand (subR (gK ε k) P) P.totalDegree (support_subR _ P)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_eq_C_mul, mono_eq s (coeff s _)]; ring
  simp_rw [e2]
  rw [integral_const]
  simp [Measure.real, muK_univ]

end PositivityTheory.Rg.Sw.FFTSteps.CA

namespace PositivityTheory.Rg.Sw.FFTSteps

open CA in
theorem cycAvg : CycAvg := by
  intro m n ε c hc P
  refine ⟨avg ε P, ?_, ?_⟩
  · intro u hu hblock
    have hK : u ∈ Formalism.REAL.Kset ε := by
      refine ⟨hu, ?_⟩
      ext a b
      simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases h : ε a = ε b
      · rw [h, mul_comm]
      · rw [hblock a b h]; simp
    have hr : u ∈ Set.range (fun k : Formalism.REAL.KG ε => Formalism.REAL.toMK k) := by
      rw [Formalism.REAL.range_toMK]; exact hK
    obtain ⟨kv, hkv⟩ := hr
    change subR u (avg ε P) = avg ε P
    rw [← hkv]
    exact avg_inv ε P kv
  · intro R hR
    rw [mul_sub, mom_sub hc, mom_avg ε hc hR, sub_self]

end PositivityTheory.Rg.Sw.FFTSteps
