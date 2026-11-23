import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlockPointNorm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionPointValue
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsLocalRep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

namespace PowerBlockPointNorm

section Generic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem pn_congr {f : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (h : ∀ k, a k = b k) :
    IsMultiHomog f b :=
  fun m hm k => (hf m hm k).trans (h k)

theorem pn_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := fun m hm => by simp at hm

theorem pn_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · exact hf m hm
  · exact hg m hm

theorem pn_sum {J : Type} (s : Finset J) {f : J → MRing ι} {a : K → ℕ}
    (h : ∀ j ∈ s, IsMultiHomog (f j) a) : IsMultiHomog (∑ j ∈ s, f j) a := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pn_zero (ι := ι) a
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact pn_add (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem pn_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem pn_C (r : ℤ) : IsMultiHomog (C r : MRing ι) 0 := by
  classical
  intro m hm k
  rw [mem_support_iff, coeff_C] at hm
  split_ifs at hm with h
  · subst h
    simp
  · exact absurd rfl hm

theorem pn_mul {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

theorem pn_pow {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (pn_one (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact pn_mul ih hf

theorem pn_prod {J : Type} (s : Finset J) (f : J → MRing ι) (d : J → K → ℕ)
    (h : ∀ j ∈ s, IsMultiHomog (f j) (d j)) : IsMultiHomog (∏ j ∈ s, f j) (∑ j ∈ s, d j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using pn_one (ι := ι)
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact pn_mul (h j (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem pn_aeval_smul {S : Type*} [CommRing S] [Algebra ℤ S] {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a)
    (c : K → S) (v : (Σ k, ι k) → S) : aeval (fun p => c p.1 * v p) f = (∏ k, c k ^ a k) * aeval v f := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hprod : ∏ p, (c p.1 * v p) ^ d p = (∏ k, c k ^ a k) * ∏ p, v p ^ d p := by
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ d ⟨k, i⟩ = c k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  rw [hprod]
  ring

theorem pn_aeval_congr_block [DecidableEq K] {S : Type*} [CommRing S] [Algebra ℤ S] {h : MRing ι} {k₀ : K} {n : ℕ}
    (hh : IsMultiHomog h (blockDeg k₀ n)) {v w : (Σ k, ι k) → S} (hvw : ∀ i, v ⟨k₀, i⟩ = w ⟨k₀, i⟩) :
    aeval v h = aeval w h := by
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq']
  refine Finset.sum_congr rfl fun d hd => congrArg _ (Finset.prod_congr rfl fun p _ => ?_)
  obtain ⟨k, i⟩ := p
  by_cases hk : k = k₀
  · subst hk
    rw [hvw]
  · have h0 : d ⟨k, i⟩ = 0 := by
      have := hh d hd k
      simp only [blockDeg, if_neg hk] at this
      exact (Finset.sum_eq_zero_iff.mp this) i (Finset.mem_univ _)
    rw [h0, pow_zero, pow_zero]

theorem pn_eval_map_int {σ : Type*} (z : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

theorem pn_aeval_mem {S : Type*} [CommRing S] (T : Subalgebra ℤ S) {σ : Type*} (u : σ → S)
    (hu : ∀ p, u p ∈ T) (f : MvPolynomial σ ℤ) : aeval u f ∈ T := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    rw [aeval_C]
    exact T.algebraMap_mem r
  | add f g hf hg =>
    rw [map_add]
    exact T.add_mem hf hg
  | mul_X f p hf =>
    rw [map_mul, aeval_X]
    exact T.mul_mem hf (hu p)

theorem pn_relevant {P : Ideal (MRing ι)} {x : (Σ k, ι k) → ℂ} (hx : x ∈ mcPts P) : IsRelevant P := fun k => by
  obtain ⟨i, hi⟩ := hx.1 k
  exact ⟨i, fun hX => hi (by simpa using hx.2 _ hX)⟩

variable {Ω : Type} [Field Ω]

theorem pn_mConeMap_homog (y : (Σ k, ι k) → Ω) {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    mConeMap y f = (∏ k, (X k : MvPolynomial K Ω) ^ a k) * C (aeval y f) := by
  have h1 : mConeMap y f = aeval (fun p => (X p.1 : MvPolynomial K Ω) * C (y p)) f := by
    rw [mConeMap]
    exact congrArg (fun φ => aeval φ f) (funext fun p => mul_comm _ _)
  rw [h1, pn_aeval_smul hf (fun k => (X k : MvPolynomial K Ω)) (fun p => C (y p))]
  have h2 : aeval (fun p => (C (y p) : MvPolynomial K Ω)) f = C (aeval y f) := aeval_C_comp_left y f
  rw [h2]

end Generic

section Block

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

def oldIdx (N : ℕ) (p : Σ k, ι k) : Σ k, addIdx ι N k := ⟨some p.1, p.2⟩

def newSubst {α : Type*} [Zero α] {N : ℕ} (u : Fin N → α) : (Σ k, addIdx ι N k) → α
  | ⟨none, j⟩ => u j
  | ⟨some _, _⟩ => 0

def newScale {S : Type*} [Zero S] (c : S) : Option K → S
  | none => c
  | some _ => 0

theorem aeval_scale_new {S : Type*} [CommRing S] [Algebra ℤ S] {N q : ℕ} {F : MRing (addIdx ι N)}
    (hF : IsMultiHomog F (blockDeg (none : Option K) q)) (z u : (Σ k, addIdx ι N k) → S) (c : S)
    (h : ∀ j, z ⟨none, j⟩ = c * u ⟨none, j⟩) : aeval z F = c ^ q * aeval u F := by
  rw [pn_aeval_congr_block hF (w := fun p => newScale c p.1 * u p) h, pn_aeval_smul hF, Fintype.prod_option]
  simp [newScale, blockDeg]

theorem homog_bind_new {N q : ℕ} {e : K → ℕ} (G : Fin N → MRing ι) (hG : ∀ j, IsMultiHomog (G j) e)
    {F : MRing (addIdx ι N)} (hF : IsMultiHomog F (blockDeg (none : Option K) q)) :
    IsMultiHomog (bind₁ (newSubst G) F) (q • e) := by
  rw [F.as_sum, map_sum]
  refine pn_sum _ fun μ hμ => ?_
  rw [bind₁_monomial]
  have hfac : ∀ p ∈ μ.support, IsMultiHomog (newSubst G p ^ μ p) (μ p • e) := by
    rintro ⟨_ | k, i⟩ hp
    · exact pn_pow (hG i) _
    · rw [show (newSubst G ⟨some k, i⟩ : MRing ι) = 0 from rfl, zero_pow (Finsupp.mem_support_iff.mp hp)]
      exact pn_zero _
  have hdeg : ∑ p ∈ μ.support, μ p = q := by
    rw [Finset.sum_subset (Finset.subset_univ _) (fun p _ hp => by simpa using hp), Fintype.sum_sigma,
      Fintype.sum_option]
    have h0 := fun k => hF μ hμ k
    simp only [h0, blockDeg]
    simp
  refine pn_congr (pn_mul (pn_C _) (pn_prod μ.support (fun p => newSubst G p ^ μ p) (fun p => μ p • e) hfac))
    fun k => ?_
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, zero_add, Pi.zero_apply]
  rw [← Finset.sum_mul, hdeg]

theorem pn_mConeMap_rename (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) (f : MRing ι) :
    mConeMap (addBlock y v) (rename (oldIdx N) f) = rename (R := Ω) some (mConeMap y f) := by
  have key : (mConeMap (addBlock y v)).comp (rename (oldIdx N)) =
      ((rename (R := Ω) (some : K → Option K)).restrictScalars ℤ).comp (mConeMap y) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, oldIdx, addBlock]
  exact DFunLike.congr_fun key f

theorem pn_mConeMap_new (y : (Σ k, ι k) → Ω) {N : ℕ} (v : Fin N → Ω) (j : Fin N) :
    mConeMap (addBlock y v) (X ⟨none, j⟩ : MRing (addIdx ι N)) = MvPolynomial.C (v j) * MvPolynomial.X none := by
  simp [mConeMap, addBlock]

theorem pn_rename_mem {y : (Σ k, ι k) → Ω} {N : ℕ} (v : Fin N → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) :
    rename (oldIdx N) f ∈ mCoordIdeal (addBlock y v) := by
  have hf' : f ∈ RingHom.ker (mConeMap y) := hf
  show _ ∈ RingHom.ker (mConeMap (addBlock y v))
  rw [RingHom.mem_ker, pn_mConeMap_rename, RingHom.mem_ker.mp hf', map_zero]

theorem pn_aeval_rename_old {N : ℕ} (z : (Σ k, addIdx ι N k) → ℂ) (f : MRing ι) :
    aeval z (rename (oldIdx N) f) = aeval (basePart₂ z) f := by
  rw [aeval_rename]
  rfl

theorem pn_oldPart_mem {y : (Σ k, ι k) → Ω} {N : ℕ} {v : Fin N → Ω} {z : (Σ k, addIdx ι N k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) : basePart₂ z ∈ mcPts (mCoordIdeal y) := by
  refine ⟨fun k => hz.1 (some k), fun f hf => ?_⟩
  have := hz.2 _ (pn_rename_mem v hf)
  rw [pn_eval_map_int, pn_aeval_rename_old] at this
  rw [pn_eval_map_int]
  exact this

theorem new_cross {y : (Σ k, ι k) → Ω} {N : ℕ} {v : Fin N → Ω} {e : K → ℕ} {G : Fin N → MRing ι}
    (hG : ∀ j, IsMultiHomog (G j) e) (hprop : ∀ i j, v i * aeval y (G j) = v j * aeval y (G i))
    {z : (Σ k, addIdx ι N k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal (addBlock y v))) (i j : Fin N) :
    z ⟨none, i⟩ * aeval (basePart₂ z) (G j) = z ⟨none, j⟩ * aeval (basePart₂ z) (G i) := by
  have hC : (C (v i) : MvPolynomial (Option K) Ω) * C (aeval y (G j)) = C (v j) * C (aeval y (G i)) := by
    rw [← C_mul, ← C_mul, hprop]
  have hmem : (X ⟨none, i⟩ * rename (oldIdx N) (G j) - X ⟨none, j⟩ * rename (oldIdx N) (G i) :
      MRing (addIdx ι N)) ∈ mCoordIdeal (addBlock y v) := by
    show _ ∈ RingHom.ker (mConeMap (addBlock y v))
    rw [RingHom.mem_ker, map_sub, map_mul (mConeMap (addBlock y v)), map_mul (mConeMap (addBlock y v)),
      pn_mConeMap_rename, pn_mConeMap_rename, pn_mConeMap_homog y (hG j), pn_mConeMap_homog y (hG i),
      pn_mConeMap_new, pn_mConeMap_new]
    simp only [map_mul, rename_C]
    linear_combination (X none * rename some (∏ k, (X k : MvPolynomial K Ω) ^ e k)) * hC
  have := hz.2 _ hmem
  rw [pn_eval_map_int] at this
  simp only [map_sub, map_mul, aeval_X, pn_aeval_rename_old, sub_eq_zero] at this
  exact this

theorem mem_chartLat_new {y : (Σ k, ι k) → Ω} {a : K → ℤ} {m N q : ℕ} {v : Fin N → Ω}
    (hv : ∀ j, v j ∈ chartLat y a m) {F : MRing (addIdx ι N)} (hF : IsMultiHomog F (blockDeg (none : Option K) q)) :
    aeval (addBlock y v) F ∈ chartLat y a (m * q) := by
  refine fun c hc => ?_
  have hpow : ∏ k, y ⟨k, c k⟩ ^ (-(((m * q : ℕ) : ℤ) * a k)) = (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) ^ q := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  rw [hpow, mul_comm, ← aeval_scale_new hF (newSubst fun j => (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) * v j)
    (addBlock y v) _ fun j => rfl]
  refine pn_aeval_mem _ _ (fun p => ?_) F
  rcases p with ⟨_ | k, i⟩
  · show (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k))) * v i ∈ chartRingZ y c
    rw [mul_comm]
    exact hv i c hc
  · exact zero_mem _

theorem common_rep {y : (Σ k, ι k) → Ω} {a : K → ℤ} {n N : ℕ} {v : Fin N → Ω} (x : (Σ k, ι k) → ℂ) (j0 : Fin N)
    (hrep : ∀ j, ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
      (∀ k, (dg k : ℤ) = dh k + n * a k) ∧ aeval y g = v j * aeval y h ∧
      eval x (map (Int.castRingHom ℂ) h) ≠ 0) :
    ∃ (e e' : K → ℕ) (G : Fin N → MRing ι) (H : MRing ι), (∀ j, IsMultiHomog (G j) e) ∧ IsMultiHomog H e' ∧
      (∀ k, (e k : ℤ) = e' k + n * a k) ∧ (∀ j, aeval y (G j) = v j * aeval y H) ∧ aeval x H ≠ 0 := by
  choose dg dh g h hg hh hd hgy hhx using hrep
  refine ⟨fun k => dg j0 k + ∑ i ∈ Finset.univ.erase j0, dh i k, fun k => ∑ i, dh i k,
    fun j => g j * ∏ i ∈ Finset.univ.erase j, h i, ∏ i, h i, fun j => ?_, ?_, fun k => ?_, fun j => ?_, ?_⟩
  · refine pn_congr (pn_mul (hg j) (pn_prod _ _ _ fun i _ => hh i)) fun k => ?_
    have e1 := Finset.add_sum_erase Finset.univ (fun i => (dh i k : ℤ)) (Finset.mem_univ j)
    have e2 := Finset.add_sum_erase Finset.univ (fun i => (dh i k : ℤ)) (Finset.mem_univ j0)
    simp only [Pi.add_apply, Finset.sum_apply]
    zify
    linear_combination hd j k - hd j0 k + e1 - e2
  · refine pn_congr (pn_prod _ _ _ fun i _ => hh i) fun k => ?_
    simp [Finset.sum_apply]
  · have e2 := Finset.add_sum_erase Finset.univ (fun i => (dh i k : ℤ)) (Finset.mem_univ j0)
    push_cast
    linear_combination hd j0 k + e2
  · rw [map_mul, hgy j, map_prod, map_prod,
      ← Finset.mul_prod_erase Finset.univ (fun i => aeval y (h i)) (Finset.mem_univ j)]
    ring
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => by rw [← pn_eval_map_int]; exact hhx i

end Block

end PowerBlockPointNorm

open PowerBlockPointNorm in

theorem PowerBlockPointNorm.proof (h1 : SectionPointValue.Statement) (h2 : LocalRep.Statement) :
    PowerBlockPointNorm.Statement := by
  intro K _ _ ι _ Ω _ y A m N v B hA _ hv hmet q F hF
  have hFv : aeval (addBlock y v) F ∈ chartLat y A.a (m * q) := mem_chartLat_new hv hF
  have hcont : ContinuousOn (secNormAt y A (m * q) (aeval (addBlock y v) F)) (mcPts (mCoordIdeal y)) := by
    rcases (mcPts (mCoordIdeal y)).eq_empty_or_nonempty with he | ⟨x0, hx0⟩
    · rw [he]
      exact continuousOn_empty _
    · obtain ⟨w, hwc, -, hwn, -, -⟩ := h1 K ι Ω y A (pn_relevant hx0) hA
      exact ((hwc (m * q) ⟨_, hFv⟩).norm).congr fun x hx => hwn (m * q) ⟨_, hFv⟩ x hx
  refine ⟨hcont, fun z hz => ?_⟩
  have hx : basePart₂ z ∈ mcPts (mCoordIdeal y) := pn_oldPart_mem hz
  obtain ⟨j0, hj0⟩ : ∃ j : Fin N, z ⟨none, j⟩ ≠ 0 := hz.1 none
  obtain ⟨w, -, hwv, hwn, -, -⟩ := h1 K ι Ω y A (pn_relevant hx) hA
  obtain ⟨e, e', G, H, hG, hH, he, hGy, hHx⟩ :=
    common_rep (basePart₂ z) j0 fun j => h2 K ι Ω y A.a m (v j) (basePart₂ z) (hv j) hx
  set x := basePart₂ z with hxdef
  have hApos : 0 < A.h x := A.pos x hx.1
  have hT : aeval x H * (A.h x : ℂ) ^ m ≠ 0 :=
    mul_ne_zero hHx (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr hApos.ne'))

  set W : Fin N → ℂ := fun j => w m ⟨v j, hv j⟩ x with hWdef
  have hval : ∀ j, aeval x (G j) = W j * aeval x H * (A.h x : ℂ) ^ m := fun j => by
    have := hwv m ⟨v j, hv j⟩ e e' (G j) H x (hG j) hH he (hGy j) hx
    simpa only [pn_eval_map_int] using this
  have hnorm : ∀ j, ‖W j‖ * B.h z = ‖z ⟨none, j⟩‖ := fun j => by
    rw [← hmet z hz j]
    exact congrArg (· * B.h z) (hwn m ⟨v j, hv j⟩ x hx).symm

  have hprop : ∀ i j, v i * aeval y (G j) = v j * aeval y (G i) := fun i j => by
    rw [hGy, hGy]
    ring
  have hzW : ∀ i j : Fin N, z ⟨none, i⟩ * W j = z ⟨none, j⟩ * W i := fun i j => by
    have := new_cross hG hprop hz i j
    rw [← hxdef, hval i, hval j] at this
    apply mul_right_cancel₀ hT
    linear_combination this
  have hW0 : W j0 ≠ 0 := by
    intro h0
    apply hj0
    have := hnorm j0
    rw [h0, norm_zero, zero_mul] at this
    exact norm_eq_zero.mp this.symm
  set lam : ℂ := z ⟨none, j0⟩ / W j0 with hlam
  have hzl : ∀ j : Fin N, z ⟨none, j⟩ = lam * W j := fun j => by
    rw [hlam, div_mul_eq_mul_div, eq_div_iff hW0]
    exact hzW j j0
  have hlamn : ‖lam‖ = B.h z := by
    rw [hlam, norm_div, ← hnorm j0, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hW0)]

  have hB : aeval y (bind₁ (newSubst G) F) = aeval y (H ^ q) * aeval (addBlock y v) F := by
    rw [aeval_bind₁, map_pow]
    exact aeval_scale_new hF _ _ (aeval y H) fun j => by
      show aeval y (G j) = aeval y H * v j
      rw [hGy j]
      ring
  have hC : aeval x (bind₁ (newSubst G) F) = (aeval x H * (A.h x : ℂ) ^ m) ^ q * aeval (newSubst W) F := by
    rw [aeval_bind₁]
    exact aeval_scale_new hF _ _ _ fun j => by
      show aeval x (G j) = _ * W j
      rw [hval j]
      ring
  have hD : aeval z F = lam ^ q * aeval (newSubst W) F := aeval_scale_new hF _ _ _ hzl
  have hdeg : ∀ k, ((q • e) k : ℤ) = (q • e') k + ((m * q : ℕ) : ℤ) * A.a k := fun k => by
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [he k]
    ring
  have hvF := hwv (m * q) ⟨_, hFv⟩ (q • e) (q • e') (bind₁ (newSubst G) F) (H ^ q) x
    (homog_bind_new G hG hF) (pn_pow hH q) hdeg (by rw [hB]; ring) hx
  rw [pn_eval_map_int, pn_eval_map_int, hC, map_pow, pow_mul] at hvF
  have hwF : w (m * q) ⟨_, hFv⟩ x = aeval (newSubst W) F := by
    apply mul_left_cancel₀ (pow_ne_zero q hT)
    linear_combination -hvF
  have hsec : secNormAt y A (m * q) (aeval (addBlock y v) F) x = ‖w (m * q) ⟨_, hFv⟩ x‖ :=
    hwn (m * q) ⟨_, hFv⟩ x hx
  have hBpos : 0 < B.h z := B.pos z hz.1
  rw [hsec, hwF, pn_eval_map_int, hD, norm_mul, norm_pow, hlamn,
    mul_div_cancel_left₀ _ (pow_ne_zero q hBpos.ne')]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
