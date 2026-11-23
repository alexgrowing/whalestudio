import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionGramMatrices.AlgebraMapNeZeroOfNotMem

noncomputable section

namespace PI.Dv.ProjGramW

open NumberField IsDedekindDomain Formalism.BasicNotions

section Det

variable {K : Type} [Field K] [NumberField K]

def famC {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V)
    (C : Matrix (Fin d) (Fin d) K) : Fin d → V :=
  fun j => ∑ i, C i j • b i

lemma famC_mul {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V)
    (C C' : Matrix (Fin d) (Fin d) K) : famC (famC b C) C' = famC b (C * C') := by
  funext j
  simp only [famC, Finset.smul_sum, smul_smul, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

lemma famC_one {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V) :
    famC b (1 : Matrix (Fin d) (Fin d) K) = b := by
  funext j
  simp [famC, Matrix.one_apply]

lemma span_famC {V : Type} [AddCommGroup V] [Module K V] {d : ℕ} (b : Fin d → V)
    (C : Matrix (Fin d) (Fin d) K) (hC : C.det ≠ 0) :
    Submodule.span K (Set.range (famC b C)) = Submodule.span K (Set.range b) := by
  have hCu : IsUnit C.det := isUnit_iff_ne_zero.mpr hC
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    have e : b j = famC (famC b C) C⁻¹ j := by
      rw [famC_mul, Matrix.mul_nonsing_inv C hCu, famC_one]
    rw [e]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

lemma span_O_famC {d : ℕ} (b : Fin d → V) (C : Matrix (Fin d) (Fin d) K) (hC : C.det ≠ 0) :
    Submodule.span K ((Submodule.span (𝓞 K) (Set.range (famC b C)) : Submodule (𝓞 K) V) : Set V) =
      Submodule.span K ((Submodule.span (𝓞 K) (Set.range b) : Submodule (𝓞 K) V) : Set V) := by
  rw [Submodule.span_span_of_tower, Submodule.span_span_of_tower, span_famC b C hC]

lemma idx_self (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {X : Submodule (𝓞 K) V} (hX : X.FG) :
    idxAt w X X = 0 := by
  have hl : LocLe w 0 X X := (locLe_zero_iff w X X).mpr fun x hx =>
    ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rw [one_smul]; exact hx⟩
  exact idx_eq_zero_of_loc hI w hX hX hl hl

lemma idx_add (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {M N P : Submodule (𝓞 K) V}
    (hM : M.FG) (hN : N.FG) (hP : P.FG) (hMN : Submodule.span K (M : Set V) = Submodule.span K (N : Set V))
    (hPN : Submodule.span K (P : Set V) = Submodule.span K (N : Set V)) :
    idxAt w M P = idxAt w M N + idxAt w N P :=
  (hI K V w M N hM hN hMN).2.1 P hP hPN

lemma vAdd_mul (w : HeightOneSpectrum (𝓞 K)) {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    vAdd w (x * y) = vAdd w x + vAdd w y := by
  unfold vAdd
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]
  ring

def stdE (d : ℕ) : Fin d → (Fin d →₀ K) := fun k => Finsupp.single k 1

lemma stdE_li (d : ℕ) : LinearIndependent K (stdE (K := K) d) := by
  have : stdE (K := K) d = ⇑(Finsupp.basisSingleOne : Module.Basis (Fin d) K (Fin d →₀ K)) := by
    funext k
    simp [stdE]
  rw [this]
  exact Finsupp.basisSingleOne.linearIndependent

def idxStd (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (C : Matrix (Fin d) (Fin d) K) : ℤ :=
  idxAt w (Submodule.span (𝓞 K) (Set.range (stdE (K := K) d)))
    (Submodule.span (𝓞 K) (Set.range (famC (stdE d) C)))

lemma idx_reduce (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} {b : Fin d → V}
    (hb : LinearIndependent K b) (C : Matrix (Fin d) (Fin d) K) (hC : C.det ≠ 0) :
    idxAt w (Submodule.span (𝓞 K) (Set.range b)) (Submodule.span (𝓞 K) (Set.range (famC b C))) =
      idxStd w C := by
  classical
  set g : (Fin d →₀ K) →ₗ[K] V := Finsupp.linearCombination K b with hg
  have hgb : ∀ k, g (stdE d k) = b k := by
    intro k
    rw [hg]
    simp [stdE, Finsupp.linearCombination_single]
  have hker : LinearMap.ker g = ⊥ := LinearMap.ker_eq_bot.mpr hb
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective g hker
  have hfg : ∀ x, f (g x) = x := fun x => by
    have := congrArg (fun (m : (Fin d →₀ K) →ₗ[K] (Fin d →₀ K)) => m x) hf
    simpa using this
  have hfb : ∀ k, f (b k) = stdE d k := fun k => by rw [← hgb k, hfg]
  have hfC : ∀ j, f (famC b C j) = famC (stdE d) C j := fun j => by
    simp only [famC, map_sum, map_smul, hfb]
  set M := Submodule.span (𝓞 K) (Set.range b) with hM
  set N := Submodule.span (𝓞 K) (Set.range (famC b C)) with hN
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range _)
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span K (M : Set V) = Submodule.span K (N : Set V) :=
    (span_O_famC b C hC).symm
  have h3 := (hI K V w M N hMfg hNfg hsp).2.2.1 (Fin d →₀ K) f

  have hrange : ∀ (u : Fin d → V), (∀ k, u k ∈ LinearMap.range g) →
      Submodule.span (𝓞 K) (Set.range u) ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) = ⊥ := by
    intro u hu
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have hle : Submodule.span (𝓞 K) (Set.range u) ≤ (LinearMap.range g).restrictScalars (𝓞 K) := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hu k
    obtain ⟨y, rfl⟩ := hle hx1
    have : f (g y) = 0 := hx2
    rw [hfg] at this
    rw [this, map_zero]
    exact Submodule.zero_mem _
  have hk1 : M ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) = ⊥ :=
    hrange b fun k => ⟨stdE d k, hgb k⟩
  have hk2 : N ⊓ (LinearMap.ker f).restrictScalars (𝓞 K) = ⊥ := by
    refine hrange _ fun j => ⟨famC (stdE d) C j, ?_⟩
    simp only [famC, map_sum, map_smul, hgb]
  have hm1 : M.map (f.restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (Set.range (stdE (K := K) d)) := by
    rw [hM, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext k
    exact hfb k
  have hm2 : N.map (f.restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) (Set.range (famC (stdE d) C)) := by
    rw [hN, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext k
    exact hfC k
  rw [h3, hk1, hk2, hm1, hm2, idx_self hI w (Submodule.fg_bot), zero_add]
  rfl

lemma li_famC {d : ℕ} {b : Fin d → V} (hb : LinearIndependent K b) (C : Matrix (Fin d) (Fin d) K)
    (hC : C.det ≠ 0) : LinearIndependent K (famC b C) := linIndep_mat hb C hC

lemma idxStd_mul (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (C1 C2 : Matrix (Fin d) (Fin d) K)
    (h1 : C1.det ≠ 0) (h2 : C2.det ≠ 0) : idxStd w (C1 * C2) = idxStd w C1 + idxStd w C2 := by
  have h12 : (C1 * C2).det ≠ 0 := by rw [Matrix.det_mul]; exact mul_ne_zero h1 h2
  have hEfg : (Submodule.span (𝓞 K) (Set.range (stdE (K := K) d))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hN1fg : (Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) C1))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hN12fg : (Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) (C1 * C2)))).FG :=
    Submodule.fg_span (Set.finite_range _)
  have hs1 := (span_O_famC (V := Fin d →₀ K) (stdE (K := K) d) C1 h1).symm
  have hs12 : Submodule.span K ((Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) (C1 * C2))) :
        Submodule (𝓞 K) (Fin d →₀ K)) : Set (Fin d →₀ K)) =
      Submodule.span K ((Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) C1)) :
        Submodule (𝓞 K) (Fin d →₀ K)) : Set (Fin d →₀ K)) := by
    rw [span_O_famC _ _ h12, span_O_famC _ _ h1]
  have hadd := idx_add (V := Fin d →₀ K) hI w hEfg hN1fg hN12fg hs1 hs12
  have hli : LinearIndependent K (famC (stdE (K := K) d) C1) := li_famC (V := Fin d →₀ K) (stdE_li d) C1 h1
  have hr := idx_reduce hI w hli C2 h2
  rw [famC_mul] at hr
  unfold idxStd
  rw [hadd, hr]
  rfl

lemma idxStd_one (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) (d : ℕ) :
    idxStd w (1 : Matrix (Fin d) (Fin d) K) = 0 := by
  unfold idxStd
  rw [famC_one]
  exact idx_self hI w (Submodule.fg_span (Set.finite_range _))

def colOp {d : ℕ} (j0 : Fin d) (v : Fin d → K) : Matrix (Fin d) (Fin d) K :=
  Matrix.of fun i j => if j = j0 then v i else (if i = j then 1 else 0)

lemma famC_std_apply {d : ℕ} (C : Matrix (Fin d) (Fin d) K) (j i : Fin d) :
    famC (stdE (K := K) d) C j i = C i j := by
  simp [famC, stdE, Finsupp.finsetSum_apply, Finsupp.single_apply]

lemma sum_smul_apply {d : ℕ} (r : Fin d → 𝓞 K) (u : Fin d → (Fin d →₀ K)) (i : Fin d) :
    (∑ k, r k • u k) i = ∑ k, r k • u k i := by
  rw [Finsupp.finsetSum_apply]
  rfl

lemma colOp_col {d : ℕ} (j0 : Fin d) (v : Fin d → K) (k : Fin d) (hk : k ≠ j0) :
    famC (stdE (K := K) d) (colOp j0 v) k = stdE d k := by
  ext i
  rw [famC_std_apply]
  by_cases h : i = k
  · subst h
    simp [colOp, stdE, hk]
  · simp [colOp, stdE, hk, h]

lemma sums_eq {d : ℕ} (j0 : Fin d) (v : Fin d → K) (r : Fin d → 𝓞 K) (hr : r j0 = 0) :
    ∑ k, r k • famC (stdE (K := K) d) (colOp j0 v) k = ∑ k, r k • stdE d k := by
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : k = j0
  · rw [hk, hr, zero_smul, zero_smul]
  · rw [colOp_col j0 v k hk]

lemma std_sum_at {d : ℕ} (j0 : Fin d) (r : Fin d → 𝓞 K) :
    (∑ k, r k • stdE (K := K) d k) j0 = algebraMap (𝓞 K) K (r j0) := by
  rw [sum_smul_apply]
  simp [stdE, Finsupp.single_apply, Algebra.smul_def]

lemma col_sum_at {d : ℕ} (j0 : Fin d) (v : Fin d → K) (r : Fin d → 𝓞 K) :
    (∑ k, r k • famC (stdE (K := K) d) (colOp j0 v) k) j0 = algebraMap (𝓞 K) K (r j0) * v j0 := by
  rw [sum_smul_apply, Finset.sum_eq_single j0]
  · rw [famC_std_apply]
    simp [colOp, Algebra.smul_def]
  · intro k _ hk
    rw [famC_std_apply]
    simp [colOp, hk, Ne.symm hk]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma algebraMap_eq_zero {r : 𝓞 K} (h : algebraMap (𝓞 K) K r = 0) : r = 0 :=
  IsFractionRing.injective (𝓞 K) K (by rw [h, map_zero])

lemma span_single_fam {d : ℕ} (j0 : Fin d) (u : Fin d → K) (hu : ∀ k, k ≠ j0 → u k = 0) :
    Submodule.span (𝓞 K) (Set.range u) = Submodule.span (𝓞 K) {u j0} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = j0
    · rw [hk]; exact Submodule.subset_span rfl
    · rw [hu k hk]; exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ rfl
    exact Submodule.subset_span ⟨j0, rfl⟩

lemma span_top_of_mem {Z : Submodule (𝓞 K) K} {z : K} (hz : z ∈ Z) (hz0 : z ≠ 0) :
    Submodule.span K (Z : Set K) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Submodule.subset_span hz) (isUnit_iff_ne_zero.mpr hz0)

lemma one_not_mem (w : HeightOneSpectrum (𝓞 K)) : (1 : 𝓞 K) ∉ w.asIdeal :=
  fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h)

lemma idx_int (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {y : K} (hy : y ≠ 0) {r : 𝓞 K} (hr : r ≠ 0) :
    idxAt w (Submodule.span (𝓞 K) {y}) (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r * y}) =
      vAdd w (algebraMap (𝓞 K) K r) := by
  classical
  have hv0 := vAdd_algebraMap_nonneg w r
  set F : ℕ := (vAdd w (algebraMap (𝓞 K) K r)).toNat with hFdef
  have hF : (F : ℤ) = vAdd w (algebraMap (𝓞 K) K r) := Int.toNat_of_nonneg hv0
  have hne := w.intValuation_ne_zero r hr
  have hval : w.intValuation r = WithZero.exp (-(F : ℤ)) := by
    rw [hF]
    unfold vAdd
    rw [HeightOneSpectrum.valuation_of_algebraMap, neg_neg, WithZero.exp_log hne]
  have hmem : r ∈ w.asIdeal ^ F := (w.intValuation_le_pow_iff_mem r F).mp (le_of_eq hval)
  obtain ⟨J, hJ⟩ := (w.intValuation_le_pow_iff_dvd r F).mp (le_of_eq hval)
  have hJw : ¬ J ≤ w.asIdeal := by
    intro hle
    have hd : w.asIdeal ^ (F + 1) ∣ Ideal.span {r} := by
      rw [hJ, pow_succ]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr hle)
    have := (w.intValuation_le_pow_iff_dvd r (F + 1)).mpr hd
    rw [hval, WithZero.exp_le_exp] at this
    push_cast at this
    linarith
  obtain ⟨t, htJ, htw⟩ := SetLike.not_le_iff_exists.mp hJw
  set X := Submodule.span (𝓞 K) {y} with hX
  set Y := Submodule.span (𝓞 K) {algebraMap (𝓞 K) K r * y} with hY
  set Z := (w.asIdeal ^ F) • X with hZ
  have hry : algebraMap (𝓞 K) K r * y = r • y := (Algebra.smul_def r y).symm
  have hry0 : algebraMap (𝓞 K) K r * y ≠ 0 :=
    mul_ne_zero (fun h => hr (algebraMap_eq_zero h)) hy
  have hyX : y ∈ X := Submodule.mem_span_singleton_self y
  have hryZ : algebraMap (𝓞 K) K r * y ∈ Z := by
    rw [hry]; exact Submodule.smul_mem_smul hmem hyX
  have hXfg : X.FG := Submodule.fg_span (Set.finite_singleton _)
  have hYfg : Y.FG := Submodule.fg_span (Set.finite_singleton _)
  have hZfg : Z.FG := Submodule.FG.of_le hXfg Submodule.smul_le_right
  have hsX : Submodule.span K (X : Set K) = ⊤ := span_top_of_mem hyX hy
  have hsY : Submodule.span K (Y : Set K) = ⊤ := span_top_of_mem (Submodule.mem_span_singleton_self _) hry0
  have hsZ : Submodule.span K (Z : Set K) = ⊤ := span_top_of_mem hryZ hry0
  have hYZ : LocLe w 0 Y Z := by
    rw [locLe_zero_iff]
    intro z hz
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hz
    refine ⟨1, one_not_mem w, ?_⟩
    rw [one_smul, hry, smul_smul]
    exact Submodule.smul_mem_smul (Ideal.mul_mem_left _ m hmem) hyX
  have hZY : LocLe w 0 Z Y := by
    rw [locLe_zero_iff]
    intro z hz
    obtain ⟨i, hi, rfl⟩ := Submodule.mem_smul_span_singleton.mp hz
    have hit : i * t ∈ Ideal.span {r} := by rw [hJ]; exact Ideal.mul_mem_mul hi htJ
    obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hit
    refine ⟨t, htw, ?_⟩
    have e : t • i • y = m • (algebraMap (𝓞 K) K r * y) := by
      rw [hry, smul_smul, smul_smul, hm, mul_comm]
    rw [e]
    exact Submodule.smul_mem _ m (Submodule.mem_span_singleton_self _)
  have hrk : Formalism.HN.rkK X = 1 := by
    unfold Formalism.HN.rkK
    rw [hsX, finrank_top, Module.finrank_self]
  have h5 := (hI K K w X X hXfg hXfg rfl).2.2.2.2.1 F
  have hadd := idx_add hI w hXfg hZfg hYfg (hsX.trans hsZ.symm) (hsY.trans hsZ.symm)
  have h0 := idx_eq_zero_of_loc hI w hZfg hYfg hZY hYZ
  rw [hadd, h5, h0, hrk, ← hF]
  simp

lemma idx_rank_one (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {c : K} (hc : c ≠ 0) :
    idxAt w (Submodule.span (𝓞 K) {(1 : K)}) (Submodule.span (𝓞 K) {c}) = vAdd w c := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap (𝓞 K) K b ≠ 0 := fun h => hb0 (algebraMap_eq_zero h)
  have haK : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h; apply hc; rw [← hab, h, zero_div]
  have ha0 : a ≠ 0 := fun h => haK (by rw [h, map_zero])
  have hα : algebraMap (𝓞 K) K a = algebraMap (𝓞 K) K b * c := by
    rw [← hab]; field_simp
  have h1 := idx_int hI w one_ne_zero ha0
  rw [mul_one] at h1
  have h2 := idx_int hI w hc hb0
  rw [← hα] at h2
  have hsp : ∀ z : K, z ≠ 0 → Submodule.span K ((Submodule.span (𝓞 K) {z} : Submodule (𝓞 K) K) : Set K) = ⊤ :=
    fun z hz => span_top_of_mem (Submodule.mem_span_singleton_self z) hz
  have hadd := idx_add hI w (M := Submodule.span (𝓞 K) {(1 : K)})
    (N := Submodule.span (𝓞 K) {algebraMap (𝓞 K) K a}) (P := Submodule.span (𝓞 K) {c})
    (Submodule.fg_span (Set.finite_singleton _)) (Submodule.fg_span (Set.finite_singleton _))
    (Submodule.fg_span (Set.finite_singleton _)) ((hsp 1 one_ne_zero).trans (hsp _ haK).symm)
    ((hsp c hc).trans (hsp _ haK).symm)
  rw [hadd, h1, idxAt_antisymm w (Submodule.span (𝓞 K) {algebraMap (𝓞 K) K a}), h2, hα,
    vAdd_mul w hbK hc]
  ring

lemma idxStd_colOp (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (j0 : Fin d) (v : Fin d → K)
    (hv : v j0 ≠ 0) (hdet : (colOp j0 v).det ≠ 0) : idxStd w (colOp j0 v) = vAdd w (v j0) := by
  classical
  set M := Submodule.span (𝓞 K) (Set.range (stdE (K := K) d)) with hM
  set N := Submodule.span (𝓞 K) (Set.range (famC (stdE (K := K) d) (colOp j0 v))) with hN
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range _)
  have hNfg : N.FG := Submodule.fg_span (Set.finite_range _)
  have hsp : Submodule.span K (M : Set (Fin d →₀ K)) = Submodule.span K (N : Set (Fin d →₀ K)) :=
    (span_O_famC (V := Fin d →₀ K) _ _ hdet).symm
  set φ : (Fin d →₀ K) →ₗ[K] K := Finsupp.lapply j0 with hφ
  have h3 := (hI K (Fin d →₀ K) w M N hMfg hNfg hsp).2.2.1 K φ
  have hkeq : M ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) := by
    ext x
    constructor
    · rintro ⟨hxM, hx0⟩
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hxM
      have h0 : (∑ k, r k • stdE (K := K) d k) j0 = 0 := hx0
      rw [std_sum_at] at h0
      have hr0 := algebraMap_eq_zero h0
      refine ⟨?_, hx0⟩
      rw [← sums_eq j0 v r hr0]
      exact (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨r, rfl⟩
    · rintro ⟨hxN, hx0⟩
      obtain ⟨r, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hxN
      have h0 : (∑ k, r k • famC (stdE (K := K) d) (colOp j0 v) k) j0 = 0 := hx0
      rw [col_sum_at] at h0
      have hr0 : r j0 = 0 :=
        algebraMap_eq_zero ((mul_eq_zero.mp h0).resolve_right hv)
      refine ⟨?_, hx0⟩
      rw [sums_eq j0 v r hr0]
      exact (Submodule.mem_span_range_iff_exists_fun _).mpr ⟨r, rfl⟩
  have hm1 : M.map (φ.restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) {(1 : K)} := by
    rw [hM, Submodule.map_span, ← Set.range_comp]
    rw [span_single_fam j0 _ (fun k hk => by simp [hφ, stdE, hk])]
    simp [hφ, stdE]
  have hm2 : N.map (φ.restrictScalars (𝓞 K)) = Submodule.span (𝓞 K) {v j0} := by
    rw [hN, Submodule.map_span, ← Set.range_comp]
    rw [span_single_fam j0 _ (fun k hk => by
      simp only [Function.comp_apply, LinearMap.restrictScalars_apply, hφ, Finsupp.lapply_apply]
      rw [famC_std_apply]; simp [colOp, hk, Ne.symm hk])]
    simp only [Function.comp_apply, LinearMap.restrictScalars_apply, hφ, Finsupp.lapply_apply]
    rw [famC_std_apply]
    simp [colOp]
  have hkfg : (N ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K)).FG := Submodule.FG.of_le hNfg inf_le_left
  unfold idxStd
  rw [h3, hkeq, idx_self hI w hkfg, zero_add, hm1, hm2]
  exact idx_rank_one hI w hv

lemma colOp_diag {d : ℕ} (k : Fin d) (c : K) :
    colOp k (fun i => if i = k then c else 0) = Matrix.diagonal (fun m => if m = k then c else 1) := by
  ext p q
  simp only [colOp, Matrix.of_apply, Matrix.diagonal_apply]
  by_cases hq : q = k
  · subst hq
    by_cases hp : p = q
    · subst hp; simp
    · simp [hp]
  · by_cases hp : p = q
    · subst hp; simp [hq]
    · simp [hp, hq]

lemma idxStd_diag (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (D : Fin d → K)
    (hD : ∀ k, D k ≠ 0) : idxStd w (Matrix.diagonal D) = vAdd w (∏ k, D k) := by
  classical
  have key : ∀ s : Finset (Fin d),
      idxStd w (Matrix.diagonal fun k => if k ∈ s then D k else 1) = vAdd w (∏ k ∈ s, D k) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty]
      rw [Matrix.diagonal_one, idxStd_one hI]
      simp [vAdd]
    | insert k s hk ih =>
      have e : (Matrix.diagonal fun m => if m ∈ insert k s then D m else 1) =
          (Matrix.diagonal fun m => if m ∈ s then D m else 1) *
            colOp k (fun i => if i = k then D k else 0) := by
        rw [colOp_diag, Matrix.diagonal_mul_diagonal]
        congr 1
        funext m
        by_cases hm : m = k
        · subst hm; simp [hk]
        · simp [hm]
      have hd1 : (Matrix.diagonal fun m => if m ∈ s then D m else 1).det ≠ 0 := by
        rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
        intro m _
        split_ifs
        · exact hD m
        · exact one_ne_zero
      have hd2 : (colOp k (fun i => if i = k then D k else 0)).det ≠ 0 := by
        rw [colOp_diag, Matrix.det_diagonal, Finset.prod_ne_zero_iff]
        intro m _
        split_ifs
        · exact hD k
        · exact one_ne_zero
      have hps : ∏ m ∈ s, D m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun m _ => hD m
      rw [e, idxStd_mul hI w _ _ hd1 hd2, ih, idxStd_colOp hI w k _ (by simp [hD k]) hd2,
        Finset.prod_insert hk, vAdd_mul w (hD k) hps]
      simp only [if_true]
      ring
  have := key Finset.univ
  simpa using this

lemma transvec_colOp {d : ℕ} (i j : Fin d) (hij : i ≠ j) (c : K) :
    Matrix.transvection i j c =
      colOp j (fun p => (if p = j then 1 else 0) + (if p = i then c else 0)) := by
  ext p q
  simp only [Matrix.transvection, colOp, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hq : q = j
  · subst hq
    by_cases hp : p = q
    · subst hp; simp [hij, Ne.symm hij]
    · by_cases hpi : p = i
      · subst hpi; simp [hp]
      · simp [hp, hpi, Ne.symm hpi]
  · by_cases hp : p = q
    · subst hp; simp [hq, Ne.symm hq]
    · simp [hp, hq, Ne.symm hq]

lemma idxStd_transvec (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ}
    (t : Matrix.TransvectionStruct (Fin d) K) : idxStd w t.toMatrix = 0 := by
  have hdet : t.toMatrix.det ≠ 0 := by rw [Matrix.TransvectionStruct.det]; exact one_ne_zero
  have e : t.toMatrix = colOp t.j (fun p => (if p = t.j then 1 else 0) + (if p = t.i then t.c else 0)) :=
    transvec_colOp t.i t.j t.hij t.c
  rw [e] at hdet ⊢
  rw [idxStd_colOp hI w _ _ (by simp [Ne.symm t.hij]) hdet]
  simp [Ne.symm t.hij, vAdd]

lemma idxStd_list (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ}
    (L : List (Matrix.TransvectionStruct (Fin d) K)) :
    idxStd w (L.map Matrix.TransvectionStruct.toMatrix).prod = 0 := by
  induction L with
  | nil => simpa using idxStd_one hI w d
  | cons t L ih =>
    rw [List.map_cons, List.prod_cons]
    have h1 : t.toMatrix.det ≠ 0 := by rw [Matrix.TransvectionStruct.det]; exact one_ne_zero
    have h2 : (L.map Matrix.TransvectionStruct.toMatrix).prod.det ≠ 0 := by
      rw [Matrix.TransvectionStruct.det_toMatrix_prod]; exact one_ne_zero
    rw [idxStd_mul hI w _ _ h1 h2, ih, idxStd_transvec hI w t, add_zero]

theorem idxStd_det (hI : IdxCalc) (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (C : Matrix (Fin d) (Fin d) K)
    (hC : C.det ≠ 0) : idxStd w C = vAdd w C.det := by
  classical
  obtain ⟨L, L', D, hCe⟩ := Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec C
  have hdL := Matrix.TransvectionStruct.det_toMatrix_prod L
  have hdL' := Matrix.TransvectionStruct.det_toMatrix_prod L'
  have hdetC : C.det = ∏ k, D k := by
    rw [hCe, Matrix.det_mul, Matrix.det_mul, hdL, hdL', Matrix.det_diagonal]
    ring
  have hD : ∀ k, D k ≠ 0 := fun k => Finset.prod_ne_zero_iff.mp (hdetC ▸ hC) k (Finset.mem_univ _)
  have hdD : (Matrix.diagonal D).det ≠ 0 := by rw [Matrix.det_diagonal, ← hdetC]; exact hC
  have h1 : (L.map Matrix.TransvectionStruct.toMatrix).prod.det ≠ 0 := by rw [hdL]; exact one_ne_zero
  have h1' : (L'.map Matrix.TransvectionStruct.toMatrix).prod.det ≠ 0 := by rw [hdL']; exact one_ne_zero
  have h12 : ((L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.diagonal D).det ≠ 0 := by
    rw [Matrix.det_mul]; exact mul_ne_zero h1 hdD
  rw [hdetC, hCe, idxStd_mul hI w _ _ h12 h1', idxStd_mul hI w _ _ h1 hdD, idxStd_list hI w L,
    idxStd_list hI w L', idxStd_diag hI w D hD]
  ring

end Det

theorem idxDet_of (hI : IdxCalc) : IdxDet := by
  intro K _ _ V _ _ _ _ w d b hb C hC
  have := idx_reduce hI w hb C hC
  rw [idxStd_det hI w C hC] at this
  exact this

end PI.Dv.ProjGramW
