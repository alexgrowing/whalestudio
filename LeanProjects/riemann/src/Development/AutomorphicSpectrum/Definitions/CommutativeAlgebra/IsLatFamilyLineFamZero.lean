import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotModel

open ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles GlobalTheory.CompanionTheory.Ar.Num

section General

variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁]
  [AddCommGroup V₂] [Module Ω V₂]

theorem pow_add_smul_mem {x : (Σ k, ι k) → Ω} {A : (∀ k, ι k) → AddSubgroup V}
    (hA : IsLatFamily o x A) {s t : ∀ k, ι k} (ht : mseg x t ≠ 0) {v : V} {m : ℕ} (n : ℕ)
    (h : (mseg x s / mseg x t) ^ m • v ∈ A t) : (mseg x s / mseg x t) ^ (n + m) • v ∈ A t := by
  rw [pow_add, mul_smul]
  exact hA.1 t ht _ (pow_mem (div_mem_chartRing _ _ _) _) _ h

theorem isLatFamily_lat {x : (Σ k, ι k) → Ω} {N : ℕ} (E : ChartBundle o (mseg x) N V) :
    IsLatFamily o x E.lat :=
  ⟨fun s _ => E.stable s, E.overlap⟩

theorem quotEquiv_of_quotIso {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra O Ω] {x : (Σ k, ι k) → Ω} {N N₁ : ℕ} {E E' : ChartBundle O (mseg x) N V}
    {F F' : ChartBundle O (mseg x) N₁ V₁} (h : QuotIso O x E E' F F') :
    QuotEquiv O x E.lat E'.lat F.lat F'.lat := by
  obtain ⟨P, hP⟩ := h
  refine ⟨P.lat, ⟨isLatFamily_lat P, fun s hs => ?_⟩, fun s hs => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hP s hs
    exact ⟨fun v w h => ⟨(h2 v).1 ⟨w, h⟩, (h4 w).1 ⟨v, h⟩⟩, fun v hv => (h2 v).2 hv, h3,
      fun v hv => (h1 v).2 hv⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hP s hs
    exact ⟨fun v h => (h1 v).1 h, fun w hw => (h4 w).2 hw⟩

def idGraph (A B' : (∀ k, ι k) → AddSubgroup V) : (∀ k, ι k) → AddSubgroup (V × V) := fun s =>
  (A s).comap (AddMonoidHom.fst V V) ⊓
    (B' s).comap (AddMonoidHom.snd V V - AddMonoidHom.fst V V)

theorem mem_idGraph {A B' : (∀ k, ι k) → AddSubgroup V} {s} {v w : V} :
    (v, w) ∈ idGraph A B' s ↔ v ∈ A s ∧ w - v ∈ B' s := by
  simp [idGraph, AddSubgroup.mem_comap]

theorem isLatFamily_idGraph {x : (Σ k, ι k) → Ω} {A B' : (∀ k, ι k) → AddSubgroup V}
    (hA : IsLatFamily o x A) (hB : IsLatFamily o x B') : IsLatFamily o x (idGraph A B') := by
  refine ⟨fun s hs a ha ⟨v, w⟩ h => ?_, fun s t hs ht ⟨v, w⟩ h => ?_⟩
  · rw [mem_idGraph] at h
    rw [Prod.smul_mk, mem_idGraph, ← smul_sub]
    exact ⟨hA.1 s hs a ha _ h.1, hB.1 s hs a ha _ h.2⟩
  · rw [mem_idGraph] at h
    obtain ⟨m, hm⟩ := hA.2 s t hs ht _ h.1
    obtain ⟨n, hn⟩ := hB.2 s t hs ht _ h.2
    refine ⟨n + m, ?_⟩
    rw [Prod.smul_mk, mem_idGraph, ← smul_sub]
    exact ⟨pow_add_smul_mem hA ht n hm, add_comm m n ▸ pow_add_smul_mem hB ht m hn⟩

theorem isQuotHom_idGraph {x : (Σ k, ι k) → Ω} {A A' B B' : (∀ k, ι k) → AddSubgroup V}
    (hA : IsLatFamily o x A) (hB : IsLatFamily o x B') (h1 : ∀ s, A' s ≤ A s)
    (h2 : ∀ s, B' s ≤ B s) (h3 : ∀ s, A s ≤ B s) (h4 : ∀ s, A' s ≤ B' s) :
    IsQuotHom o x A A' B B' (idGraph A B') := by
  refine ⟨isLatFamily_idGraph hA hB, fun s _ => ⟨fun v w h => ?_, fun v hv => ⟨v, ?_⟩,
    fun w => ?_, fun v hv => ?_⟩⟩
  · rw [mem_idGraph] at h
    exact ⟨h.1, by simpa using add_mem (h2 s h.2) (h3 s h.1)⟩
  · simp [mem_idGraph, hv]
  · simp [mem_idGraph]
  · simp [mem_idGraph, h1 s hv, h4 s hv]

theorem quotExact_tower {x : (Σ k, ι k) → Ω} {A A' A'' : (∀ k, ι k) → AddSubgroup V}
    (hA : IsLatFamily o x A) (hA' : IsLatFamily o x A') (hA'' : IsLatFamily o x A'')
    (h1 : ∀ s, A' s ≤ A s) (h2 : ∀ s, A'' s ≤ A' s) : QuotExact o x A' A'' A A'' A A' := by
  refine ⟨_, _, isQuotHom_idGraph hA' hA'' h2 (fun s => (h2 s).trans (h1 s)) h1 fun _ => le_rfl,
    isQuotHom_idGraph hA hA' (fun s => (h2 s).trans (h1 s)) h1 (fun _ => le_rfl) h2,
    fun s _ => ⟨fun v h => ?_, fun c hc => ⟨c, ?_⟩, fun b => ?_⟩⟩
  · simpa using (mem_idGraph.1 h).2
  · simp [mem_idGraph, hc]
  · simp only [mem_idGraph, zero_sub, neg_mem_iff]
    constructor
    · rintro ⟨-, h⟩
      exact ⟨b, h, by simp⟩
    · rintro ⟨a, ha, h⟩
      have : b ∈ A' s := by simpa using add_mem (h2 s h) ha
      exact ⟨h1 s this, this⟩

theorem quotEquiv_refl {x : (Σ k, ι k) → Ω} {A A' : (∀ k, ι k) → AddSubgroup V}
    (hA : IsLatFamily o x A) (hA' : IsLatFamily o x A') (h : ∀ s, A' s ≤ A s) :
    QuotEquiv o x A A' A A' := by
  refine ⟨_, isQuotHom_idGraph hA hA' h h (fun _ => le_rfl) fun _ => le_rfl,
    fun s _ => ⟨fun v h => ?_, fun c hc => ⟨c, ?_⟩⟩⟩
  · simpa using (mem_idGraph.1 h).2
  · simp [mem_idGraph, hc]

theorem quotEquiv_symm {x : (Σ k, ι k) → Ω} {A A' : (∀ k, ι k) → AddSubgroup V}
    {B B' : (∀ k, ι k) → AddSubgroup V₁} (h : QuotEquiv o x A A' B B') :
    QuotEquiv o x B B' A A' := by
  obtain ⟨Γ, ⟨hΓ, h1⟩, h2⟩ := h
  refine ⟨fun s => (Γ s).comap (AddEquiv.prodComm : V₁ × V ≃+ V × V₁).toAddMonoidHom,
    ⟨⟨fun s hs a ha ⟨w, v⟩ h => hΓ.1 s hs a ha (v, w) h,
      fun s t hs ht ⟨w, v⟩ h => hΓ.2 s t hs ht (v, w) h⟩, fun s hs => ⟨fun w v h => ?_, ?_, ?_, ?_⟩⟩,
    fun s hs => ⟨fun w h => ?_, ?_⟩⟩
  · exact ((h1 s hs).1 v w h).symm
  · exact (h2 s hs).2
  · exact fun v => ⟨(h2 s hs).1 v, (h1 s hs).2.2.2 v⟩
  · exact fun w hw => ((h1 s hs).2.2.1 w).2 hw
  · exact ((h1 s hs).2.2.1 w).1 h
  · exact (h1 s hs).2.1

theorem le_of_quotEquiv_zero {x : (Σ k, ι k) → Ω} {A A' : (∀ k, ι k) → AddSubgroup V}
    {B : (∀ k, ι k) → AddSubgroup V₁} (h : QuotEquiv o x A A' B B) {s} (hs : mseg x s ≠ 0) :
    A s ≤ A' s := by
  obtain ⟨Γ, ⟨-, h1⟩, h2⟩ := h
  intro v hv
  obtain ⟨w, hw⟩ := (h1 s hs).2.1 v hv
  have h0 := ((h1 s hs).2.2.1 w).2 ((h1 s hs).1 v w hw).2
  exact (h2 s hs).1 v (by simpa using sub_mem hw h0)

def lineFam (o : Type*) [CommRing o] [Algebra o Ω] (x : (Σ k, ι k) → Ω) (u : Ω) (a : K → ℤ) :
    (∀ k, ι k) → AddSubgroup Ω := fun s =>
  (chartRing o (mseg x) s).toSubring.toAddSubgroup.map (AddMonoidHom.mulRight (u * chartMon x s a))

theorem isLine_lineFam (x : (Σ k, ι k) → Ω) (u : Ω) (a : K → ℤ) :
    IsLine o x u a (lineFam o x u a) := by
  intro s _ v
  simp only [lineFam, AddSubgroup.mem_map]
  exact ⟨fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩, fun ⟨r, hr, h⟩ => ⟨r, hr, h.symm⟩⟩

theorem isScaled_line {x : (Σ k, ι k) → Ω} {u c : Ω} {a : K → ℤ} {A A'}
    (hA : IsLine o x u a A) (hA' : IsLine o x (c * u) a A') : IsScaled x c A A' := by
  intro s hs v
  rw [hA' s hs]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨_, (hA s hs _).2 ⟨r, hr, rfl⟩, by rw [smul_eq_mul]; ring⟩
  · rintro ⟨e, he, rfl⟩
    obtain ⟨r, hr, rfl⟩ := (hA s hs _).1 he
    exact ⟨r, hr, by rw [smul_eq_mul]; ring⟩

theorem chartMon_mul_neg {x : (Σ k, ι k) → Ω} {s} (hs : mseg x s ≠ 0) (a : K → ℤ) :
    chartMon x s a * chartMon x s (-a) = 1 := by
  unfold chartMon
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun k _ => ?_
  have : x ⟨k, s k⟩ ≠ 0 := (Finset.prod_ne_zero_iff.1 hs) k (Finset.mem_univ k)
  rw [← zpow_add₀ this]; simp

theorem isDualLat_line {x : (Σ k, ι k) → Ω} {u : Ω} (hu : u ≠ 0) {a : K → ℤ} {A B}
    (hA : IsLine o x u a A) (hB : IsLine o x u⁻¹ (-a) B) :
    IsDualLat o x (LinearMap.mul Ω Ω) A B := by
  refine ⟨⟨fun w w' h => by simpa using LinearMap.congr_fun h 1,
    fun f => ⟨f 1, by ext; simp⟩⟩, fun s hs w => ?_⟩
  have key : (u * chartMon x s a) * (u⁻¹ * chartMon x s (-a)) = 1 := by
    rw [mul_mul_mul_comm, mul_inv_cancel₀ hu, chartMon_mul_neg hs, one_mul]
  rw [hB s hs]
  constructor
  · rintro ⟨r, hr, rfl⟩ v hv
    obtain ⟨r', hr', rfl⟩ := (hA s hs _).1 hv
    rw [LinearMap.mul_apply', mul_mul_mul_comm, key, mul_one]
    exact mul_mem hr' hr
  · intro h
    refine ⟨_, h _ ((hA s hs _).2 ⟨1, one_mem _, rfl⟩), ?_⟩
    rw [LinearMap.mul_apply', one_mul, mul_right_comm, key, one_mul]

end General

section Line

variable {o : Type*} [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]

def pt (t : Ω) : (Σ _ : Unit, Fin 2) → Ω := fun p => ![1, t] p.2

theorem mseg_pt (t : Ω) (s : Unit → Fin 2) : mseg (pt t) s = ![1, t] (s ()) := by
  simp [mseg, pt]

theorem chartMon_pt (t : Ω) (s : Unit → Fin 2) (a : Unit → ℤ) :
    chartMon (pt t) s a = ![1, t] (s ()) ^ a () := by
  simp [chartMon, pt]

theorem t_mem (t : Ω) : t ∈ chartRing o (mseg (pt t)) (fun _ => 0) := by
  simpa [mseg_pt] using div_mem_chartRing (o := o) (mseg (pt t)) (fun _ => 0) (fun _ => 1)

theorem tinv_mem (t : Ω) : t⁻¹ ∈ chartRing o (mseg (pt t)) (fun _ => 1) := by
  simpa [mseg_pt] using div_mem_chartRing (o := o) (mseg (pt t)) (fun _ => 1) (fun _ => 0)

theorem chart_cases (s : Unit → Fin 2) : s = (fun _ => 0) ∨ s = fun _ => 1 := by
  have : s = fun _ => s () := rfl
  rw [this]
  generalize s () = i
  fin_cases i <;> simp

theorem trivFlagMod_euler (ϖ : o) {t : Ω} (ht : t ≠ 0) :
    TrivFlagMod o ϖ (pt t) 2 ![fun _ => -1, fun _ => 1] := by
  have h0 := t_mem (o := o) t
  have h1 := tinv_mem (o := o) t
  refine ⟨fun s => ![!![1, 0; t, 1], !![t⁻¹, -1; 1, 0]] (s ()), fun s _ => ?_, fun s r _ _ => ?_⟩
  · rcases chart_cases s with rfl | rfl
    · refine ⟨fun i j => ?_, 1, one_mem _, 0, zero_mem _, by simp⟩
      fin_cases i <;> fin_cases j <;> simp [h0]
    · refine ⟨fun i j => ?_, 1, one_mem _, 0, zero_mem _, by simp⟩
      fin_cases i <;> fin_cases j <;> simp [h1]
  · rcases chart_cases s with rfl | rfl <;> rcases chart_cases r with rfl | rfl
    · refine ⟨0, 1, 0, fun i j => ?_, fun i j => ?_, fun i j h => ?_, fun i => ?_, fun i j => ?_, by simp⟩
      · fin_cases i <;> fin_cases j <;> simp
      · simp
      · exact Matrix.one_apply_ne h.ne'
      · simp [chartMon_pt]
      · fin_cases i <;> fin_cases j <;> simp [h0]
    · refine ⟨1, !![1, t⁻¹; 0, t⁻¹ * t⁻¹], 0, fun i j => ?_, fun i j => ?_, fun i j h => ?_,
        fun i => ?_, fun i j => ?_, ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [h1, mul_mem, -mul_inv_rev]
      · simp
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> simp [chartMon_pt, mseg_pt, ht]
      · fin_cases i <;> fin_cases j <;> simp [mseg_pt, h1, ht]
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mseg_pt, ht, Matrix.mul_apply, Fin.sum_univ_two]
    · refine ⟨1, !![1, -t; 0, t * t], 0, fun i j => ?_, fun i j => ?_, fun i j h => ?_,
        fun i => ?_, fun i j => ?_, ?_⟩
      · fin_cases i <;> fin_cases j <;> simp [h0, mul_mem]
      · simp
      · fin_cases i <;> fin_cases j <;> simp_all
      · fin_cases i <;> simp [chartMon_pt, mseg_pt, ht]
      · fin_cases i <;> fin_cases j <;> simp [mseg_pt, h0, ht]
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mseg_pt, ht, Matrix.mul_apply, Fin.sum_univ_two]
    · refine ⟨0, 1, 0, fun i j => ?_, fun i j => ?_, fun i j h => ?_, fun i => ?_, fun i j => ?_, by simp⟩
      · fin_cases i <;> fin_cases j <;> simp
      · simp
      · exact Matrix.one_apply_ne h.ne'
      · fin_cases i <;> simp [chartMon_pt, ht]
      · fin_cases i <;> fin_cases j <;> simp [h1]

theorem exists_poly_zero {t a : Ω} (ha : a ∈ chartRing o (mseg (pt t)) (fun _ => 0)) :
    ∃ P : Polynomial o, Polynomial.aeval t P = a := by
  have : chartRing o (mseg (pt t)) (fun _ => 0) ≤ (Polynomial.aeval t).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    rcases chart_cases s with rfl | rfl
    · exact ⟨1, by simp [mseg_pt]⟩
    · exact ⟨Polynomial.X, by simp [mseg_pt]⟩
  exact this ha

theorem exists_poly_one {t a : Ω} (ht : t ≠ 0) (ha : a ∈ chartRing o (mseg (pt t)) (fun _ => 1)) :
    ∃ P : Polynomial o, Polynomial.aeval t⁻¹ P = a := by
  have : chartRing o (mseg (pt t)) (fun _ => 1) ≤ (Polynomial.aeval t⁻¹).range := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨s, rfl⟩
    rcases chart_cases s with rfl | rfl
    · exact ⟨Polynomial.X, by simp [mseg_pt]⟩
    · exact ⟨1, by simp [mseg_pt, ht]⟩
  exact this ha

open Polynomial in
theorem dvd_of_overlap {t : Ω} (ht0 : t ≠ 0) (ht : Function.Injective (aeval (R := o) t)) (ϖ : o)
    (G D Z : o[X]) (m : ℕ)
    (h : t ^ m * aeval t⁻¹ G = aeval t D * (t ^ m * t) + algebraMap o Ω ϖ * aeval t Z) :
    C ϖ ∣ G := by
  set k := G.natDegree
  letI : Invertible t⁻¹ := invertibleOfNonzero (inv_ne_zero ht0)
  have hr := eval₂_reflect_mul_pow (algebraMap o Ω) t⁻¹ k G le_rfl
  rw [invOf_eq_inv, inv_inv, ← aeval_def, ← aeval_def] at hr
  have hp : reflect k G * X ^ m = D * X ^ (m + k + 1) + C ϖ * (Z * X ^ k) := by
    apply ht
    simp only [map_mul, map_add, map_pow, aeval_X, aeval_C]
    have : aeval t (reflect k G) = aeval t⁻¹ G * t ^ k := by
      rw [← hr, mul_assoc, ← mul_pow, inv_mul_cancel₀ ht0, one_pow, mul_one]
    rw [this]
    linear_combination t ^ k * h
  rw [C_dvd_iff_dvd_coeff]
  intro i
  by_cases hi : i ≤ k
  · have := congrArg (fun P => coeff P (k - i + m)) hp
    simp only [coeff_mul_X_pow, coeff_add, coeff_C_mul, coeff_reflect] at this
    rw [coeff_mul_X_pow', if_neg (by omega), zero_add, revAt_le (by omega),
      show k - (k - i) = i by omega] at this
    exact ⟨_, this⟩
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _

open Polynomial in

theorem not_trivFlagMod_one {ϖ : o} (hϖ : ¬ IsUnit ϖ) {t : Ω} (ht0 : t ≠ 0)
    (ht : Function.Injective (aeval (R := o) t)) (ht' : Function.Injective (aeval (R := o) t⁻¹))
    {N : ℕ} (b : Fin (N + 1) → Unit → ℤ) (hb : b 0 () = 1) :
    ¬ TrivFlagMod o ϖ (pt t) (N + 1) b := by
  rintro ⟨g, h1, h2⟩
  have n0 : mseg (pt t) (fun _ => 0) ≠ 0 := by simp [mseg_pt]
  have n1 : mseg (pt t) (fun _ => 1) ≠ 0 := by simp [mseg_pt, ht0]
  obtain ⟨m, U, Z, -, hZ, hU, hd, -, he⟩ := h2 _ _ n1 n0
  obtain ⟨hg1, h, hh, r, hr, hdet⟩ := h1 _ n1
  have col : ∀ i, ∃ W : o[X], g (fun _ => 1) i 0 = algebraMap o Ω ϖ * aeval t⁻¹ W := by
    intro i
    obtain ⟨G, hG⟩ := exists_poly_one ht0 (hg1 i 0)
    obtain ⟨D, hD⟩ := exists_poly_zero ((h1 _ n0).1 i 0)
    obtain ⟨Z', hZ'⟩ := exists_poly_zero (hZ i 0)
    have e := congrFun (congrFun he i) 0
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.mul_apply,
      Finset.sum_eq_single 0 (fun j _ hj => by rw [hU j 0 (Fin.pos_iff_ne_zero.2 hj), mul_zero])
        (by simp), hd 0, ← hG, ← hD, ← hZ'] at e
    obtain ⟨W, hW⟩ := dvd_of_overlap ht0 ht ϖ G D Z' m
      (by simpa [mseg_pt, chartMon_pt, hb] using e)
    exact ⟨W, by rw [← hG, hW]; simp⟩
  choose W hW using col
  choose P hP using fun i j => exists_poly_one ht0 (hg1 i j)
  obtain ⟨H, hH⟩ := exists_poly_one ht0 hh
  obtain ⟨R, hR⟩ := exists_poly_one ht0 hr
  have hPW : ∀ i, P i 0 = C ϖ * W i := fun i => ht' (by rw [hP, hW]; simp)
  have hdP : (Matrix.of P).det * H = 1 + C ϖ * R := by
    apply ht'
    have : g (fun _ => 1) = (aeval t⁻¹).mapMatrix (Matrix.of P) := by
      ext i j; simp [hP]
    rw [map_mul, AlgHom.map_det, ← this, hH, hdet]
    simp [hR]
  have hdiv : C ϖ ∣ (Matrix.of P).det := by
    rw [Matrix.det_succ_column_zero]
    refine Finset.dvd_sum fun i _ => ?_
    rw [Matrix.of_apply, hPW]
    exact ((dvd_mul_right _ _).mul_left _).mul_right _
  have h1' : C ϖ ∣ (1 : o[X]) := by
    have := hdiv.mul_right H
    rw [hdP] at this
    exact (dvd_add_left (dvd_mul_right _ _)).1 this
  exact hϖ (isUnit_C.1 (isUnit_of_dvd_one h1'))

theorem isLatFamily_lineFam_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (u : Ω) : IsLatFamily o x (lineFam o x u 0) := by
  refine ⟨fun s hs a ha v hv => ?_, fun s t hs ht v hv => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := (isLine_lineFam x u 0 s hs v).1 hv
    exact (isLine_lineFam x u 0 s hs _).2 ⟨_, mul_mem ha hr, by rw [smul_eq_mul, mul_assoc]⟩
  · obtain ⟨r, hr, rfl⟩ := (isLine_lineFam x u 0 s hs v).1 hv
    obtain ⟨m, hm⟩ := exists_pow_mul_mem_chartRing (mseg x) s t hs hr
    exact ⟨m, (isLine_lineFam x u 0 t ht _).2 ⟨_, hm, by simp [chartMon, mul_assoc]⟩⟩

theorem lineFam_mul_le {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (c : o) (u : Ω) (a : K → ℤ) (s) :
    lineFam o x (algebraMap o Ω c * u) a s ≤ lineFam o x u a s := by
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨r * algebraMap o Ω c, (chartRing o (mseg x) s).mul_mem hr (Subalgebra.algebraMap_mem _ c), by simp; ring⟩

theorem quotExact_const {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    (x : (Σ k, ι k) → Ω) (ϖ : o) :
    QuotExact o x (lineFam o x (algebraMap o Ω ϖ * 1) 0)
      (lineFam o x (algebraMap o Ω ϖ * (algebraMap o Ω ϖ * 1)) 0) (lineFam o x 1 0)
      (lineFam o x (algebraMap o Ω ϖ * (algebraMap o Ω ϖ * 1)) 0) (lineFam o x 1 0)
      (lineFam o x (algebraMap o Ω ϖ * 1) 0) :=
  quotExact_tower (isLatFamily_lineFam_zero _ _) (isLatFamily_lineFam_zero _ _)
    (isLatFamily_lineFam_zero _ _) (lineFam_mul_le x ϖ _ _) (lineFam_mul_le x ϖ _ _)

open Polynomial in

theorem not_quotEquiv_zero {ϖ : o} (hϖ : ¬ IsUnit ϖ) {t : Ω}
    (ht : Function.Injective (aeval (R := o) t)) (B : (Unit → Fin 2) → AddSubgroup Ω) :
    ¬ QuotEquiv o (pt t) (lineFam o (pt t) 1 0) (lineFam o (pt t) (algebraMap o Ω ϖ * 1) 0) B B := by
  intro h
  have n0 : mseg (pt t) (fun _ => 0) ≠ 0 := by simp [mseg_pt]
  obtain ⟨r, hr, e⟩ := le_of_quotEquiv_zero h n0
    ((isLine_lineFam (pt t) 1 0 _ n0 1).2 ⟨1, one_mem _, by simp [chartMon]⟩)
  obtain ⟨P, rfl⟩ := exists_poly_zero hr
  have : C ϖ * P = 1 := ht (by simpa [chartMon, mul_comm] using e)
  exact hϖ (isUnit_C.1 (IsUnit.of_mul_eq_one _ this))

end Line

section Concrete

open Polynomial

noncomputable def genT : FractionRing ℤ[X] := algebraMap ℤ[X] (FractionRing ℤ[X]) X

theorem transc_genT : Transcendental ℤ genT :=
  (transcendental_algebraMap_iff (IsFractionRing.injective _ _)).2 (transcendental_X ℤ)

theorem genT_ne_zero : genT ≠ 0 := fun h => transc_genT (h ▸ isAlgebraic_zero)

theorem euler_order :
    TrivFlagMod ℤ 2 (pt genT) 2 ![fun _ => -1, fun _ => 1] ∧
    ¬ TrivFlagMod ℤ 2 (pt genT) 2 ![fun _ => 1, fun _ => -1] :=
  ⟨trivFlagMod_euler _ genT_ne_zero, not_trivFlagMod_one (by decide) genT_ne_zero
    (transcendental_iff_injective.1 transc_genT)
    (transcendental_iff_injective.1 fun h => transc_genT (by simpa using h.inv)) _ rfl⟩

theorem quot_two_ne_zero (B : (Unit → Fin 2) → AddSubgroup (FractionRing ℤ[X])) :
    ¬ QuotEquiv ℤ (pt genT) (lineFam ℤ (pt genT) 1 0)
      (lineFam ℤ (pt genT) (algebraMap ℤ _ 2 * 1) 0) B B :=
  not_quotEquiv_zero (by decide) (transcendental_iff_injective.1 transc_genT) B

end Concrete

end GlobalTheory.CompanionTheory.Ar.Num.QuotModel
