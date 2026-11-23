import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

noncomputable section

namespace ModelDimension.Near

open Formalism.L2.Pj Filter Topology

def Prim {V : Type} [CommRing V] {n r : ℕ} (u : Matrix (Fin n) (Fin r) V) : Prop :=
  ∀ (p : V) (a : Fin r → V) (cv : Fin n → V), p ≠ 0 → u.mulVec a = p • cv → ∃ a', a = p • a'

section Lin

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {n r : ℕ}

theorem exists_left_inv {u u' : Matrix (Fin n) (Fin r) V} (hu : Prim u)
    (hc : ∀ i j, u' i j - u i j ∈ IsLocalRing.maximalIdeal V) : ∃ B : Matrix (Fin r) (Fin n) V, B * u' = 1 := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmax := hπ.maximalIdeal_eq
  have hπm : IsLocalRing.residue V π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hmax]
    exact Ideal.mem_span_singleton_self π
  have hinj : LinearMap.ker (Matrix.toLin' (u.map (IsLocalRing.residue V))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    rw [Matrix.toLin'_apply] at hx
    choose a ha using fun j => IsLocalRing.residue_surjective (x j)
    have hm : ∀ i, u.mulVec a i ∈ IsLocalRing.maximalIdeal V := by
      intro i
      rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_mulVec]
      have e1 : (⇑(IsLocalRing.residue V) ∘ a) = x := funext ha
      rw [e1]
      exact congrFun hx i
    rw [hmax] at hm
    choose cv hcv using fun i => Ideal.mem_span_singleton'.mp (hm i)
    have hmul : u.mulVec a = π • cv := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hcv i]
    obtain ⟨a', ha'⟩ := hu π a cv hπ.ne_zero hmul
    funext j
    rw [← ha j, ha', Pi.smul_apply, smul_eq_mul, map_mul, hπm, zero_mul]
    rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hBb : LinearMap.toMatrix' g * u.map (IsLocalRing.residue V) = 1 := by
    have h1 := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1
  have hsurj : ∀ i j, ∃ b, IsLocalRing.residue V b = LinearMap.toMatrix' g i j :=
    fun i j => IsLocalRing.residue_surjective _
  choose B₁ hB₁ using hsurj
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Matrix (Fin r) (Fin n) V,
      ∀ i j, IsLocalRing.residue V (B₀ i j) = LinearMap.toMatrix' g i j := ⟨Matrix.of B₁, hB₁⟩
  have hred : (B₀ * u').map (IsLocalRing.residue V) = 1 := by
    rw [Matrix.map_mul]
    have e1 : B₀.map (IsLocalRing.residue V) = LinearMap.toMatrix' g := by
      ext i j
      exact hB₀ i j
    have e2 : u'.map (IsLocalRing.residue V) = u.map (IsLocalRing.residue V) := by
      ext i j
      simp only [Matrix.map_apply]
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact hc i j
    rw [e1, e2, hBb]
  have hdet : IsUnit (B₀ * u').det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    have e3 : (IsLocalRing.residue V).mapMatrix (B₀ * u') = 1 := hred
    rw [e3, Matrix.det_one]
    exact one_ne_zero
  refine ⟨(B₀ * u')⁻¹ * B₀, ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]

variable {K : Type} [Field K] [Algebra V K] [IsFractionRing V K]

omit [IsDiscreteValuationRing V] in
theorem Prim.integral {u : Matrix (Fin n) (Fin r) V} (hu : Prim u) (a : Fin r → K) (cv : Fin n → V)
    (h : (u.map (algebraMap V K)).mulVec a = fun j => algebraMap V K (cv j)) (i : Fin r) :
    a i ∈ (algebraMap V K).range := by
  obtain ⟨p, hp⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors V) Finset.univ a
  have hp' : ∀ j, ∃ y, algebraMap V K y = (p : V) • a j := fun j => hp j (Finset.mem_univ j)
  choose a'' ha'' using hp'
  have hp0 : (p : V) ≠ 0 := nonZeroDivisors.ne_zero p.2
  have hpK : algebraMap V K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).mpr hp0
  have hmul : u.mulVec a'' = (p : V) • cv := by
    funext j
    apply IsFractionRing.injective V K
    rw [RingHom.map_mulVec]
    have e1 : (algebraMap V K ∘ a'') = (p : V) • a := funext ha''
    rw [e1, Matrix.mulVec_smul, h]
    simp [Algebra.smul_def]
  obtain ⟨a', ha'⟩ := hu (p : V) a'' cv hp0 hmul
  refine ⟨a' i, ?_⟩
  apply mul_left_cancel₀ hpK
  have e2 : algebraMap V K (a'' i) = algebraMap V K p * algebraMap V K (a' i) := by
    rw [ha', Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← e2, ha'' i, Algebra.smul_def]

theorem vV_eq_zero {x : K} (hx : x ≠ 0) (h1 : x ∈ (algebraMap V K).range) (h2 : x⁻¹ ∈ (algebraMap V K).range) :
    vV V x = 0 := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hle : valV V x ≤ 1 := by
    rw [← ha]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
  have hle' : valV V x⁻¹ ≤ 1 := by
    rw [← hb]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ b
  have hge : 1 ≤ valV V x := by
    calc (1 : _) = valV V (x * x⁻¹) := by rw [mul_inv_cancel₀ hx, map_one]
      _ = valV V x * valV V x⁻¹ := map_mul _ _ _
      _ ≤ valV V x * 1 := by gcongr
      _ = valV V x := mul_one _
  unfold vV
  rw [le_antisymm hle hge, WithZero.log_one, neg_zero]

theorem diag_mul {A B : Matrix (Fin r) (Fin r) K} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin r) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem vV_diag_eq {g : Matrix (Fin n) (Fin r) K} {C C' : Matrix (Fin r) (Fin r) K} (hC : C.BlockTriangular id)
    (hC' : C'.BlockTriangular id) (h0 : ∀ i, C i i ≠ 0) (h0' : ∀ i, C' i i ≠ 0) {u u' : Matrix (Fin n) (Fin r) V}
    {B : Matrix (Fin r) (Fin n) V} (hB : B * u = 1) (hu' : Prim u') (e : g * C = u.map (algebraMap V K))
    (e' : g * C' = u'.map (algebraMap V K)) (i : Fin r) : vV V (C' i i) = vV V (C i i) := by
  classical
  have hdetC : IsUnit C.det := by
    rw [Matrix.det_of_isUpperTriangular hC]
    exact Ne.isUnit (Finset.prod_ne_zero_iff.mpr fun i _ => h0 i)
  have hdetC' : IsUnit C'.det := by
    rw [Matrix.det_of_isUpperTriangular hC']
    exact Ne.isUnit (Finset.prod_ne_zero_iff.mpr fun i _ => h0' i)
  letI := C.invertibleOfIsUnitDet hdetC
  letI := C'.invertibleOfIsUnitDet hdetC'
  have hCi : (C⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hC
  have hCi' : (C'⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hC'
  obtain ⟨X, hX⟩ : ∃ X, X = C⁻¹ * C' := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = C'⁻¹ * C := ⟨_, rfl⟩
  have hXY : X * Y = 1 := by
    rw [hX, hY, Matrix.mul_assoc, ← Matrix.mul_assoc C', Matrix.mul_nonsing_inv _ hdetC', Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hdetC]
  have hXtri : X.BlockTriangular id := hX ▸ hCi.mul hC'
  have hYtri : Y.BlockTriangular id := hY ▸ hCi'.mul hC
  have hXint : ∀ i j, X i j ∈ (algebraMap V K).range := by
    have hBK : B.map (algebraMap V K) * u.map (algebraMap V K) = 1 := by
      rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    have hBg : B.map (algebraMap V K) * g = C⁻¹ := by
      have h1 : B.map (algebraMap V K) * g * C = 1 := by rw [Matrix.mul_assoc, e, hBK]
      calc B.map (algebraMap V K) * g = B.map (algebraMap V K) * g * C * C⁻¹ := by
            rw [Matrix.mul_assoc (B.map (algebraMap V K) * g), Matrix.mul_nonsing_inv _ hdetC, Matrix.mul_one]
        _ = C⁻¹ := by rw [h1, Matrix.one_mul]
    have hXeq : X = (B * u').map (algebraMap V K) := by
      rw [Matrix.map_mul, ← e', ← Matrix.mul_assoc, hBg, hX]
    intro i j
    rw [hXeq]
    exact ⟨(B * u') i j, rfl⟩
  have hYint : ∀ i j, Y i j ∈ (algebraMap V K).range := by
    intro i j
    have h2 : u'.map (algebraMap V K) * Y = u.map (algebraMap V K) := by
      rw [← e', ← e, hY, Matrix.mul_assoc, ← Matrix.mul_assoc C', Matrix.mul_nonsing_inv _ hdetC', Matrix.one_mul]
    have hcol : (u'.map (algebraMap V K)).mulVec (fun k => Y k j) = fun l => algebraMap V K (u l j) := by
      funext l
      have h3 := congrFun (congrFun h2 l) j
      rw [Matrix.mul_apply] at h3
      simp only [Matrix.mulVec, dotProduct]
      rw [h3]
      rfl
    exact Prim.integral hu' (fun k => Y k j) (fun l => u l j) hcol i
  have hdiag := diag_mul hXtri hYtri i
  rw [hXY, Matrix.one_apply_eq] at hdiag
  have hXi0 : X i i ≠ 0 := left_ne_zero_of_mul_eq_one hdiag.symm
  have hXinv : (X i i)⁻¹ ∈ (algebraMap V K).range := by
    rw [inv_eq_of_mul_eq_one_right hdiag.symm]
    exact hYint i i
  have hv0 : vV V (X i i) = 0 := vV_eq_zero hXi0 (hXint i i) hXinv
  have hCinv : (C⁻¹) i i = (C i i)⁻¹ := by
    have h4 := diag_mul hCi hC i
    rw [Matrix.nonsing_inv_mul _ hdetC, Matrix.one_apply_eq] at h4
    exact eq_inv_of_mul_eq_one_left h4.symm
  have hXii : X i i = (C i i)⁻¹ * C' i i := by
    rw [hX, diag_mul hCi hC' i, hCinv]
  have hC'eq : C' i i = C i i * X i i := by
    rw [hXii, ← mul_assoc, mul_inv_cancel₀ (h0 i), one_mul]
  rw [hC'eq, vV_mul (h0 i) hXi0, hv0, add_zero]

end Lin

section Close

variable (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K] [Algebra V K]
  [IsFractionRing V K] {S : Type} [CommRing S] (ψ : S →+* K)

def closeF : Filter (S →+* K) where
  sets := {P | ∃ (F : Finset S) (n : ℕ), ∀ ψ' : S →+* K,
    (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV V (ψ' s - ψ s)) → ψ' ∈ P}
  univ_sets := ⟨∅, 0, fun _ _ => trivial⟩
  sets_of_superset := fun ⟨F, n, h⟩ hs => ⟨F, n, fun ψ' h' => hs (h ψ' h')⟩
  inter_sets := by
    classical
    rintro P Q ⟨F, n, h⟩ ⟨F', n', h'⟩
    refine ⟨F ∪ F', max n n', fun ψ' hh => ⟨h ψ' fun s hs => ?_, h' ψ' fun s hs => ?_⟩⟩
    · exact (hh s (Finset.mem_union_left _ hs)).imp id fun q => le_trans (by exact_mod_cast le_max_left _ _) q
    · exact (hh s (Finset.mem_union_right _ hs)).imp id fun q => le_trans (by exact_mod_cast le_max_right _ _) q

def Tend (a : (S →+* K) → K) (b : K) : Prop :=
  ∀ c : K, c ≠ 0 → ∀ᶠ ψ' in closeF V ψ, valV V (a ψ' - b) < valV V c

variable {V ψ}

private theorem mem_closeF_lemma {P : Set (S →+* K)} (F : Finset S) (n : ℕ)
    (h : ∀ ψ' : S →+* K, (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV V (ψ' s - ψ s)) → ψ' ∈ P) : P ∈ closeF V ψ :=
  ⟨F, n, h⟩

private theorem valV_lt_of_vV_lt_lemma_2 {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (h : vV V y < vV V x) :
    valV V x < valV V y := by
  unfold vV at h
  exact (WithZero.log_lt_log (valV_ne_zero hx) (valV_ne_zero hy)).mp (by omega)

theorem tend_val (s : S) : Tend V ψ (fun ψ' => ψ' s) (ψ s) := by
  intro c hc
  refine mem_closeF_lemma {s} (vV V c + 1).toNat fun ψ' h => ?_
  show valV V (ψ' s - ψ s) < valV V c
  have hc0 : 0 < valV V c := zero_lt_iff.mpr (valV_ne_zero hc)
  by_cases hd : ψ' s - ψ s = 0
  · rw [hd, map_zero]
    exact hc0
  · rcases h s (Finset.mem_singleton_self s) with h1 | h1
    · exact absurd (sub_eq_zero.mpr h1) hd
    · apply valV_lt_of_vV_lt_lemma_2 hd hc
      have h2 := Int.self_le_toNat (vV V c + 1)
      omega

theorem Tend.add {a a' : (S →+* K) → K} {b b' : K} (h : Tend V ψ a b) (h' : Tend V ψ a' b') :
    Tend V ψ (fun ψ' => a ψ' + a' ψ') (b + b') := by
  intro c hc
  filter_upwards [h c hc, h' c hc] with ψ' h1 h2
  have e : a ψ' + a' ψ' - (b + b') = (a ψ' - b) + (a' ψ' - b') := by ring
  rw [e]
  exact Valuation.map_add_lt _ h1 h2

theorem tend_const (b : K) : Tend V ψ (fun _ => b) b := by
  intro c hc
  exact Filter.Eventually.of_forall fun _ => by
    show valV V (b - b) < valV V c
    rw [sub_self, map_zero]
    exact zero_lt_iff.mpr (valV_ne_zero hc)

theorem Tend.mul_const {a : (S →+* K) → K} {b : K} (h : Tend V ψ a b) (d : K) :
    Tend V ψ (fun ψ' => a ψ' * d) (b * d) := by
  intro c hc
  by_cases hd : d = 0
  · exact Filter.Eventually.of_forall fun ψ' => by
      show valV V (a ψ' * d - b * d) < valV V c
      rw [hd, mul_zero, mul_zero, sub_self, map_zero]
      exact zero_lt_iff.mpr (valV_ne_zero hc)
  · filter_upwards [h (c / d) (div_ne_zero hc hd)] with ψ' h1
    have hvd : 0 < valV V d := zero_lt_iff.mpr (valV_ne_zero hd)
    have e : a ψ' * d - b * d = (a ψ' - b) * d := by ring
    rw [e, map_mul]
    have e2 : valV V c = valV V (c / d) * valV V d := by rw [← map_mul, div_mul_cancel₀ c hd]
    rw [e2]
    exact mul_lt_mul_of_pos_right h1 hvd

theorem Tend.sum {I : Type} (s : Finset I) {a : I → (S →+* K) → K} {b : I → K} (h : ∀ i, Tend V ψ (a i) (b i)) :
    Tend V ψ (fun ψ' => ∑ i ∈ s, a i ψ') (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tend_const (V := V) (ψ := ψ) (0 : K))
  | insert i s hi ih =>
    have h2 := (h i).add ih
    simpa [Finset.sum_insert hi] using h2

theorem Tend.div {a a' : (S →+* K) → K} {b b' : K} (h : Tend V ψ a b) (h' : Tend V ψ a' b') (hb : b' ≠ 0) :
    Tend V ψ (fun ψ' => a ψ' / a' ψ') (b / b') := by
  intro c hc
  have hvb : valV V b' ≠ 0 := valV_ne_zero hb
  obtain ⟨t, ht, hbt⟩ : ∃ t : K, t ≠ 0 ∧ valV V b * valV V t ≤ valV V c * valV V b' * valV V b' := by
    by_cases hb0 : b = 0
    · exact ⟨1, one_ne_zero, by rw [hb0, map_zero, zero_mul]; exact zero_le⟩
    · refine ⟨c * b' * b' / b, div_ne_zero (mul_ne_zero (mul_ne_zero hc hb) hb) hb0, le_of_eq ?_⟩
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      field_simp
  filter_upwards [h (c * b') (mul_ne_zero hc hb), h' b' hb, h' t ht] with ψ' h1 h2 h3
  have ha' : valV V (a' ψ') = valV V b' := Valuation.map_eq_of_sub_lt _ h2
  have ha'0 : a' ψ' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha'
    exact hvb ha'.symm
  have e : a ψ' / a' ψ' - b / b' = (a ψ' - b) / a' ψ' + -(b * (a' ψ' - b') / (a' ψ' * b')) := by
    field_simp
    ring
  rw [e]
  apply Valuation.map_add_lt
  · rw [map_div₀, ha']
    have e3 : valV V c = valV V (c * b') / valV V b' := by
      rw [map_mul, mul_div_assoc, div_self hvb, mul_one]
    rw [e3]
    exact (div_lt_div_iff_of_pos_right (zero_lt_iff.mpr hvb)).mpr h1
  · by_cases hb0 : b = 0
    · rw [hb0, zero_mul, zero_div, neg_zero, map_zero]
      exact zero_lt_iff.mpr (valV_ne_zero hc)
    · rw [Valuation.map_neg, map_div₀, map_mul, map_mul, ha']
      have hpos : 0 < valV V b' * valV V b' := zero_lt_iff.mpr (mul_ne_zero hvb hvb)
      have e4 : valV V c = valV V c * valV V b' * valV V b' / (valV V b' * valV V b') := by
        rw [mul_assoc, mul_div_assoc, div_self (mul_ne_zero hvb hvb), mul_one]
      rw [e4]
      refine (div_lt_div_iff_of_pos_right hpos).mpr (lt_of_lt_of_le ?_ hbt)
      exact mul_lt_mul_of_pos_left h3 (zero_lt_iff.mpr (valV_ne_zero hb0))

theorem eventually_ne {h : S} (hh : ψ h ≠ 0) : ∀ᶠ ψ' in closeF V ψ, ψ' h ≠ 0 := by
  filter_upwards [tend_val h (ψ h) hh] with ψ' h1 h0
  rw [h0, zero_sub, Valuation.map_neg] at h1
  exact lt_irrefl _ h1

open Classical in

def ext (h : S) (χ₀ : Localization.Away h →+* K) (ψ' : S →+* K) : Localization.Away h →+* K :=
  if hh : ψ' h = 0 then χ₀ else IsLocalization.Away.lift h (Ne.isUnit hh)

theorem ext_comp {h : S} (χ₀ : Localization.Away h →+* K) {ψ' : S →+* K} (hh : ψ' h ≠ 0) :
    (ext h χ₀ ψ').comp (algebraMap S _) = ψ' := by
  rw [ext, dif_neg hh]
  exact IsLocalization.Away.lift_comp h _

theorem tend_ext {h : S} (hh : ψ h ≠ 0) {χ₀ : Localization.Away h →+* K} (h0 : χ₀.comp (algebraMap S _) = ψ)
    (a : Localization.Away h) : Tend V ψ (fun ψ' => ext h χ₀ ψ' a) (χ₀ a) := by
  obtain ⟨n, s, hs⟩ := IsLocalization.Away.surj h a
  have key : ∀ φ : Localization.Away h →+* K, φ (algebraMap S _ h) ≠ 0 →
      φ a = φ (algebraMap S _ s) / φ (algebraMap S _ h) ^ n := by
    intro φ hφ
    rw [← hs, map_mul, map_pow, mul_div_assoc, div_self (pow_ne_zero _ hφ), mul_one]
  have hχ : ∀ x, χ₀ (algebraMap S _ x) = ψ x := fun x => by rw [← h0]; rfl
  have ht : Tend V ψ (fun ψ' => ψ' s / ψ' h ^ n) (ψ s / ψ h ^ n) := by
    have h1 : Tend V ψ (fun ψ' => ψ' (h ^ n)) (ψ (h ^ n)) := tend_val (h ^ n)
    simp only [map_pow] at h1
    exact (tend_val s).div h1 (pow_ne_zero _ hh)
  rw [key χ₀ (by rw [hχ]; exact hh), hχ, hχ]
  intro c hc
  filter_upwards [ht c hc, eventually_ne hh] with ψ' h1 h2
  have hE : ∀ x, ext h χ₀ ψ' (algebraMap S _ x) = ψ' x := fun x => by
    rw [← RingHom.comp_apply, ext_comp χ₀ h2]
  rw [key _ (by rw [hE]; exact h2), hE, hE]
  exact h1

theorem Tend.cong {a : (S →+* K) → K} {b : V} (h : Tend V ψ a (algebraMap V K b)) :
    ∀ᶠ ψ' in closeF V ψ, ∃ b' : V, algebraMap V K b' = a ψ' ∧ b' - b ∈ IsLocalRing.maximalIdeal V := by
  filter_upwards [h 1 one_ne_zero] with ψ' h1
  rw [map_one] at h1
  have hint : a ψ' - algebraMap V K b ∈ (algebraMap V K).range := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro w
    have hw : w = IsDiscreteValuationRing.maximalIdeal V := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (w.isPrime.isMaximal w.ne_bot)
    rw [hw]
    exact le_of_lt h1
  obtain ⟨y, hy⟩ := hint
  refine ⟨b + y, by rw [map_add, hy, add_sub_cancel], ?_⟩
  rw [add_sub_cancel_left]
  have h3 : valV V (algebraMap V K y) < 1 := by
    rw [hy]
    exact h1
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ y).mp h3

end Close

end ModelDimension.Near
