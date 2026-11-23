import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EichlerIsometry

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SelfDual

open Matrix GlobalTheory.HL.Eichler GlobalTheory.UnramOrder

theorem exists_eq_span_range {R : Type*} [CommRing R] [IsPrincipalIdealRing R] (n : ℕ) :
    ∀ N : Submodule R (Fin n → R), ∃ b : Fin n → Fin n → R,
      N = Submodule.span R (Set.range b) := by
  induction n with
  | zero => intro N; exact ⟨fun _ => 0, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro N
    let ι : (Fin n → R) →ₗ[R] (Fin (n + 1) → R) :=
      { toFun := fun v => Fin.cons 0 v
        map_add' := fun v w => by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp
        map_smul' := fun c v => by ext i; refine Fin.cases ?_ (fun i => ?_) i <;> simp }
    obtain ⟨b, hb⟩ := ih (N.comap ι)
    obtain ⟨g, hg⟩ := IsPrincipalIdealRing.principal
      (N.map (LinearMap.proj (R := R) (φ := fun _ : Fin (n + 1) => R) 0))
    obtain ⟨x, hx, hxg⟩ : g ∈ N.map (LinearMap.proj (R := R) (φ := fun _ : Fin (n + 1) => R) 0) :=
      hg ▸ Submodule.mem_span_singleton_self g
    refine ⟨Fin.cons x fun i => ι (b i), le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hg ▸ Submodule.mem_map_of_mem hy)
      have h0 : (y - a • x) 0 = 0 := by
        have h1 : x 0 = g := hxg
        have h2 : a * g = y 0 := ha
        simp [h1, h2]
      have h1 : ι (Fin.tail (y - a • x)) = y - a • x := by
        show Fin.cons 0 (Fin.tail (y - a • x)) = _
        rw [← h0, Fin.cons_self_tail]
      have h2 : Fin.tail (y - a • x) ∈ N.comap ι := by
        rw [Submodule.mem_comap, h1]; exact N.sub_mem hy (N.smul_mem a hx)
      rw [hb] at h2
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
      refine (Submodule.mem_span_range_iff_exists_fun R).2 ⟨Fin.cons a d, ?_⟩
      rw [← hd, map_sum] at h1
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, ← map_smul, h1]
      abel
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      refine Fin.cases hx (fun i => ?_) i
      have : b i ∈ N.comap ι := hb ▸ Submodule.subset_span ⟨i, rfl⟩
      exact this

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_mul_mem (L : LocE F E) (x : E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O := by
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) x (Algebra.IsIntegral.isIntegral x)
  refine ⟨m, nonZeroDivisors.coe_ne_zero m, (L.O_def _).2 ?_⟩
  convert hm using 1
  rw [Submonoid.smul_def, Algebra.smul_def]
  rfl

theorem exists_mul_mem_finset (L : LocE F E) (s : Finset E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ ∀ x ∈ s, algebraMap F E c * x ∈ L.O := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert x s _ ih =>
    obtain ⟨c, hc, h⟩ := ih
    obtain ⟨d, hd, h'⟩ := exists_mul_mem L x
    refine ⟨c * d, mul_ne_zero hc hd, fun y hy => ?_⟩
    rw [Subring.coe_mul, map_mul]
    rcases Finset.mem_insert.1 hy with rfl | hy
    · rw [mul_assoc]
      exact L.O.mul_mem ((algebraMap_mem_iff L _).2 c.2) h'
    · rw [mul_right_comm]
      exact L.O.mul_mem (h y hy) ((algebraMap_mem_iff L _).2 d.2)

theorem exists_eq_span_of_fg (L : LocE F E) [IsPrincipalIdealRing L.O] {n : ℕ}
    {Λ : Submodule L.O (Fin n → E)} (h : Λ.FG) :
    ∃ b : Fin n → Fin n → E, Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨c, hc, hs⟩ := exists_mul_mem_finset L
    (s.biUnion fun x => Finset.univ.image fun i => x i)
  have hc' : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)
  have h1 : algebraMap F E (c : F)⁻¹ * algebraMap F E c = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hc', map_one]
  let f : (Fin n → L.O) →ₗ[L.O] (Fin n → E) :=
    { toFun := fun v i => algebraMap F E (c : F)⁻¹ * v i
      map_add' := fun v w => by ext i; simp [mul_add]
      map_smul' := fun a v => by
        ext i
        show _ * ((a : E) * v i) = (a : E) * (_ * _)
        ring }
  have hle : Submodule.span L.O (s : Set (Fin n → E)) ≤ LinearMap.range f := by
    rw [Submodule.span_le]
    intro x hx
    refine ⟨fun i => ⟨algebraMap F E c * x i, hs _ ?_⟩, ?_⟩
    · exact Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    · ext i
      show algebraMap F E (c : F)⁻¹ * (algebraMap F E c * x i) = _
      rw [← mul_assoc, h1, one_mul]
  obtain ⟨b, hb⟩ := exists_eq_span_range n
    ((Submodule.span L.O (s : Set (Fin n → E))).comap f)
  refine ⟨fun i => f (b i), ?_⟩
  rw [← Submodule.map_comap_eq_of_le hle, hb, Submodule.map_span, ← Set.range_comp]
  rfl

theorem hf_sum_l (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type*} [Fintype ι]
    (a : ι → E) (b : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ k, a k • b k) y = ∑ k, a k * hf L Hm (b k) y := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hf]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, hf_add_l, hf_smul_l, ih]

theorem hf_sum_r (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type*} [Fintype ι]
    (a : ι → E) (b : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm y (∑ k, a k • b k) = ∑ k, L.cj (a k) * hf L Hm y (b k) := by
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp [hf]
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, hf_add_r, hf_smul_r, ih]

theorem span_range_eq_top (L : LocE F E) {n : ℕ} {ι : Type*} {b : ι → Fin n → E}
    (h : IsLat L (Submodule.span L.O (Set.range b))) : Submodule.span E (Set.range b) = ⊤ := by
  rw [← h.2, Submodule.span_span_of_tower]

theorem exists_dual (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E} (hH : IsUnit Hm.det)
    {b : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤) :
    ∃ y : Fin n → Fin n → E, ∀ i j, hf L Hm (b i) (y j) = if i = j then 1 else 0 := by
  have h1 : ∀ i, ∃ a : Fin n → E, ∑ k, a k • b k = Pi.single i 1 := fun i =>
    (Submodule.mem_span_range_iff_exists_fun E).1 (hb ▸ Submodule.mem_top)
  choose C hC using h1
  have h2 : Matrix.of C * Matrix.of b = 1 := by
    ext i j
    have := congrFun (hC i) j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.of_apply, this, Pi.single_apply, eq_comm]
  have h3 : Matrix.of b * Hm * (Hm⁻¹ * Matrix.of C) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hH, mul_eq_one_comm.1 h2]
  refine ⟨fun j k => L.cj ((Hm⁻¹ * Matrix.of C) k j), fun i j => ?_⟩
  rw [← Matrix.one_apply, ← h3, Matrix.mul_apply]
  simp only [hf, L.cj_cj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_apply (M := Matrix.of b), Finset.sum_mul]
  rfl

theorem sum_hf_smul (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    {b : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤)
    (ho : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) (x : Fin n → E) :
    ∑ i, hf L Hm x (b i) • b i = x := by
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1
    (hb ▸ Submodule.mem_top : x ∈ Submodule.span E (Set.range b))
  simp [hf_sum_l, ho]

noncomputable def transfer (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (b b' : Fin n → Fin n → E) : (Fin n → E) →ₗ[E] (Fin n → E) where
  toFun x := ∑ i, hf L Hm x (b i) • b' i
  map_add' x y := by simp [hf_add_l, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [hf_smul_l, Finset.smul_sum, mul_smul]

theorem exists_isom (L : LocE F E) {n : ℕ} {Hm : Matrix (Fin n) (Fin n) E}
    {b b' : Fin n → Fin n → E} (hb : Submodule.span E (Set.range b) = ⊤)
    (hb' : Submodule.span E (Set.range b') = ⊤)
    (ho : ∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0)
    (ho' : ∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) :
    ∃ g ∈ isomG L Hm, ∀ i, g (b i) = b' i := by
  have key : ∀ {b b' : Fin n → Fin n → E}, Submodule.span E (Set.range b) = ⊤ →
      (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) →
      (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) →
      (transfer L Hm b' b).comp (transfer L Hm b b') = LinearMap.id := by
    intro b b' hb ho ho'
    refine LinearMap.ext fun x => ?_
    show ∑ j, hf L Hm (∑ i, hf L Hm x (b i) • b' i) (b' j) • b j = x
    simp [hf_sum_l, ho', sum_hf_smul L hb ho]
  refine ⟨LinearEquiv.ofLinear (transfer L Hm b b') (transfer L Hm b' b) (key hb' ho' ho)
    (key hb ho ho'), fun x y => ?_, fun i => ?_⟩
  · show hf L Hm (∑ i, hf L Hm x (b i) • b' i) (∑ i, hf L Hm y (b i) • b' i) = _
    conv_rhs => rw [← sum_hf_smul L hb ho x, ← sum_hf_smul L hb ho y]
    simp only [hf_sum_l L Hm (fun i => hf L Hm x (b i)), hf_sum_r L Hm (fun i => hf L Hm y (b i)),
      ho, ho']
  · show ∑ j, hf L Hm (b i) (b j) • b' j = _
    simp [ho]

theorem exists_orthonormal [IsNonarchimedeanLocalField F] [CharZero F] (L : LocE F E) {n : ℕ}
    {Hm : Matrix (Fin n) (Fin n) E} (hH : IsHermND L Hm) {Λ : Submodule L.O (Fin n → E)}
    (hΛ : IsSD L Hm Λ) : ∃ b : Fin n → Fin n → E,
      (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) ∧
      Λ = Submodule.span L.O (Set.range b) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨htr, -, -, hpir, -, -, -, hnorm⟩ := order_facts L ϖ hϖ
  obtain ⟨b, rfl⟩ := exists_eq_span_of_fg L hΛ.1.1
  have hmem : ∀ i, b i ∈ Submodule.span L.O (Set.range b) := fun i =>
    Submodule.subset_span ⟨i, rfl⟩
  obtain ⟨y, hy⟩ := exists_dual L hH.2 (span_range_eq_top L hΛ.1)
  have hsm : ∀ (a : L.O) (v : Fin n → E), a • v = (a : E) • v := fun _ _ => rfl
  have hy' : ∀ j, ∃ a : Fin n → L.O, ∑ k, a k • b k = y j := fun j => by
    refine (Submodule.mem_span_range_iff_exists_fun L.O).1 ((hΛ.2 _).1 fun x hx => ?_)
    obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).1 hx
    simp [hsm, hf_sum_l, hy]
  choose A hA using hy'
  let c : L.O →+* L.O := (L.cj : E →+* E).restrict L.O L.O fun x hx => cj_mem L hx
  have hcv : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun _ => rfl
  have hc : ∀ x, c (c x) = x := fun x => Subtype.ext (L.cj_cj x)
  let G : Matrix (Fin n) (Fin n) L.O :=
    fun i j => ⟨hf L Hm (b i) (b j), (hΛ.2 _).2 (hmem j) _ (hmem i)⟩
  have hGv : ∀ i j, (G i j : E) = hf L Hm (b i) (b j) := fun _ _ => rfl
  have hG : ∀ i j, c (G i j) = G j i := fun i j => Subtype.ext (hf_cj L hH.1 _ _)
  have hGA : G * (Matrix.of fun k j => c (A j k)) = 1 := by
    ext i j
    have h := hy i j
    rw [← hA j] at h
    simp only [hsm, hf_sum_r] at h
    rw [Matrix.mul_apply, Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one,
      ZeroMemClass.coe_zero, ← h, AddSubmonoidClass.coe_finset_sum]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hint : ∀ a : 𝒪[F], algebraMap F E a ∈ L.O := fun a => (algebraMap_mem_iff L a).2 a.2
  let i : 𝒪[F] →+* L.O := (algebraMap 𝒪[F] E).codRestrict L.O hint
  let : Algebra 𝒪[F] L.O := i.toAlgebra
  have hfix : ∀ x, c x = x → x ∈ (algebraMap 𝒪[F] L.O).range := fun x hx => by
    obtain ⟨a, ha⟩ := exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
    exact ⟨a, Subtype.ext ha.symm⟩
  have hinj : Function.Injective (algebraMap 𝒪[F] L.O) := fun a b h =>
    Subtype.ext (algebraMap_inj L (congrArg Subtype.val h))
  obtain ⟨P, hP, hGP⟩ := GlobalTheory.UnramifiedHermitian.exists_eq_transpose_mul_map (R₀ := 𝒪[F]) c hc hfix
    (by
      obtain ⟨w, hw, h⟩ := htr 1
      exact ⟨⟨w, hw⟩, Subtype.ext (by simpa [hcv] using h)⟩)
    (fun u hu hu' => by
      obtain ⟨v, hv⟩ := hu'.exists_right_inv
      have hv' := congrArg c hv
      rw [map_mul, hu, map_one] at hv'
      obtain ⟨s, rfl⟩ := hfix v (by linear_combination v * hv' - c v * hv)
      obtain ⟨r, rfl⟩ := hfix u hu
      have hr : IsUnit r := IsUnit.of_mul_eq_one s (hinj (by rw [map_mul, hv, map_one]))
      obtain ⟨x, hx, h⟩ := hnorm hr.unit
      exact ⟨⟨x, hx⟩, Subtype.ext h⟩)
    hG (Matrix.isUnit_det_of_right_inverse hGA)
  have hQ : (P⁻¹)ᵀ * G * (P⁻¹).map c = 1 := by
    rw [hGP, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.transpose_one, Matrix.one_mul, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hP,
      Matrix.map_one _ (map_zero c) (map_one c)]
  refine ⟨fun i => ∑ k, P⁻¹ k i • b k, fun i j => ?_, le_antisymm ?_ ?_⟩
  · have h := congrArg Subtype.val (congrFun (congrFun hQ i) j)
    rw [Matrix.one_apply, apply_ite Subtype.val, OneMemClass.coe_one, ZeroMemClass.coe_zero] at h
    rw [← h]
    simp only [hsm, hf_sum_l, hf_sum_r, Matrix.mul_apply, AddSubmonoidClass.coe_finset_sum,
      Subring.coe_mul, Matrix.transpose_apply, Matrix.map_apply, hcv, hGv]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine (Submodule.mem_span_range_iff_exists_fun L.O).2 ⟨fun i => P i k, ?_⟩
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h : ∀ l, ∑ i, P i k * P⁻¹ l i = if l = k then 1 else 0 := fun l => by
      rw [← Matrix.one_apply, ← Matrix.nonsing_inv_mul _ hP, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    simp [← Finset.sum_smul, h]
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hmem l)

end GlobalTheory.HL.SelfDual

theorem GlobalTheory.HL.SelfDual.orthonormal_basis_and_one_orbit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → (∀ Λ, IsSD L Hm Λ → ∃ b : Fin n → Fin n → E, (∀ i j, hf L Hm (b i) (b j) = if i = j then 1 else 0) ∧ Λ = Submodule.span L.O (Set.range b)) ∧ ∀ Λ Λ', IsSD L Hm Λ → IsSD L Hm Λ' → ∃ g ∈ isomG L Hm, g • Λ = Λ' := by
  intro F _ _ _ _ _ E _ _ _ L n Hm hH
  refine ⟨fun Λ hΛ => exists_orthonormal L hH hΛ, fun Λ Λ' hΛ hΛ' => ?_⟩
  obtain ⟨b, ho, rfl⟩ := exists_orthonormal L hH hΛ
  obtain ⟨b', ho', rfl⟩ := exists_orthonormal L hH hΛ'
  obtain ⟨g, hg, h⟩ := exists_isom L (span_range_eq_top L hΛ.1) (span_range_eq_top L hΛ'.1) ho ho'
  refine ⟨g, hg, ?_⟩
  rw [Submodule.smul_span, Set.smul_set_range]
  simp only [LinearEquiv.smul_def, h]
