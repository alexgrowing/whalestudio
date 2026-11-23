import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd

set_option autoImplicit false
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PlaceInt
namespace GlobalTheory.LatticeIndex

theorem not_dvd_relIndex {G : Type} [AddCommGroup G] (A B : AddSubgroup G) (k ℓ : ℕ) (hl : ℓ.Prime)
    (hk : Nat.Coprime k ℓ) (h0 : A.relIndex B ≠ 0) (h : ∀ b ∈ B, k • b ∈ A) : ¬ ℓ ∣ A.relIndex B := by
  intro hdvd
  have : Fact ℓ.Prime := ⟨hl⟩
  have : (A.addSubgroupOf B).FiniteIndex := ⟨h0⟩
  rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card] at hdvd
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' ℓ hdvd
  induction x using QuotientAddGroup.induction_on with
  | H b =>
    have hkb : k • (b : B ⧸ A.addSubgroupOf B) = 0 := by
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      simpa using h b b.2
    have hd := addOrderOf_dvd_of_nsmul_eq_zero hkb
    rw [hx] at hd
    exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hk.symm hd)

section Idx
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem index_range_matrix (m : Matrix (Fin n) (Fin n) (𝓞 E)) (hm : m.det ≠ 0) :
    (LinearMap.range m.mulVecLin).toAddSubgroup.index = (Algebra.norm ℤ m.det).natAbs := by
  classical
  have hinj : Function.Injective m.mulVecLin := by
    intro x y hxy
    have h0 : m.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hm h0)
  let N : Submodule ℤ (Fin n → 𝓞 E) := (LinearMap.range m.mulVecLin).restrictScalars ℤ
  let e : (Fin n → 𝓞 E) ≃+ N := AddEquiv.ofBijective
    ((m.mulVecLin.restrictScalars ℤ).codRestrict N (fun x => ⟨x, rfl⟩)).toAddMonoidHom
    ⟨fun x y h => hinj (congrArg Subtype.val h), fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩
  have h1 := Submodule.natAbs_det_equiv N e
  have h2 : N.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin n → 𝓞 E) →+ N) =
      m.mulVecLin.restrictScalars ℤ := by
    ext x
    rfl
  have h3 : LinearMap.det m.mulVecLin = m.det := LinearMap.det_toLin' m
  rw [h2, LinearMap.det_restrictScalars, h3] at h1
  rw [AddSubgroup.index_eq_card, h1]
  rfl

def incl (E : Type) [Field E] [NumberField E] (n : ℕ) : (Fin n → 𝓞 E) →ₗ[𝓞 E] (Fin n → E) :=
  (Algebra.linearMap (𝓞 E) E).compLeft (Fin n)

theorem incl_apply (v : Fin n → 𝓞 E) (i : Fin n) : incl E n v i = algebraMap (𝓞 E) E (v i) := rfl

theorem incl_inj : Function.Injective (incl E n) := by
  intro u v huv
  funext i
  have := congrFun huv i
  rw [incl_apply, incl_apply] at this
  exact FaithfulSMul.algebraMap_injective (𝓞 E) E this

theorem mem_std {v : Fin n → E} : v ∈ stdLat E n ↔ ∃ u, incl E n u = v := by
  simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  constructor
  · intro h
    choose u hu using h
    exact ⟨u, funext fun i => by rw [incl_apply, hu]⟩
  · rintro ⟨u, rfl⟩ i
    exact ⟨u i, (incl_apply u i).symm⟩

theorem incl_mulVec (m : Matrix (Fin n) (Fin n) (𝓞 E)) (v : Fin n → 𝓞 E) :
    incl E n (m.mulVec v) = (m.map (algebraMap (𝓞 E) E)).mulVec (incl E n v) := by
  funext i
  simp only [incl_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

variable [IsCMField E]

theorem index_part (Λ : GenLat E n) (N M ℓ : ℕ) (hL : Λ.LevOK N M) (hl : ℓ.Prime) (A : Adapt Λ N ℓ) (r : ℕ) :
    ((Algebra.norm ℤ A.q.det).natAbs ^ r).factorization ℓ = (Λ.mIdx N r).factorization ℓ ∧ Λ.mIdx N r ≠ 0 := by
  classical
  obtain ⟨hNodd, -, hNL⟩ := hL
  have hN : N ≠ 0 := hNodd.pos.ne'
  have hk₁ : A.k₁ ≠ 0 := by
    intro h0
    have := A.cop₁
    rw [h0, Nat.coprime_zero_left] at this
    exact hl.ne_one this
  let ι : (Fin n → 𝓞 E) →+ (Fin n → E) := (incl E n).toAddMonoidHom
  have hgq : A.g.det * A.q.det = ((A.k₁ * N : ℕ) : 𝓞 E) ^ n := by
    have := congrArg Matrix.det A.gq
    rwa [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at this
  have hc0 : ((A.k₁ * N : ℕ) : 𝓞 E) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast mul_ne_zero hk₁ hN)
  have hq0 : A.q.det ≠ 0 := fun h => hc0 (by rw [← hgq, h, mul_zero])
  have hg0 : A.g.det ≠ 0 := fun h => hc0 (by rw [← hgq, h, zero_mul])
  have hginj : Function.Injective A.g.mulVecLin := fun x y hxy => by
    have h0 : A.g.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub]
      exact sub_eq_zero.mpr hxy
    exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hg0 h0)
  set large₂ := Λ.Ln.toAddSubgroup with hLg
  set X := (Ideal.span {(N : 𝓞 E)} • stdLat E n).toAddSubgroup with hX
  let L' := large₂.comap ι
  let X' := X.comap ι
  let Z' := (LinearMap.range A.g.mulVecLin).toAddSubgroup
  let Y' := (LinearMap.range (A.g * A.q).mulVecLin).toAddSubgroup
  have hmemX : ∀ v, v ∈ X ↔ ∃ s ∈ stdLat E n, (N : 𝓞 E) • s = v := fun v => by
    simp only [hX, Submodule.mem_toAddSubgroup, Submodule.ideal_span_singleton_smul]
    exact Submodule.mem_smul_pointwise_iff_exists _ _ _
  have hX' : ∀ b, b ∈ X' ↔ ∃ u, (N : 𝓞 E) • u = b := by
    intro b
    show incl E n b ∈ X ↔ _
    rw [hmemX]
    constructor
    · rintro ⟨s, hs, hsb⟩
      obtain ⟨u, rfl⟩ := (mem_std (E := E)).mp hs
      exact ⟨u, incl_inj (by rw [map_smul, hsb])⟩
    · rintro ⟨u, rfl⟩
      exact ⟨incl E n u, (mem_std (E := E)).mpr ⟨u, rfl⟩, (map_smul _ _ _).symm⟩
  have hXL : X'.relIndex L' = X.relIndex large₂ := by
    rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self]
    intro v hv
    have hv' : v ∈ Λ.La ⊓ stdLat E n := hv
    obtain ⟨u, rfl⟩ := (mem_std (E := E)).mp (Submodule.mem_inf.mp hv').2
    exact ⟨u, rfl⟩
  have hXL' : X' ≤ L' := fun b hb => hNL hb
  have hYX : Y' ≤ X' := by
    intro x hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
    refine (hX' _).mpr ⟨(A.k₁ : 𝓞 E) • u, ?_⟩
    rw [Matrix.mulVecLin_apply, A.gq, Matrix.smul_mulVec, Matrix.one_mulVec, smul_smul, Nat.cast_mul, mul_comm]
  have hYZ : Y' ≤ Z' := by
    intro x hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
    exact LinearMap.mem_range.mpr ⟨A.q.mulVec u, by rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]⟩
  have hZL : Z' ≤ L' := by
    intro x hx
    obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hx
    show incl E n (A.g.mulVec u) ∈ Λ.Ln
    rw [incl_mulVec]
    exact A.cols _ ((mem_std (E := E)).mpr ⟨u, rfl⟩)
  have hYL : Y' ≤ L' := hYX.trans hXL'
  have hYZval : Y'.relIndex Z' = (Algebra.norm ℤ A.q.det).natAbs := by
    have e1 : Y' = (LinearMap.range A.q.mulVecLin).toAddSubgroup.map
        (A.g.mulVecLin : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E)) := by
      show (LinearMap.range (A.g * A.q).mulVecLin).toAddSubgroup = _
      rw [Matrix.mulVecLin_mul, LinearMap.range_comp]
      rfl
    have e2 : Z' = (⊤ : Submodule (𝓞 E) (Fin n → 𝓞 E)).toAddSubgroup.map
        (A.g.mulVecLin : (Fin n → 𝓞 E) →+ (Fin n → 𝓞 E)) := by
      show (LinearMap.range A.g.mulVecLin).toAddSubgroup = _
      rw [LinearMap.range_eq_map]
      rfl
    rw [e1, e2, AddSubgroup.relIndex_map_map_of_injective _ _ hginj, Submodule.top_toAddSubgroup,
      AddSubgroup.relIndex_top_right]
    exact index_range_matrix A.q hq0
  have hYtop : Y'.index ≠ 0 := by
    rw [index_range_matrix (A.g * A.q) (by rw [Matrix.det_mul]; exact mul_ne_zero hg0 hq0)]
    exact Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr (by rw [Matrix.det_mul]; exact mul_ne_zero hg0 hq0))
  have e1 := AddSubgroup.relIndex_mul_relIndex Y' X' L' hYX hXL'
  have e2 := AddSubgroup.relIndex_mul_relIndex Y' Z' L' hYZ hZL
  have e3 := AddSubgroup.relIndex_mul_relIndex Y' L' ⊤ hYL le_top
  rw [AddSubgroup.relIndex_top_right, AddSubgroup.relIndex_top_right] at e3
  have h0 : Y'.relIndex L' ≠ 0 := fun h => hYtop (by rw [← e3, h, zero_mul])
  have h1 : Y'.relIndex X' * X'.relIndex L' ≠ 0 := by rw [e1]; exact h0
  have h2 : Y'.relIndex Z' * Z'.relIndex L' ≠ 0 := by rw [e2]; exact h0
  obtain ⟨hYX0, hXL0⟩ := mul_ne_zero_iff.mp h1
  obtain ⟨hYZ0, hZL0⟩ := mul_ne_zero_iff.mp h2
  have d1 : ¬ ℓ ∣ Y'.relIndex X' := by
    refine not_dvd_relIndex Y' X' A.k₁ ℓ hl A.cop₁ hYX0 fun b hb => ?_
    obtain ⟨u, rfl⟩ := (hX' b).mp hb
    refine LinearMap.mem_range.mpr ⟨u, ?_⟩
    rw [Matrix.mulVecLin_apply, A.gq, Matrix.smul_mulVec, Matrix.one_mulVec, ← Nat.cast_smul_eq_nsmul (𝓞 E),
      smul_smul, Nat.cast_mul]
  have d2 : ¬ ℓ ∣ Z'.relIndex L' := by
    refine not_dvd_relIndex Z' L' A.k₁ ℓ hl A.cop₁ hZL0 fun b hb => ?_
    obtain ⟨v, hv, hkv⟩ := A.spans _ hb
    obtain ⟨u, rfl⟩ := (mem_std (E := E)).mp hv
    refine LinearMap.mem_range.mpr ⟨u, incl_inj ?_⟩
    rw [Matrix.mulVecLin_apply, incl_mulVec, ← hkv, map_nsmul, Nat.cast_smul_eq_nsmul]
    rfl
  have key : (X'.relIndex L').factorization ℓ = (Y'.relIndex Z').factorization ℓ := by
    have a1 := congrArg (fun t => t.factorization ℓ) e1
    have a2 := congrArg (fun t => t.factorization ℓ) e2
    simp only [Nat.factorization_mul hYX0 hXL0, Nat.factorization_mul hYZ0 hZL0, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd d1, Nat.factorization_eq_zero_of_not_dvd d2, zero_add, add_zero] at a1 a2
    rw [a1, ← a2]
  rw [hYZval] at key
  refine ⟨?_, ?_⟩
  · show _ = ((X.relIndex large₂) ^ r).factorization ℓ
    rw [Nat.factorization_pow, Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply, ← hXL, key]
  · show (X.relIndex large₂) ^ r ≠ 0
    rw [← hXL]
    exact pow_ne_zero _ hXL0
end Idx

section Val
variable {R K Γ : Type} [CommRing R] [Field K] [Algebra R K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ)

def HasMax (I : Submodule R K) (x : Γ) : Prop := (∀ y ∈ I, w y ≤ x) ∧ ∃ y ∈ I, w y = x

variable {w}

theorem HasMax.unique {I : Submodule R K} {x y : Γ} (h : HasMax w I x) (h' : HasMax w I y) : x = y := by
  obtain ⟨a, ha, hax⟩ := h.2
  obtain ⟨b, hb, hby⟩ := h'.2
  exact le_antisymm (hax ▸ h'.1 a ha) (hby ▸ h.1 b hb)

theorem HasMax.mul {I J : Submodule R K} {x y : Γ} (h : HasMax w I x) (h' : HasMax w J y) :
    HasMax w (I * J) (x * y) := by
  refine ⟨fun z hz => ?_, ?_⟩
  · refine Submodule.mul_induction_on hz (fun a ha b hb => ?_) (fun a b ha hb => w.map_add_le ha hb)
    rw [map_mul]
    exact mul_le_mul' (h.1 a ha) (h'.1 b hb)
  · obtain ⟨a, ha, hax⟩ := h.2
    obtain ⟨b, hb, hby⟩ := h'.2
    exact ⟨a * b, Submodule.mul_mem_mul ha hb, by rw [map_mul, hax, hby]⟩

theorem hasMax_span (hw : ∀ r : R, w (algebraMap R K r) ≤ 1) {s : Set K} {x : Γ} (h : ∀ y ∈ s, w y ≤ x)
    (h' : ∃ y ∈ s, w y = x) : HasMax w (Submodule.span R s) x := by
  refine ⟨fun z hz => ?_, ?_⟩
  · induction hz using Submodule.span_induction with
    | mem y hy => exact h y hy
    | zero => simp
    | add a b _ _ ha hb => exact w.map_add_le ha hb
    | smul r a _ ha =>
      rw [Algebra.smul_def, map_mul]
      calc w (algebraMap R K r) * w a ≤ 1 * x := mul_le_mul' (hw r) ha
        _ = x := one_mul x
  · obtain ⟨y, hy, hyx⟩ := h'
    exact ⟨y, Submodule.subset_span hy, hyx⟩

theorem hasMax_one (hw : ∀ r : R, w (algebraMap R K r) ≤ 1) : HasMax w (1 : Submodule R K) 1 := by
  rw [Submodule.one_eq_span]
  refine hasMax_span hw (fun y hy => ?_) ⟨1, rfl, map_one w⟩
  rw [Set.mem_singleton_iff.mp hy, map_one]

theorem HasMax.pow (hw : ∀ r : R, w (algebraMap R K r) ≤ 1) {I : Submodule R K} {x : Γ} (h : HasMax w I x) (m : ℕ) :
    HasMax w (I ^ m) (x ^ m) := by
  induction m with
  | zero => simpa using hasMax_one hw
  | succ m ih => simpa [pow_succ] using ih.mul h

theorem hasMax_prod (hw : ∀ r : R, w (algebraMap R K r) ≤ 1) {ι : Type} (s : Finset ι) (I : ι → Submodule R K)
    (x : ι → Γ) (h : ∀ i, HasMax w (I i) (x i)) : HasMax w (∏ i ∈ s, I i) (∏ i ∈ s, x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasMax_one hw
  | insert i s hi ih => simpa [Finset.prod_insert hi] using (h i).mul ih
end Val

section Det
variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem det_cols {m : Matrix (Fin n) (Fin n) E} {a : E} {v u : Fin n → Fin n → E} (h : ∀ i, a • v i = m.mulVec (u i)) :
    a ^ n * Matrix.det (Matrix.of fun i j => v j i) = m.det * Matrix.det (Matrix.of fun i j => u j i) := by
  have hm : a • Matrix.of (fun i j => v j i) = m * Matrix.of (fun i j => u j i) := by
    ext i j
    have := congrFun (h j) i
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
  rw [← Matrix.det_mul, ← hm, Matrix.det_smul, Fintype.card_fin]

theorem det_std {u : Fin n → Fin n → E} (h : ∀ i, u i ∈ stdLat E n) :
    ∃ r : 𝓞 E, algebraMap (𝓞 E) E r = Matrix.det (Matrix.of fun i j => u j i) := by
  choose u' hu' using fun i => (mem_std (E := E) (n := n)).mp (h i)
  refine ⟨Matrix.det (Matrix.of fun i j => u' j i), ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [RingHom.mapMatrix_apply, ← hu', incl_apply]

theorem single_std (i : Fin n) : (Pi.single i 1 : Fin n → E) ∈ stdLat E n := by
  refine (mem_std (E := E)).mpr ⟨Pi.single i 1, funext fun j => ?_⟩
  rw [incl_apply]
  by_cases hj : j = i
  · subst hj; simp
  · simp [hj]

theorem det_single : Matrix.det (Matrix.of fun i j : Fin n => (Pi.single j 1 : Fin n → E) i) = 1 := by
  have : (Matrix.of fun i j : Fin n => (Pi.single j 1 : Fin n → E) i) = 1 := by
    ext i j
    simp [Pi.single_apply, Matrix.one_apply]
  rw [this, Matrix.det_one]

variable [IsCMField E] {Λ : GenLat E n} {N ℓ : ℕ} (A : Adapt Λ N ℓ)
  {Γ : Type} [LinearOrderedCommGroupWithZero Γ] (w : Valuation E Γ) (hw : ∀ r : 𝓞 E, w (algebraMap (𝓞 E) E r) ≤ 1)
include hw

theorem detSet_Ln (h1 : w (A.k₁ : E) = 1) :
    (∀ y ∈ detSet Λ.Ln, w y ≤ w (algebraMap (𝓞 E) E A.g.det)) ∧ algebraMap (𝓞 E) E A.g.det ∈ detSet Λ.Ln := by
  have hG : ∀ j, (fun i => algebraMap (𝓞 E) E (A.g i j)) ∈ Λ.Ln := by
    intro j
    have := A.cols _ (single_std (E := E) j)
    convert this using 1
    funext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨?_, ⟨fun j i => algebraMap (𝓞 E) E (A.g i j), hG, ?_⟩⟩
  · rintro y ⟨v, hv, rfl⟩
    choose u hu hku using fun i => A.spans (v i) (hv i)
    have hc := det_cols (m := A.g.map (algebraMap (𝓞 E) E)) (a := (A.k₁ : E)) (v := v) (u := u) hku
    obtain ⟨r, hr⟩ := det_std (E := E) hu
    have hwr : w (Matrix.det (Matrix.of fun i j => u j i)) ≤ 1 := by
      rw [← hr]
      exact hw r
    have key := congrArg w hc
    rw [map_mul, map_mul, map_pow, h1, one_pow, one_mul] at key
    rw [key, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact le_trans (mul_le_mul' le_rfl hwr) (le_of_eq (mul_one _))
  · rw [RingHom.map_det]
    rfl

theorem detSet_La (h1 : w (A.k : E) = 1) :
    w A.ga.det ≠ 0 ∧ (∀ y ∈ detSet Λ.La, w y ≤ (w A.ga.det)⁻¹) ∧ ∃ y ∈ detSet Λ.La, w y = (w A.ga.det)⁻¹ := by
  have hD : A.ga.det ≠ 0 := by
    have h1 : (Matrix.of fun i b => IsCMField.complexConj E (A.ga b i)) * A.ga = 1 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      rw [A.unitary i j, Matrix.one_apply]
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hwD : w A.ga.det ≠ 0 := (Valuation.ne_zero_iff w).mpr hD
  refine ⟨hwD, ?_, ?_⟩
  · rintro y ⟨v, hv, rfl⟩
    have hu : ∀ i, A.ga.mulVec ((A.k : E) • v i) ∈ stdLat E n := fun i => by
      rw [Matrix.mulVec_smul]
      exact A.into (v i) (hv i)
    have hc := det_cols (m := A.ga) (a := (1 : E)) (v := fun i => A.ga.mulVec ((A.k : E) • v i))
      (u := fun i => (A.k : E) • v i) (fun i => one_smul _ _)
    obtain ⟨r, hr⟩ := det_std (E := E) hu
    have hsm : Matrix.det (Matrix.of fun i j => ((A.k : E) • v j) i) =
        (A.k : E) ^ n * Matrix.det (Matrix.of fun i j => v j i) := by
      have : (Matrix.of fun i j => ((A.k : E) • v j) i) = (A.k : E) • Matrix.of fun i j => v j i := by
        ext
        simp
      rw [this, Matrix.det_smul, Fintype.card_fin]
    rw [hsm, one_pow, one_mul, ← hr] at hc
    have key := congrArg w hc
    rw [map_mul, map_mul, map_pow, h1, one_pow, one_mul] at key
    have hb := hw r
    rw [key] at hb
    calc w _ = (w A.ga.det)⁻¹ * (w A.ga.det * w (Matrix.det (Matrix.of fun i j => v j i))) := by
          rw [← mul_assoc, inv_mul_cancel₀ hwD, one_mul]
      _ ≤ (w A.ga.det)⁻¹ * 1 := mul_le_mul' le_rfl hb
      _ = _ := mul_one _
  · choose u hu hku using fun j => A.onto _ (single_std (E := E) (n := n) j)
    refine ⟨_, ⟨u, hu, rfl⟩, ?_⟩
    have hc := det_cols (m := A.ga) (a := (A.k : E)) (v := fun j => (Pi.single j 1 : Fin n → E)) (u := u) hku
    rw [det_single, mul_one] at hc
    have key := congrArg w hc
    rw [map_pow, h1, one_pow, map_mul] at key
    exact eq_inv_of_mul_eq_one_right key.symm

omit hw in
theorem det_p (hN : N ≠ 0) : algebraMap (𝓞 E) E A.p.det * (A.k₁ : E) ^ n =
    (A.k : E) ^ n * A.ga.det * algebraMap (𝓞 E) E A.g.det := by
  have hD : A.ga.det ≠ 0 := by
    have h1 : (Matrix.of fun i b => IsCMField.complexConj E (A.ga b i)) * A.ga = 1 := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.of_apply]
      rw [A.unitary i j, Matrix.one_apply]
    intro h0
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hP : algebraMap (𝓞 E) E A.p.det * algebraMap (𝓞 E) E A.q.det = ((A.k * N : ℕ) : E) ^ n * A.ga.det := by
    have := congrArg Matrix.det A.prod
    rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul,
      map_mul] at this
    exact this
  have hG : algebraMap (𝓞 E) E A.g.det * algebraMap (𝓞 E) E A.q.det = ((A.k₁ * N : ℕ) : E) ^ n := by
    have := congrArg (fun M => algebraMap (𝓞 E) E M.det) A.gq
    simp only [Matrix.det_mul, map_mul, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one, map_pow,
      map_natCast] at this
    exact_mod_cast this
  have hk : (A.k : E) ≠ 0 := by exact_mod_cast A.odd.pos.ne'
  have hQ : algebraMap (𝓞 E) E A.q.det ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hP
    refine mul_ne_zero (pow_ne_zero _ ?_) hD hP.symm
    push_cast
    exact mul_ne_zero hk (by exact_mod_cast hN)
  apply mul_right_cancel₀ hQ
  push_cast at hP hG
  linear_combination (A.k₁ : E) ^ n * hP - (A.k : E) ^ n * A.ga.det * hG
end Det

theorem valV_integral (T : CDVR) {x : T.Fr} (hx : IsIntegral ℤ x) : valV T.V x ≤ 1 := by
  unfold valV
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp (hx.tower_top (A := T.V))
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ y

theorem valV_nat (T : CDVR) {k ℓ : ℕ} (hk : Nat.Coprime k ℓ) (hl : ¬ IsUnit (ℓ : T.V)) : valV T.V (k : T.Fr) = 1 := by
  unfold valV
  have hk1 : (k : T.V) ∉ IsLocalRing.maximalIdeal T.V := by
    intro h1
    have h2 : (ℓ : T.V) ∈ IsLocalRing.maximalIdeal T.V := (IsLocalRing.mem_maximalIdeal _).mpr hl
    have hg := Nat.gcd_eq_gcd_ab k ℓ
    rw [hk.gcd_eq_one] at hg
    have h3 := congrArg (Int.cast : ℤ → T.V) hg
    push_cast at h3
    have h4 : (1 : T.V) ∈ IsLocalRing.maximalIdeal T.V := by
      rw [h3]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ h1) (Ideal.mul_mem_right _ _ h2)
    exact (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top ((Ideal.eq_top_iff_one _).mpr h4)
  rw [← map_natCast (algebraMap T.V T.Fr) k]
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (v := IsDiscreteValuationRing.maximalIdeal T.V)).mpr hk1

theorem latidx (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (c : Coeff l)
    (n : ℕ) (Λ : GenLat E n) (N M ℓ : ℕ) (_ : Λ.Unimod) (hL : Λ.LevOK N M) (hl : ℓ.Prime) (A : Adapt Λ N ℓ) :
    ((Algebra.norm ℤ A.q.det).natAbs ^ (Dw.p + Dw.q)).factorization ℓ = (Λ.mIdx N (Dw.p + Dw.q)).factorization ℓ ∧
    Λ.mIdx N (Dw.p + Dw.q) ≠ 0 ∧ ∀ (β : c.F), β ≠ 0 → BetaIs (Dw := Dw) c Λ β → ∀ (T : CDVR) (io : c.F →+* T.Fr),
    ¬ IsUnit (ℓ : T.V) → vV T.V (io (∏ τ : E →+* ℂ, embK c τ A.p.det ^ Dw.mult τ)) = vV T.V (io β) ∧ A.p.det ≠ 0 := by
  obtain ⟨hi1, hi2⟩ := index_part Λ N M ℓ hL hl A (Dw.p + Dw.q)
  refine ⟨hi1, hi2, fun β hβ hB T io hl' => ?_⟩
  have hN : N ≠ 0 := hL.1.pos.ne'
  let w' := (valV T.V).comap io
  let wt : (E →+* ℂ) → Valuation E _ := fun τ => (valV T.V).comap (io.comp (embF c τ))
  have hw' : ∀ r : 𝓞 c.F, w' (algebraMap (𝓞 c.F) c.F r) ≤ 1 := fun r =>
    valV_integral T ((RingOfIntegers.isIntegral_coe r).map_of_comp_eq (RingHom.id ℤ) io (RingHom.ext_int _ _))
  have hwt : ∀ τ, ∀ r : 𝓞 E, wt τ (algebraMap (𝓞 E) E r) ≤ 1 := fun τ r =>
    valV_integral T ((RingOfIntegers.isIntegral_coe r).map_of_comp_eq (RingHom.id ℤ) (io.comp (embF c τ))
      (RingHom.ext_int _ _))
  have hnat : ∀ τ, ∀ {k : ℕ}, Nat.Coprime k ℓ → wt τ (k : E) = 1 := fun τ k hk => by
    show valV T.V (io (embF c τ (k : E))) = 1
    rw [map_natCast, map_natCast]
    exact valV_nat T hk hl'
  have hLa : ∀ τ, HasMax w' (Submodule.span (𝓞 c.F) (embF c τ '' detSet Λ.La)) (wt τ A.ga.det)⁻¹ := by
    intro τ
    obtain ⟨_, hle, ⟨y, hy, hyeq⟩⟩ := detSet_La A (wt τ) (hwt τ) (hnat τ A.cop)
    refine hasMax_span hw' ?_ ⟨embF c τ y, ⟨y, hy, rfl⟩, hyeq⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hle d hd
  have hLn : ∀ τ, HasMax w' (Submodule.span (𝓞 c.F) (embF c τ '' detSet Λ.Ln))
      (wt τ (algebraMap (𝓞 E) E A.g.det)) := by
    intro τ
    obtain ⟨hle, hmem⟩ := detSet_Ln A (wt τ) (hwt τ) (hnat τ A.cop₁)
    refine hasMax_span hw' ?_ ⟨embF c τ _, ⟨_, hmem, rfl⟩, rfl⟩
    rintro _ ⟨d, hd, rfl⟩
    exact hle d hd
  have hbeta : HasMax w' (Submodule.span (𝓞 c.F) {β}) (w' β) :=
    hasMax_span hw' (fun y hy => by rw [Set.mem_singleton_iff.mp hy]) ⟨β, rfl, rfl⟩
  have hL1 := hbeta.mul (hasMax_prod hw' Finset.univ _ _ fun τ => (hLa τ).pow hw' (Dw.mult τ))
  have hR1 := hasMax_prod hw' Finset.univ _ _ fun τ => (hLn τ).pow hw' (Dw.mult τ)
  unfold BetaIs idealAt at hB
  rw [hB] at hL1
  have heq := hL1.unique hR1
  have hdet := det_p A hN
  have hpt : ∀ τ, wt τ (algebraMap (𝓞 E) E A.p.det) =
      wt τ A.ga.det * wt τ (algebraMap (𝓞 E) E A.g.det) := by
    intro τ
    have := congrArg (wt τ) hdet
    rw [map_mul, map_pow, hnat τ A.cop₁, one_pow, mul_one, map_mul, map_mul, map_pow, hnat τ A.cop, one_pow,
      one_mul] at this
    exact this
  have hD0 : ∀ τ, wt τ A.ga.det ≠ 0 := fun τ => (detSet_La A (wt τ) (hwt τ) (hnat τ A.cop)).1
  have hinv : ∏ τ, ((wt τ A.ga.det)⁻¹) ^ (Dw.mult τ) = (∏ τ, (wt τ A.ga.det) ^ (Dw.mult τ))⁻¹ := by
    rw [← Finset.prod_inv_distrib]
    simp_rw [inv_pow]
  rw [hinv, mul_inv_eq_iff_eq_mul₀ (Finset.prod_ne_zero_iff.mpr fun τ _ => pow_ne_zero _ (hD0 τ))] at heq
  have key : valV T.V (io (∏ τ, embK c τ A.p.det ^ Dw.mult τ)) = valV T.V (io β) := by
    rw [map_prod, map_prod]
    simp_rw [map_pow]
    change ∏ τ, (wt τ (algebraMap (𝓞 E) E A.p.det)) ^ (Dw.mult τ) = w' β
    simp_rw [hpt, mul_pow]
    rw [Finset.prod_mul_distrib, heq, mul_comm]
  refine ⟨?_, ?_⟩
  · unfold vV
    rw [key]
  · intro h0
    have hD : A.ga.det ≠ 0 := by
      have h1 : (Matrix.of fun i b => IsCMField.complexConj E (A.ga b i)) * A.ga = 1 := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.of_apply]
        rw [A.unitary i j, Matrix.one_apply]
      intro h0
      have := congrArg Matrix.det h1
      rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
      exact zero_ne_one this
    have := congrArg Matrix.det A.prod
    rw [Matrix.det_smul, Fintype.card_fin, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Matrix.det_mul, map_mul,
      h0, map_zero, zero_mul] at this
    refine mul_ne_zero (pow_ne_zero _ ?_) hD this.symm
    have hk : (A.k : E) ≠ 0 := by exact_mod_cast A.odd.pos.ne'
    push_cast
    exact mul_ne_zero hk (by exact_mod_cast hN)

end GlobalTheory.LatticeIndex
