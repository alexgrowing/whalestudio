import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IntegerApproximationCountHolds

open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

namespace BoundedBasis

section Algebra

theorem exists_generators_mod_smul {R : Type*} [CommRing R] [IsDedekindDomain R] {a : R}
    (ha : a ≠ 0) (r : ℕ) : ∀ (M : Type) [AddCommGroup M] [Module R M]
      (φ : M →ₗ[R] (Fin r → R)), Function.Injective φ →
      ∃ x : Fin r → M, ∀ m : M, ∃ (c : Fin r → R) (m' : M), m = ∑ i, c i • x i + a • m' := by
  induction r with
  | zero =>
    intro M _ _ φ hφ
    refine ⟨fun _ => 0, fun m => ⟨fun _ => 0, 0, ?_⟩⟩
    have : m = 0 := hφ (Subsingleton.elim _ _)
    simp [this]
  | succ r ih =>
    intro M _ _ φ hφ
    let π : M →ₗ[R] R := (LinearMap.proj 0).comp φ
    have hI : ∃ y : M, ∀ m : M, ∃ (c : R) (m' : M), π m = c * π y + a * π m' := by
      by_cases h0 : ∀ m, π m = 0
      · exact ⟨0, fun m => ⟨0, 0, by simp [h0 m]⟩⟩
      · push Not at h0
        obtain ⟨z, hz⟩ := h0
        obtain ⟨y, hy⟩ := IsDedekindDomain.exists_eq_span_pair (I := LinearMap.range π)
          (x := a * π z) ⟨a • z, by simp⟩ (mul_ne_zero ha hz)
        obtain ⟨y', rfl⟩ : y ∈ (LinearMap.range π : Ideal R) := by
          rw [hy]; exact Ideal.subset_span (by simp)
        refine ⟨y', fun m => ?_⟩
        have hm : π m ∈ (LinearMap.range π : Ideal R) := ⟨m, rfl⟩
        rw [hy, Ideal.mem_span_pair] at hm
        obtain ⟨s, t, hst⟩ := hm
        exact ⟨t, s • z, by rw [← hst, map_smul, smul_eq_mul]; ring⟩
    obtain ⟨y, hy⟩ := hI
    let φ' : LinearMap.ker π →ₗ[R] (Fin r → R) :=
      LinearMap.pi fun i => (LinearMap.proj i.succ).comp (φ.comp (LinearMap.ker π).subtype)
    have hφ' : Function.Injective φ' := by
      rw [injective_iff_map_eq_zero]
      intro m hm
      refine Subtype.ext (hφ ?_)
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rw [Submodule.coe_zero, map_zero]
        exact m.2
      · simpa [φ'] using congrFun hm i
    obtain ⟨x, hx⟩ := ih (LinearMap.ker π) φ' hφ'
    refine ⟨Fin.cons y fun i => (x i : M), fun m => ?_⟩
    obtain ⟨c, m₁, h⟩ := hy m
    obtain ⟨d, m₂, h₂⟩ := hx ⟨m - c • y - a • m₁, by
      rw [LinearMap.mem_ker, map_sub, map_sub, map_smul, map_smul, h]; simp⟩
    refine ⟨Fin.cons c d, m₁ + (m₂ : M), ?_⟩
    have h₃ := congrArg Subtype.val h₂
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul] at h₃
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_add]
    rw [sub_sub, sub_eq_iff_eq_add] at h₃
    rw [h₃]
    abel

theorem exists_finset_representatives {α β : Type*} [Finite β] (S : Set α) (f : S → β) :
    ∃ V : Finset S, V.card ≤ Nat.card β ∧ ∀ s : S, ∃ t ∈ V, f t = f s := by
  classical
  have := Fintype.ofFinite (Set.range f)
  refine ⟨Finset.univ.image fun b : Set.range f => b.2.choose, ?_, fun s => ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective _ Subtype.val_injective
  · exact ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨f s, s, rfl⟩),
      (⟨s, rfl⟩ : f s ∈ Set.range f).choose_spec⟩

variable {E : Type} [Field E] [NumberField E]

theorem card_quotient_range_vecMulLinear {r : ℕ} (N : Matrix (Fin r) (Fin r) (𝓞 E))
    (hN : N.det ≠ 0) :
    Nat.card ((Fin r → 𝓞 E) ⧸ LinearMap.range N.vecMulLinear) =
      (Algebra.norm ℤ N.det).natAbs := by
  have hinj : Function.Injective N.vecMulLinear := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact Matrix.eq_zero_of_vecMul_eq_zero hN hx
  let P : Submodule ℤ (Fin r → 𝓞 E) := (LinearMap.range N.vecMulLinear).restrictScalars ℤ
  let e : (Fin r → 𝓞 E) ≃+ P := (LinearEquiv.ofInjective _ hinj).toAddEquiv
  have key := Submodule.natAbs_det_equiv P e
  have hcomp : P.subtype ∘ₗ AddMonoidHom.toIntLinearMap (e : (Fin r → 𝓞 E) →+ P) =
      (Matrix.toLin' Nᵀ).restrictScalars ℤ :=
    LinearMap.ext fun x => by
      change x ᵥ* N = Nᵀ *ᵥ x
      rw [Matrix.mulVec_transpose]
  rw [hcomp, LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_transpose] at key
  rw [key]
  rfl

theorem natAbs_norm_le_pow {x : 𝓞 E} {a : ℝ} (h : ∀ σ : E →+* ℂ, ‖σ (x : E)‖ ≤ a) :
    ((Algebra.norm ℤ x).natAbs : ℝ) ≤ a ^ finrank ℚ E := by
  have h3 := congrArg norm (Algebra.norm_eq_prod_embeddings ℚ ℂ (x : E))
  have h4 : ∏ σ : E →ₐ[ℚ] ℂ, ‖σ (x : E)‖ ≤ a ^ finrank ℚ E := by
    rw [← AlgHom.card ℚ E ℂ, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun σ _ => h σ.toRingHom
  rw [norm_prod, ← Algebra.coe_norm_int] at h3
  refine le_trans (le_of_eq ?_) (h3 ▸ h4)
  simp [Nat.cast_natAbs]

theorem norm_det_le_pow {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ i k, ‖M i k‖ ≤ b) : ‖M.det‖ ≤ (r * b) ^ r := by
  have h1 := Matrix.det_le (A := M) (abv := NormedField.toAbsoluteValue ℂ) (x := b) h
  rw [Fintype.card_fin, nsmul_eq_mul] at h1
  refine le_trans h1 ?_
  rw [mul_pow]
  gcongr
  exact_mod_cast Nat.factorial_le_pow r

theorem finrank_eq_two_mul_fdeg [IsCMField E] : finrank ℚ E = 2 * fdeg E := by
  have h := IsTotallyComplex.finrank E
  unfold fdeg
  omega

end Algebra

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_add_left (G : Matrix (Fin r) (Fin r) E) (x x' y : Fin r → E) :
    herm G (x + x') y = herm G x y + herm G x' y := by
  simp [herm, add_mul, Finset.sum_add_distrib]

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : E) (x y : Fin r → E) :
    herm G (c • x) y = c * herm G x y := by
  simp [herm, Finset.mul_sum, mul_assoc]

theorem herm_eq_dotProduct (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = (x ᵥ* G) ⬝ᵥ fun b => cc (y b) := by
  simp only [herm, vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm

noncomputable def gramOf (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) :
    Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i k => herm G (v i) (v k)

theorem gramOf_eq (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) :
    gramOf G v = Matrix.of v * G * ((Matrix.of v).map (IsCMField.complexConj E).toRingHom)ᵀ := by
  ext i k
  simp only [gramOf, herm, Matrix.of_apply, Matrix.mul_apply, Finset.sum_mul, transpose_apply,
    map_apply]
  exact Finset.sum_comm

omit [NumberField E] [IsCMField E] in
theorem det_of_ne_zero {v : Fin r → Fin r → E} (hv : LinearIndependent E v) :
    (Matrix.of v).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1
    ((Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of v)).1 hv)).ne_zero

theorem det_gramOf_ne_zero {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    {v : Fin r → Fin r → E} (hv : LinearIndependent E v) : (gramOf G v).det ≠ 0 := by
  rw [gramOf_eq, det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  refine mul_ne_zero (mul_ne_zero (det_of_ne_zero hv) hG) ?_
  exact (map_ne_zero _).2 (det_of_ne_zero hv)

omit [NumberField E] [IsCMField E] in
theorem vecMul_of (c : Fin r → E) (v : Fin r → Fin r → E) :
    c ᵥ* Matrix.of v = ∑ i, c i • v i := by
  ext k
  simp [vecMul, dotProduct, Finset.sum_apply]

theorem herm_vecMul_left (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (c : Fin r → E)
    (k : Fin r) : herm G (c ᵥ* Matrix.of v) (v k) = (c ᵥ* gramOf G v) k := by
  rw [gramOf_eq, ← vecMul_vecMul, ← vecMul_vecMul, herm_eq_dotProduct]
  rfl

theorem herm_vecMul (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (c d : Fin r → E) :
    herm G (c ᵥ* Matrix.of v) (d ᵥ* Matrix.of v) = herm (gramOf G v) c d := by
  rw [herm_eq_dotProduct, herm_eq_dotProduct, gramOf_eq, ← vecMul_vecMul, ← vecMul_vecMul,
    ← dotProduct_mulVec _ _ᵀ, mulVec_transpose]
  congr 1
  ext b
  simp [cc, vecMul, dotProduct]

omit [NumberField E] [IsCMField E] in
theorem exists_vecMul_eq {v : Fin r → Fin r → E} (hv : LinearIndependent E v) (x : Fin r → E) :
    ∃ c, x = c ᵥ* Matrix.of v :=
  ⟨x ᵥ* (Matrix.of v)⁻¹, by
    rw [vecMul_vecMul, nonsing_inv_mul _ (det_of_ne_zero hv).isUnit, vecMul_one]⟩

omit [NumberField E] [IsCMField E] in

theorem exists_gl_mulVec {v w : Fin r → Fin r → E} (hv : LinearIndependent E v)
    (hw : LinearIndependent E w) : ∃ γ : GL (Fin r) E, ∀ c : Fin r → E,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ (c ᵥ* Matrix.of w) = c ᵥ* Matrix.of v := by
  have hw' : IsUnit (Matrix.of w)ᵀ.det := by
    rw [det_transpose]; exact (det_of_ne_zero hw).isUnit
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero ((Matrix.of v)ᵀ * ((Matrix.of w)ᵀ)⁻¹) ?_,
    fun c => ?_⟩
  · rw [det_mul, det_transpose]
    exact mul_ne_zero (det_of_ne_zero hv) (isUnit_nonsing_inv_det _ hw').ne_zero
  · change ((Matrix.of v)ᵀ * ((Matrix.of w)ᵀ)⁻¹) *ᵥ _ = _
    rw [← mulVec_transpose, mulVec_mulVec, Matrix.mul_assoc, nonsing_inv_mul _ hw',
      Matrix.mul_one, mulVec_transpose]

end Herm

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : DataX E r)

noncomputable def pairing (v : Fin r → Fin r → E) (hv : ∀ i, v i ∈ X.L') :
    X.Λ →ₗ[𝓞 E] (Fin r → 𝓞 E) where
  toFun x k := ⟨herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k),
    X.L'_int _ (X.NA_sub _ x.2) _ (hv k)⟩
  map_add' x y := by
    funext k
    refine RingOfIntegers.ext ?_
    change herm X.Gm ((X.NA : E) • ((x : Fin r → E) + y)) (v k) =
      herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k) +
        herm X.Gm ((X.NA : E) • (y : Fin r → E)) (v k)
    rw [smul_add, herm_add_left]
  map_smul' c x := by
    funext k
    refine RingOfIntegers.ext ?_
    change herm X.Gm ((X.NA : E) • ((c : E) • (x : Fin r → E))) (v k) =
      (c : E) * herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k)
    rw [smul_comm, herm_smul_left]

theorem coe_pairing (v : Fin r → Fin r → E) (hv : ∀ i, v i ∈ X.L') (x : X.Λ) (c : Fin r → E)
    (hc : (x : Fin r → E) = c ᵥ* Matrix.of v) (k : Fin r) :
    ((pairing X v hv x k : 𝓞 E) : E) = (((X.NA : E) • c) ᵥ* gramOf X.Gm v) k := by
  change herm X.Gm ((X.NA : E) • (x : Fin r → E)) (v k) = _
  rw [hc, ← smul_vecMul, herm_vecMul_left]

theorem pairing_injective {v : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L')
    (hi : LinearIndependent E v) : Function.Injective (pairing X v hv) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨c, hc⟩ := exists_vecMul_eq hi x
  have h : ((X.NA : E) • c) ᵥ* gramOf X.Gm v = 0 := by
    funext k
    rw [← coe_pairing X v hv x c hc k, hx]
    simp
  have h1 := Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero X.Gm_det hi) h
  have h2 : c = 0 := (smul_eq_zero.1 h1).resolve_left (by exact_mod_cast X.NA_pos.ne')
  refine Subtype.ext ?_
  rw [hc, h2, zero_vecMul]
  rfl

theorem smul_vecMul_mem {v : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L') (o : Fin r → 𝓞 E) :
    (X.NC : E) • ((fun i => (o i : E)) ᵥ* Matrix.of v) ∈ X.Λ := by
  refine X.NC_sub _ ?_
  rw [vecMul_of]
  exact Submodule.sum_mem _ fun i _ => X.L'.smul_mem (o i) (hv i)

theorem exists_mem_of_pairing {v w : Fin r → Fin r → E} (hv : ∀ i, v i ∈ X.L')
    (hw : ∀ i, w i ∈ X.L') (hvi : LinearIndependent E v) (hwi : LinearIndependent E w)
    (A : Matrix (Fin r) (Fin r) (𝓞 E)) (hvA : gramOf X.Gm v = A.map (algebraMap (𝓞 E) E))
    (hwA : gramOf X.Gm w = A.map (algebraMap (𝓞 E) E))
    (h : ∀ x : X.Λ, pairing X w hw x - pairing X v hv x ∈
      LinearMap.range (((X.NA * X.NC * X.g : ℕ) : 𝓞 E) • A).vecMulLinear) :
    ∃ γ ∈ X.Γ, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i := by
  obtain ⟨γ, hγ⟩ := exists_gl_mulVec hvi hwi
  have key : ∀ x ∈ X.Λ, ∀ c d : Fin r → E, x = c ᵥ* Matrix.of v → x = d ᵥ* Matrix.of w →
      ∃ o : Fin r → 𝓞 E, d = c + (X.g : E) • (X.NC : E) • fun i => (o i : E) := by
    intro x hx c d hc hd
    obtain ⟨o, ho⟩ := h ⟨x, hx⟩
    refine ⟨o, ?_⟩
    have h1 : ((X.NA : E) • (d - (c + (X.g : E) • (X.NC : E) • fun i => (o i : E)))) ᵥ*
        gramOf X.Gm v = 0 := by
      funext k
      have h2 := congrArg (algebraMap (𝓞 E) E) (congrFun ho k)
      have h3 := coe_pairing X v hv ⟨x, hx⟩ c hc k
      have h4 := coe_pairing X w hw ⟨x, hx⟩ d hd k
      rw [hwA, ← hvA] at h4
      rw [Pi.sub_apply, map_sub] at h2
      change _ = ((pairing X w hw ⟨x, hx⟩ k : 𝓞 E) : E) - (pairing X v hv ⟨x, hx⟩ k : 𝓞 E) at h2
      rw [h3, h4] at h2
      rw [smul_sub, smul_add, sub_vecMul, add_vecMul, Pi.sub_apply, Pi.add_apply, ← sub_sub, ← h2,
        hvA]
      simp only [vecMulLinear_apply, vecMul, dotProduct, map_sum, Matrix.smul_apply, smul_eq_mul,
        map_mul, map_natCast, Pi.smul_apply, map_apply, Pi.zero_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      push_cast
      ring
    have h5 := Matrix.eq_zero_of_vecMul_eq_zero (det_gramOf_ne_zero X.Gm_det hvi) h1
    exact sub_eq_zero.1 ((smul_eq_zero.1 h5).resolve_left (by exact_mod_cast X.NA_pos.ne'))
  have hg : ∀ y ∈ X.Λ, (X.g : E) • y ∈ X.Λ := fun y hy => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
  have hcong : ∀ x ∈ X.Λ, ∃ y ∈ X.Λ,
      (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = (X.g : E) • y := by
    intro x hx
    obtain ⟨c, hc⟩ := exists_vecMul_eq hvi x
    obtain ⟨d, hd⟩ := exists_vecMul_eq hwi x
    obtain ⟨o, ho⟩ := key x hx c d hc hd
    refine ⟨_, smul_vecMul_mem X hv o, ?_⟩
    have : (γ : Matrix (Fin r) (Fin r) E) *ᵥ x = d ᵥ* Matrix.of v := by rw [hd, hγ]
    rw [this, ho, add_vecMul, ← hc, smul_vecMul, smul_vecMul, add_sub_cancel_left]
  refine ⟨γ, X.cong γ ⟨fun x y => ?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩ hcong, fun i => ?_⟩
  · obtain ⟨c, rfl⟩ := exists_vecMul_eq hwi x
    obtain ⟨d, rfl⟩ := exists_vecMul_eq hwi y
    rw [hγ, hγ, herm_vecMul, herm_vecMul, hvA, hwA]
  · obtain ⟨y, hy, h⟩ := hcong x hx
    rw [sub_eq_iff_eq_add.1 h]
    exact add_mem (hg y hy) hx
  · obtain ⟨c, rfl⟩ := exists_vecMul_eq hwi x
    obtain ⟨d, hd⟩ := exists_vecMul_eq hwi ((γ : Matrix (Fin r) (Fin r) E) *ᵥ (c ᵥ* Matrix.of w))
    obtain ⟨o, ho⟩ := key _ hx c d (hγ c) hd
    rw [hd, ho, add_vecMul, smul_vecMul, smul_vecMul] at hx
    exact (Submodule.add_mem_iff_left _ (hg _ (smul_vecMul_mem X hw o))).1 hx
  · have := hγ (Pi.single i 1)
    rw [single_one_vecMul, single_one_vecMul] at this
    exact this.symm

end Lattice

end BoundedBasis

open BoundedBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def IsBoundedBasis (X : DataX E r) (B : ℝ) (v : Fin r → Fin r → E) : Prop :=
  (∀ i, v i ∈ X.L') ∧ LinearIndependent E v ∧
    ∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B

theorem exists_finset_boundedBasis_of_gram (X : DataX E r) {B : ℝ} (hB : 0 ≤ B)
    (A : Matrix (Fin r) (Fin r) (𝓞 E)) :
    ∃ V : Finset (Fin r → Fin r → E), (∀ v ∈ V, IsBoundedBasis X B v) ∧
      (∀ v, IsBoundedBasis X B v → gramOf X.Gm v = A.map (algebraMap (𝓞 E) E) →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i) ∧
      (V.card : ℝ) ≤ ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by
  classical
  let S : Set (Fin r → Fin r → E) :=
    {v | IsBoundedBasis X B v ∧ gramOf X.Gm v = A.map (algebraMap (𝓞 E) E)}
  rcases S.eq_empty_or_nonempty with hS | ⟨u, hu, huA⟩
  · refine ⟨∅, by simp, fun v hv hA => ?_, by simp; positivity⟩
    exact absurd (show v ∈ S from ⟨hv, hA⟩) (by simp [hS])
  set n : ℕ := X.NA * X.NC * X.g with hn
  have hn0 : n ≠ 0 := (Nat.mul_pos (Nat.mul_pos X.NA_pos X.NC_pos) X.g_pos).ne'
  set N : Matrix (Fin r) (Fin r) (𝓞 E) := (n : 𝓞 E) • A with hN
  have hA : A.det ≠ 0 := by
    intro h0
    apply det_gramOf_ne_zero X.Gm_det hu.2.1
    rw [huA, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hN0 : N.det ≠ 0 := by
    rw [hN, det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hn0)) hA
  have hcard := card_quotient_range_vecMulLinear N hN0
  have hbound : ((Algebra.norm ℤ N.det).natAbs : ℝ) ≤ ((r * (n * B)) ^ r) ^ finrank ℚ E := by
    refine natAbs_norm_le_pow fun σ => ?_
    have h1 : σ ((N.det : 𝓞 E) : E) = (N.map (σ.comp (algebraMap (𝓞 E) E))).det :=
      RingHom.map_det (σ.comp (algebraMap (𝓞 E) E)) N
    rw [h1]
    refine norm_det_le_pow _ (by positivity) fun i k => ?_
    have h2 : algebraMap (𝓞 E) E (A i k) = herm X.Gm (u i) (u k) :=
      (congrFun (congrFun huA i) k).symm
    simp only [hN, map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_natCast,
      RingHom.comp_apply, h2, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hu.2.2 σ i k) (by positivity)
  have : Finite ((Fin r → 𝓞 E) ⧸ LinearMap.range N.vecMulLinear) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard, Int.natAbs_ne_zero, Algebra.norm_ne_zero_iff]
    exact hN0
  obtain ⟨x, hx⟩ := exists_generators_mod_smul hN0 r X.Λ _ (pairing_injective X hu.1 hu.2.1)
  obtain ⟨V, hV, hV'⟩ := exists_finset_representatives S fun v j =>
    (LinearMap.range N.vecMulLinear).mkQ (pairing X v.1 v.2.1.1 (x j))
  refine ⟨V.image Subtype.val, ?_, fun v hv hvA => ?_, ?_⟩
  · intro v hv
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.1 hv
    exact w.2.1
  · obtain ⟨w, hwV, hw⟩ := hV' ⟨v, hv, hvA⟩
    obtain ⟨γ, hγ, h⟩ := exists_mem_of_pairing X hv.1 w.2.1.1 hv.2.1 w.2.1.2.1 A hvA w.2.2
      fun m => by
        obtain ⟨c, m', rfl⟩ := hx m
        rw [map_add, map_add, add_sub_add_comm, map_sum, map_sum, ← Finset.sum_sub_distrib,
          map_smul, map_smul, ← smul_sub]
        refine add_mem (Submodule.sum_mem _ fun j _ => ?_) ⟨(pairing X w.1 w.2.1.1 m' -
          pairing X v hv.1 m') ᵥ* N.adjugate, ?_⟩
        · rw [map_smul, map_smul, ← smul_sub]
          exact Submodule.smul_mem _ _ ((Submodule.Quotient.eq _).1 (congrFun hw j))
        · rw [vecMulLinear_apply, vecMul_vecMul, adjugate_mul, vecMul_smul, vecMul_one]
    exact ⟨γ, hγ, w.1, Finset.mem_image_of_mem _ hwV, h⟩
  · rw [Nat.card_fun, hcard, Nat.card_eq_fintype_card, Fintype.card_fin] at hV
    calc ((V.image Subtype.val).card : ℝ) ≤ ((Algebra.norm ℤ N.det).natAbs : ℝ) ^ r := by
          exact_mod_cast Finset.card_image_le.trans hV
      _ ≤ (((r * (n * B)) ^ r) ^ finrank ℚ E) ^ r := by gcongr
      _ = _ := by
          rw [← pow_mul, ← pow_mul, finrank_eq_two_mul_fdeg, hn]
          push_cast
          congr 1 <;> ring

theorem exists_finset_boundedBasis (X : DataX E r) {B : ℝ} (hB : 0 ≤ B) :
    ∃ V : Finset (Fin r → Fin r → E), (∀ v ∈ V, IsBoundedBasis X B v) ∧
      (∀ v, IsBoundedBasis X B v →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = (γ : Matrix (Fin r) (Fin r) E) *ᵥ w i) ∧
      (V.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
        ((X.NA : ℝ) * X.NC * r * B) ^ (2 * fdeg E * r ^ 2) * (X.g : ℝ) ^ (2 * fdeg E * r ^ 2) := by
  classical
  obtain ⟨hfin, hc⟩ := PackingSeparation.count (E := E) B hB
  rw [Set.ncard_eq_toFinset_card _ hfin] at hc
  choose V hV₁ hV₂ hV₃ using exists_finset_boundedBasis_of_gram X hB
  let T : Finset (Fin r → Fin r → 𝓞 E) :=
    Fintype.piFinset fun _ => Fintype.piFinset fun _ => hfin.toFinset
  have hT : (T.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) := by
    rw [Fintype.card_piFinset_const, Fintype.card_piFinset_const]
    push_cast
    calc ((hfin.toFinset.card : ℝ) ^ r) ^ r ≤ (((1 + 2 * B) ^ (2 * fdeg E)) ^ r) ^ r := by gcongr
      _ = _ := by rw [← pow_mul, ← pow_mul, sq]
  refine ⟨T.biUnion fun A => V (Matrix.of A), fun v hv => ?_, fun v hv => ?_, ?_⟩
  · obtain ⟨A, -, h⟩ := Finset.mem_biUnion.1 hv
    exact hV₁ _ v h
  · let A : Fin r → Fin r → 𝓞 E := fun i k =>
      ⟨herm X.Gm (v i) (v k), X.L'_int _ (hv.1 i) _ (hv.1 k)⟩
    obtain ⟨γ, hγ, w, hw, h⟩ := hV₂ (Matrix.of A) v hv rfl
    refine ⟨γ, hγ, w, Finset.mem_biUnion.2 ⟨A, ?_, hw⟩, h⟩
    simp only [T, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i k τ => hv.2.2 τ i k
  · calc ((T.biUnion fun A => V (Matrix.of A)).card : ℝ)
        ≤ ∑ A ∈ T, ((V (Matrix.of A)).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ T, ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) :=
          Finset.sum_le_sum fun A _ => hV₃ _
      _ = T.card * ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
          ((X.NA : ℝ) * X.NC * X.g * r * B) ^ (2 * fdeg E * r ^ 2) := by gcongr
      _ = _ := by
          simp only [mul_pow]
          ring

theorem exists_finset_types_of_bounded_bases (X : DataX E r) {B : ℝ} (hB : 1 ≤ B) :
    ∃ V : Finset (Fin r → Fin r → E),
      (∀ v ∈ V, (∀ i, v i ∈ X.L') ∧ LinearIndependent E v ∧
        ∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B) ∧
      (∀ v : Fin r → Fin r → E, (∀ i, v i ∈ X.L') → LinearIndependent E v →
        (∀ (τ : E →+* ℂ) (i k : Fin r), ‖τ (herm X.Gm (v i) (v k))‖ ≤ B) →
        ∃ γ ∈ X.Γ, ∃ w ∈ V, ∀ i, v i = Matrix.mulVec (γ : Matrix (Fin r) (Fin r) E) (w i)) ∧
      (V.card : ℝ) ≤ (1 + 2 * B) ^ (2 * fdeg E * r ^ 2) *
        ((X.NA : ℝ) * X.NC * r * B) ^ (2 * fdeg E * r ^ 2) * (X.g : ℝ) ^ (2 * fdeg E * r ^ 2) ∧
      (V.card : ℝ) ≤ (3 * (X.NA : ℝ) * X.NC * X.g * r * B ^ 2) ^ (2 * fdeg E * r ^ 2) := by
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  obtain ⟨V, h₁, h₂, h₃⟩ := exists_finset_boundedBasis X hB0
  refine ⟨V, h₁, fun v a b c => h₂ v ⟨a, b, c⟩, h₃, h₃.trans ?_⟩
  rw [← mul_pow, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ _
  calc (1 + 2 * B) * ((X.NA : ℝ) * X.NC * r * B) * X.g
      ≤ (3 * B) * ((X.NA : ℝ) * X.NC * r * B) * X.g := by gcongr; linarith
    _ = _ := by ring

end GlobalTheory
