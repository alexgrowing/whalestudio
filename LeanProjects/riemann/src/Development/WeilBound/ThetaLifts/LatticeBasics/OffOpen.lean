import Development.WeilBound.ThetaLifts.LatticeBasics.OffOpenAlt
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB

noncomputable section

set_option linter.unusedSectionVars false

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Matrix PositivityTheory.ThKEnd

namespace Off

theorem exists_gi {k : Type} [Field k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) : ∃ S : Matrix (Fin n) (Fin n) k, A * S * A = A := by
  obtain ⟨g, hg⟩ := (toLin' A).rangeRestrict.exists_rightInverse_of_surjective (LinearMap.range_rangeRestrict _)
  obtain ⟨s, hs⟩ := LinearMap.exists_extend g
  refine ⟨LinearMap.toMatrix' s, toLin'.injective (LinearMap.ext fun v => ?_)⟩
  rw [toLin'_mul, toLin'_mul, toLin'_toMatrix']
  have := LinearMap.congr_fun hs ((toLin' A).rangeRestrict v)
  exact (congrArg (toLin' A) this).trans (congrArg Subtype.val (LinearMap.congr_fun hg ((toLin' A).rangeRestrict v)))

theorem det_one {R : Type} [CommRing R] {n : ℕ} {N Q : Matrix (Fin n) (Fin n) R} (h : Q * N = N) (h' : N * Q = 0) :
    (1 + N).det = 1 := by rw [← h, det_one_add_mul_comm, h', add_zero, Matrix.det_one]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem det_ne {B : Base F E} {r s : ℕ} (h : Y.IsSkew σ B r s) : Y.J.det ≠ 0 := fun z => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨e, A, hA⟩ := h.sig w
  let q : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr e)
  have := congrArg det (show (Aᵀ.submatrix id q * (Complex.I • Y.J.map (B.emb w).1).submatrix q q) * (A.map star).submatrix q id =
      fromBlocks 1 0 0 (-1) by
    rw [submatrix_mul_equiv, submatrix_mul_equiv]; exact hA)
  rw [det_mul, det_mul, det_submatrix_equiv_self, det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, z, map_zero, mul_zero,
    mul_zero, zero_mul, det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, det_neg, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ (neg_ne_zero.2 one_ne_zero) this.symm

theorem mm {a b e : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b e E) : (A * B).map σ = A.map σ * B.map σ :=
  Matrix.map_mul (f := σ.toRingHom)

theorem form_mul (J C D : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    form σ J (C *ᵥ v) (D *ᵥ w) = form σ (Cᵀ * J * D.map σ) v w := by
  rw [form, form, show (fun i => σ ((D *ᵥ w) i)) = D.map σ *ᵥ fun i => σ (w i) by ext i; simp [mulVec, dotProduct],
    mulVec_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, Matrix.mul_assoc]

theorem incV_mul (C : Matrix (Fin n) (Fin n) E) (v : Fin n → E) : incV F (C *ᵥ v) = incM F C *ᵥ incV F v :=
  funext fun i => RingHom.map_mulVec (inclR (F := F) (AF F)) C v i

theorem incM_one : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_zero : incM F (0 : Matrix (Fin n) (Fin n) E) = 0 := Matrix.map_zero _ (map_zero _)

theorem incM_sub (A B : Matrix (Fin n) (Fin n) E) : incM F (A - B) = incM F A - incM F B :=
  Matrix.map_sub _ (map_sub _) _ _

theorem mem_span {C : Matrix (Fin n) (Fin n) E} {w : Fin n → AE F E} :
    w ∈ Submodule.span (AE F E) (incV F '' (LinearMap.range C.mulVecLin : Set (Fin n → E))) ↔ ∃ x, incM F C *ᵥ x = w := by
  constructor
  · refine fun h => (Submodule.span_le (p := LinearMap.range (incM F C).mulVecLin)).2 ?_ h
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨_, (incV_mul C v).symm⟩
  · rintro ⟨x, rfl⟩
    rw [mulVec_eq_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [op_smul_eq_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ⟨Pi.single i 1, mulVec_single_one C i⟩, rfl⟩)

def Gen (C : Matrix (Fin n) (Fin n) E) (m : UA σ Y.J) : Prop :=
  (∀ u ∈ LinearMap.range C.mulVecLin, mat m *ᵥ incV F u = incV F u) ∧
    ∀ z : Fin n → E, (∀ u ∈ LinearMap.range C.mulVecLin, form σ Y.J z u = 0) → mat m *ᵥ incV F z - incV F z ∈
      Submodule.span (AE F E) (incV F '' (LinearMap.range C.mulVecLin : Set (Fin n → E)))

variable {C : Matrix (Fin n) (Fin n) E} {m : UA σ Y.J}

theorem Gen.fix (h : Gen C m) : mat m * incM F C = incM F C := by
  ext i j
  exact congrFun (h.1 _ ⟨Pi.single j 1, mulVec_single_one C j⟩) i

theorem Gen.cols (h : Gen C m) {P : Matrix (Fin n) (Fin n) E} (hP : Pᵀ * Y.J * C.map σ = 0) :
    ∃ X, mat m * incM F P = incM F P + incM F C * X := by
  choose x hx using fun j => mem_span.1 (h.2 (P *ᵥ Pi.single j 1) (by
    rintro _ ⟨v, rfl⟩
    rw [mulVecLin_apply, form_mul, hP]; simp [form]))
  refine ⟨(of x)ᵀ, ext fun i j => ?_⟩
  have := congrFun (hx j) i
  rw [mulVec_single_one] at this
  exact eq_add_of_sub_eq' this.symm

theorem Gen.det (h : Gen C m) (hC : Cᵀ * Y.J * C.map σ = 0) : (mat m).det = 1 := by
  obtain ⟨S, hS⟩ := exists_gi (Y.J * C.map σ)ᵀ
  obtain ⟨T, hT⟩ := exists_gi C
  set R := (Y.J * C.map σ)ᵀ with hR
  have r : ∀ P : Matrix (Fin n) (Fin n) E, Pᵀ * Y.J * C.map σ = (R * P)ᵀ := fun P => by simp [hR, Matrix.mul_assoc]
  have rC : R * C = 0 := transpose_eq_zero.1 (r C ▸ hC)
  obtain ⟨X, hX⟩ := h.cols (P := 1 - S * R) (by rw [r, Matrix.mul_sub, ← Matrix.mul_assoc, hS]; simp)
  have rm : incM F R * mat m = incM F R := by
    have e : (mat m)ᵀ * incM F Y.J * (mat m).map (cA σ) = incM F Y.J := m.2
    have : incM F R = (incM F Y.J * (incM F C).map (cA σ))ᵀ := by rw [incM_conj, ← incM_mul]; rfl
    rw [this, ← transpose_transpose (mat m), ← transpose_mul]
    nth_rw 1 [← h.fix]
    rw [show (mat m * incM F C).map (cA σ) = (mat m).map (cA σ) * (incM F C).map (cA σ) from Matrix.map_mul (f := (cA σ).toRingHom),
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, e]
  have pm : incM F (1 - S * R) * (mat m - 1) = mat m - 1 := by
    rw [incM_sub, incM_one, incM_mul, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_sub (incM F R), rm]; simp
  have pc : incM F (1 - S * R) * incM F C = incM F C := by
    rw [← incM_mul, Matrix.sub_mul, Matrix.mul_assoc, rC]; simp
  have e : (mat m - 1) * incM F (1 - S * R) = incM F C * X := by rw [Matrix.sub_mul, hX]; simp
  rw [← add_sub_cancel 1 (mat m), ← pm, det_one_add_mul_comm, e]
  refine det_one (Q := incM F (C * T)) (by rw [← Matrix.mul_assoc, ← incM_mul, hT]) ?_
  rw [incM_mul, ← Matrix.mul_assoc, ← e, Matrix.mul_assoc _ _ (incM F C), pc, Matrix.sub_mul, h.fix]; simp

theorem Gen.conj (h : Gen C m) {δ : UA σ Y.J} {d d' : Matrix (Fin n) (Fin n) E} (hd : mat δ = incM F d) (hd' : mat δ⁻¹ = incM F d')
    {T T' : Matrix (Fin n) (Fin n) E} (hT : d * C = C * T) (hT' : d' * C = C * T') : Gen C (δ * m * δ⁻¹) := by
  have e : ∀ z, mat (δ * m * δ⁻¹) *ᵥ incV F z = mat δ *ᵥ (mat m *ᵥ incV F (d' *ᵥ z)) := fun z => by
    rw [incV_mul, ← hd', mulVec_mulVec, mulVec_mulVec]; rfl
  have e' : ∀ z, mat δ *ᵥ incV F (d' *ᵥ z) = incV F z := fun z => by
    rw [incV_mul, ← hd', mulVec_mulVec, show mat δ * mat δ⁻¹ = 1 from δ.1.mul_inv, one_mulVec]
  refine ⟨?_, fun z hz => ?_⟩
  · rintro _ ⟨v, rfl⟩
    rw [e, h.1 _ ⟨T' *ᵥ v, by simp [hT']⟩, e']
  · have u : dᵀ * Y.J * d.map σ = Y.J := incM_inj (F := F) (by
      rw [incM_mul, incM_mul, ← incM_conj, show incM F dᵀ = (incM F d)ᵀ from rfl, ← hd]; exact δ.2)
    have dd : d * d' = 1 := incM_inj (F := F) (by rw [incM_mul, ← hd, ← hd', incM_one]; exact δ.1.mul_inv)
    obtain ⟨x, hx⟩ := mem_span.1 (h.2 (d' *ᵥ z) (by
      rintro _ ⟨v, rfl⟩
      rw [← hz _ ⟨T *ᵥ v, rfl⟩, ← u, ← form_mul, mulVec_mulVec, dd, one_mulVec, u]; simp [hT]))
    refine mem_span.2 ⟨incM F T *ᵥ x, ?_⟩
    rw [e, ← e' z, ← mulVec_sub, ← hx, hd, mulVec_mulVec, mulVec_mulVec, ← incM_mul, ← incM_mul, hT]

theorem frame {γ : G2 σ Y} (hγ : γ ∈ rat2 σ Y) : ∃ A B : Matrix (Fin n) (Fin n) E,
    mat2 γ * dC n (AE F E) = fromRows (incM F A) (incM F B) ∧ Aᵀ * Y.J * A.map σ = Bᵀ * Y.J * B.map σ := by
  obtain ⟨g, hg⟩ := hγ
  have e : mat2 γ = incM F g.1 := (congrArg Units.val hg).symm
  have u : g.1ᵀ * dbl Y.J * g.1.map σ = dbl Y.J := incM_inj (F := F) (by
    have : (mat2 γ)ᵀ * dbl (incM F Y.J) * (mat2 γ).map (cA σ) = dbl (incM F Y.J) := γ.2
    rw [e, incM_conj] at this
    have d : incM F (dbl Y.J) = dbl (incM F Y.J) := by simp [incM, dbl, fromBlocks_map, Matrix.map_neg]
    rw [incM_mul, incM_mul, d]; exact this)
  obtain ⟨A, B, hAB⟩ : ∃ A B, g.1 * dC n E = fromRows A B := ⟨_, _, (fromRows_toRows _).symm⟩
  refine ⟨A, B, by rw [e, ← incM_diag, ← incM_mul, hAB]; exact fromRows_map _ _ _, ?_⟩
  have : (g.1 * dC n E)ᵀ * dbl Y.J * (g.1 * dC n E).map σ = 0 := by
    calc _ = (dC n E)ᵀ * (g.1ᵀ * dbl Y.J * g.1.map σ) * (dC n E).map σ := by simp only [mm, transpose_mul, Matrix.mul_assoc]
      _ = 0 := by rw [u]; exact (isLagr_diagCols σ Y.J).1
  rw [hAB] at this
  simpa [dbl, transpose_fromRows, fromRows_map, fromCols_mul_fromBlocks, fromCols_mul_fromRows, ← sub_eq_add_neg, sub_eq_zero] using this

variable {γ x : G2 σ Y} {A B : Matrix (Fin n) (Fin n) (AE F E)}

theorem inj (h : mat2 γ⁻¹ * dC n (AE F E) = fromRows A B) {Z : Matrix (Fin n) (Fin n) (AE F E)} (a : A * Z = 0) (b : B * Z = 0) :
    Z = 0 := by
  have : mat2 γ * (fromRows A B * Z) = 0 := by rw [fromRows_mul, a, b]; simp
  rw [← h, ← Matrix.mul_assoc, ← Matrix.mul_assoc, show mat2 γ * mat2 γ⁻¹ = 1 from γ.1.mul_inv, Matrix.one_mul, dC, diagCols,
    fromRows_mul] at this
  exact ext fun i j => by simpa using congrFun (congrFun this (.inl i)) j

theorem par_iff (h : mat2 γ⁻¹ * dC n (AE F E) = fromRows A B) (hx : IsEmb 1 m x) {t : GL (Fin n) (AE F E)} :
    IsPar (γ * x * γ⁻¹) t ↔ A * t.1 = A ∧ B * t.1 = mat m * B := by
  have l : ∀ {M N : Matrix (Fin n ⊕ Fin n) (Fin n) (AE F E)}, mat2 γ * M = N ↔ M = mat2 γ⁻¹ * N := fun {M N} =>
    ⟨fun h => by rw [← h, ← Matrix.mul_assoc, show mat2 γ⁻¹ * mat2 γ = 1 from γ.1.inv_mul, Matrix.one_mul],
      fun h => by rw [h, ← Matrix.mul_assoc, show mat2 γ * mat2 γ⁻¹ = 1 from γ.1.mul_inv, Matrix.one_mul]⟩
  rw [isPar_iff, show mat2 (γ * x * γ⁻¹) = mat2 γ * mat2 x * mat2 γ⁻¹ from rfl, Matrix.mul_assoc, Matrix.mul_assoc, l, h,
    ← Matrix.mul_assoc, h, hx, fromBlocks_mul_fromRows, fromRows_mul, fromRows_ext_iff, show mat (1 : UA σ Y.J) = 1 from rfl]
  simp [eq_comm]

end Off

open Off in
theorem offOpen : OffOpen := by
  intro F E _ _ _ _ _ σ B₀ n Y r s _ hY e he γ hγ hno
  obtain ⟨A, B, hL, iso⟩ := frame (inv_mem hγ)
  obtain ⟨S, hS⟩ := exists_gi A
  set K := 1 - S * A with hK
  have aK : A * K = 0 := by rw [hK, Matrix.mul_sub, ← Matrix.mul_assoc, hS]; simp
  have kK : ∀ Z : Matrix (Fin n) (Fin n) E, A * Z = 0 → K * Z = Z := fun Z h => by rw [hK, Matrix.sub_mul, Matrix.mul_assoc, h]; simp
  have bC : Bᵀ * Y.J * (B * K).map σ = 0 := by
    rw [mm, ← Matrix.mul_assoc, ← iso, Matrix.mul_assoc, ← mm, aK, Matrix.map_zero _ (map_zero _), Matrix.mul_zero]
  have cC : (B * K)ᵀ * Y.J * (B * K).map σ = 0 := by
    rw [transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Bᵀ, bC, Matrix.mul_zero]
  have norm : ∀ δ : UA σ Y.J, ∀ d, mat δ = incM F d → δ ∈ ratU σ Y.J → γ * e (1, δ) * γ⁻¹ ∈ par2 σ Y →
      ∃ T, d * (B * K) = B * K * T := fun δ d hd hδ hp => by
    obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 hp
    obtain ⟨T, hT⟩ := par_rat ht (mul_mem (mul_mem hγ ((he _ _).rat (one_mem _) hδ)) (inv_mem hγ))
    obtain ⟨a, b⟩ := (par_iff hL (he _ _)).1 ht
    rw [hT, ← incM_mul] at a
    rw [hT, hd, ← incM_mul, ← incM_mul] at b
    refine ⟨T * K, ?_⟩
    rw [Matrix.mul_assoc B, kK _ (by rw [← Matrix.mul_assoc, incM_inj a, aK]), ← Matrix.mul_assoc, ← incM_inj b, Matrix.mul_assoc]
  refine ⟨LinearMap.range (B * K).mulVecLin, fun h0 => hno ?_, ?_, fun m hm => ?_, fun δ hδ hp m hm => ?_⟩
  · have c0 : B * K = 0 := toLin'.injective (by rw [map_zero]; exact LinearMap.range_eq_bot.1 h0)
    have k0 : K = 0 := incM_inj (F := F) ((inj hL (by rw [← incM_mul, aK, incM_zero]) (by rw [← incM_mul, c0, incM_zero])).trans
      incM_zero.symm)
    obtain ⟨a, rfl⟩ : IsUnit A := (isUnit_iff_isUnit_det _).2 (isUnit_det_of_left_inverse (sub_eq_zero.1 k0).symm)
    obtain ⟨b, rfl⟩ : IsUnit B := (isUnit_iff_isUnit_det _).2 (Ne.isUnit fun h0 => by
      have := congrArg det iso
      rw [det_mul, det_mul, det_mul, det_mul, det_transpose, det_transpose, h0, zero_mul, zero_mul,
        show (a.1.map σ).det = σ a.1.det from (RingHom.map_det σ.toRingHom _).symm] at this
      have d : a.1.det ≠ 0 := GeneralLinearGroup.det_ne_zero a
      exact mul_ne_zero (mul_ne_zero d (det_ne hY)) ((map_ne_zero σ).2 d) this)
    have ud : (b * a⁻¹).1ᵀ * Y.J * (b * a⁻¹).1.map σ = Y.J := by
      calc _ = (a⁻¹).1ᵀ * (b.1ᵀ * Y.J * b.1.map σ) * (a⁻¹).1.map σ := by
            simp only [Units.val_mul, mm, transpose_mul, Matrix.mul_assoc]
        _ = (a * a⁻¹).1ᵀ * Y.J * (a * a⁻¹).1.map σ := by
            rw [← iso]; simp only [Units.val_mul, mm, transpose_mul, Matrix.mul_assoc]
        _ = Y.J := by simp
    let δ : UA σ Y.J := ⟨GeneralLinearGroup.map (inclR (F := F) (AF F)) (b * a⁻¹), by
      show (incM F (b * a⁻¹).1)ᵀ * incM F Y.J * (incM F (b * a⁻¹).1).map (cA σ) = incM F Y.J
      rw [incM_conj, show (incM F (b * a⁻¹).1)ᵀ = incM F (b * a⁻¹).1ᵀ from rfl, ← incM_mul, ← incM_mul, ud]⟩
    refine ⟨δ⁻¹, inv_mem ⟨_, rfl⟩, inv_mem_iff.1 (mem_parabolic_GL2_iff.2 ⟨GeneralLinearGroup.map (inclR (F := F) (AF F)) a, ?_⟩)⟩
    rw [_root_.mul_inv_rev, inv_inv]
    show mat2 (e (1, δ⁻¹)) * mat2 γ⁻¹ * dC n (AE F E) = dC n (AE F E) * incM F a.1
    rw [Matrix.mul_assoc, hL, he, fromBlocks_mul_fromRows, dC, diagCols, fromRows_mul,
      show mat δ⁻¹ = incM F ((b * a⁻¹)⁻¹).1 from rfl, ← incM_mul, ← Units.val_mul, show mat (1 : UA σ Y.J) = 1 from rfl]
    simp
  · rintro _ ⟨v, rfl⟩ _ ⟨w, rfl⟩
    rw [mulVecLin_apply, mulVecLin_apply, form_mul, cC]; simp [form]
  · induction hm using Subgroup.closure_induction with
    | mem m hm =>
      obtain ⟨X, hX⟩ := Gen.cols hm bC
      have kk : incM F K * incM F K = incM F K := by rw [← incM_mul, kK _ aK]
      have a0 : incM F A * incM F K = 0 := by rw [← incM_mul, aK, incM_zero]
      have d1 : (1 + incM F K * X).det = 1 := det_one (Q := incM F K) (by rw [← Matrix.mul_assoc, kk]) (inj hL
        (by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, a0]; simp) (by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← incM_mul, ← sub_eq_of_eq_add' hX, Matrix.sub_mul, Matrix.mul_assoc,
            ← incM_mul, Gen.fix hm, sub_self]))
      obtain ⟨t, ht⟩ := (isUnit_iff_isUnit_det _).2 (d1 ▸ isUnit_one)
      refine ⟨t, (par_iff hL (he _ _)).2 ⟨?_, ?_⟩, Units.ext (ht ▸ d1 : t.1.det = 1), Units.ext (Gen.det hm cC)⟩
      · rw [ht, Matrix.mul_add, ← Matrix.mul_assoc, a0]; simp
      · rw [ht, Matrix.mul_add, ← Matrix.mul_assoc, ← incM_mul, hX, Matrix.mul_one]
    | one => exact ⟨1, (par_iff hL (he _ _)).2 ⟨Matrix.mul_one _, (Matrix.mul_one _).trans (Matrix.one_mul _).symm⟩, map_one _, map_one _⟩
    | mul m m' _ _ h h' =>
      obtain ⟨t, a, b, c⟩ := h
      obtain ⟨t', a', b', c'⟩ := h'
      refine ⟨t * t', ?_, by rw [map_mul, b, b', mul_one], by rw [Subgroup.coe_mul, map_mul, c, c', mul_one]⟩
      convert a.mul a' using 1
      rw [show ((1, m * m') : UA σ Y.J × UA σ Y.J) = (1, m) * (1, m') by simp, map_mul]; group
    | inv m _ h =>
      obtain ⟨t, a, b, c⟩ := h
      refine ⟨t⁻¹, ?_, by rw [map_inv, b, inv_one], by rw [Subgroup.coe_inv, map_inv, c, inv_one]⟩
      convert a.inv using 1
      rw [show ((1, m⁻¹) : UA σ Y.J × UA σ Y.J) = (1, m)⁻¹ by simp, map_inv]; group
  · obtain ⟨d, hd⟩ := id hδ
    have h1 : mat δ = incM F d.1 := (congrArg Units.val hd).symm
    have h2 : mat δ⁻¹ = incM F (d⁻¹).1 := (congrArg Units.val ((map_inv _ d).trans (congrArg _ hd))).symm
    obtain ⟨T, hT⟩ := norm δ _ h1 hδ hp
    obtain ⟨T', hT'⟩ := norm δ⁻¹ _ h2 (inv_mem hδ) (by
      convert inv_mem hp using 1
      rw [show ((1, δ⁻¹) : UA σ Y.J × UA σ Y.J) = (1, δ)⁻¹ by simp, map_inv]; group)
    exact (Subgroup.closure_le ((unipU σ Y _).comap (MulAut.conj δ).toMonoidHom)).2
      (fun m hm => Subgroup.subset_closure (Gen.conj hm h1 h2 hT hT')) hm

end GlobalTheory.ThK.Dbl

end
