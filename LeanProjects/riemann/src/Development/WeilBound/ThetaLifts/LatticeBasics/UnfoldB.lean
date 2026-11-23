import Development.WeilBound.ThetaLifts.LatticeBasics.PairsStable
import Development.WeilBound.ThetaLifts.LatticeBasics.LeviEx
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldA

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

theorem HasSig.aniso {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) (h0 : min r s = 0) {x : Fin n → ℂ}
    (hx : x ⬝ᵥ M *ᵥ star x = 0) : x = 0 := by
  obtain ⟨e, A, hA⟩ := h
  set D : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hD
  have h1 : Aᵀ * (M * A.map star * D) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, hD, Matrix.fromBlocks_multiply]; simp
  have h2 : A * (M * A.map star * D)ᵀ = 1 := by
    have := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq (by simp [e]))).1 h1
    simpa using congrArg Matrix.transpose this
  obtain ⟨y, rfl⟩ : ∃ y, x = A *ᵥ y := ⟨(M * A.map star * D)ᵀ *ᵥ x, by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]⟩
  have h3 : star (A *ᵥ y) = A.map star *ᵥ star y := by
    ext i; simp [Matrix.mulVec, dotProduct]
  rw [h3, Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hA] at hx
  have h4 : y ⬝ᵥ star y = 0 := by
    rcases Nat.min_eq_zero_iff.1 h0 with rfl | rfl
    · rwa [show D = -1 by ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | simp [hD, Matrix.one_apply],
        Matrix.neg_mulVec, dotProduct_neg, neg_eq_zero, Matrix.one_mulVec] at hx
    · rwa [show D = 1 by ext (i | i) (j | j) <;> first | exact i.elim0 | exact j.elim0 | simp [hD, Matrix.one_apply],
        Matrix.one_mulVec] at hx
  open ComplexOrder in rw [dotProduct_self_star_eq_zero.1 h4, Matrix.mulVec_zero]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

variable (σ) in

def Aniso (J : Matrix (Fin n) (Fin n) E) : Prop := ∀ x, form σ J x x = 0 → x = 0

theorem aniso_of {B : Base F E} {r s : ℕ} (hB : B.IsGood σ) (hY : Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) (h0 : min r s = 0) :
    Aniso σ Y.J := fun x hx => by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have e : ((B.emb w).1 ∘ x) ⬝ᵥ Y.J.map (B.emb w).1 *ᵥ star ((B.emb w).1 ∘ x) = 0 := by
    rw [← map_zero (B.emb w).1, ← hx]
    simp [form, Matrix.mulVec, dotProduct, hB.cm.2.2.2]
  have : (B.emb w).1 ∘ x = 0 := hY.elim (fun h => HasSig.aniso (h.sig w) h0 e) fun h => HasSig.aniso (h.sig w) h0 (by
    rw [Matrix.smul_mulVec, dotProduct_smul, e, smul_zero])
  exact funext fun i => (map_eq_zero _).1 (congrFun this i)

instance nontrivAF : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))

instance nontrivAE : Nontrivial (AE F E) :=
  (Algebra.TensorProduct.includeLeft_injective (S := F) (algebraMap F E).injective).nontrivial

abbrev dC (n : ℕ) (R : Type) [CommRing R] : Matrix (Fin n ⊕ Fin n) (Fin n) R := diagCols (Fin n)

theorem isPar_iff {p : G2 σ Y} {t} : IsPar p t ↔ mat2 p * dC n (AE F E) = dC n (AE F E) * t.1 := Iff.rfl

theorem incM_inj {a b : Type} : Function.Injective (incM F : Matrix a b E → _) :=
  Matrix.map_injective (inclR (F := F) (E := E) (AF F)).injective

theorem incM_diag : incM F (dC n E) = dC n (AE F E) := by
  simp [incM, diagCols, Matrix.fromRows_map]

theorem IsPar.mul {p p' : G2 σ Y} {t t'} (h : IsPar p t) (h' : IsPar p' t') : IsPar (p * p') (t * t') := by
  rw [isPar_iff] at *
  rw [show mat2 (p * p') = mat2 p * mat2 p' from rfl, Units.val_mul, Matrix.mul_assoc, h', ← Matrix.mul_assoc, h, Matrix.mul_assoc]

theorem IsPar.inv {p : G2 σ Y} {t} (h : IsPar p t) : IsPar p⁻¹ t⁻¹ := by
  rw [isPar_iff] at *
  have : mat2 p⁻¹ * (mat2 p * dC n (AE F E)) * (t⁻¹).1 = mat2 p⁻¹ * dC n (AE F E) := by
    rw [h, Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [← this, ← Matrix.mul_assoc, show mat2 p⁻¹ * mat2 p = 1 from p.1.inv_mul, Matrix.one_mul]

theorem mem_parabolic_GL2_iff {p : G2 σ Y} : p ∈ par2 σ Y ↔ ∃ t, IsPar p t := by
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure h⟩
  induction h using Subgroup.closure_induction with
  | mem _ h => exact h
  | one => exact ⟨1, isPar_iff.2 ((Matrix.one_mul _).trans (Matrix.mul_one _).symm)⟩
  | mul _ _ _ _ h h' => exact ⟨_, h.choose_spec.mul h'.choose_spec⟩
  | inv _ _ h => exact ⟨_, h.choose_spec.inv⟩

theorem det_rat {t : GL (Fin n) (AE F E)} {T : Matrix (Fin n) (Fin n) E} (h : t.1 = incM F T) :
    ∃ u : Eˣ, Matrix.GeneralLinearGroup.det t = Units.map (inclR (F := F) (AF F)).toMonoidHom u := by
  have e : (Matrix.GeneralLinearGroup.det t).1 = inclR (F := F) (AF F) T.det := by
    rw [RingHom.map_det]; exact congrArg Matrix.det h
  exact ⟨Units.mk0 T.det fun h0 => (Matrix.GeneralLinearGroup.det t).ne_zero (by rw [e, h0, map_zero]), Units.ext e⟩

theorem par_rat {p : G2 σ Y} {t} (h : IsPar p t) (hp : p ∈ rat2 σ Y) : ∃ T, t.1 = incM F T := by
  obtain ⟨g, hg⟩ := hp
  have e : mat2 p = incM F g.1 := (congrArg Units.val hg).symm
  rw [isPar_iff, e, ← incM_diag, ← incM_mul, incM_diag] at h
  refine ⟨(g.1 * dC n E).toRows₁, ?_⟩
  refine Eq.trans ?_ (congrArg Matrix.toRows₁ h).symm
  simp [diagCols, Matrix.fromRows_mul]

theorem detInv_rat {χ : Chr F E} (hχ : IsHecke F E χ) {γ : UA σ Y.J} (h : γ ∈ ratU σ Y.J) : detInv χ γ = 1 := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨u, hu⟩ := det_rat (t := γ.1) (T := g.1) (congrArg Units.val hg).symm
  rw [detInv, hu, hχ.2]; simp

theorem detInv_mul (χ : Chr F E) (g h : UA σ Y.J) : detInv χ (g * h) = detInv χ g * detInv χ h := by
  simp [detInv, mul_comm]

theorem norm_detInv (χ : Chr F E) (g : UA σ Y.J) : ‖detInv χ g‖ = 1 := Circle.norm_coe _

theorem continuous_detInv {χ : Chr F E} (hχ : IsHecke F E χ) : Continuous (detInv χ : UA σ Y.J → ℂ) := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  exact continuous_subtype_val.comp ((hχ.1.comp (Matrix.GeneralLinearGroup.continuous_det.comp continuous_subtype_val)).inv)

theorem absE_det (hJ : Aniso σ Y.J) (h : UA σ Y.J) : absE F E (Matrix.GeneralLinearGroup.det h.1) = 1 := by
  have d0 : Y.J.det ≠ 0 := fun h0 => by
    obtain ⟨v, hv, e⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
    exact hv (hJ v (by rw [form, Matrix.dotProduct_mulVec, e, zero_dotProduct]))
  have u : IsUnit (incM F Y.J).det := by
    rw [incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact d0.isUnit.map _
  have e := congrArg Matrix.det (show (mat h)ᵀ * incM F Y.J * (mat h).map (cA σ) = incM F Y.J from h.2)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_right_comm, u.mul_eq_right,
    show ((mat h).map (cA σ)).det = sigR (AF F) σ (mat h).det from (RingHom.map_det (sigR (AF F) σ) _).symm] at e
  have e2 : Matrix.GeneralLinearGroup.det h.1 * GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det h.1) = 1 := Units.ext e
  have e3 := congrArg (absE F E) e2
  rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one] at e3
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, e3])

theorem IsEmb.par {h : UA σ Y.J} {x : G2 σ Y} (e : IsEmb h h x) : IsPar x h.1 := by
  rw [isPar_iff, e]; simp [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, mat]

theorem IsEmb.rat {h h' : UA σ Y.J} {x : G2 σ Y} (e : IsEmb h h' x) (a : h ∈ ratU σ Y.J) (b : h' ∈ ratU σ Y.J) : x ∈ rat2 σ Y := by
  obtain ⟨g, hg⟩ := a
  obtain ⟨g', hg'⟩ := b
  refine ⟨⟨Matrix.fromBlocks g.1 0 0 g'.1, Matrix.fromBlocks (g⁻¹).1 0 0 (g'⁻¹).1, by simp [Matrix.fromBlocks_multiply],
    by simp [Matrix.fromBlocks_multiply]⟩, Units.ext (Eq.trans ?_ e.symm)⟩
  rw [show mat h = incM F g.1 from (congrArg Units.val hg).symm, show mat h' = incM F g'.1 from (congrArg Units.val hg').symm]
  show incM F (Matrix.fromBlocks g.1 0 0 g'.1) = _
  simp [incM, Matrix.fromBlocks_map]

theorem orbit (hJ : Aniso σ Y.J) {γ : G2 σ Y} (hγ : γ ∈ rat2 σ Y) :
    ∃ δ ∈ ratU σ Y.J, ∀ x, IsEmb 1 δ x → x * γ ∈ par2 σ Y := by
  obtain ⟨g, hg⟩ := hγ
  have e : mat2 γ = incM F g.1 := (congrArg Units.val hg).symm
  have mm : ∀ {a b e : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b e E), (A * B).map σ = A.map σ * B.map σ :=
    fun A B => Matrix.map_mul (f := σ.toRingHom)
  have u : g.1ᵀ * dbl Y.J * g.1.map σ = dbl Y.J := incM_inj (F := F) (by
    have : (mat2 γ)ᵀ * dbl (incM F Y.J) * (mat2 γ).map (cA σ) = dbl (incM F Y.J) := γ.2
    rw [e, incM_conj] at this
    have d : incM F (dbl Y.J) = dbl (incM F Y.J) := by simp [incM, dbl, Matrix.fromBlocks_map, Matrix.map_neg]
    rw [incM_mul, incM_mul, d]; exact this)
  obtain ⟨A, B, hAB⟩ : ∃ A B, g.1 * dC n E = Matrix.fromRows A B := ⟨_, _, (Matrix.fromRows_toRows _).symm⟩
  have iso : Aᵀ * Y.J * A.map σ = Bᵀ * Y.J * B.map σ := by
    have : (g.1 * dC n E)ᵀ * dbl Y.J * (g.1 * dC n E).map σ = 0 := by
      calc _ = (dC n E)ᵀ * (g.1ᵀ * dbl Y.J * g.1.map σ) * (dC n E).map σ := by
            simp only [mm, Matrix.transpose_mul, Matrix.mul_assoc]
        _ = 0 := by rw [u]; exact (isLagr_diagCols σ Y.J).1
    rw [hAB] at this
    simpa [dbl, Matrix.transpose_fromRows, Matrix.fromRows_map, Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows,
      ← sub_eq_add_neg, sub_eq_zero] using this
  have fm : ∀ (C : Matrix (Fin n) (Fin n) E) v, form σ Y.J (C *ᵥ v) (C *ᵥ v) = form σ (Cᵀ * Y.J * C.map σ) v v := fun C v => by
    rw [form, form, show (fun i => σ ((C *ᵥ v) i)) = C.map σ *ᵥ fun i => σ (v i) by ext i; simp [Matrix.mulVec, dotProduct],
      Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have inj : ∀ v, A *ᵥ v = 0 → B *ᵥ v = 0 → v = 0 := fun v a b => by
    have : (g⁻¹).1 *ᵥ (g.1 * dC n E) *ᵥ v = 0 := by
      rw [hAB, Matrix.fromRows_mulVec, a, b]; simp
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, dC, diagCols, Matrix.fromRows_mulVec] at this
    exact funext fun i => by simpa using congrFun this (.inl i)
  have un : ∀ C : Matrix (Fin n) (Fin n) E, (∀ v, C *ᵥ v = 0 → v = 0) → IsUnit C := fun C h =>
    (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit fun h0 => by
      obtain ⟨v, hv, e⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      exact hv (h v e))
  obtain ⟨a, rfl⟩ := un A fun v h => inj v h (hJ _ (by rw [fm, ← iso, ← fm, h]; simp [form]))
  obtain ⟨b, rfl⟩ := un B fun v h => inj v (hJ _ (by rw [fm, iso, ← fm, h]; simp [form])) h
  have ud : (a * b⁻¹).1ᵀ * Y.J * (a * b⁻¹).1.map σ = Y.J := by
    calc _ = (b⁻¹).1ᵀ * (a.1ᵀ * Y.J * a.1.map σ) * (b⁻¹).1.map σ := by
          simp only [Units.val_mul, mm, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = (b * b⁻¹).1ᵀ * Y.J * (b * b⁻¹).1.map σ := by
          rw [iso]; simp only [Units.val_mul, mm, Matrix.transpose_mul, Matrix.mul_assoc]
      _ = Y.J := by simp
  refine ⟨⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) (a * b⁻¹), ?_⟩, ⟨_, rfl⟩, fun x hx =>
    mem_parabolic_GL2_iff.2 ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) a, ?_⟩⟩
  · show (incM F (a * b⁻¹).1)ᵀ * incM F Y.J * (incM F (a * b⁻¹).1).map (cA σ) = incM F Y.J
    rw [incM_conj, show (incM F (a * b⁻¹).1)ᵀ = incM F (a * b⁻¹).1ᵀ from rfl, ← incM_mul, ← incM_mul, ud]
  · show mat2 x * mat2 γ * dC n (AE F E) = dC n (AE F E) * incM F a.1
    have : mat2 γ * dC n (AE F E) = incM F (Matrix.fromRows a.1 b.1) := by rw [e, ← incM_diag, ← incM_mul, hAB]
    rw [Matrix.mul_assoc, this, hx]
    show Matrix.fromBlocks 1 0 0 (incM F (a * b⁻¹).1) * (Matrix.fromRows a.1 b.1).map _ = _
    rw [Matrix.fromRows_map, Matrix.fromBlocks_mul_fromRows, dC, diagCols, Matrix.fromRows_mul]
    show Matrix.fromRows (1 * incM F a.1 + 0 * incM F b.1) (0 * incM F a.1 + incM F (a * b⁻¹).1 * incM F b.1) = _
    rw [← incM_mul, ← Units.val_mul, inv_mul_cancel_right]; simp

end GlobalTheory.ThK.Dbl

end
