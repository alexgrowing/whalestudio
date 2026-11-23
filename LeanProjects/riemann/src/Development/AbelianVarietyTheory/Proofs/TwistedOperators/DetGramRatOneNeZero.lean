import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SelfReciprocalLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInfiniteDecomp

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.QuadSymbol GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField GlobalTheory.HermLocal
open scoped TensorProduct Matrix ComplexConjugate

namespace GlobalTheory.TraceClasses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (P : SelfRecip E r)

instance : Module.Finite (maximalRealSubfield E) (Fld P) := Module.Finite.trans E (Fld P)

instance : Field (plus P) := (Subalgebra.isField_of_algebraic (plus P)).toField

instance : NumberField (Fld P) := NumberField.of_module_finite E (Fld P)

instance : NumberField (plus P) := NumberField.of_module_finite (maximalRealSubfield E) (plus P)

theorem invol_coe (a : plus P) : invol P a = a := a.2

section Imaginary

variable {θ : E} (h0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)

include hθ in
theorem invol_theta : invol P (algebraMap E (Fld P) θ) = -algebraMap E (Fld P) θ := by
  rw [invol_algebraMap, hθ, map_neg]

include h0 hθ

theorem exists_add_mul (y : Fld P) : ∃ a b : plus P, y = a + b * algebraMap E (Fld P) θ := by
  have h1 : algebraMap E (Fld P) θ ≠ 0 := (map_ne_zero _).2 h0
  refine ⟨⟨(y + invol P y) / 2, ?_⟩, ⟨(y - invol P y) / (2 * algebraMap E (Fld P) θ), ?_⟩, ?_⟩
  · change invol P _ = _
    simp only [map_div₀, map_add, invol_invol, map_ofNat, AlgHom.id_apply, add_comm]
  · change invol P _ = _
    simp only [map_div₀, map_sub, map_mul, invol_invol, map_ofNat, AlgHom.id_apply, invol_theta P hθ]
    field_simp
    ring
  · simp only
    field_simp
    ring

theorem exists_basis_theta :
    ∃ e : Module.Basis (Fin 2) (plus P) (Fld P), e 0 = 1 ∧ e 1 = algebraMap E (Fld P) θ := by
  have h1 : algebraMap E (Fld P) θ ≠ 0 := (map_ne_zero _).2 h0
  have hli : LinearIndependent (plus P) ![(1 : Fld P), algebraMap E (Fld P) θ] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have e1 : (s : Fld P) + t * algebraMap E (Fld P) θ = 0 := by
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
      exact hst
    have e2 := congrArg (invol P) e1
    rw [map_add, map_mul, invol_coe, invol_coe, invol_theta P hθ, map_zero] at e2
    have hs : (s : Fld P) = 0 := by linear_combination (e1 + e2) / 2
    have ht : (t : Fld P) * algebraMap E (Fld P) θ = 0 := by linear_combination e1 - hs
    exact ⟨Subtype.ext hs, Subtype.ext ((mul_eq_zero.1 ht).resolve_right h1)⟩
  refine ⟨Module.Basis.mk hli fun y _ => ?_, by simp, by simp⟩
  obtain ⟨a, b, rfl⟩ := exists_add_mul P h0 hθ y
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨![a, b], ?_⟩
  simp [Algebra.smul_def]

theorem adjoin_eq_top : Algebra.adjoin (plus P) (Set.range (algebraMap E (Fld P))) = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨a, b, rfl⟩ := exists_add_mul P h0 hθ y
  exact add_mem (Subalgebra.algebraMap_mem _ a)
    (mul_mem (Subalgebra.algebraMap_mem _ b) (Algebra.subset_adjoin ⟨θ, rfl⟩))

theorem exists_bases : ∃ (b : Module.Basis (Fin r) (maximalRealSubfield E) (plus P)) (B : Module.Basis (Fin r) E (Fld P)),
    ∀ i, B i = b i := by
  obtain ⟨e, -⟩ := exists_basis_theta P h0 hθ
  have h1 := Module.finrank_mul_finrank (maximalRealSubfield E) (plus P) (Fld P)
  have h2 := Module.finrank_mul_finrank (maximalRealSubfield E) E (Fld P)
  rw [Module.finrank_eq_card_basis e, Fintype.card_fin] at h1
  rw [finrank_fld, Algebra.IsQuadraticExtension.finrank_eq_two] at h2
  let b := Module.finBasisOfFinrankEq (maximalRealSubfield E) (plus P) (n := r) (by omega)
  have hb : ∀ a : plus P, (a : Fld P) ∈ Submodule.span E (Set.range fun i => (b i : Fld P)) := fun a => by
    rw [← b.sum_repr a, AddSubmonoidClass.coe_finset_sum]
    exact sum_mem fun i _ => Submodule.smul_mem _ (b.repr a i : E) (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨b, basisOfTopLeSpanOfCardEqFinrank (fun i => (b i : Fld P)) (fun y _ => ?_)
    (by rw [finrank_fld, Fintype.card_fin]), fun i => congrFun (coe_basisOfTopLeSpanOfCardEqFinrank ..) i⟩
  obtain ⟨a, c, rfl⟩ := exists_add_mul P h0 hθ y
  refine add_mem (hb a) ?_
  rw [mul_comm, ← Algebra.smul_def]
  exact Submodule.smul_mem _ _ (hb c)

variable (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

omit h0 hθ in
theorem involBase_inclPlus (a : k ⊗[(maximalRealSubfield E)] plus P) :
    involBase P k (inclPlus P k a) = inclPlus P k a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [involBase, inclPlus, invol_coe]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem mem_norms_iff {d : plus P} (hd : (d : Fld P) = algebraMap E _ θ * algebraMap E _ θ)
    (x : (k ⊗[(maximalRealSubfield E)] plus P)ˣ) :
    x ∈ norms P k ↔ IsValue (1 ⊗ₜ d) (x : k ⊗[(maximalRealSubfield E)] plus P) := by
  let t : k ⊗[(maximalRealSubfield E)] Fld P := 1 ⊗ₜ algebraMap E (Fld P) θ
  have key : ∀ a b, (inclPlus P k a + inclPlus P k b * t) *
      involBase P k (inclPlus P k a + inclPlus P k b * t) = inclPlus P k (a ^ 2 - (1 ⊗ₜ d) * b ^ 2) := by
    intro a b
    have e1 : involBase P k t = -t := by simp [t, involBase, invol_theta P hθ, TensorProduct.tmul_neg]
    have e2 : inclPlus P k (1 ⊗ₜ d) = t * t := by simp [t, inclPlus, hd]
    simp only [map_add, map_mul, map_sub, map_pow, involBase_inclPlus, e1, e2]
    ring
  constructor
  · rintro ⟨c, hc⟩
    have hc' : (c : k ⊗[(maximalRealSubfield E)] Fld P) * involBase P k c = inclPlus P k x := congrArg Units.val hc
    obtain ⟨a, b, h⟩ : ∃ a b, (c : k ⊗[(maximalRealSubfield E)] Fld P) = inclPlus P k a + inclPlus P k b * t := by
      generalize (c : k ⊗[(maximalRealSubfield E)] Fld P) = z
      induction z using TensorProduct.induction_on with
      | zero => exact ⟨0, 0, by simp⟩
      | tmul s y =>
        obtain ⟨a, b, rfl⟩ := exists_add_mul P h0 hθ y
        exact ⟨s ⊗ₜ a, s ⊗ₜ b, by simp [t, inclPlus, TensorProduct.tmul_add]⟩
      | add y z hy hz =>
        obtain ⟨a, b, rfl⟩ := hy
        obtain ⟨a', b', rfl⟩ := hz
        exact ⟨a + a', b + b', by simp only [map_add]; ring⟩
    have hi : Function.Injective (inclPlus P k) :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := k) (plus P).val.toLinearMap
        Subtype.val_injective
    exact ⟨a, b, hi (by rw [← hc', h, key])⟩
  · rintro ⟨a, b, h⟩
    have hu : IsUnit (inclPlus P k a + inclPlus P k b * t) :=
      isUnit_of_mul_isUnit_left (by rw [key, ← h]; exact x.isUnit.map _)
    exact ⟨hu.unit, Units.ext ((key a b).trans (congrArg _ h.symm))⟩

end Imaginary

section Gram

variable (B : Module.Basis (Fin r) E (Fld P)) (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]

def gram (x : k ⊗[(maximalRealSubfield E)] plus P) : Matrix (Fin r) (Fin r) (k ⊗[(maximalRealSubfield E)] E) :=
  Matrix.of fun i j => traceForm P k x (1 ⊗ₜ B i) (1 ⊗ₜ B j)

def gramRat (t : plus P) : Matrix (Fin r) (Fin r) E :=
  Matrix.of fun i j => Algebra.trace E (Fld P) (t * B i * invol P (B j))

theorem gram_tmul (t : plus P) :
    gram P B k (1 ⊗ₜ t) = (gramRat P B t).map fun e => (1 : k) ⊗ₜ[(maximalRealSubfield E)] e := by
  ext i j
  simp [gram, gramRat, traceForm, traceBase, inclPlus, involBase]

theorem conj_trace (y : Fld P) :
    IsCMField.complexConj E (Algebra.trace E (Fld P) y) = Algebra.trace E (Fld P) (invol P y) := by
  let σ : Fld P ≃+* Fld P :=
    { (invol P).toRingHom with
      invFun := invol P, left_inv := invol_invol P, right_inv := invol_invol P }
  have := Algebra.trace_eq_of_equiv_equiv (IsCMField.complexConj E).toRingEquiv σ
    (RingHom.ext fun e => (invol_algebraMap P e).symm) y
  rw [this]
  exact (IsCMField.complexConj E).apply_symm_apply _

theorem gramRat_herm (t : plus P) (a b : Fin r) :
    IsCMField.complexConj E (gramRat P B t a b) = gramRat P B t b a := by
  simp only [gramRat, Matrix.of_apply, conj_trace, map_mul, invol_coe, invol_invol, mul_right_comm]

theorem traceBase_inclBase_mul (e : k ⊗[(maximalRealSubfield E)] E) (y : k ⊗[(maximalRealSubfield E)] Fld P) :
    traceBase P k (inclBase P k e * y) = e * traceBase P k y := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, add_mul, ha, hb]
  | tmul a e =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, mul_add, ha, hb]
    | tmul b y => simp [traceBase, inclBase, ← Algebra.smul_def]

theorem involBase_inclBase (e : k ⊗[(maximalRealSubfield E)] E) :
    involBase P k (inclBase P k e) = inclBase P k (ccBase E k e) := by
  induction e using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a e => simp [involBase, inclBase, invol_algebraMap]

theorem exists_coord : ∃ ψ : (k ⊗[(maximalRealSubfield E)] Fld P) ≃+ (Fin r → k ⊗[(maximalRealSubfield E)] E),
    (∀ e y, ψ (inclBase P k e * y) = e • ψ y) ∧
      ∀ y, y = ∑ i, inclBase P k (ψ y i) * 1 ⊗ₜ B i := by
  let ψ := ((B.equivFun.restrictScalars (maximalRealSubfield E)).baseChange (maximalRealSubfield E) k _ _ ≪≫ₗ
    TensorProduct.piRight (maximalRealSubfield E) k k fun _ : Fin r => E).toAddEquiv
  have h : ∀ a y i, ψ (a ⊗ₜ y) i = a ⊗ₜ B.repr y i := fun _ _ _ => rfl
  refine ⟨ψ, fun e y => ?_, fun y => ?_⟩
  · induction e using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, add_mul, ha, hb, add_smul]
    | tmul a e =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add, mul_add, ha, hb, smul_add]
      | tmul b y =>
        funext i
        simp [inclBase, ← Algebra.smul_def, h]
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [map_add, Pi.add_apply, add_mul, Finset.sum_add_distrib, ← ha, ← hb]
    | tmul b y =>
      conv_lhs => rw [← B.sum_repr y, TensorProduct.tmul_sum]
      simp [inclBase, ← Algebra.smul_def, h]

theorem gramForm_eq (G : Matrix (Fin r) (Fin r) E) (u u' : Fin r → k ⊗[(maximalRealSubfield E)] E) :
    gramForm k G u u' = u ⬝ᵥ (G.map fun e => (1 : k) ⊗ₜ[(maximalRealSubfield E)] e) *ᵥ fun j => ccBase E k (u' j) := by
  simp only [gramForm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, Matrix.map_apply]

theorem isometric_iff (G : Matrix (Fin r) (Fin r) E) (x : k ⊗[(maximalRealSubfield E)] plus P) :
    Isometric P k G x ↔ ∃ Q : Matrix (Fin r) (Fin r) (k ⊗[(maximalRealSubfield E)] E), IsUnit Q.det ∧
      gram P B k x = Qᵀ * G.map (fun e => (1 : k) ⊗ₜ[(maximalRealSubfield E)] e) * Q.map (ccBase E k) := by
  obtain ⟨ψ, h1, h2⟩ := exists_coord P B k
  constructor
  · rintro ⟨φ, g1, g2⟩
    refine ⟨Matrix.of fun a i => φ (1 ⊗ₜ B i) a, ?_, ?_⟩
    · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_surjective_iff_isUnit]
      intro u
      obtain ⟨y, rfl⟩ := φ.surjective u
      refine ⟨ψ y, ?_⟩
      conv_rhs => rw [h2 y]
      funext a
      simp only [map_sum, g1, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    · ext i j
      simp only [gram, Matrix.of_apply, ← g2, gramForm, Matrix.mul_apply, Matrix.transpose_apply,
        Matrix.map_apply, Finset.sum_mul]
      exact Finset.sum_comm
  · rintro ⟨Q, hQ, h⟩
    rw [← Matrix.isUnit_iff_isUnit_det] at hQ
    refine ⟨ψ.trans (LinearEquiv.ofBijective (Matrix.toLin' Q) ⟨Matrix.mulVec_injective_of_isUnit hQ,
      Matrix.mulVec_surjective_iff_isUnit.2 hQ⟩).toAddEquiv, fun e y => ?_, fun y y' => ?_⟩
    · change Q *ᵥ ψ _ = e • Q *ᵥ ψ y
      rw [h1, Matrix.mulVec_smul]
    · change gramForm k G (Q *ᵥ ψ y) (Q *ᵥ ψ y') = _
      have e : (fun b => ccBase E k ((Q *ᵥ ψ y') b)) = Q.map (ccBase E k) *ᵥ fun b => ccBase E k (ψ y' b) := by
        funext b
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
      rw [gramForm_eq, e, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        Matrix.mulVec_mulVec, ← h]
      conv_rhs => rw [h2 y, h2 y']
      simp only [traceForm, map_sum, map_mul, involBase_inclBase, Finset.mul_sum, Finset.sum_mul,
        dotProduct, Matrix.mulVec, gram, Matrix.of_apply]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_comm _ (ccBase E k _), ← traceBase_inclBase_mul, ← traceBase_inclBase_mul]
      congr 1
      ring

theorem isometric_tmul_iff (G : Matrix (Fin r) (Fin r) E) (t : plus P) :
    Isometric P k G (1 ⊗ₜ t) ↔ CongrOver k G (gramRat P B t) := by
  rw [isometric_iff P B, gram_tmul]
  rfl

variable {B} {b : Module.Basis (Fin r) (maximalRealSubfield E) (plus P)} (hB : ∀ i, B i = b i)

include hB

theorem det_gram (x : k ⊗[(maximalRealSubfield E)] plus P) :
    (gram P B k x).det = algebraMap k _ (Algebra.norm k x) * (1 : k) ⊗ₜ[(maximalRealSubfield E)] (gramRat P B 1).det := by
  let c := Algebra.TensorProduct.basis k b
  have h : gram P B k x = ((algebraMap k _).mapMatrix (Algebra.leftMulMatrix c x))ᵀ * gram P B k 1 := by
    ext i j
    have e : inclPlus P k x * 1 ⊗ₜ B i = ∑ l, c.repr (x * c i) l • ((1 : k) ⊗ₜ[(maximalRealSubfield E)] B l) := by
      have hc : ∀ l, inclPlus P k (c l) = 1 ⊗ₜ B l := fun l => by simp [c, inclPlus, hB]
      simp only [← hc, ← map_smul, ← map_sum, c.sum_repr, map_mul]
    simp only [gram, traceForm, Matrix.of_apply, e, Matrix.mul_apply, Matrix.transpose_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Finset.sum_mul,
      map_sum, smul_mul_assoc, map_smul, map_one, one_mul, ← Algebra.smul_def]
  rw [h, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, ← Algebra.norm_eq_matrix_det,
    Algebra.TensorProduct.one_def, gram_tmul]
  congr 1
  exact (RingHom.map_det (Algebra.TensorProduct.includeRight :
    E →ₐ[(maximalRealSubfield E)] k ⊗[(maximalRealSubfield E)] E).toRingHom _).symm

theorem det_gramRat_one_ne_zero : (gramRat P B 1).det ≠ 0 := by
  have : gramRat P B 1 = Algebra.traceMatrix E B := by
    ext i j
    simp [gramRat, hB, invol_coe]
  rw [this]
  exact Algebra.discr_not_zero_of_basis E B

theorem det_gramRat_ne_zero {t : plus P} (ht : t ≠ 0) : (gramRat P B t).det ≠ 0 := by
  intro h
  have h1 := det_gram P (maximalRealSubfield E) hB (1 ⊗ₜ t)
  have h2 : (gram P B (maximalRealSubfield E) (1 ⊗ₜ t)).det = (1 : (maximalRealSubfield E)) ⊗ₜ[(maximalRealSubfield E)] (gramRat P B t).det := by
    rw [gram_tmul]
    exact (RingHom.map_det (Algebra.TensorProduct.includeRight :
      E →ₐ[(maximalRealSubfield E)] (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] E).toRingHom _).symm
  rw [h2, h, TensorProduct.tmul_zero] at h1
  refine IsUnit.ne_zero (IsUnit.mul ?_ ?_) h1.symm
  · exact ((ht.isUnit.map (Algebra.TensorProduct.includeRight :
      plus P →ₐ[(maximalRealSubfield E)] (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] plus P)).map (Algebra.norm (maximalRealSubfield E))).map _
  · exact (det_gramRat_one_ne_zero P hB).isUnit.map (Algebra.TensorProduct.includeRight :
      E →ₐ[(maximalRealSubfield E)] (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] E)

end Gram

section Congr

variable {G G' : Matrix (Fin r) (Fin r) E}

theorem congr_map {A C : Type} [CommRing A] [Algebra (maximalRealSubfield E) A] [Field C] (f : A ⊗[(maximalRealSubfield E)] E →+* C)
    (τ : E →+* C) (σ : C → C) (h1 : ∀ e, f (1 ⊗ₜ e) = τ e) (h2 : ∀ z, f (ccBase E A z) = σ (f z))
    (h : CongrOver A G G') :
    ∃ Q : Matrix (Fin r) (Fin r) C, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map σ := by
  obtain ⟨Q, hQ, h⟩ := h
  refine ⟨Q.map f, ?_, ?_⟩
  · rw [show (Q.map f).det = f Q.det from (RingHom.map_det f Q).symm]
    exact (hQ.map f).ne_zero
  · have := congrArg (fun M => M.map f) h
    simp only [Matrix.map_mul, Matrix.map_map, Function.comp_def, h1, h2] at this
    exact this

theorem congr_of_self (h : CongrOver (maximalRealSubfield E) G G') :
    ∃ Q : Matrix (Fin r) (Fin r) E, Q.det ≠ 0 ∧ G' = Qᵀ * G * Q.map ReciprocityTheory.ChartRestriction.G.FD.cc :=
  congr_map (Algebra.TensorProduct.lid (maximalRealSubfield E) E).toRingEquiv.toRingHom (RingHom.id E) _
    (fun e => one_smul (maximalRealSubfield E) e) (fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
      | tmul a e => exact ((IsCMField.complexConj E).toLinearEquiv.map_smul a e).symm
      | add a b ha hb =>
        simp only [ReciprocityTheory.ChartRestriction.G.FD.cc, map_add] at ha hb ⊢
        rw [ha, hb]) h

theorem congr_complex (h : ∀ w : InfinitePlace (maximalRealSubfield E), CongrOver w.Completion G G') (τ : E →+* ℂ) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ G'.map τ = Qᵀ * G.map τ * Q.map conj := by
  let ρ := τ.comp (algebraMap (maximalRealSubfield E) E)
  let w := InfinitePlace.mk ρ
  have hw : w.IsReal := IsTotallyReal.isReal w
  letI : Algebra (maximalRealSubfield E) ℂ := ρ.toAlgebra
  let g : w.Completion →ₐ[(maximalRealSubfield E)] ℂ :=
    ⟨InfinitePlace.Completion.extensionEmbedding w, fun a =>
      (InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ a)).trans
        (DFunLike.congr_fun (InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 hw)) a)⟩
  have hg : ∀ a, conj (g a) = g a := fun a => by
    have : g a = (InfinitePlace.Completion.extensionEmbeddingOfIsReal hw a : ℂ) :=
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw a).symm
    rw [this, Complex.conj_ofReal]
  let f := (Algebra.TensorProduct.productMap g (⟨τ, fun _ => rfl⟩ : E →ₐ[(maximalRealSubfield E)] ℂ)).toRingHom
  have hf : ∀ a e, f (a ⊗ₜ e) = g a * τ e := fun _ _ => rfl
  refine congr_map f τ _ (fun e => by rw [hf, map_one, one_mul]) (fun z => ?_) (h w)
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    rw [Algebra.TensorProduct.map_tmul, hf, hf, map_mul, hg]
    exact congrArg _ (IsCMField.complexEmbedding_complexConj E τ e)
  | add a b ha hb => simp only [map_add, ha, hb]

end Congr

def unitOf (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k] : (plus P)ˣ →* (k ⊗[(maximalRealSubfield E)] plus P)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : plus P →ₐ[(maximalRealSubfield E)] k ⊗[(maximalRealSubfield E)] plus P).toMonoidHom

theorem exists_unitOf (q : NormClass P (maximalRealSubfield E)) : ∃ t, (unitOf P (maximalRealSubfield E) t : NormClass P (maximalRealSubfield E)) = q := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  refine ⟨Units.map (Algebra.TensorProduct.lid (maximalRealSubfield E) (plus P)).toMonoidHom x, congrArg _ (Units.ext ?_)⟩
  exact (Algebra.TensorProduct.lid (maximalRealSubfield E) (plus P)).symm_apply_apply x

theorem toLocal_unitOf (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k] (t : (plus P)ˣ) :
    toLocal P k (unitOf P (maximalRealSubfield E) t) = unitOf P k t :=
  congrArg (fun x : (k ⊗[(maximalRealSubfield E)] plus P)ˣ => (x : NormClass P k)) (Units.ext (by
    change toLocalPlus P k (1 ⊗ₜ (t : plus P)) = 1 ⊗ₜ (t : plus P)
    simp [toLocalPlus]))

theorem mem_classes_iff (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k] (G : Matrix (Fin r) (Fin r) E)
    (x : (k ⊗[(maximalRealSubfield E)] plus P)ˣ) : (x : NormClass P k) ∈ classes P k G ↔ Isometric P k G x := by
  refine ⟨?_, fun h => ⟨x, rfl, h⟩⟩
  rintro ⟨y, hy, h⟩
  have := Isometric.of_norm P k (QuotientGroup.eq.1 hy) h
  rwa [mul_inv_cancel_left] at this

theorem norm_div_mem {B : Module.Basis (Fin r) E (Fld P)} {b : Module.Basis (Fin r) (maximalRealSubfield E) (plus P)}
    (hB : ∀ i, B i = b i) (k : Type) [Field k] [Algebra (maximalRealSubfield E) k] {G : Matrix (Fin r) (Fin r) E}
    {δ : (maximalRealSubfield E)ˣ} (hδ : ((δ : (maximalRealSubfield E)) : E) * (gramRat P B 1).det = G.det)
    {x : (k ⊗[(maximalRealSubfield E)] plus P)ˣ} (h : Isometric P k G x) :
    Units.map (Algebra.norm k : _ →* _) x / QuadSymbol.toUnits (maximalRealSubfield E) k δ ∈ normGroup (maximalRealSubfield E) E k := by
  obtain ⟨Q, -, h⟩ := (isometric_iff P B k G x).1 h
  let ι : E →+* k ⊗[(maximalRealSubfield E)] E := Algebra.TensorProduct.includeRight.toRingHom
  have h1 : (gram P B k x).det = Q.det * ι G.det * ccBase E k Q.det := by
    rw [RingHom.map_det, AlgHom.map_det, ← Matrix.det_transpose Q, ← Matrix.det_mul, ← Matrix.det_mul]
    exact congrArg Matrix.det h
  have h2 : ι ((δ : (maximalRealSubfield E)) : E) = algebraMap k _ (algebraMap (maximalRealSubfield E) k δ) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.algebraMap_apply' (δ : (maximalRealSubfield E))).symm
  rw [det_gram P k hB, ← hδ, map_mul, h2] at h1
  refine mem_normGroup_iff.2 ⟨Q.det, ?_⟩
  rw [Units.val_div_eq_div_val, eq_div_iff (Units.ne_zero _)]
  refine (algebraMap k (k ⊗[(maximalRealSubfield E)] E)).injective ?_
  rw [map_mul, GlobalTheory.Published.algebraMap_norm_tensor]
  refine (((det_gramRat_one_ne_zero P hB).isUnit.map ι).mul_left_inj).1 (Eq.trans ?_ h1.symm)
  change Q.det * ccBase E k Q.det * algebraMap k _ (algebraMap (maximalRealSubfield E) k δ) * _ = _
  ring

theorem congrOver_of_mk_eq (B : Module.Basis (Fin r) E (Fld P)) (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k]
    {G : Matrix (Fin r) (Fin r) E} {t : (plus P)ˣ} {s : (k ⊗[(maximalRealSubfield E)] plus P)ˣ}
    (h : (unitOf P k t : NormClass P k) = s) (hs : Isometric P k G s) : CongrOver k G (gramRat P B t) :=
  (isometric_tmul_iff P B k G t).1 ((mem_classes_iff P k G (unitOf P k t)).1 ⟨s, h.symm, hs⟩)

theorem mapsTo (G : Matrix (Fin r) (Fin r) E) :
    Set.MapsTo (diagonal P) (classes P (maximalRealSubfield E) G) (adelicClasses P G) := by
  intro q hq
  let B := Module.finBasisOfFinrankEq E (Fld P) (finrank_fld P)
  obtain ⟨t, rfl⟩ := exists_unitOf P q
  have h := congr_of_self ((isometric_tmul_iff P B _ G t).1 ((mem_classes_iff P _ G _).1 hq))
  have key : ∀ (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k],
      toLocal P k (unitOf P (maximalRealSubfield E) t) ∈ classes P k G := fun k _ _ => by
    rw [toLocal_unitOf, mem_classes_iff]
    exact (isometric_tmul_iff P B k G t).2 (CongrOver.of_congr h)
  refine ⟨fun v => key _, fun w => key _, ((finite_not_integral (F := (maximalRealSubfield E)) (t : plus P)).union
    (finite_not_integral (F := (maximalRealSubfield E)) ((t⁻¹ : (plus P)ˣ) : plus P))).subset fun v hv => ?_⟩
  by_contra hn
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn
  exact hv ⟨unitOf P _ t, hn.1, hn.2, (toLocal_unitOf P _ t).symm⟩

section Main

variable {θ : E} (h0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ) {d : plus P}
  (hd : (d : Fld P) = algebraMap E _ θ * algebraMap E _ θ)

include h0 hθ

theorem isQuadraticExtension : Algebra.IsQuadraticExtension (plus P) (Fld P) := by
  obtain ⟨e, -⟩ := exists_basis_theta P h0 hθ
  exact { finrank_eq_two' := by rw [Module.finrank_eq_card_basis e, Fintype.card_fin] }

include hd

theorem diagonal_injective : Function.Injective (diagonal P) := by
  intro q q' h
  obtain ⟨e, e0, e1⟩ := exists_basis_theta P h0 hθ
  have := isQuadraticExtension P h0 hθ
  have e2 : e 1 * e 1 = algebraMap _ _ d := by rw [e1]; exact hd.symm
  obtain ⟨t, rfl⟩ := exists_unitOf P q
  obtain ⟨t', rfl⟩ := exists_unitOf P q'
  have key : ∀ (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k],
      toLocal P k (unitOf P (maximalRealSubfield E) t) = toLocal P k (unitOf P (maximalRealSubfield E) t') →
      IsValue (1 ⊗ₜ d) (1 ⊗ₜ ((t⁻¹ * t' : (plus P)ˣ) : plus P) : k ⊗[(maximalRealSubfield E)] plus P) := fun k _ _ h => by
    rw [toLocal_unitOf, toLocal_unitOf, QuotientGroup.eq, ← map_inv, ← map_mul] at h
    exact (mem_norms_iff P h0 hθ k hd _).1 h
  obtain ⟨u, v, huv⟩ := form_of_local (F := (maximalRealSubfield E)) e e0 e2 (t⁻¹ * t')
    (fun v => key _ (congrFun (congrArg Prod.fst h) v)) fun w => key _ (congrFun (congrArg Prod.snd h) w)
  rw [QuotientGroup.eq, ← map_inv, ← map_mul, mem_norms_iff P h0 hθ _ hd]
  refine ⟨1 ⊗ₜ u, 1 ⊗ₜ v, ?_⟩
  change (1 : (maximalRealSubfield E)) ⊗ₜ[(maximalRealSubfield E)] ((t⁻¹ * t' : (plus P)ˣ) : plus P) = _
  rw [huv]
  simp [TensorProduct.tmul_sub]

theorem isValue_of_mk_eq (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k] {u x : (k ⊗[(maximalRealSubfield E)] plus P)ˣ}
    (h : (u : NormClass P k) = x) (hu : IsValue (1 ⊗ₜ d) u.1) : IsValue (1 ⊗ₜ d) x.1 := by
  have h3 := mul_mem ((mem_norms_iff P h0 hθ k hd u).2 hu) (QuotientGroup.eq.1 h)
  rw [mul_inv_cancel_left] at h3
  exact (mem_norms_iff P h0 hθ k hd x).1 h3

theorem mk_unitOf_eq (k : Type) [CommRing k] [Algebra (maximalRealSubfield E) k] {t : (plus P)ˣ} {s : (k ⊗[(maximalRealSubfield E)] plus P)ˣ}
    (h : IsValue (1 ⊗ₜ d) ((s : k ⊗[(maximalRealSubfield E)] plus P) * 1 ⊗ₜ ((t : plus P)⁻¹))) :
    (unitOf P k t : NormClass P k) = s := by
  rw [QuotientGroup.eq, mem_norms_iff P h0 hθ k hd, mul_comm, ← map_inv]
  rwa [← Units.val_inv_eq_inv_val] at h

theorem finite_not_isValue
    (x : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] plus P)ˣ)
    (hu : {v | ¬ IsUnitClass P v (x v)}.Finite) : {v | ¬ IsValue (1 ⊗ₜ d) (x v).1}.Finite := by
  have hd0 : d ≠ 0 := fun h =>
    mul_self_ne_zero.2 ((map_ne_zero (algebraMap E (Fld P))).2 h0) (hd.symm.trans (congrArg Subtype.val h))
  refine (hu.union (finite_not_form (F := (maximalRealSubfield E)) hd0)).subset fun v hv => ?_
  by_cases h : IsUnitClass P v (x v)
  · obtain ⟨u, u1, u2, u3⟩ := h
    exact Or.inr ⟨u, u1, u2, fun h => hv (isValue_of_mk_eq P h0 hθ hd _ u3 h)⟩
  · exact Or.inl h

theorem exists_unitOf_eq {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, IsCMField.complexConj E (G a b) = G b a)
    (hG0 : G.det ≠ 0)
    (x : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (v.adicCompletion (maximalRealSubfield E) ⊗[(maximalRealSubfield E)] plus P)ˣ)
    (y : ∀ v : InfinitePlace (maximalRealSubfield E), (v.Completion ⊗[(maximalRealSubfield E)] plus P)ˣ)
    (hx : ∀ v, Isometric P _ G (x v).1) (hy : ∀ v, Isometric P _ G (y v).1)
    (hu : {v | ¬ IsUnitClass P v (x v)}.Finite) :
    ∃ t : (plus P)ˣ, (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)),
        (unitOf P (v.adicCompletion (maximalRealSubfield E)) t : NormClass P (v.adicCompletion (maximalRealSubfield E))) = x v) ∧
      ∀ v : InfinitePlace (maximalRealSubfield E), (unitOf P v.Completion t : NormClass P v.Completion) = y v := by
  obtain ⟨e, e0, e1⟩ := exists_basis_theta P h0 hθ
  obtain ⟨b, B, hB⟩ := exists_bases P h0 hθ
  have := isQuadraticExtension P h0 hθ
  have e2 : e 1 * e 1 = algebraMap _ _ d := by rw [e1]; exact hd.symm
  have hT := det_gramRat_one_ne_zero P hB
  have hm : G.det / (gramRat P B 1).det ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
    exact congrArg₂ (· / ·) (GlobalTheory.Published.cc_det_of_herm hG)
      (GlobalTheory.Published.cc_det_of_herm (gramRat_herm P B 1))
  obtain ⟨δ, hδ⟩ : ∃ δ : (maximalRealSubfield E)ˣ, ((δ : (maximalRealSubfield E)) : E) * (gramRat P B 1).det = G.det :=
    ⟨Units.mk0 ⟨_, hm⟩ fun h => div_ne_zero hG0 hT (congrArg Subtype.val h), div_mul_cancel₀ _ hT⟩
  have n1 := fun v => norm_div_mem P hB _ hδ (hx v)
  have n2 := fun w => norm_div_mem P hB _ hδ (hy w)
  obtain ⟨t, tf, ti⟩ := exists_global (F := (maximalRealSubfield E)) (E := E) e e0 e2 (adjoin_eq_top P h0 hθ) x y
    (finite_not_isValue P h0 hθ hd x hu) δ n1 n2
  exact ⟨t, fun v => mk_unitOf_eq P h0 hθ hd _ (tf v), fun v => mk_unitOf_eq P h0 hθ hd _ (ti v)⟩

theorem surjOn {G : Matrix (Fin r) (Fin r) E} (hG : ∀ a b, IsCMField.complexConj E (G a b) = G b a)
    (hG0 : G.det ≠ 0) : Set.SurjOn (diagonal P) (classes P (maximalRealSubfield E) G) (adelicClasses P G) := by
  rintro z ⟨hf, hi, hu⟩
  choose x hx hx' using hf
  choose y hy hy' using hi
  obtain ⟨b, B, hB⟩ := exists_bases P h0 hθ
  obtain ⟨t, tf, ti⟩ := exists_unitOf_eq P h0 hθ hd hG hG0 x y hx' hy' (by simpa only [hx] using hu)
  have h1 := congr_of_local hG (gramRat_herm P B t) hG0 (det_gramRat_ne_zero P hB t.ne_zero)
    (fun v => congrOver_of_mk_eq P B _ (tf v) (hx' v))
    (congr_complex fun w => congrOver_of_mk_eq P B _ (ti w) (hy' w))
  have h2 : Isometric P (maximalRealSubfield E) G (unitOf P (maximalRealSubfield E) t).1 :=
    (isometric_tmul_iff P B (maximalRealSubfield E) G t).2 (CongrOver.of_congr h1)
  refine ⟨unitOf P (maximalRealSubfield E) t, (mem_classes_iff P (maximalRealSubfield E) G _).2 h2, Prod.ext (funext fun v => ?_)
    (funext fun w => ?_)⟩
  · exact (toLocal_unitOf P _ t).trans ((tf v).trans (hx v))
  · exact (toLocal_unitOf P _ t).trans ((ti w).trans (hy w))

end Main

theorem rationalEqAdelic : RationalEqAdelic := by
  intro E _ _ _ _ r G hG hG0 P
  obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
  let d : plus P := ⟨algebraMap E _ θ * algebraMap E _ θ, by
    change invol P _ = _
    rw [map_mul, invol_theta P hθ, neg_mul_neg]
    rfl⟩
  exact ⟨mapsTo P G, (diagonal_injective P h0 hθ (d := d) rfl).injOn, surjOn P h0 hθ (d := d) rfl hG hG0⟩

end GlobalTheory.TraceClasses

end
