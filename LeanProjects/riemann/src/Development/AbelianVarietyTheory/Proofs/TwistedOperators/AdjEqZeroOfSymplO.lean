import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipMean

section Ring

variable {K S : Type} [CommRing K] [Ring S] [Algebra K S] {p q x : S}

def levi (t t' : K) (p q : S) : S := 1 + (t - 1) • p + (t' - 1) • q

theorem levi_mul_swap (hpp : p * p = p) (hqq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0) {t t' : K}
    (h : t * t' = 1) : levi t t' p q * levi t' t p q = 1 := by
  simp only [levi, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, hpp, hqq, hpq, hqp,
    smul_zero, add_zero, zero_add, smul_smul]
  match_scalars <;> first | ring1 | linear_combination h | linear_combination -h

theorem levi_conj (hpp : p * p = p) (hqq : q * q = q) (hqp : q * p = 0) {t t' : K}
    (h : t * t' = 1) (hx : x = p * x * q) :
    levi t t' p q * (1 + x) = (1 + (t * t) • x) * levi t t' p q := by
  have h1 : p * x = x := calc
    p * x = p * (p * x * q) := by rw [← hx]
    _ = p * x * q := by rw [← mul_assoc, ← mul_assoc, hpp]
    _ = x := hx.symm
  have h2 : x * q = x := calc
    x * q = p * x * q * q := by rw [← hx]
    _ = p * x * q := by rw [mul_assoc, hqq]
    _ = x := hx.symm
  have h3 : q * x = 0 := calc
    q * x = q * (p * x * q) := by rw [← hx]
    _ = 0 := by rw [← mul_assoc, ← mul_assoc, hqp, zero_mul, zero_mul]
  have h4 : x * p = 0 := calc
    x * p = p * x * q * p := by rw [← hx]
    _ = 0 := by rw [mul_assoc, hqp, mul_zero]
  simp only [levi, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, h1, h2, h3, h4,
    smul_zero, add_zero, zero_add, smul_smul]
  match_scalars <;> first | ring1 | linear_combination t * h | linear_combination -t * h

theorem one_add_pow (hx : x * x = 0) (k : ℕ) : (1 + x) ^ k = 1 + (k : K) • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih]
    simp only [add_mul, mul_add, smul_mul_assoc, one_mul, mul_one, hx, smul_zero, add_zero]
    push_cast
    match_scalars <;> ring1

theorem levi_two_conj (hpp : p * p = p) (hqq : q * q = q) (hpq : p * q = 0) (hqp : q * p = 0) (h1 : x * p = 0)
    (h2 : q * x = 0) (h3 : x = p * x + x * q - p * x * q) {t h : K} (ht : t = 2) (hh : 2 * h = 1) :
    (p * ((2 : K) • (p * x * q) - x * x) * q = (2 : K) • (p * x * q) - x * x) ∧
    levi t h p q * (1 + x) = (1 + x) * (1 + x) * (1 + ((2 : K) • (p * x * q) - x * x)) * levi t h p q := by
  subst ht
  have a1 : x * (p * x) = 0 := by rw [← mul_assoc, h1, zero_mul]
  have a2 : x * (p * (x * q)) = 0 := by rw [← mul_assoc, h1, zero_mul]
  have e1 : x * (x * q) = x * x := by
    have : x * x = x * (p * x + x * q - p * x * q) := by rw [← h3]
    rw [this, mul_sub, mul_add, a1, mul_assoc p, a2, zero_add, sub_zero]
  have b1 : x * (q * x) = 0 := by rw [h2, mul_zero]
  have b2 : p * (x * (q * x)) = 0 := by rw [b1, mul_zero]
  have e2 : p * (x * x) = x * x := by
    have : x * x = (p * x + x * q - p * x * q) * x := by rw [← h3]
    rw [this, sub_mul, add_mul, mul_assoc x q, b1, mul_assoc p x x, mul_assoc (p * x), mul_assoc p, b2, add_zero, sub_zero,
      ← mul_assoc p p, hpp]
  have e3 : x * (x * x) = 0 := by rw [← e2, ← mul_assoc, h1, zero_mul]
  have h5 : p * (x * q) = p * x + x * q - x := by
    have := h3
    rw [mul_assoc, eq_sub_iff_add_eq] at this
    exact eq_sub_of_add_eq' this
  have l1 : ∀ z, p * (p * z) = p * z := fun z => by rw [← mul_assoc, hpp]
  have l2 : ∀ z, q * (q * z) = q * z := fun z => by rw [← mul_assoc, hqq]
  have l3 : ∀ z, p * (q * z) = 0 := fun z => by rw [← mul_assoc, hpq, zero_mul]
  have l4 : ∀ z, q * (p * z) = 0 := fun z => by rw [← mul_assoc, hqp, zero_mul]
  have l5 : ∀ z, x * (p * z) = 0 := fun z => by rw [← mul_assoc, h1, zero_mul]
  have l6 : ∀ z, q * (x * z) = 0 := fun z => by rw [← mul_assoc, h2, zero_mul]
  constructor
  · simp only [mul_assoc, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, l1, hpp, l2, hqq, e1, e2]
  · simp only [levi, mul_assoc, mul_add, add_mul, mul_sub, sub_mul, smul_mul_assoc, mul_smul_comm, one_mul, mul_one,
      l1, l2, l3, l4, l5, l6, hpp, hqq, hpq, hqp, h1, h2, e1, e2, e3, smul_zero, add_zero, zero_add, sub_zero, smul_smul,
      smul_add, smul_sub]
    rw [h5]
    simp only [mul_zero, zero_mul, smul_zero, add_zero, zero_add, sub_zero]
    match_scalars <;> first | ring1 | linear_combination hh | linear_combination -hh | linear_combination 2 * hh | linear_combination -2 * hh

theorem core_conj {G : Type} [Group G] (φ : G →* S) (hφ : Function.Injective φ) (hpp : p * p = p) (hqq : q * q = q)
    (hpq : p * q = 0) (hqp : q * p = 0) (h1 : x * p = 0) (h2 : q * x = 0) (h3 : x = p * x + x * q - p * x * q)
    {g a b : G} (hg : φ g = 1 + x) {t t' u u' : K} (ht : t = 2) (htt : 2 * t' = 1) (hu : u = 3) (huu : 3 * u' = 1)
    (ha : φ a = levi t t' p q) (hb : φ b = levi u u' p q) :
    a * ((g * g)⁻¹ * (a * g * a⁻¹)) * a⁻¹ = ((g * g)⁻¹ * (a * g * a⁻¹)) ^ 4 ∧
    b * ((g * g)⁻¹ * (a * g * a⁻¹)) * b⁻¹ = ((g * g)⁻¹ * (a * g * a⁻¹)) ^ 9 := by
  obtain ⟨hy, hc⟩ := levi_two_conj hpp hqq hpq hqp h1 h2 h3 ht htt
  generalize (2 : K) • (p * x * q) - x * x = y at hy hc
  generalize hz : (g * g)⁻¹ * (a * g * a⁻¹) = z
  have can : ∀ (v w : G) (X Y : S), φ v * X * φ w = φ v * Y * φ w → X = Y := fun v w X Y e => by
    have e1 : ∀ Z : S, φ v⁻¹ * (φ v * Z * φ w) * φ w⁻¹ = Z := fun Z => by
      have i1 : φ v⁻¹ * φ v = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
      have i2 : φ w * φ w⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      rw [mul_assoc, mul_assoc, i2, mul_one, ← mul_assoc, i1, one_mul]
    rw [← e1 X, e, e1]
  have mz : φ z = 1 + y := by
    refine can (g * g) a _ _ ?_
    have e : g * g * z * a = a * g := by rw [← hz]; group
    have e' := congrArg φ e
    simp only [map_mul, hg, ha] at e' ⊢
    rw [e', hc]
  have yy : y * y = 0 := calc
    y * y = p * y * q * (p * y * q) := by rw [hy]
    _ = p * y * (q * p) * y * q := by simp only [mul_assoc]
    _ = 0 := by rw [hqp]; simp
  have pw : ∀ k : ℕ, φ (z ^ k) = 1 + (k : K) • y := fun k => by rw [map_pow, mz, one_add_pow (K := K) yy]
  have conj : ∀ (c : G) {v v' : K} (k : ℕ), φ c = levi v v' p q → v * v' = 1 → v * v = (k : K) → c * z * c⁻¹ = z ^ k := by
    intro c v v' k hcv hvv hk
    rw [mul_inv_eq_iff_eq_mul]
    apply hφ
    rw [map_mul, map_mul, pw, mz, hcv, levi_conj hpp hqq hqp hvv hy.symm, hk]
  exact ⟨conj a 4 ha (by rw [ht]; exact htt) (by rw [ht]; norm_num),
    conj b 9 hb (by rw [hu]; exact huu) (by rw [hu]; norm_num)⟩

end Ring

theorem eq_zero_of_trace_mul {F E R : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] [CommRing R] [Algebra F R] (z : R ⊗[F] E)
    (h : ∀ w, Algebra.trace R (R ⊗[F] E) (z * w) = 0) : z = 0 := by
  classical
  let b := Module.finBasis F E
  let b' := (Algebra.traceForm F E).dualBasis (traceForm_nondegenerate F E) b
  have tr : ∀ (a : R) (e : E), Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) = a * algebraMap F R (Algebra.trace F E e) := by
    intro a e
    have h1 : (a ⊗ₜ[F] e : R ⊗[F] E) = a • ((1 : R) ⊗ₜ[F] e) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, smul_eq_mul]
    congr 1
    rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
    congr 1
    ext x
    simp
  have key : ∀ (k) (z : R ⊗[F] E), (Algebra.TensorProduct.basis R b').repr z k =
      Algebra.trace R (R ⊗[F] E) (z * (1 : R) ⊗ₜ[F] b k) := by
    intro k z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, add_mul]
    | tmul a e =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, tr, Algebra.TensorProduct.basis_repr_tmul]
      simp [b', LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  refine (Algebra.TensorProduct.basis R b').ext_elem fun k => ?_
  rw [key, h]; simp

theorem trace_single_mul' {R : Type} [CommRing R] {a b : ℕ} (i : Fin a) (j : Fin b) (w : R)
    (u : Matrix (Fin a) (Fin b) R) : (Matrix.single j i w * u).trace = u i j * w := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.single_apply, ite_and, mul_comm]

section Mean

variable {D : D7} {m n : ℕ}

theorem continuous_smul_Mx (u : AE D) : Continuous fun a : Mx D m n => u • a := by
  obtain ⟨r1, -⟩ := Formalism.IndefR.Eqv.ae_facts (D := D)
  exact continuous_pi fun i => continuous_pi fun j =>
    continuous_const.mul ((continuous_apply j).comp (continuous_apply i))

theorem mean_smul {μ : Measure (Mx D m n)} {𝓕 : Set (Mx D m n)} (h : IsCovolOne (ratMx D m n) μ 𝓕)
    {c : D.host.E} (hc : c ≠ 0) (φ : Mx D m n → ℂ) (hφ : ∀ γ ∈ ratMx D m n, ∀ a, φ (γ + a) = φ a) :
    ∫ a in 𝓕, φ (incA D c • a) ∂μ = ∫ a in 𝓕, φ a ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D m n
  haveI : BorelSpace (Mx D m n) := ⟨rfl⟩
  haveI : Countable (ratMx D m n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hcc : incA D c * incA D c⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hc, map_one]
  have hcc' : incA D c⁻¹ * incA D c = 1 := by rw [mul_comm, hcc]
  let e : Mx D m n ≃+ Mx D m n :=
    { toFun := fun a => incA D c • a
      invFun := fun a => incA D c⁻¹ • a
      left_inv := fun a => by simp only [smul_smul, hcc', one_smul]
      right_inv := fun a => by simp only [smul_smul, hcc, one_smul]
      map_add' := fun a b => smul_add _ a b }
  have he : Continuous e := continuous_smul_Mx _
  have hes : Continuous e.symm := continuous_smul_Mx _
  have hΓ : ∀ x, e x ∈ ratMx D m n ↔ x ∈ ratMx D m n := fun x => by
    refine ⟨fun hx => ?_, fun hx => ratMx_smul c hx⟩
    have := ratMx_smul c⁻¹ hx
    rwa [show incA D c⁻¹ • e x = x from e.symm_apply_apply x] at this
  obtain ⟨hμ, hF, h1⟩ := id h
  let me : Mx D m n ≃ᵐ Mx D m n :=
    { toEquiv := e.toEquiv
      measurable_toFun := he.measurable
      measurable_invFun := hes.measurable }
  have hmp : MeasurePreserving me (μ.map e.symm) μ :=
    (MeasurePreserving.symm me.symm ⟨me.symm.measurable, rfl⟩)
  have hmp' : MeasurePreserving e (μ.map e.symm) μ := hmp
  have hν : (μ.map e.symm).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ e.symm hes (by simpa using he)
  have hF' : IsAddFundamentalDomain (ratMx D m n) (e ⁻¹' 𝓕) (μ.map e.symm) := by
    let f : ratMx D m n → ratMx D m n := fun y => ⟨e.symm y, (hΓ _).1 (by simp)⟩
    have hf : Function.Bijective f := by
      constructor
      · intro a b hab
        exact Subtype.ext (e.symm.injective (congrArg Subtype.val hab))
      · intro x
        exact ⟨⟨e x, (hΓ _).2 x.2⟩, Subtype.ext (by simp [f])⟩
    refine hF.preimage_of_equiv hmp'.quasiMeasurePreserving hf ?_
    intro y x
    simp [f, AddSubgroup.vadd_def]
  have hv : (μ.map e.symm) (e ⁻¹' 𝓕) = 1 := (hmp.measure_preimage_equiv 𝓕).trans h1
  have hcov : IsCovolOne (ratMx D m n) (μ.map e.symm) (e ⁻¹' 𝓕) := ⟨hν, hF', hv⟩
  have heq := covolOne_measure_eq h hcov
  have h3 : ∫ w in e ⁻¹' 𝓕, φ (e w) ∂(μ.map e.symm) = ∫ w in 𝓕, φ w ∂μ :=
    hmp.setIntegral_preimage_emb me.measurableEmbedding φ 𝓕
  rw [heq] at h3 hcov
  rw [← h3]
  refine (covolOne_integral_eq h hcov (fun a => φ (e a)) fun γ hγ a => ?_).symm
  rw [map_add]
  exact hφ _ ((hΓ γ).2 hγ) _

end Mean

section Levi

variable {D : D7} (W : HSp D) {s : ℕ}

structure IsDualPair (C : Matrix (Fin W.rank) (Fin s) D.host.E) (C' : Matrix (Fin W.rank) (Fin s) D.host.E)
    (L B : Matrix (Fin s) (Fin W.rank) D.host.E) : Prop where
  hB : B = Cᴴ * W.gram
  hL : Lᴴ = W.gram * C'
  LC : L * C = 1
  LC' : L * C' = 0
  BC : B * C = 0
  BC' : B * C' = 1

variable {W}

theorem exists_dualPair {C : Matrix (Fin W.rank) (Fin s) D.host.E} (hC : IsIsoFrame W C) :
    ∃ C' L B, IsDualPair W C C' L B := by
  obtain ⟨L, h1, h2⟩ := GlobalTheory.AutFunCompare.exists_dual D.sp.cm W C hC.2.1 hC.2.2
  have hG := gram_isUnit_det W
  have h3 : Cᴴ * W.gram * C = 0 := hC.2.2
  have h2' : L * W.gram⁻¹ * Lᴴ = 0 := h2
  refine ⟨W.gram⁻¹ * Lᴴ, L, Cᴴ * W.gram, rfl, ?_, h1, ?_, h3, ?_⟩
  · rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul]
  · rw [← Matrix.mul_assoc]; exact h2'
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc W.gram, Matrix.mul_nonsing_inv _ hG, Matrix.one_mul,
      ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]

variable {C C' : Matrix (Fin W.rank) (Fin s) D.host.E} {L B : Matrix (Fin s) (Fin W.rank) D.host.E}

theorem IsDualPair.hB' (h : IsDualPair W C C' L B) : B = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * W.gram := h.hB

theorem IsDualPair.pp (h : IsDualPair W C C' L B) : (C * L) * (C * L) = C * L := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, h.LC, Matrix.one_mul]

theorem IsDualPair.qq (h : IsDualPair W C C' L B) : (C' * B) * (C' * B) = C' * B := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h.BC', Matrix.one_mul]

theorem IsDualPair.pq (h : IsDualPair W C C' L B) : (C * L) * (C' * B) = 0 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc L, h.LC', Matrix.zero_mul, Matrix.mul_zero]

theorem IsDualPair.qp (h : IsDualPair W C C' L B) : (C' * B) * (C * L) = 0 := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, h.BC, Matrix.zero_mul, Matrix.mul_zero]

theorem IsDualPair.pH (h : IsDualPair W C C' L B) : (C * L)ᴴ * W.gram = W.gram * (C' * B) := by
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, h.hL, ← h.hB, Matrix.mul_assoc]

theorem IsDualPair.qH (h : IsDualPair W C C' L B) : (C' * B)ᴴ * W.gram = W.gram * (C * L) := by
  have := congrArg Matrix.conjTranspose h.pH
  rw [Matrix.conjTranspose_mul _ W.gram, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul W.gram,
    gram_conjTranspose] at this
  exact this.symm

theorem IsDualPair.levi_unitary (h : IsDualPair W C C' L B) {t t' : D.host.E} (ht : star t = t) (ht' : star t' = t')
    (htt : t * t' = 1) : (levi t t' (C * L) (C' * B))ᴴ * (W.gram * levi t t' (C * L) (C' * B)) = W.gram := by
  have e : (levi t t' (C * L) (C' * B))ᴴ * W.gram = W.gram * levi t' t (C * L) (C' * B) := by
    simp only [levi, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_sub, star_one,
      ht, ht', Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, h.pH, h.qH]
    abel
  rw [← Matrix.mul_assoc, e, Matrix.mul_assoc,
    levi_mul_swap h.pp h.qq h.pq h.qp (by rw [mul_comm]; exact htt), Matrix.mul_one]

theorem rat_levi {n : ℕ} (t t' : D.host.E) (p q : Matrix (Fin n) (Fin n) D.host.E) :
    rat (levi t t' p q) = levi (incA D t) (incA D t') (rat p) (rat q) := by
  simp only [levi, rat_add, rat_smul, rat_one, map_sub, map_one]

theorem IsDualPair.exists_levi (h : IsDualPair W C C' L B) {t t' : D.host.E} (ht : star t = t) (ht' : star t' = t')
    (htt : t * t' = 1) : ∃ a : GA D W, a ∈ GQ W ∧ mt W a = rat (levi t t' (C * L) (C' * B)) := by
  have hu : adj (rat (levi t t' (C * L) (C' * B))) * (gA W * rat (levi t t' (C * L) (C' * B))) = gA W := by
    have := congrArg rat (h.levi_unitary ht ht' htt)
    rw [rat_mul, rat_mul, rat_conjTranspose] at this
    exact this
  exact ⟨ofMat W _ hu, (mem_GQ_iff W _).2 ⟨_, (mt_ofMat W _ hu).symm⟩, mt_ofMat W _ hu⟩

theorem IsDualPair.levi_mul (h : IsDualPair W C C' L B) (t t' : D.host.E) :
    levi t t' (C * L) (C' * B) * C = t • C := by
  simp only [levi, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc, h.LC, h.BC, Matrix.mul_one,
    Matrix.mul_zero, smul_zero, add_zero]
  module

end Levi

section Sc

variable {D : D7} {V W : HSp D} {s : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}

def meanL (C : Mx D W.rank s) (μ : Measure (Mx D s V.rank)) (𝓐 : Set (Mx D s V.rank)) (f : WO V W → ℂ) : ℂ :=
  ∫ a in 𝓐, f (C ⬝ a) ∂μ

def Sc (ψ : AddChar (AF D.host.F) ℂ) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (C : Mx D W.rank s)
    (μ : Measure (Mx D s V.rank)) (𝓐 : Set (Mx D s V.rank)) (g : GA D W) (c : ℂ) : Prop :=
  ∀ f, IsThetaFunO ψ V W f → meanL C μ 𝓐 (ω (1, g) f) = c * meanL C μ 𝓐 f

variable {C : Mx D W.rank s} {μ : Measure (Mx D s V.rank)} {𝓐 : Set (Mx D s V.rank)} {g g' : GA D W} {c d : ℂ}

theorem om_mul (g g' : GA D W) (f : WO V W → ℂ) : ω (1, g * g') f = ω (1, g) (ω (1, g') f) := by
  have : ((1 : GA D V), g * g') = (1, g) * (1, g') := by simp
  rw [this, map_mul]; rfl

theorem om_one (f : WO V W → ℂ) : ω (1, 1) f = f := by
  have : ((1 : GA D V), (1 : GA D W)) = 1 := rfl
  rw [this, map_one]; rfl

theorem Sc.one : Sc ψ ω C μ 𝓐 1 1 := fun f _ => by rw [om_one, one_mul]

theorem Sc.mul (hω : IsWeilDatumO ψ V W χS χT ω) (h : Sc ψ ω C μ 𝓐 g c) (h' : Sc ψ ω C μ 𝓐 g' d) :
    Sc ψ ω C μ 𝓐 (g * g') (c * d) := fun f hf => by
  rw [om_mul, h _ (hω.om_pres _ _ hf), h' f hf, mul_assoc]

theorem Sc.inv (hω : IsWeilDatumO ψ V W χS χT ω) (h : Sc ψ ω C μ 𝓐 g c) (hc : c ≠ 0) :
    Sc ψ ω C μ 𝓐 g⁻¹ c⁻¹ := fun f hf => by
  have := h _ (hω.om_pres (1, g⁻¹) f hf)
  rw [← om_mul, mul_inv_cancel, om_one] at this
  rw [this, inv_mul_cancel_left₀ hc]

theorem Sc.pow (hω : IsWeilDatumO ψ V W χS χT ω) (h : Sc ψ ω C μ 𝓐 g c) (k : ℕ) : Sc ψ ω C μ 𝓐 (g ^ k) (c ^ k) := by
  induction k with
  | zero => simpa using Sc.one
  | succ k ih => rw [pow_succ, pow_succ]; exact ih.mul hω h

theorem Sc.unique (h : Sc ψ ω C μ 𝓐 g c) (h' : Sc ψ ω C μ 𝓐 g d) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (h0 : meanL C μ 𝓐 f ≠ 0) : c = d :=
  mul_right_cancel₀ h0 ((h f hf).symm.trans (h' f hf))

theorem symplO_frame (hC : adj C ⬝ (gA W ⬝ C) = 0) (y y' : Mx D s V.rank) :
    symplO V W (C ⬝ y) (C ⬝ y') = 0 := by
  have : adj (C ⬝ y') ⬝ (gA W ⬝ (C ⬝ y)) = 0 := by
    rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA W), ← Matrix.mul_assoc (adj C), hC]
    simp
  unfold symplO
  rw [hO_eq_trace, this]
  simp

theorem theta_frame_periodic {C₀ : Matrix (Fin W.rank) (Fin s) D.host.E} (hC : adj (rat C₀) ⬝ (gA W ⬝ rat C₀) = 0)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) :
    ∀ γ ∈ ratMx D s V.rank, ∀ a : Mx D s V.rank, f (rat C₀ ⬝ (γ + a)) = f (rat C₀ ⬝ a) := by
  rintro _ ⟨γ, rfl⟩ a
  have e : rat C₀ ⬝ (((incA D).toAddMonoidHom.mapMatrix γ : Mx D s V.rank) + a) = ratW W V (C₀ * γ) + rat C₀ ⬝ a := by
    rw [Matrix.mul_add, ratW_eq, rat_mul]; rfl
  have h0 : symplOH V W (ratW W V (C₀ * γ)) (rat C₀ ⬝ a) = 0 := by
    unfold symplOH
    rw [ratW_eq, rat_mul, symplO_frame hC, mul_zero]
  rw [e, hf.quasi, h0, neg_zero, AddChar.map_zero_eq_one, one_mul]

theorem Sc_of_rat (hω : IsWeilDatumO ψ V W χS χT ω) (hcov : IsCovolOne (ratMx D s V.rank) μ 𝓐)
    {C₀ : Matrix (Fin W.rank) (Fin s) D.host.E} (hC : adj (rat C₀) ⬝ (gA W ⬝ rat C₀) = 0) {a : GA D W} (ha : a ∈ GQ W)
    {t t' : D.host.E} (htt : t * t' = 1) (hat : mt W a ⬝ rat C₀ = incA D t • rat C₀) :
    Sc ψ ω (rat C₀) μ 𝓐 a 1 := by
  intro f hf
  have ht' : t' ≠ 0 := right_ne_zero_of_mul_eq_one htt
  have key : ∀ y : Mx D s V.rank, ω (1, a) f (rat C₀ ⬝ y) = f (rat C₀ ⬝ (incA D t' • y)) := fun y => by
    have := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω 1 (GQ V).one_mem a ha f hf (rat C₀ ⬝ (incA D t' • y))
    have e : actO V W 1 a (rat C₀ ⬝ (incA D t' • y)) = rat C₀ ⬝ y := by
      rw [actO_eq, inv_one, mt_one, Matrix.mul_one, ← Matrix.mul_assoc, hat, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        ← map_mul, htt, map_one, one_smul]
    rwa [e] at this
  unfold meanL
  simp_rw [key]
  rw [one_mul]
  exact mean_smul hcov ht' (fun y => f (rat C₀ ⬝ y)) (theta_frame_periodic hC hf)

end Sc

section Unip

variable {D : D7} {V W : HSp D} {s : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {μ : Measure (Mx D s V.rank)} {𝓐 : Set (Mx D s V.rank)}
  {C C' : Matrix (Fin W.rank) (Fin s) D.host.E} {L B : Matrix (Fin s) (Fin W.rank) D.host.E}

theorem rat_mul_sq {n : ℕ} (M N : Matrix (Fin n) (Fin n) D.host.E) : rat M * rat N = rat (M * N) := (rat_mul M N).symm

theorem gen_relations (h : IsDualPair W C C' L B) {x : Mx D W.rank W.rank} (h1 : x ⬝ rat C = 0) (h2 : rat B ⬝ x = 0)
    (h3 : ∀ v : Fin W.rank → D.host.E, B.mulVec v = 0 → ∃ a : Fin s → AE D,
      x.mulVec (fun i => incA D (v i)) = (rat C).mulVec a) :
    x * rat (C * L) = 0 ∧ rat (C' * B) * x = 0 ∧
      x = rat (C * L) * x + x * rat (C' * B) - rat (C * L) * x * rat (C' * B) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [show rat (C * L) = rat C ⬝ rat L from rat_mul C L]
    show x ⬝ (rat C ⬝ rat L) = 0
    rw [← Matrix.mul_assoc, h1, Matrix.zero_mul]
  · rw [show rat (C' * B) = rat C' ⬝ rat B from rat_mul C' B]
    show (rat C' ⬝ rat B) ⬝ x = 0
    rw [Matrix.mul_assoc, h2, Matrix.mul_zero]
  · obtain ⟨Y, hY⟩ : ∃ Y : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Y = 1 - C' * B := ⟨_, rfl⟩
    obtain ⟨Z, hZ⟩ : ∃ Z : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Z = 1 - C * L := ⟨_, rfl⟩
    have hBY : B * Y = 0 := by
      rw [hY, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h.BC', Matrix.one_mul, sub_self]
    have hv : ∀ j, ∃ a : Fin s → AE D, x.mulVec (fun i => incA D (Y i j)) = (rat C).mulVec a := fun j =>
      h3 _ (funext fun i => congrFun (congrFun hBY i) j)
    choose a ha using hv
    obtain ⟨Am, e1⟩ : ∃ Am : Mx D s W.rank, x * rat Y = rat C ⬝ Am := ⟨Matrix.of fun k j => a j k, by
      ext i j
      exact congrFun (ha j) i⟩
    have e2 : rat Z ⬝ rat C = 0 := by
      rw [← rat_mul, hZ, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, h.LC, Matrix.mul_one, sub_self, rat_zero]
    have e3 : rat Z * (x * rat Y) = 0 := by
      rw [e1]
      show rat Z ⬝ (rat C ⬝ Am) = 0
      rw [← Matrix.mul_assoc, e2, Matrix.zero_mul]
    rw [hY, hZ, rat_sub, rat_sub, rat_one] at e3
    generalize rat (C * L) = p at e3 ⊢
    generalize rat (C' * B) = q at e3 ⊢
    have e4 : (1 - p) * (x * (1 - q)) = x - (p * x + x * q - p * x * q) := by noncomm_ring
    exact sub_eq_zero.1 (e4.symm.trans e3)

theorem gen_apply {n : ℕ} {x : Mx D W.rank W.rank} {x' : Mx D W.rank n}
    (r3 : x = rat (C * L) * x + x * rat (C' * B) - rat (C * L) * x * rat (C' * B)) (hq : rat (C' * B) ⬝ x' = 0) :
    x ⬝ x' = rat C ⬝ (rat L ⬝ (x ⬝ x')) := by
  have e1 : x ⬝ x' = (rat (C * L) * x + x * rat (C' * B) - rat (C * L) * x * rat (C' * B)) ⬝ x' := by rw [← r3]
  rw [Matrix.sub_mul, Matrix.add_mul, Matrix.mul_assoc x, hq, Matrix.mul_zero, add_zero, Matrix.mul_assoc (rat (C * L) * x),
    hq, Matrix.mul_zero, sub_zero, Matrix.mul_assoc, rat_mul C L, Matrix.mul_assoc] at e1
  exact e1

theorem scalar_eq_one (hω : IsWeilDatumO ψ V W χS χT ω) (hcov : IsCovolOne (ratMx D s V.rank) μ 𝓐)
    (h : IsDualPair W C C' L B) (hiso : adj (rat C) ⬝ (gA W ⬝ rat C) = 0) {g : GA D W} {x : Mx D W.rank W.rank}
    (hx : mt W g = 1 + x) (r1 : x * rat (C * L) = 0) (r2 : rat (C' * B) * x = 0)
    (r3 : x = rat (C * L) * x + x * rat (C' * B) - rat (C * L) * x * rat (C' * B)) {c : ℂ} (hc : c ≠ 0)
    (hs : Sc ψ ω (rat C) μ 𝓐 g c) {f₀ : WO V W → ℂ} (hf₀ : IsThetaFunO ψ V W f₀) (h0 : meanL (rat C) μ 𝓐 f₀ ≠ 0) :
    c = 1 := by
  have hpp : rat (C * L) * rat (C * L) = rat (C * L) := by rw [rat_mul_sq, h.pp]
  have hqq : rat (C' * B) * rat (C' * B) = rat (C' * B) := by rw [rat_mul_sq, h.qq]
  have hpq : rat (C * L) * rat (C' * B) = 0 := by rw [rat_mul_sq, h.pq, rat_zero]
  have hqp : rat (C' * B) * rat (C * L) = 0 := by rw [rat_mul_sq, h.qp, rat_zero]
  have levi_sc : ∀ {t t' : D.host.E}, star t = t → star t' = t' → t * t' = 1 → ∃ a : GA D W,
      mt W a = levi (incA D t) (incA D t') (rat (C * L)) (rat (C' * B)) ∧ Sc ψ ω (rat C) μ 𝓐 a 1 := by
    intro t t' ht ht' htt
    obtain ⟨a, ha, ma⟩ := h.exists_levi ht ht' htt
    refine ⟨a, ma.trans (rat_levi _ _ _ _), Sc_of_rat hω hcov hiso ha htt ?_⟩
    rw [ma, ← rat_mul, h.levi_mul, rat_smul]
  have e2 : star (2 : D.host.E) = 2 := by simp
  have e3 : star (3 : D.host.E) = 3 := by simp
  have e2' : star (1 / 2 : D.host.E) = 1 / 2 := by simp
  have e3' : star (1 / 3 : D.host.E) = 1 / 3 := by simp
  obtain ⟨a, ma, Sa⟩ := levi_sc e2 e2' (by norm_num)
  obtain ⟨b, mb, Sb⟩ := levi_sc e3 e3' (by norm_num)
  have hh2 : (2 : AE D) * incA D (1 / 2) = 1 := by
    rw [show (2 : AE D) = incA D 2 from (map_ofNat (incA D) 2).symm, ← map_mul]
    norm_num
  have hh3 : (3 : AE D) * incA D (1 / 3) = 1 := by
    rw [show (3 : AE D) = incA D 3 from (map_ofNat (incA D) 3).symm, ← map_mul]
    norm_num
  obtain ⟨c4, c9⟩ := core_conj (K := AE D) ((Units.coeHom (Mx D W.rank W.rank)).comp (matHom W)) (mt_injective W) hpp hqq hpq hqp
    r1 r2 r3 hx (map_ofNat (incA D) 2) hh2 (map_ofNat (incA D) 3) hh3 ma mb
  generalize hz : (g * g)⁻¹ * (a * g * a⁻¹) = z at c4 c9
  have Sz : Sc ψ ω (rat C) μ 𝓐 z ((c * c)⁻¹ * (1 * c * 1⁻¹)) := by
    rw [← hz]
    exact ((hs.mul hω hs).inv hω (mul_ne_zero hc hc)).mul hω ((Sa.mul hω hs).mul hω (Sa.inv hω one_ne_zero))
  have hd : (c * c)⁻¹ * (1 * c * 1⁻¹) = c⁻¹ := by field_simp
  rw [hd] at Sz
  have d4 : 1 * c⁻¹ * 1⁻¹ = c⁻¹ ^ 4 := by
    have := (Sa.mul hω Sz).mul hω (Sa.inv hω one_ne_zero)
    rw [c4] at this
    exact this.unique (Sz.pow hω 4) hf₀ h0
  have d9 : 1 * c⁻¹ * 1⁻¹ = c⁻¹ ^ 9 := by
    have := (Sb.mul hω Sz).mul hω (Sb.inv hω one_ne_zero)
    rw [c9] at this
    exact this.unique (Sz.pow hω 9) hf₀ h0
  simp only [one_mul, inv_one, mul_one] at d4 d9
  have hi : c⁻¹ ≠ 0 := inv_ne_zero hc
  have d3 : c⁻¹ ^ 3 = 1 := mul_left_cancel₀ hi (by rw [mul_one, ← pow_succ']; exact d4.symm)
  have : c⁻¹ = 1 := by rw [d9, show 9 = 3 * 3 from rfl, pow_mul, d3, one_pow]
  exact inv_eq_one.1 this

end Unip

section Final

variable {D : D7} {V W : HSp D} {s : ℕ} {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {μ : Measure (Mx D s V.rank)} {𝓐 : Set (Mx D s V.rank)}

theorem adj_eq_zero_of_symplO {C : Mx D W.rank s} {x : WO V W}
    (h : ∀ y : Mx D s V.rank, symplO V W x (C ⬝ y) = 0) : adj C ⬝ (gA W ⬝ x) = 0 := by
  obtain ⟨u, hu⟩ : ∃ u : Mx D s V.rank, u = adj C ⬝ (gA W ⬝ x) := ⟨_, rfl⟩
  rw [← hu]
  ext i j
  have key : ∀ w : AE D, Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * u i j * w) = 0 := fun w => by
    have := h (adj (gA V ⬝ (Matrix.single j i w : Mx D V.rank s)))
    unfold symplO at this
    have e : giA V ⬝ (adj (C ⬝ adj (gA V ⬝ (Matrix.single j i w : Mx D V.rank s))) ⬝ (gA W ⬝ x)) =
        (Matrix.single j i w : Mx D V.rank s) ⬝ u := by
      rw [adj_mul, adj_adj, hu]
      simp only [Matrix.mul_assoc, giA_gA_cancel]
    have e2 : ((Matrix.single j i w : Mx D V.rank s) ⬝ u).trace = u i j * w := by
      exact trace_single_mul' i j w u
    rw [hO_eq_trace, e, e2, ← mul_assoc] at this
    exact this
  have hz := eq_zero_of_trace_mul (F := D.host.F) (E := D.host.E) (R := AF D.host.F) _ key
  have hξ : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one]
  have := congrArg (incA D D.host.xi0⁻¹ * ·) hz
  simpa [← mul_assoc, hξ] using this

theorem iso_rat {C : Matrix (Fin W.rank) (Fin s) D.host.E} (hC : IsIsoFrame W C) : adj (rat C) ⬝ (gA W ⬝ rat C) = 0 := by
  have h : Cᴴ * (W.gram * C) = 0 := by rw [← Matrix.mul_assoc]; exact hC.2.2
  have := congrArg rat h
  rw [rat_mul, rat_mul, rat_zero] at this
  exact this

theorem mean_unip {C : Matrix (Fin W.rank) (Fin s) D.host.E} (hC : IsIsoFrame W C)
    (hω : IsWeilDatumO ψ V W χS χT ω) (hcov : IsCovolOne (ratMx D s V.rank) μ 𝓐)
    (hsc : ∀ g : GA D W, (∀ y : Mx D s V.rank, mt W g ⬝ (rat C ⬝ y) = rat C ⬝ y) →
      (∀ x : WO V W, adj (rat C) ⬝ (gA W ⬝ x) = 0 → ∃ y : Mx D s V.rank, mt W g ⬝ x = x + rat C ⬝ y) →
      ∃ c : ℂ, c ≠ 0 ∧ Sc ψ ω (rat C) μ 𝓐 g c) {n : GA D W} (hn : n ∈ NI W C) :
    Sc ψ ω (rat C) μ 𝓐 n 1 := by
  obtain ⟨C', L, B, h⟩ := exists_dualPair hC
  have hiso := iso_rat hC
  by_cases h0 : ∀ f, IsThetaFunO ψ V W f → meanL (rat C) μ 𝓐 f = 0
  · intro f hf
    rw [h0 _ (hω.om_pres _ _ hf), h0 f hf, mul_zero]
  push Not at h0
  obtain ⟨f₀, hf₀, hm⟩ := h0
  unfold NI at hn
  refine Subgroup.closure_induction (p := fun g _ => Sc ψ ω (rat C) μ 𝓐 g 1) ?_ Sc.one ?_ ?_ hn
  · rintro g ⟨g1, g2, g3⟩
    have g1' : (mt W g - 1) ⬝ rat C = 0 := g1
    obtain ⟨r1, r2, r3⟩ := gen_relations h (x := mt W g - 1) g1' (by rw [h.hB]; exact g2)
      (fun v hv => g3 v (by rw [← h.hB'] ; exact hv))
    obtain ⟨c, hc, hs⟩ := hsc g (fun y => by
        have e : mt W g ⬝ rat C = rat C := by rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at g1'
        rw [← Matrix.mul_assoc, e])
      (fun x' hx' => by
        have hB : rat B ⬝ x' = 0 := by
          rw [h.hB, rat_mul, rat_conjTranspose, Matrix.mul_assoc]
          exact hx'
        have hq : rat (C' * B) ⬝ x' = 0 := by rw [rat_mul, Matrix.mul_assoc, hB, Matrix.mul_zero]
        refine ⟨rat L ⬝ ((mt W g - 1) ⬝ x'), ?_⟩
        rw [← gen_apply r3 hq, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel])
    have := scalar_eq_one hω hcov h hiso (add_sub_cancel 1 (mt W g)).symm r1 r2 r3 hc hs hf₀ hm
    rwa [this] at hs
  · intro a b _ _ ha hb
    simpa using ha.mul hω hb
  · intro a _ ha
    simpa using ha.inv hω one_ne_zero

end Final

end GlobalTheory.UnipMean

end
