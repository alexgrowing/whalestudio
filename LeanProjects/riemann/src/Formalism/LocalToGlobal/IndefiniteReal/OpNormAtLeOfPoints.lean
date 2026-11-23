import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.TraceOfDiag

open Module NumberField Matrix

noncomputable section

namespace Formalism.IndefR.LatticeTransfer

open Formalism.IndefR.TransferLatticeStatement

namespace BlockMetrics

section Forms

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
  (v : InfinitePlace K)

theorem fc_smul (c : K) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.fcoord b X v x := by
  have h : Formalism.HermitianLatticesTheory.vecAt b v (c • x) = v.embedding c • Formalism.HermitianLatticesTheory.vecAt b v x := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply]
  simp only [Formalism.HermitianLatticesTheory.fcoord, h, Matrix.mulVec_smul]

def fcA : V →+ (ι → ℂ) :=
  AddMonoidHom.mk' (Formalism.HermitianLatticesTheory.fcoord b X v) (Formalism.HermitianLatticesTheory.fcoord_add b X v)

theorem fc_sum {α : Type} (s : Finset α) (f : α → V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (∑ a ∈ s, f a) = ∑ a ∈ s, Formalism.HermitianLatticesTheory.fcoord b X v (f a) := by
  exact map_sum (fcA b X v) f s

theorem maj_sum_left {α : Type} (s : Finset α) (c : α → K) (f : α → V) (y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (∑ a ∈ s, c a • f a) y =
      ∑ a ∈ s, star (v.embedding (c a)) * Formalism.HermitianLatticesTheory.majAt b X v (f a) y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
    star_mul', Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem maj_sum_right {α : Type} (s : Finset α) (c : α → K) (f : α → V) (x : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (∑ a ∈ s, c a • f a) =
      ∑ a ∈ s, v.embedding (c a) * Formalism.HermitianLatticesTheory.majAt b X v x (f a) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_sum, fc_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem maj_add_left (x x' y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (x + x') y = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x' y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, star_add, add_mul,
    Finset.sum_add_distrib]

theorem maj_add_right (x y y' : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (y + y') = Formalism.HermitianLatticesTheory.majAt b X v x y + Formalism.HermitianLatticesTheory.majAt b X v x y' := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_add, Pi.add_apply, mul_add,
    Finset.sum_add_distrib]

theorem maj_smul_left (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v (a • x) y = starRingEnd ℂ (v.embedding a) * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, star_mul', Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [starRingEnd_apply]
  ring

theorem maj_smul_right (a : K) (x y : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x (a • y) = v.embedding a * Formalism.HermitianLatticesTheory.majAt b X v x y := by
  simp only [Formalism.HermitianLatticesTheory.majAt, fc_smul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem maj_self (x : V) :
    Formalism.HermitianLatticesTheory.majAt b X v x x = ((Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 : ℝ) : ℂ) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Complex.conj_mul' _

theorem normAt_eq_sqrt (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x = Real.sqrt (Formalism.HermitianLatticesTheory.majAt b X v x x).re := by
  rw [maj_self, Complex.ofReal_re, Real.sqrt_sq]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  exact Real.sqrt_nonneg _

theorem normAt_eq_norm (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x =
      ‖(WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι)‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]

theorem fcoord_map (hX : ∀ v, IsUnit (X v).det) (φ : V →ₗ[K] V) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b X v (φ x) =
      ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v).mulVec
        (Formalism.HermitianLatticesTheory.fcoord b X v x) := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b v (φ x) =
      ((LinearMap.toMatrix b b φ).map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← LinearMap.toMatrix_mulVec_repr b b φ x, RingHom.map_mulVec]
    rfl
  simp only [Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]

end Forms

theorem dense_emb {K : Type} [Field K] [NumberField K] (v : InfinitePlace K) (hv : v.IsComplex) :
    DenseRange v.embedding := by
  rcases Complex.subfield_eq_of_closed (v.embedding.fieldRange.isClosed_topologicalClosure) with h | h
  · exfalso
    have hr : ComplexEmbedding.IsReal v.embedding := by
      rw [ComplexEmbedding.isReal_iff]
      ext x
      have hx : v.embedding x ∈ v.embedding.fieldRange.topologicalClosure :=
        v.embedding.fieldRange.le_topologicalClosure (RingHom.mem_fieldRange.2 ⟨x, rfl⟩)
      rw [h] at hx
      obtain ⟨r, hr⟩ := RingHom.mem_fieldRange.1 hx
      rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
      simp
    exact (InfinitePlace.isComplex_iff.1 hv) hr
  · intro z
    have hz : z ∈ v.embedding.fieldRange.topologicalClosure := by
      rw [h]; exact Subfield.mem_top z
    have hc : (v.embedding.fieldRange.topologicalClosure : Set ℂ) = closure (Set.range v.embedding) := by
      rw [← RingHom.coe_fieldRange]; rfl
    rw [← hc]; exact hz

theorem dense_fcoord {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) :
    DenseRange fun x : V => (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x) : EuclideanSpace ℂ ι) := by
  have hemb : DenseRange v.embedding := dense_emb v (IsTotallyComplex.isComplex v)
  have h1 : DenseRange fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x := by
    have hpi : DenseRange (Pi.map fun _ : ι => v.embedding) := DenseRange.piMap fun _ => hemb
    have hr : Set.range (fun x : V => Formalism.HermitianLatticesTheory.vecAt b v x) =
        Set.range (Pi.map fun _ : ι => v.embedding) := by
      ext u; constructor
      · rintro ⟨x, rfl⟩; exact ⟨fun i => b.repr x i, rfl⟩
      · rintro ⟨c, rfl⟩
        refine ⟨b.equivFun.symm c, ?_⟩
        funext i
        have hc := congr_fun (b.equivFun.apply_symm_apply c) i
        rw [Basis.equivFun_apply] at hc
        show v.embedding (b.repr (b.equivFun.symm c) i) = v.embedding (c i)
        rw [hc]
    rw [DenseRange, hr]; exact hpi
  have h2 : Continuous fun u : ι → ℂ => (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    fun_prop
  have h3 : Function.Surjective fun u : ι → ℂ =>
      (WithLp.toLp 2 ((X v)⁻¹.mulVec u) : EuclideanSpace ℂ ι) := by
    intro w
    refine ⟨(X v).mulVec (WithLp.ofLp w), ?_⟩
    simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hX v)]
  exact h3.denseRange.comp h1 h2

theorem opNormAt_le_of_points {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [IsTotallyComplex K] [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det)
    (φ : V →ₗ[K] V) (v : InfinitePlace K) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ f, Formalism.HermitianLatticesTheory.normAt b X v (φ f) ≤ C * Formalism.HermitianLatticesTheory.normAt b X v f) :
    Formalism.HN.opNormAt b X b X v φ ≤ C := by
  unfold Formalism.HN.opNormAt
  set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X v)⁻¹ * (LinearMap.toMatrix b b φ).map v.embedding * X v)) with hTd
  refine ContinuousLinearMap.opNorm_le_bound T hC fun u => ?_
  refine (dense_fcoord b X hX v).induction_on (p := fun w => ‖T w‖ ≤ C * ‖w‖) u ?_ ?_
  · exact isClosed_le (by fun_prop) (by fun_prop)
  · intro f
    have hT : T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)) =
        WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v (φ f)) := by
      rw [fcoord_map b X v hX φ f]; rfl
    show ‖T (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f))‖ ≤ C * ‖WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v f)‖
    rw [hT, ← normAt_eq_norm, ← normAt_eq_norm]
    exact h f

theorem sesq_ext {K V : Type} [Field K] [AddCommGroup V] [Module K V] {F G : V → V → ℂ}
    {σ : K →+* ℂ} (hσ : ∃ a : K, (σ a).im ≠ 0)
    (hF : (∀ x x' y, F (x + x') y = F x y + F x' y) ∧ (∀ x y y', F x (y + y') = F x y + F x y') ∧
      (∀ (a : K) x y, F (a • x) y = starRingEnd ℂ (σ a) * F x y) ∧
      (∀ (a : K) x y, F x (a • y) = σ a * F x y))
    (hG : (∀ x x' y, G (x + x') y = G x y + G x' y) ∧ (∀ x y y', G x (y + y') = G x y + G x y') ∧
      (∀ (a : K) x y, G (a • x) y = starRingEnd ℂ (σ a) * G x y) ∧
      (∀ (a : K) x y, G x (a • y) = σ a * G x y))
    (h : ∀ x, F x x = G x x) (x y : V) : F x y = G x y := by
  obtain ⟨a, ha⟩ := hσ
  obtain ⟨F1, F2, F3, F4⟩ := hF
  obtain ⟨G1, G2, G3, G4⟩ := hG
  have e1 := h (x + y)
  have e2 := h (a • x + y)
  simp only [F1, F2, F3, F4, G1, G2, G3, G4] at e1 e2
  rw [h x, h y] at e1 e2
  have hne : starRingEnd ℂ (σ a) - σ a ≠ 0 := by
    intro h0
    apply ha
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  have key : (starRingEnd ℂ (σ a) - σ a) * (F x y - G x y) = 0 := by
    linear_combination e2 - σ a * e1
  rcases mul_eq_zero.1 key with h0 | h0
  · exact absurd h0 hne
  · exact sub_eq_zero.1 h0

theorem exists_im_ne_zero {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
    (v : InfinitePlace K) : ∃ a : K, (v.embedding a).im ≠ 0 := by
  have hv := IsTotallyComplex.isComplex v
  rw [InfinitePlace.isComplex_iff, ComplexEmbedding.isReal_iff] at hv
  by_contra hcon
  push_neg at hcon
  apply hv
  ext a
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hcon a)

end BlockMetrics

open BlockMetrics

private theorem normAt_smul_indefinite_real {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (a : K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (a • x) = ‖v.embedding a‖ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  rw [normAt_eq_norm, normAt_eq_norm, fc_smul, WithLp.toLp_smul, norm_smul]

private theorem normAt_add_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x y : V) :
    Formalism.HermitianLatticesTheory.normAt b X v (x + y) ≤ Formalism.HermitianLatticesTheory.normAt b X v x + Formalism.HermitianLatticesTheory.normAt b X v y := by
  rw [normAt_eq_norm, normAt_eq_norm, normAt_eq_norm, Formalism.HermitianLatticesTheory.fcoord_add, WithLp.toLp_add]
  exact norm_add_le _ _

private theorem normAt_finset_sum_le {K V ι : Type} [Field K] [NumberField K] [StarRing K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] (b : Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) {α : Type} (s : Finset α)
    (f : α → V) :
    Formalism.HermitianLatticesTheory.normAt b X v (∑ a ∈ s, f a) ≤ ∑ a ∈ s, Formalism.HermitianLatticesTheory.normAt b X v (f a) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (normAt_smul_indefinite_real b X v (0 : K) (0 : V)).le
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (normAt_add_le b X v _ _).trans (add_le_add le_rfl ih)

theorem metric : Metric := by
  intro K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hX hU
  have hinv : ∀ (g : G) (y : V), ρ g (ρ g⁻¹ y) = y := by
    intro g y
    show (ρ g * ρ g⁻¹) y = y
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  have hρ : ∀ (v : InfinitePlace K) (g : G) (x y : V),
      Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := by
    intro v g x y
    calc Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) y
        = Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g (ρ g⁻¹ y)) := by rw [hinv]
      _ = Formalism.HermitianLatticesTheory.majAt b X v x (ρ g⁻¹ y) := hU v g x _
  refine ⟨fun T _ _ _ τ v x y => ?_, fun H χ g v => ?_⟩
  · have hc := fun g => (charFacts K G T τ g).2 v.embedding
    have hc1 : starRingEnd ℂ (v.embedding (charOf τ 1 / (Fintype.card G : K))) =
        v.embedding (charOf τ 1 / (Fintype.card G : K)) := by
      have h1 := (hc 1).1
      rw [inv_one] at h1
      simp only [map_div₀, map_natCast]
      rw [starRingEnd_apply, ← h1]
    simp only [Formalism.IndefR.TransferLatticeStatement.eS, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [maj_smul_left, maj_smul_right, maj_sum_left, maj_sum_right, hc1]
    congr 1
    refine Fintype.sum_equiv (Equiv.inv G) _ _ fun g => ?_
    have hg := (hc g⁻¹).1
    rw [inv_inv] at hg
    simp only [Equiv.inv_apply, inv_inv]
    rw [hρ, ← hg]
  · have hρn : ∀ (k : G) (z : V), Formalism.HermitianLatticesTheory.normAt b X v (ρ k z) = Formalism.HermitianLatticesTheory.normAt b X v z := by
      intro k z; rw [normAt_eq_sqrt, hU, ← normAt_eq_sqrt]
    have hχ : ∀ h : H, ‖v.embedding (((χ h⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K)‖ = 1 := by
      intro h
      rw [InfinitePlace.norm_embedding_eq]
      have ht : χ h⁻¹ ∈ NumberField.Units.torsion K := χ.isOfFinOrder (isOfFinOrder_of_finite h⁻¹)
      exact (NumberField.Units.mem_torsion K).1 ht v
    refine opNormAt_le_of_points b X hX _ v 1 zero_le_one fun f => ?_
    rw [one_mul, LinearMap.comp_apply]
    simp only [Formalism.IndefR.TransferLatticeStatement.epP, LinearMap.smul_apply, LinearMap.sum_apply]
    rw [normAt_smul_indefinite_real]
    refine (mul_le_mul_of_nonneg_left (normAt_finset_sum_le b X v _ _) (norm_nonneg _)).trans ?_
    simp only [normAt_smul_indefinite_real, hχ, hρn, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      map_inv₀, map_natCast, norm_inv, Complex.norm_natCast]
    rw [Fintype.card_eq_nat_card, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 (Nat.card_pos (α := H)).ne'), one_mul]

theorem unitOfNorm : UnitOfNorm := by
  intro K _ _ _ _ G _ _ V _ _ _ _ ι _ _ b X ρ hn v g x y
  refine sesq_ext (F := fun x y => Formalism.HermitianLatticesTheory.majAt b X v (ρ g x) (ρ g y))
    (G := Formalism.HermitianLatticesTheory.majAt b X v) (σ := v.embedding) (exists_im_ne_zero v)
    ⟨?_, ?_, ?_, ?_⟩ ⟨?_, ?_, ?_, ?_⟩ ?_ x y
  · intro x x' y; simp only [map_add]; exact maj_add_left b X v _ _ _
  · intro x y y'; simp only [map_add]; exact maj_add_right b X v _ _ _
  · intro a x y; simp only [map_smul]; exact maj_smul_left b X v _ _ _
  · intro a x y; simp only [map_smul]; exact maj_smul_right b X v _ _ _
  · exact fun x x' y => maj_add_left b X v _ _ _
  · exact fun x y y' => maj_add_right b X v _ _ _
  · exact fun a x y => maj_smul_left b X v _ _ _
  · exact fun a x y => maj_smul_right b X v _ _ _
  · intro z
    show Formalism.HermitianLatticesTheory.majAt b X v (ρ g z) (ρ g z) = Formalism.HermitianLatticesTheory.majAt b X v z z
    rw [maj_self, maj_self, hn]

end Formalism.IndefR.LatticeTransfer
