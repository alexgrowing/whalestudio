import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactHaarRightInvariantInst

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory.KHolExt

variable {n : ℕ} {ε : Fin n → Bool}

def Hol (ε : Fin n → Bool) (a : KG ε → ℂ) : Prop :=
  ∃ F : (Fin n → Fin n → ℂ) → ℂ, DifferentiableOn ℂ F {y | Matrix.of y ∈ KC ε} ∧
    ∀ k : KG ε, F (fun i j => toMK k i j) = a k

lemma Hol.const (c : ℂ) : Hol ε (fun _ => c) :=
  ⟨fun _ => c, differentiableOn_const c, fun _ => rfl⟩

lemma Hol.add {a b : KG ε → ℂ} (ha : Hol ε a) (hb : Hol ε b) : Hol ε (fun k => a k + b k) := by
  obtain ⟨F, hF, hFa⟩ := ha
  obtain ⟨G, hG, hGb⟩ := hb
  refine ⟨fun y => F y + G y, hF.add hG, fun k => ?_⟩
  simp only [hFa, hGb]

lemma Hol.mul {a b : KG ε → ℂ} (ha : Hol ε a) (hb : Hol ε b) : Hol ε (fun k => a k * b k) := by
  obtain ⟨F, hF, hFa⟩ := ha
  obtain ⟨G, hG, hGb⟩ := hb
  refine ⟨fun y => F y * G y, hF.mul hG, fun k => ?_⟩
  simp only [hFa, hGb]

lemma Hol.sum {ι : Type} (s : Finset ι) {a : ι → KG ε → ℂ} (ha : ∀ i, Hol ε (a i)) :
    Hol ε (fun k => ∑ i ∈ s, a i k) := by
  choose F hF hFa using ha
  refine ⟨fun y => ∑ i ∈ s, F i y, ?_, fun k => ?_⟩
  · have hs := DifferentiableOn.sum (𝕜 := ℂ) (u := s) (fun i _ => hF i)
    have e : (fun y => ∑ i ∈ s, F i y) = ∑ i ∈ s, F i := by
      funext y
      rw [Finset.sum_apply]
    rw [e]
    exact hs
  simp only [hFa]

lemma Hol.entry (i j : Fin n) : Hol ε (fun k => toMK k i j) := by
  refine ⟨fun y => y i j, ?_, fun k => rfl⟩
  have hd : Differentiable ℂ (fun y : Fin n → Fin n → ℂ => y i j) := by fun_prop
  exact hd.differentiableOn

lemma differentiable_det (f : (Fin n → Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (hf : ∀ i j, Differentiable ℂ (fun y => f y i j)) : Differentiable ℂ (fun y => (f y).det) := by
  simp only [Matrix.det_apply']
  have hp : ∀ σ : Equiv.Perm (Fin n), Differentiable ℂ (fun y => ∏ i, f y (σ i) i) := fun σ => by
    have h : Differentiable ℂ (∏ i, (fun y : Fin n → Fin n → ℂ => f y (σ i) i)) :=
      Finset.prod_induction (fun i => (fun y : Fin n → Fin n → ℂ => f y (σ i) i))
        (fun g => Differentiable ℂ g) (fun a b ha hb => ha.mul hb) (differentiable_const 1)
        (fun i _ => hf (σ i) i)
    have e : (fun y => ∏ i, f y (σ i) i) = ∏ i, (fun y => f y (σ i) i) := by
      funext y
      rw [Finset.prod_apply]
    rw [e]
    exact h
  have hs := Differentiable.sum (𝕜 := ℂ) (u := Finset.univ)
    (A := fun (σ : Equiv.Perm (Fin n)) (y : Fin n → Fin n → ℂ) => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i)
    (fun σ _ => (differentiable_const (((Equiv.Perm.sign σ : ℤ) : ℂ))).mul (hp σ))
  have e : (fun y => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i) =
      ∑ σ : Equiv.Perm (Fin n), (fun y => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f y (σ i) i) := by
    funext y
    rw [Finset.sum_apply]
  rw [e]
  exact hs

lemma toMK_inv (k : KG ε) : toMK k⁻¹ = star (toMK k) := by
  have hu : toMK k * star (toMK k) = 1 :=
    Matrix.mem_unitaryGroup_iff.1 ((mem_KG ε (k : UJ ε)).1 k.2).1
  have hl : toMK k⁻¹ * toMK k = 1 := Units.inv_mul ((k : UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ)
  calc toMK k⁻¹ = toMK k⁻¹ * (toMK k * star (toMK k)) := by rw [hu, mul_one]
    _ = star (toMK k) := by rw [← mul_assoc, hl, one_mul]

lemma toMK_mul (g k : KG ε) : toMK (g * k) = toMK g * toMK k := rfl

lemma Hol.conjEntry (i j : Fin n) : Hol ε (fun k => star (toMK k i j)) := by
  refine ⟨fun y => ((Matrix.of y).det)⁻¹ * (Matrix.of y).adjugate j i, ?_, fun k => ?_⟩
  · have hdet : Differentiable ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y).det) :=
      differentiable_det (fun y => Matrix.of y) (fun a b => by simp only [Matrix.of_apply]; fun_prop)
    have hadj : Differentiable ℂ (fun y : Fin n → Fin n → ℂ => (Matrix.of y).adjugate j i) := by
      simp only [Matrix.adjugate_apply]
      exact differentiable_det _ (fun a b => by
        simp only [Matrix.updateRow_apply, Matrix.of_apply]
        split_ifs <;> fun_prop)
    intro y hy
    have hy1 : IsUnit (Matrix.of y) := by
      simp only [Set.mem_setOf_eq, KC] at hy
      exact hy.1
    have hne : (Matrix.of y).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 hy1).ne_zero
    exact ((hdet y).inv hne).differentiableWithinAt.mul (hadj y).differentiableWithinAt
  · have hu : toMK k * star (toMK k) = 1 :=
      Matrix.mem_unitaryGroup_iff.1 ((mem_KG ε (k : UJ ε)).1 k.2).1
    have hinv : (toMK k)⁻¹ = star (toMK k) := Matrix.inv_eq_right_inv hu
    have key : (toMK k)⁻¹ j i = ((toMK k).det)⁻¹ * (toMK k).adjugate j i := by
      rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv, smul_eq_mul]
    change ((toMK k).det)⁻¹ * (toMK k).adjugate j i = star (toMK k i j)
    rw [← key, hinv, Matrix.star_apply]

def Sep (ε : Fin n → Bool) (p : KG ε → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → KG ε → ℂ) (b : ι → C(KG ε, ℂ)), (∀ i, Hol ε (a i)) ∧
    ∀ g k, p (g⁻¹ * k) = ∑ i, a i g * b i k

lemma Sep.const (c : ℂ) : Sep ε (fun _ => c) :=
  ⟨Unit, inferInstance, fun _ _ => c, fun _ => ContinuousMap.const _ 1, fun _ => Hol.const c,
    fun g k => by simp⟩

lemma Sep.add {p q : KG ε → ℂ} (hp : Sep ε p) (hq : Sep ε q) : Sep ε (fun k => p k + q k) := by
  obtain ⟨ι, _, a, b, ha, hab⟩ := hp
  obtain ⟨κ, _, c, d, hc, hcd⟩ := hq
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim a c, Sum.elim b d, ?_, fun g k => ?_⟩
  · rintro (i | i)
    · exact ha i
    · exact hc i
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hab, hcd]

lemma Sep.mul {p q : KG ε → ℂ} (hp : Sep ε p) (hq : Sep ε q) : Sep ε (fun k => p k * q k) := by
  obtain ⟨ι, _, a, b, ha, hab⟩ := hp
  obtain ⟨κ, _, c, d, hc, hcd⟩ := hq
  refine ⟨ι × κ, inferInstance, fun x g => a x.1 g * c x.2 g, fun x => b x.1 * d x.2,
    fun x => (ha x.1).mul (hc x.2), fun g k => ?_⟩
  show p (g⁻¹ * k) * q (g⁻¹ * k) = _
  rw [hab, hcd, Fintype.sum_prod_type, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousMap.mul_apply]
  ring

lemma isEmb (ε : Fin n → Bool) : Topology.IsEmbedding (fun k : KG ε => toMK k) := by
  have hc : Continuous (fun k : KG ε => toMK k) :=
    Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hi : Function.Injective (fun k : KG ε => toMK k) := fun a b h =>
    Subtype.ext (Subtype.ext (Units.ext h))
  exact (hc.isClosedEmbedding hi).isEmbedding

def ent (ε : Fin n → Bool) (i j : Fin n) : C(KG ε, ℂ) :=
  ⟨fun k => toMK k i j, (continuous_apply_apply i j).comp (isEmb ε).continuous⟩

lemma Sep.entry (i j : Fin n) : Sep ε (ent ε i j) := by
  refine ⟨Fin n, inferInstance, fun l g => star (toMK g l i), fun l => ent ε l j,
    fun l => Hol.conjEntry l i, fun g k => ?_⟩
  show toMK (g⁻¹ * k) i j = ∑ l, star (toMK g l i) * toMK k l j
  rw [toMK_mul, toMK_inv, Matrix.mul_apply]
  simp only [Matrix.star_apply]

lemma Sep.conjEntry (i j : Fin n) : Sep ε (star (ent ε i j) : C(KG ε, ℂ)) := by
  refine ⟨Fin n, inferInstance, fun l g => toMK g l i, fun l => star (ent ε l j),
    fun l => Hol.entry l i, fun g k => ?_⟩
  show star (toMK (g⁻¹ * k) i j) = ∑ l, toMK g l i * star (toMK k l j)
  rw [toMK_mul, toMK_inv, Matrix.mul_apply, star_sum]
  simp only [Matrix.star_apply, star_mul', star_star]

def sepAlg (ε : Fin n → Bool) : StarSubalgebra ℂ C(KG ε, ℂ) where
  carrier := {p | Sep ε p ∧ Sep ε (star p : C(KG ε, ℂ))}
  mul_mem' := fun {p q} hp hq => ⟨hp.1.mul hq.1, by
    rw [star_mul']; exact hp.2.mul hq.2⟩
  add_mem' := fun {p q} hp hq => ⟨hp.1.add hq.1, by
    rw [star_add]; exact hp.2.add hq.2⟩
  algebraMap_mem' := fun c => ⟨by
    have : ((algebraMap ℂ C(KG ε, ℂ) c : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => c := by
      funext k; simp
    rw [this]; exact Sep.const c, by
    have : ((star (algebraMap ℂ C(KG ε, ℂ) c) : C(KG ε, ℂ)) : KG ε → ℂ) = fun _ => star c := by
      funext k; simp
    rw [this]; exact Sep.const _⟩
  star_mem' := fun {p} hp => ⟨hp.2, by rw [star_star]; exact hp.1⟩

lemma sepAlg_dense (ε : Fin n → Bool) : (sepAlg ε).topologicalClosure = ⊤ := by
  refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
  intro x y hxy
  have hne : toMK x ≠ toMK y := fun h => hxy ((isEmb ε).injective h)
  obtain ⟨i, j, hij⟩ : ∃ i j, toMK x i j ≠ toMK y i j := by
    by_contra hcon
    push_neg at hcon
    exact hne (Matrix.ext hcon)
  have hmem : ent ε i j ∈ sepAlg ε := ⟨Sep.entry i j, Sep.conjEntry i j⟩
  exact ⟨_, ⟨ent ε i j, hmem, rfl⟩, hij⟩

private theorem integrable_of_continuous_isFiniteMeasure {E : Type*} [NormedAddCommGroup E] {f : KG ε → E} (hf : Continuous f) :
    Integrable f (muK ε) :=
  hf.integrable_of_hasCompactSupport (isClosed_tsupport f).isCompact

lemma eq_zero_of_orth (φ : C(KG ε, ℂ))
    (h : ∀ p : C(KG ε, ℂ), Sep ε p → ∫ k, p k * φ k ∂(muK ε) = 0) : φ = 0 := by
  let L : C(KG ε, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun p => ∫ k, p k * φ k ∂(muK ε)
      map_add' := fun p q => by
        simp only [ContinuousMap.add_apply, add_mul]
        exact integral_add (integrable_of_continuous_isFiniteMeasure (p.continuous.mul φ.continuous))
          (integrable_of_continuous_isFiniteMeasure (q.continuous.mul φ.continuous))
      map_smul' := fun c p => by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
        exact integral_const_mul c _ }
  have hL : Continuous L := by
    refine AddMonoidHomClass.continuous_of_bound L (∫ k, ‖φ k‖ ∂(muK ε)) fun p => ?_
    calc ‖L p‖ = ‖∫ k, p k * φ k ∂(muK ε)‖ := rfl
      _ ≤ ∫ k, ‖p‖ * ‖φ k‖ ∂(muK ε) := by
          refine norm_integral_le_of_norm_le ((integrable_of_continuous_isFiniteMeasure φ.continuous).norm.const_mul _) ?_
          refine Filter.Eventually.of_forall fun k => ?_
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (p.norm_coe_le_norm k) (norm_nonneg _)
      _ = (∫ k, ‖φ k‖ ∂(muK ε)) * ‖p‖ := by rw [integral_const_mul, mul_comm]
  have hcl : IsClosed {p : C(KG ε, ℂ) | L p = 0} := isClosed_eq hL continuous_const
  have hsub : ((sepAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) ⊆ {p | L p = 0} := by
    intro p hp
    exact h p hp.1
  have hall : ∀ p : C(KG ε, ℂ), L p = 0 := by
    intro p
    have hp : p ∈ closure ((sepAlg ε : StarSubalgebra ℂ C(KG ε, ℂ)) : Set C(KG ε, ℂ)) := by
      rw [← StarSubalgebra.topologicalClosure_coe, SetLike.mem_coe, sepAlg_dense]
      exact StarSubalgebra.mem_top
    exact closure_minimal hsub hcl hp
  have h1 : ∫ k, (star φ) k * φ k ∂(muK ε) = 0 := hall (star φ)
  have e : ∀ k, (star φ) k * φ k = ((‖φ k‖ ^ 2 : ℝ) : ℂ) := fun k => by
    rw [ContinuousMap.star_apply, Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  simp only [e, integral_ofReal] at h1
  have hreal : ∫ k, ‖φ k‖ ^ 2 ∂(muK ε) = 0 := by exact_mod_cast h1
  have hae : (fun k => ‖φ k‖ ^ 2) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun k => sq_nonneg ‖φ k‖)
      (integrable_of_continuous_isFiniteMeasure (φ.continuous.norm.pow 2))).1 hreal
  have heq : (fun k => ‖φ k‖ ^ 2) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) (φ.continuous.norm.pow 2) continuous_const).1 hae
  ext k
  have hk := congrFun heq k
  simpa using hk

end GlobalTheory.KHolExt
