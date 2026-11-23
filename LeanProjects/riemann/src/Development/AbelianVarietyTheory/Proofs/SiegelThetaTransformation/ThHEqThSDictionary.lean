import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.Dict

noncomputable section

section Levels

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
theorem _root_.GlobalTheory.SW.Dict.intM_nsmul {K κ ι : Type} [Field K] (R : ℕ) {x : Matrix κ ι K}
    (h : _root_.GlobalTheory.SW.IntM x) :
    _root_.GlobalTheory.SW.IntM (R • x) := by
  intro k i
  simpa using (h k i).nsmul R

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
theorem _root_.GlobalTheory.SW.Dict.isSB_comp {K K' κ ι κ' ι' : Type} [Field K] [Field K']
    (e : Matrix κ ι K →+ Matrix κ' ι' K') (D D' : ℕ) (hD : 0 < D) (hD' : 0 < D')
    (h1 : ∀ x, _root_.GlobalTheory.SW.IntM x → _root_.GlobalTheory.SW.IntM (D • e x))
    (h2 : ∀ x, _root_.GlobalTheory.SW.IntM (e x) → _root_.GlobalTheory.SW.IntM (D' • x))
    {φ : Matrix κ' ι' K' → ℂ} (h : _root_.GlobalTheory.SW.IsSB φ) :
    _root_.GlobalTheory.SW.IsSB (fun x => φ (e x)) := by
  obtain ⟨R, hR, hsupp, hper⟩ := h
  simp only [Nat.cast_smul_eq_nsmul] at hsupp hper
  refine ⟨D * (D' * R), by positivity, ?_, ?_⟩ <;> simp only [Nat.cast_smul_eq_nsmul]
  · intro x hx
    have hx' := hsupp (e x) hx
    have h3 : _root_.GlobalTheory.SW.IntM (e (R • x)) := by rwa [map_nsmul]
    have h4 := _root_.GlobalTheory.SW.Dict.intM_nsmul D (h2 _ h3)
    rwa [smul_smul, smul_smul, mul_assoc] at h4
  · intro x y hy
    have h3 := _root_.GlobalTheory.SW.Dict.intM_nsmul D' (h1 y hy)
    have h4 := hper (e x) _ h3
    simp only [map_add, map_nsmul]
    rw [← h4, smul_smul, smul_smul]
    congr 2
    ring_nf

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
theorem _root_.GlobalTheory.SW.Dict.exists_den {K ι : Type} [Field K] [NumberField K]
    [Finite ι] (x : ι → K) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, IsIntegral ℤ (D • x i) := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image x)
  have hy' : ∀ i, IsIntegral ℤ (y • x i) := fun i => by
    simpa [Algebra.smul_def] using h (x i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun i => ?_⟩
  rcases Int.natAbs_eq y with hyn | hyn
  · have := hy' i
    rw [hyn] at this
    simpa [natCast_zsmul] using this
  · have := (hy' i).neg
    rw [hyn, neg_smul, neg_neg] at this
    simpa [natCast_zsmul] using this

end Levels

variable {E : Type} [Field E] [NumberField E] {n N : ℕ}

def ofQEquiv (E : Type) [Field E] [NumberField E] (n N : ℕ) :
    Matrix (Fin n) (QI E N) ℚ ≃+ Matrix (Fin n) (Fin N) E where
  toFun := ofQ
  invFun x := Matrix.of fun k p => (Module.finBasis ℚ E).repr (x k p.1) p.2
  left_inv m := by
    ext k p
    simp only [ofQ, Matrix.of_apply]
    rw [(Module.finBasis ℚ E).repr_sum_self]
  right_inv x := by
    ext k a
    simp only [ofQ, Matrix.of_apply]
    exact (Module.finBasis ℚ E).sum_repr _
  map_add' m m' := by
    ext k a
    simp [ofQ, add_smul, Finset.sum_add_distrib]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.Dict.exists_den_ofQ : ∃ D : ℕ, 0 < D ∧
    ∀ m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ, _root_.GlobalTheory.SW.IntM m →
    _root_.GlobalTheory.SW.IntM (D • _root_.GlobalTheory.SW.Dict.ofQEquiv E n N m) := by
  obtain ⟨D, hD, hb⟩ := _root_.GlobalTheory.SW.Dict.exists_den (Module.finBasis ℚ E)
  refine ⟨D, hD, fun m hm k a => ?_⟩
  show IsIntegral ℤ (D • ∑ j, m k (a, j) • Module.finBasis ℚ E j)
  rw [Finset.smul_sum]
  refine IsIntegral.sum _ fun j _ => ?_
  rw [smul_comm, Algebra.smul_def]
  exact ((hm k (a, j)).map (IsScalarTower.toAlgHom ℤ ℚ E)).mul (hb j)

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.Dict.exists_den_symm : ∃ D : ℕ, 0 < D ∧
    ∀ x : Matrix (Fin n) (Fin N) E, _root_.GlobalTheory.SW.IntM x →
    _root_.GlobalTheory.SW.IntM (D • (_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).symm x) := by
  obtain ⟨D, hD, hc⟩ := _root_.GlobalTheory.SW.Dict.exists_den
    (fun p : _ × Fin (Module.finrank ℚ E) => (Module.finBasis ℚ E).repr (integralBasis E p.1) p.2)
  have key : ∀ y ∈ Submodule.span ℤ (Set.range (integralBasis E)),
      ∀ j, IsIntegral ℤ (D • (Module.finBasis ℚ E).repr y j) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact fun j => hc (i, j)
    | zero => intro j; simpa using isIntegral_zero
    | add y z _ _ hy hz =>
      intro j
      simpa [smul_add] using (hy j).add (hz j)
    | smul a y _ hy =>
      intro j
      rw [map_zsmul, Finsupp.smul_apply, smul_comm]
      simpa [zsmul_eq_mul] using (isIntegral_algebraMap (R := ℤ) (A := ℚ) (x := a)).mul (hy j)
  refine ⟨D, hD, fun x hx k p => ?_⟩
  show IsIntegral ℤ (D • (Module.finBasis ℚ E).repr (x k p.1) p.2)
  exact key _ ((mem_span_integralBasis E).mpr ⟨⟨x k p.1, hx k p.1⟩, rfl⟩) p.2

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.Dict.isSB_iff (φ : Matrix (Fin n) (Fin N) E → ℂ) :
    _root_.GlobalTheory.SW.IsSB φ ↔
      _root_.GlobalTheory.SW.IsSB (fun m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ =>
        φ (_root_.GlobalTheory.SW.ofQ m)) := by
  obtain ⟨D, hD, h1⟩ := _root_.GlobalTheory.SW.Dict.exists_den_ofQ (E := E) (n := n) (N := N)
  obtain ⟨D', hD', h2⟩ := _root_.GlobalTheory.SW.Dict.exists_den_symm (E := E) (n := n) (N := N)
  constructor
  · intro h
    refine _root_.GlobalTheory.SW.Dict.isSB_comp
      (_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).toAddMonoidHom D D' hD hD' h1 (fun m hm => ?_) h
    simpa using h2 _ hm
  · intro h
    have := _root_.GlobalTheory.SW.Dict.isSB_comp
      (_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).symm.toAddMonoidHom D' D hD' hD h2
      (fun x hx => by simpa using h1 _ hx) h
    convert this using 2 with x
    exact congrArg φ ((_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).apply_symm_apply x).symm

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.Dict.exists_emb_comb (c : Fin (Module.finrank ℚ E) → ℂ) :
    ∃ w : (E →+* ℂ) → ℂ, ∀ j, ∑ σ : E →+* ℂ, σ (Module.finBasis ℚ E j) * w σ = c j := by
  classical
  have hcard : Fintype.card (Fin (Module.finrank ℚ E)) = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [Fintype.card_fin, AlgHom.card]
  let e : Fin (Module.finrank ℚ E) ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let M := Algebra.embeddingsMatrixReindex ℚ ℂ (Module.finBasis ℚ E) e
  have hdet : M.det ≠ 0 := by
    intro h0
    have h := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (Module.finBasis ℚ E) e
    rw [h0, zero_pow two_ne_zero, map_eq_zero] at h
    exact Algebra.discr_not_zero_of_basis ℚ (Module.finBasis ℚ E) h
  obtain ⟨v, hv⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr
    ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet))) c
  refine ⟨fun σ => v (e.symm (RingHom.equivRatAlgHom E ℂ σ)), fun j => ?_⟩
  rw [← hv]
  simp only [mulVec, dotProduct]
  refine Fintype.sum_equiv ((RingHom.equivRatAlgHom E ℂ).trans e.symm) _ _ fun σ => ?_
  simp [M, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
theorem _root_.GlobalTheory.SW.Dict.sum_type {Ψ : Finset (E →+* ℂ)}
    (hΨ : _root_.GlobalTheory.SW.IsType Ψ) (f : (E →+* ℂ) → ℂ) :
    ∑ σ, f σ = ∑ τ : Ψ, (f τ + f (ComplexEmbedding.conjugate τ.1)) := by
  classical
  have hc : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
    fun φ => by ext x; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [Finset.sum_add_distrib, Finset.sum_coe_sort Ψ f]
  have hconj : ∑ τ : Ψ, f (ComplexEmbedding.conjugate τ.1) = ∑ σ ∈ Ψᶜ, f σ := by
    rw [Finset.sum_coe_sort Ψ (fun σ => f (ComplexEmbedding.conjugate σ))]
    refine Finset.sum_nbij' ComplexEmbedding.conjugate ComplexEmbedding.conjugate ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact Finset.mem_compl.mpr ((hΨ a).mp ha)
    · intro a ha
      have := (hΨ (ComplexEmbedding.conjugate a)).mpr
      rw [hc] at this
      exact this (Finset.mem_compl.mp ha)
    · intro a _; exact hc a
    · intro a _; exact hc a
    · intro a _; rfl
  rw [hconj]
  exact (Finset.sum_add_sum_compl Ψ f).symm

variable (Ψ : Finset (E →+* ℂ))

def vec (σ : E →+* ℂ) (m : QI E N → ℂ) : Fin N → ℂ :=
  fun a => ∑ j, σ (Module.finBasis ℚ E j) * m (a, j)

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable (Ψ : Finset (E →+* ℂ)) in
theorem _root_.GlobalTheory.SW.Dict.quad_tauOf (Z : _root_.GlobalTheory.SW.CM Ψ N N)
    (m : _root_.GlobalTheory.SW.QI E N → ℂ) (hm : ∀ p, conj (m p) = m p) :
    m ⬝ᵥ _root_.GlobalTheory.SW.tauOf Ψ Z *ᵥ m =
      2 * ∑ τ : Ψ, _root_.GlobalTheory.SW.Dict.vec τ.1 m ⬝ᵥ Z τ *ᵥ
        fun a => conj (_root_.GlobalTheory.SW.Dict.vec τ.1 m a) := by
  rw [two_mul]
  simp only [dotProduct, mulVec, _root_.GlobalTheory.SW.tauOf, _root_.GlobalTheory.SW.Dict.vec, Matrix.of_apply, map_sum, map_mul, hm, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_add, add_mul, Finset.sum_add_distrib]
  congr 1
  ·
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · refine (Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
    conv_lhs => rw [Finset.sum_comm]
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
    refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable (Ψ : Finset (E →+* ℂ)) in
theorem _root_.GlobalTheory.SW.Dict.lin_zetaOf (z z' : _root_.GlobalTheory.SW.CM Ψ n N)
    (k : Fin n) (m : _root_.GlobalTheory.SW.QI E N → ℂ) (hm : ∀ p, conj (m p) = m p) :
    m ⬝ᵥ _root_.GlobalTheory.SW.zetaOf Ψ z z' k =
      ∑ τ : Ψ, (_root_.GlobalTheory.SW.Dict.vec τ.1 m ⬝ᵥ z τ k +
        z' τ k ⬝ᵥ fun a => conj (_root_.GlobalTheory.SW.Dict.vec τ.1 m a)) := by
  simp only [dotProduct, _root_.GlobalTheory.SW.zetaOf, _root_.GlobalTheory.SW.Dict.vec, map_sum, map_mul, hm, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := (Finset.univ : Finset Ψ))]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset Ψ))]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable (Ψ : Finset (E →+* ℂ)) in
theorem _root_.GlobalTheory.SW.Dict.map_ofQ (σ : E →+* ℂ)
    (m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ) (k : Fin n) (a : Fin N) :
    σ (_root_.GlobalTheory.SW.ofQ m k a) =
      _root_.GlobalTheory.SW.Dict.vec σ (_root_.GlobalTheory.SW.qv (m k)) a := by
  simp only [_root_.GlobalTheory.SW.ofQ, Matrix.of_apply, map_sum,
    _root_.GlobalTheory.SW.Dict.vec, _root_.GlobalTheory.SW.qv]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast, mul_comm]

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable (Ψ : Finset (E →+* ℂ)) in
theorem _root_.GlobalTheory.SW.Dict.thH_eq (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (Z : _root_.GlobalTheory.SW.CM Ψ N N) (z z' : _root_.GlobalTheory.SW.CM Ψ n N) :
    _root_.GlobalTheory.SW.thH Ψ φ Z z z' =
      _root_.GlobalTheory.SW.thS (fun m => φ (_root_.GlobalTheory.SW.ofQ m))
        (_root_.GlobalTheory.SW.tauOf Ψ Z) (_root_.GlobalTheory.SW.zetaOf Ψ z z') := by
  have hreal : ∀ (m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ) k p,
      conj (_root_.GlobalTheory.SW.qv (m k) p) = _root_.GlobalTheory.SW.qv (m k) p := by
    intro m k p
    simp [_root_.GlobalTheory.SW.qv]
  unfold _root_.GlobalTheory.SW.thH _root_.GlobalTheory.SW.thS
  rw [← (_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).toEquiv.tsum_eq]
  refine tsum_congr fun m => ?_
  change φ (_root_.GlobalTheory.SW.ofQ m) * _ = _
  congr 2
  rw [Finset.sum_congr rfl fun k _ => by
    rw [_root_.GlobalTheory.SW.Dict.quad_tauOf Ψ Z _ (hreal m k),
      _root_.GlobalTheory.SW.Dict.lin_zetaOf Ψ z z' k _ (hreal m k)]]
  unfold _root_.GlobalTheory.SW.expo
  change 2 * (π : ℂ) * I * ∑ τ : Ψ, ∑ k, (((fun a => (τ : E →+* ℂ) (_root_.GlobalTheory.SW.ofQ m k a)) ⬝ᵥ
    Z τ *ᵥ fun a => conj ((τ : E →+* ℂ) (_root_.GlobalTheory.SW.ofQ m k a))) +
    (fun a => (τ : E →+* ℂ) (_root_.GlobalTheory.SW.ofQ m k a)) ⬝ᵥ z τ k +
    z' τ k ⬝ᵥ fun a => conj ((τ : E →+* ℂ) (_root_.GlobalTheory.SW.ofQ m k a))) = _
  simp only [_root_.GlobalTheory.SW.Dict.map_ofQ]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Finset.sum_add_distrib]
  ring

variable {Ψ}

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable (Ψ : Finset (E →+* ℂ)) in
variable {Ψ} in
theorem _root_.GlobalTheory.SW.Dict.zetaOf_surj (hΨ : _root_.GlobalTheory.SW.IsType Ψ)
    (ζ : Fin n → _root_.GlobalTheory.SW.QI E N → ℂ) :
    ∃ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.zetaOf Ψ z z' = ζ := by
  choose w hw using fun (k : Fin n) (a : Fin N) =>
    _root_.GlobalTheory.SW.Dict.exists_emb_comb (E := E) (fun j => ζ k (a, j))
  refine ⟨fun τ => Matrix.of fun k a => w k a τ,
    fun τ => Matrix.of fun k a => w k a (ComplexEmbedding.conjugate τ.1), ?_⟩
  funext k p
  obtain ⟨a, j⟩ := p
  rw [← hw k a j, _root_.GlobalTheory.SW.Dict.sum_type hΨ]
  simp only [_root_.GlobalTheory.SW.zetaOf, Matrix.of_apply, ComplexEmbedding.conjugate_coe_eq]
  exact Finset.sum_congr rfl fun _ _ => by ring

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] {n N : ℕ} in
variable (Ψ : Finset (E →+* ℂ)) in
variable {Ψ} in
theorem _root_.GlobalTheory.SW.Dict.tauOf_mem (hΨ : _root_.GlobalTheory.SW.IsType Ψ)
    (Z : _root_.GlobalTheory.SW.CM Ψ N N) (hZ : Z ∈ _root_.GlobalTheory.SW.Hn Ψ N) :
    _root_.GlobalTheory.SW.tauOf Ψ Z ∈ _root_.GlobalTheory.SW.Siegel (_root_.GlobalTheory.SW.QI E N) := by
  have hinv : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate φ) = φ :=
    fun φ => by ext y; simp [ComplexEmbedding.conjugate_coe_eq]
  refine ⟨Matrix.IsSymm.ext fun p q => ?_, ?_⟩
  · simp only [_root_.GlobalTheory.SW.tauOf, Matrix.of_apply]
    exact Finset.sum_congr rfl fun _ _ => add_comm _ _
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨Matrix.IsHermitian.ext fun p q => ?_, fun x hx => ?_⟩
  · simp only [Matrix.map_apply, star_trivial, _root_.GlobalTheory.SW.tauOf, Matrix.of_apply]
    congr 1
    exact Finset.sum_congr rfl fun _ _ => add_comm _ _
  rw [star_trivial]
  set m : _root_.GlobalTheory.SW.QI E N → ℂ := fun p => (x p : ℂ) with hmdef
  have hm : ∀ p, conj (m p) = m p := fun p => Complex.conj_ofReal _
  have hid : x ⬝ᵥ (_root_.GlobalTheory.SW.tauOf Ψ Z).map Complex.im *ᵥ x =
      (m ⬝ᵥ _root_.GlobalTheory.SW.tauOf Ψ Z *ᵥ m).im := by
    simp only [m, dotProduct, mulVec, Matrix.map_apply, Complex.im_sum, Complex.im_ofReal_mul,
      Complex.im_mul_ofReal]
  rw [hid, _root_.GlobalTheory.SW.Dict.quad_tauOf Ψ Z m hm]
  set v := fun τ : Ψ => _root_.GlobalTheory.SW.Dict.vec τ.1 m with hvdef
  have hterm : ∀ τ : Ψ, (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)).im =
      (star (fun a => conj (v τ a)) ⬝ᵥ _root_.GlobalTheory.SW.imH (Z τ) *ᵥ
        fun a => conj (v τ a)).re := by
    intro τ
    have hstar : star (fun a => conj (v τ a)) = v τ := by
      funext a; simp
    have hconjT : v τ ⬝ᵥ (Z τ)ᴴ *ᵥ (fun a => conj (v τ a)) =
        conj (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)) := by
      simp only [dotProduct, mulVec, conjTranspose_apply, map_sum, map_mul, Complex.star_def,
        Complex.conj_conj, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hstar]
    unfold _root_.GlobalTheory.SW.imH
    rw [Matrix.smul_mulVec, dotProduct_smul, Matrix.sub_mulVec, dotProduct_sub, hconjT,
      Complex.sub_conj, smul_eq_mul]
    all_goals simp [Complex.mul_re, Complex.inv_re, Complex.inv_im, Complex.normSq]
    all_goals field_simp
  have hpos : ∀ τ : Ψ, v τ ≠ 0 → 0 < (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)).im := by
    intro τ hv
    have hw : (fun a => conj (v τ a)) ≠ 0 := by
      intro h0
      apply hv
      funext a
      have := congrFun h0 a
      simpa using this
    have := (hZ τ).dotProduct_mulVec_pos hw
    rw [hterm]
    exact (Complex.lt_def.mp this).1
  have hnonneg : ∀ τ : Ψ, 0 ≤ (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)).im := by
    intro τ
    by_cases hv : v τ = 0
    · rw [hv]; simp
    · exact (hpos τ hv).le
  have hex : ∃ τ : Ψ, v τ ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hall : ∀ σ : E →+* ℂ, ∀ a, ∑ j, σ (Module.finBasis ℚ E j) * m (a, j) = 0 := by
      intro σ a
      by_cases hσ : σ ∈ Ψ
      · exact congrFun (hne ⟨σ, hσ⟩) a
      · have hc : ComplexEmbedding.conjugate σ ∈ Ψ := by
          have := (hΨ (ComplexEmbedding.conjugate σ)).mpr
          rw [hinv] at this
          exact this hσ
        have h1 := congrFun (hne ⟨_, hc⟩) a
        simp only [hvdef, _root_.GlobalTheory.SW.Dict.vec,
          ComplexEmbedding.conjugate_coe_eq, Pi.zero_apply] at h1
        have h2 := congrArg conj h1
        simpa [map_sum, hm] using h2
    apply hx
    funext p
    obtain ⟨a, j0⟩ := p
    obtain ⟨w, hw⟩ := _root_.GlobalTheory.SW.Dict.exists_emb_comb (E := E) (fun j => m (a, j))
    have hsq : ∑ j, m (a, j) * m (a, j) = 0 := by
      calc ∑ j, m (a, j) * m (a, j)
          = ∑ j, (∑ σ : E →+* ℂ, σ (Module.finBasis ℚ E j) * w σ) * m (a, j) := by
            simp only [hw]
        _ = ∑ σ : E →+* ℂ, w σ * ∑ j, σ (Module.finBasis ℚ E j) * m (a, j) := by
            simp only [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        _ = 0 := by simp [hall]
    have hsqR : ∑ j, x (a, j) * x (a, j) = 0 := by
      have : ((∑ j, x (a, j) * x (a, j) : ℝ) : ℂ) = 0 := by
        push_cast
        exact hsq
      exact_mod_cast this
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x (a, j)))).mp hsqR
      j0 (Finset.mem_univ _)
    simpa using mul_self_eq_zero.mp h0
  obtain ⟨τ0, hτ0⟩ := hex
  have hsum : 0 < ∑ τ : Ψ, (v τ ⬝ᵥ Z τ *ᵥ fun a => conj (v τ a)).im :=
    Finset.sum_pos' (fun τ _ => hnonneg τ) ⟨τ0, Finset.mem_univ _, hpos τ0 hτ0⟩
  simp only [Complex.im_sum, Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero]
  simpa [hvdef] using mul_pos two_pos hsum

end

end GlobalTheory.SW.Dict

open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in

theorem _root_.GlobalTheory.SW.thH_eq_thS_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), _root_.GlobalTheory.SW.IsType Ψ → ∀ (n N : ℕ), Function.Bijective (_root_.GlobalTheory.SW.ofQ : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ → Matrix (Fin n) (Fin N) E) ∧ (∀ Z ∈ _root_.GlobalTheory.SW.Hn Ψ N, _root_.GlobalTheory.SW.tauOf Ψ Z ∈ _root_.GlobalTheory.SW.Siegel (_root_.GlobalTheory.SW.QI E N)) ∧ (∀ ζ : Fin n → _root_.GlobalTheory.SW.QI E N → ℂ, ∃ z z' : _root_.GlobalTheory.SW.CM Ψ n N, _root_.GlobalTheory.SW.zetaOf Ψ z z' = ζ) ∧ (∀ (φ : Matrix (Fin n) (Fin N) E → ℂ) Z z z', _root_.GlobalTheory.SW.thH Ψ φ Z z z' = _root_.GlobalTheory.SW.thS (fun m => φ (_root_.GlobalTheory.SW.ofQ m)) (_root_.GlobalTheory.SW.tauOf Ψ Z) (_root_.GlobalTheory.SW.zetaOf Ψ z z')) ∧ ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, _root_.GlobalTheory.SW.IsSB φ ↔ _root_.GlobalTheory.SW.IsSB (fun m : Matrix (Fin n) (_root_.GlobalTheory.SW.QI E N) ℚ => φ (_root_.GlobalTheory.SW.ofQ m)) := by
  intro E _ _ _ Ψ hΨ n N
  exact ⟨(_root_.GlobalTheory.SW.Dict.ofQEquiv E n N).bijective,
    fun Z hZ => _root_.GlobalTheory.SW.Dict.tauOf_mem hΨ Z hZ,
    fun ζ => _root_.GlobalTheory.SW.Dict.zetaOf_surj hΨ ζ,
    fun φ Z z z' => _root_.GlobalTheory.SW.Dict.thH_eq Ψ φ Z z z',
    fun φ => _root_.GlobalTheory.SW.Dict.isSB_iff φ⟩
