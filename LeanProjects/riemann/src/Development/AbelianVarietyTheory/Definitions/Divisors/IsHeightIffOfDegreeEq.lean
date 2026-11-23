import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.BlockSphereMeanLinForm
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSubPtsCutBaseChangeIff
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import Development.AbelianVarietyTheory.Definitions.Divisors.IrreducibleOfIrreducibleMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Adelic

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.ChowHt

section Sizes

variable {F K : Type} [Field F] [Field K] {N n : ℕ}

def finSize (w : Matrix (Fin N) (Fin n) F) (φ : F →+* K) (v : AbsoluteValue K ℝ) (y : Fin N → K) : ℝ :=
  ⨆ k, v (∑ j, φ (w j k) * y j)

def archSize (A : Matrix (Fin N) (Fin N) ℂ) (y : Fin N → ℂ) : ℝ := Real.sqrt (∑ i, ‖∑ j, A j i * y j‖ ^ 2)

theorem pointHeight_eq [NumberField F] [NumberField K] [Algebra F K] (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (y : Fin N → K) :
    pointHeight w A y = ((∑ᶠ v : FinitePlace K, Real.log (finSize w (algebraMap F K) v.1 y)) +
      ∑ τ : K →+* ℂ, Real.log (archSize (A (τ.comp (algebraMap F K))) fun j => τ (y j))) /
        (Module.finrank ℚ K : ℝ) := rfl

theorem le_finSize (w : Matrix (Fin N) (Fin n) F) (φ : F →+* K) (v : AbsoluteValue K ℝ) (y : Fin N → K) (k : Fin n) :
    v (∑ j, φ (w j k) * y j) ≤ finSize w φ v y :=
  le_ciSup (f := fun k => v (∑ j, φ (w j k) * y j)) (Set.finite_range _).bddAbove k

theorem finSize_nonneg (w : Matrix (Fin N) (Fin n) F) (φ : F →+* K) (v : AbsoluteValue K ℝ) (y : Fin N → K) :
    0 ≤ finSize w φ v y := Real.iSup_nonneg fun _ => v.nonneg _

theorem finSize_smul (w : Matrix (Fin N) (Fin n) F) (φ : F →+* K) (v : AbsoluteValue K ℝ) (c : K) (y : Fin N → K) :
    finSize w φ v (c • y) = v c * finSize w φ v y := by
  rw [finSize, finSize, Real.mul_iSup_of_nonneg (v.nonneg c)]
  refine iSup_congr fun k => ?_
  rw [← map_mul, Finset.mul_sum]
  exact congrArg v (Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _)

theorem archSize_smul (A : Matrix (Fin N) (Fin N) ℂ) (c : ℂ) (y : Fin N → ℂ) :
    archSize A (c • y) = ‖c‖ * archSize A y := by
  rw [archSize, archSize, ← Real.sqrt_sq (norm_nonneg c), ← Real.sqrt_mul (sq_nonneg _), Finset.mul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [← mul_pow, ← norm_mul, Finset.mul_sum]
  exact congrArg (‖·‖ ^ 2) (Finset.sum_congr rfl fun j _ => mul_left_comm _ _ _)

theorem finSize_pos {w : Matrix (Fin N) (Fin n) F} (hw : Submodule.span F (Set.range w.col) = ⊤) (φ : F →+* K)
    (v : AbsoluteValue K ℝ) {y : Fin N → K} (hy : y ≠ 0) : 0 < finSize w φ v y := by
  refine (finSize_nonneg w φ v y).lt_of_ne' fun h => hy (funext fun j => ?_)
  have h0 : ∀ k, ∑ j, φ (w j k) * y j = 0 := fun k =>
    v.eq_zero.1 (le_antisymm (h ▸ le_finSize w φ v y k) (v.nonneg _))
  have key : ∀ u ∈ Submodule.span F (Set.range w.col), ∑ j, φ (u j) * y j = 0 := fun u hu => by
    induction hu using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; exact h0 k
    | zero => simp
    | add a b _ _ ha hb => simp [add_mul, Finset.sum_add_distrib, ha, hb]
    | smul c a _ ha => simp [mul_assoc, ← Finset.mul_sum, ha]
  simpa [Pi.single_apply, apply_ite φ] using key (Pi.single j 1) (hw ▸ trivial)

theorem archSize_pos {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) {y : Fin N → ℂ} (hy : y ≠ 0) :
    0 < archSize A y := by
  refine Real.sqrt_pos.2 ((Finset.sum_nonneg fun _ _ => sq_nonneg _).lt_of_ne' fun h => hy ?_)
  refine Matrix.eq_zero_of_vecMul_eq_zero hA (funext fun i => ?_)
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h i (Finset.mem_univ i)
  simpa [Matrix.vecMul, dotProduct, mul_comm] using this

theorem norm_pairing_le {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.det ≠ 0) (u y : Fin N → ℂ) :
    ‖∑ j, u j * y j‖ ≤ frameNorm A u * archSize A y := by
  have e : ∑ j, u j * y j = ∑ i, A⁻¹.mulVec u i * ∑ j, A j i * y j := by
    conv_lhs => rw [← Matrix.one_mulVec u, ← A.mul_nonsing_inv hA.isUnit, ← Matrix.mulVec_mulVec]
    generalize A⁻¹.mulVec u = c
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem pairing_mulVec_le (w : Matrix (Fin N) (Fin n) F) (φ : F →+* K) {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) {x : Fin n → K} (hx : ∀ k, v (x k) ≤ 1) (y : Fin N → K) :
    v (∑ j, (w.map φ).mulVec x j * y j) ≤ finSize w φ v y := by
  have e : ∑ j, (w.map φ).mulVec x j * y j = ∑ k, x k * ∑ j, φ (w j k) * y j := by
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  refine Finset.sum_induction _ (fun a => v a ≤ finSize w φ v y) (fun a b ha hb => (hv a b).trans (max_le ha hb))
    (by rw [map_zero]; exact finSize_nonneg w φ v y) fun k _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_left (v.nonneg _) (hx k)).trans (le_finSize w φ v y k)

variable {Ω : Type} [Field Ω] [Algebra F Ω]

abbrev coordField (F : Type) [Field F] [Algebra F Ω] (y : Fin N → Ω) : IntermediateField F Ω :=
  IntermediateField.adjoin F (Set.range y)

instance numberField_coordField [NumberField F] [Algebra.IsAlgebraic F Ω] (y : Fin N → Ω) :
    NumberField (coordField F y) :=
  have : FiniteDimensional F (coordField F y) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  NumberField.of_module_finite F _

def vecHeight [NumberField F] [Algebra.IsAlgebraic F Ω] (w : Matrix (Fin N) (Fin n) F)
    (A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (y : Fin N → Ω) : ℝ :=
  pointHeight w A (K := coordField F y) fun j => ⟨y j, IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩⟩

end Sizes

structure HermSys (F : Type) [Field F] [NumberField F] extends LinSys F where

  n : ℕ

  w : Matrix (Fin N) (Fin n) F

  A : (F →+* ℂ) → Matrix (Fin N) (Fin N) ℂ

  abelian₂ : ℝ

namespace HermSys

variable {F : Type} [Field F] [NumberField F] (T : HermSys F)

def gen (k : Fin T.n) : T.L.Sec := T.comb (T.w.col k)

def lattice : Submodule (𝓞 F) (Fin T.N → F) := Submodule.span (𝓞 F) (Set.range T.w.col)

def latticeOver (E : Type) [Field E] [Algebra F E] : Submodule (𝓞 E) (Fin T.N → E) :=
  Submodule.span (𝓞 E) (Set.range (T.w.map (algebraMap F E)).col)

def wVec {E : Type} [Field E] [Algebra F E] (x : Fin T.n → E) : Fin T.N → E := (T.w.map (algebraMap F E)).mulVec x

def normAt {E : Type} [Field E] [Algebra F E] (τ : E →+* ℂ) (u : Fin T.N → E) : ℝ :=
  frameNorm (T.A (τ.comp (algebraMap F E))) fun j => τ (u j)

def meanLogNorm {E : Type} [Field E] [NumberField E] [Algebra F E] (u : Fin T.N → E) : ℝ :=
  (∑ τ : E →+* ℂ, Real.log (T.normAt τ u)) / (Module.finrank ℚ E : ℝ)

def meanLogMaxNorm : ℝ := (∑ σ : F →+* ℂ, Real.log (⨆ k, T.normAt σ (T.w.col k))) / (Module.finrank ℚ F : ℝ)

def Spans : Prop := Submodule.span F (Set.range T.w.col) = ⊤

structure IsAlgebraicData : Prop where

  variety : T.IsVariety

  indep : T.Indep

  spans : T.Spans

  bpf : T.BasePointFree

def Hermitian : Prop := ∀ σ, (T.A σ).det ≠ 0

def ConjInvariant : Prop := ConjCompat T.A

def NormsLe : Prop := ∀ (k : Fin T.n) (σ : F →+* ℂ), T.normAt σ (T.w.col k) ≤ T.abelian₂

def IntGenerates : Prop := ∀ u ∈ T.lattice, u ∈ Submodule.span ℤ (Set.range T.w.col)

structure ShortGenerators : Prop where

  int : T.IntGenerates

  le : T.NormsLe

  one_le : 1 ≤ T.abelian₂

structure IsMetrized : Prop where

  alg : T.IsAlgebraicData

  herm : T.Hermitian

  conj : T.ConjInvariant

  le : T.NormsLe

  del_pos : 0 < T.del

def IsHeight (h : ℝ) : Prop :=
  ∃ (d : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F), 0 < d ∧ IsChowForm T.imageIdeal T.D d f ∧
    ((T.D : ℝ) + 1) * d * h = formHeight d T.w T.A f

theorem isHeight_iff {h : ℝ} : T.IsHeight h ↔ ∃ (d : ℕ) (f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F),
    IsChowForm T.imageIdeal T.D d f ∧ ((T.D : ℝ) + 1) * d * h = formHeight d T.w T.A f :=
  ⟨fun ⟨d, f, _, hf⟩ => ⟨d, f, hf⟩, fun ⟨d, f, hf, e⟩ => ⟨d, f, hf.isChowFormInt.pos, hf, e⟩⟩

theorem isHeight_of_isChowForm {d : ℕ} {f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F}
    (hf : IsChowForm T.imageIdeal T.D d f) : T.IsHeight (formHeight d T.w T.A f / (((T.D : ℝ) + 1) * d)) :=
  T.isHeight_iff.2 ⟨d, f, hf, mul_div_cancel₀ _
    (mul_ne_zero (by positivity) (Nat.cast_ne_zero.2 hf.isChowFormInt.pos.ne'))⟩

theorem isHeight_iff_of_degree_eq {d : ℕ} {g : MvPolynomial (Fin (T.D + 1) × Fin T.N) F}
    (hg : IsChowForm T.imageIdeal T.D d g) (hd : (d : ℤ) = T.del) {h : ℝ} :
    T.IsHeight h ↔ ∃ f : MvPolynomial (Fin (T.D + 1) × Fin T.N) F, IsChowForm T.imageIdeal T.D d f ∧
      ((T.D : ℝ) + 1) * T.del * h = formHeight d T.w T.A f := by
  rw [isHeight_iff, ← hd, Int.cast_natCast]
  refine ⟨fun ⟨d', f, hf, e⟩ => ?_, fun ⟨f, hf⟩ => ⟨d, f, hf⟩⟩
  obtain rfl := (hf.isChowFormInt.unique hg.isChowFormInt).1
  exact ⟨f, hf, e⟩

def baseChange (E : Type) [Field E] [NumberField E] [Algebra F E] : HermSys E where
  toLinSys := T.toLinSys.baseChange E
  n := T.n
  w := T.w.map (algebraMap F E)
  A τ := T.A (τ.comp (algebraMap F E))
  abelian₂ := T.abelian₂

theorem lattice_baseChange (E : Type) [Field E] [NumberField E] [Algebra F E] :
    (T.baseChange E).lattice = T.latticeOver E := rfl

theorem wVec_mem {E : Type} [Field E] [Algebra F E] (x : Fin T.n → 𝓞 E) :
    T.wVec (fun k => (x k : E)) ∈ T.latticeOver E := by
  have e : T.wVec (fun k => (x k : E)) = ∑ k, x k • (T.w.map (algebraMap F E)).col k := by
    funext j
    simp [wVec, Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  rw [e]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

section Norms

variable {K : Type} [Field K] {φ : F →+* K} {σ : F →+* ℂ}

def finNorm (v : AbsoluteValue K ℝ) (x : T.PtOver φ) (u : Fin T.N → K) : ℝ :=
  v (∑ j, u j * T.coords x.1 j) / finSize T.w φ v (T.coords x.1)

def finNormPow (v : AbsoluteValue K ℝ) (x : T.PtOver φ) {m : ℤ} (f : (lbZPow T.L m).Sec) : ℝ :=
  v (T.powVal x.1 f) / finSize T.w φ v (T.coords x.1) ^ m

def archNorm (x : T.PtOver σ) (u : Fin T.N → ℂ) : ℝ :=
  ‖∑ j, u j * T.coords x.1 j‖ / archSize (T.A σ) (T.coords x.1)

def archNormPow (x : T.PtOver σ) {m : ℤ} (f : (lbZPow T.L m).Sec) : ℝ :=
  ‖T.powVal x.1 f‖ / archSize (T.A σ) (T.coords x.1) ^ m

theorem finNormPow_eq_chart (v : AbsoluteValue K ℝ) (x : T.PtOver φ) {m : ℤ} (f : (lbZPow T.L m).Sec) (i : T.L.ι)
    (hi : ptOf x.1 ∈ T.L.U i) : T.finNormPow v x f =
      v (valR x.1 _ (Twist.zfun f i)) / finSize T.w φ v (fun j => valR x.1 _ ((T.b j).f i)) ^ m := by
  obtain ⟨c, hc, h₁, h₂⟩ := T.exists_frame_change x.1 i hi
  rw [h₂, show (fun j => valR x.1 _ ((T.b j).f i)) = c • T.coords x.1 from funext fun j => h₁ _, finSize_smul,
    map_mul, map_zpow₀, mul_zpow, mul_div_mul_left _ _ (zpow_ne_zero _ (v.ne_zero hc)), finNormPow]

theorem archNormPow_eq_chart (x : T.PtOver σ) {m : ℤ} (f : (lbZPow T.L m).Sec) (i : T.L.ι)
    (hi : ptOf x.1 ∈ T.L.U i) : T.archNormPow x f =
      ‖valR x.1 _ (Twist.zfun f i)‖ / archSize (T.A σ) (fun j => valR x.1 _ ((T.b j).f i)) ^ m := by
  obtain ⟨c, hc, h₁, h₂⟩ := T.exists_frame_change x.1 i hi
  rw [h₂, show (fun j => valR x.1 _ ((T.b j).f i)) = c • T.coords x.1 from funext fun j => h₁ _, archSize_smul,
    norm_mul, norm_zpow, mul_zpow, mul_div_mul_left _ _ (zpow_ne_zero _ (norm_ne_zero_iff.2 hc)), archNormPow]

variable {T}

theorem IsAlgebraicData.finSize_coords_pos (h : T.IsAlgebraicData) (v : AbsoluteValue K ℝ) (x : T.PtOver φ) :
    0 < finSize T.w φ v (T.coords x.1) := finSize_pos h.spans φ v (h.bpf.coords_ne_zero _)

theorem Hermitian.archSize_coords_pos (h : T.Hermitian) (hb : T.BasePointFree) (x : T.PtOver σ) :
    0 < archSize (T.A σ) (T.coords x.1) := archSize_pos (h σ) (hb.coords_ne_zero _)

theorem Hermitian.archNorm_le (h : T.Hermitian) (hb : T.BasePointFree) (x : T.PtOver σ) (u : Fin T.N → ℂ) :
    T.archNorm x u ≤ frameNorm (T.A σ) u :=
  (div_le_iff₀ (h.archSize_coords_pos hb x)).2 (norm_pairing_le (h σ) _ _)

theorem finNorm_mulVec_le_one {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (x : T.PtOver φ) {a : Fin T.n → K}
    (ha : ∀ k, v (a k) ≤ 1) : T.finNorm v x ((T.w.map φ).mulVec a) ≤ 1 :=
  div_le_one_of_le₀ (pairing_mulVec_le T.w φ hv ha _) (finSize_nonneg _ _ _ _)

end Norms

def ptHeight {Ω : Type} [Field Ω] [Algebra F Ω] [Algebra.IsAlgebraic F Ω] (x : T.Pt Ω) : ℝ :=
  vecHeight T.w T.A (T.coords x.1)

abbrev geomPts (E : Type) [Field E] [Algebra F E] (I : (T.toLinSys.baseChange E).Y.IdealSheafData) :
    Set ((T.toLinSys.baseChange E).Pt (AlgebraicClosure E)) :=
  (T.toLinSys.baseChange E).subPts I (AlgebraicClosure E)

def cycleHeight (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E]
    (I : (T.toLinSys.baseChange E).Y.IdealSheafData) : ℝ :=
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure E) := Algebra.IsAlgebraic.trans F E _
  ∑ᶠ x ∈ T.geomPts E I, T.ptHeight (LinSys.toBase x)

abbrev linSection (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) :
    (T.toLinSys.baseChange E).Y.IdealSheafData :=
  (T.toLinSys.baseChange E).cut s

end HermSys

structure Tuple (F : Type) [Field F] [NumberField F] extends HermSys F where

  bd : Closeds Y

  j₀ : ℕ

  th : (lbPow L j₀).Sec

namespace Tuple

variable {F : Type} [Field F] [NumberField F] (T : Tuple F)

def U : T.Y.Opens := T.bd.compl

structure IsGeometric : Prop where

  alg : T.IsAlgebraicData

  bd_ne : T.bd ≠ ⊤

structure IsBirationalOffBoundary : Prop where

  birational : T.Birational

  noContract : T.NoContract T.bd

  one_le : 1 ≤ T.j₀

  th_ne : T.th ≠ 0

  th_vanish : ∀ y ∈ T.bd, y ∉ nonzeroLocus T.th

structure IsAdelic : Prop where

  geom : T.IsGeometric

  bir : T.IsBirationalOffBoundary

  herm : T.Hermitian

  conj : T.ConjInvariant

  short : T.ShortGenerators

theorem IsAdelic.isMetrized {T : Tuple F} (h : T.IsAdelic) (hd : 0 < T.del) : T.IsMetrized :=
  ⟨h.geom.alg, h.herm, h.conj, h.short.le, hd⟩

def theta (h : ℝ) : ℝ := T.n * T.D * T.j₀ * T.del * (2 + |h| + Real.log T.abelian₂)

def InOpen (E : Type) [Field E] [Algebra F E] (I : (T.toLinSys.baseChange E).Y.IdealSheafData) : Prop :=
  ∀ y ∈ I.support, T.toLinSys.bcFst E y ∈ T.U

structure IsGoodSection (E : Type) [Field E] [Algebra F E] (s : Fin T.D → Fin T.N → E) : Prop where

  finiteEtale : (T.toLinSys.baseChange E).IsFiniteEtaleSub (T.linSection E s)

  inOpen : T.InOpen E (T.linSection E s)

theorem IsGoodSection.finite_geomPts {T : Tuple F} {E : Type} [Field E] [Algebra F E] {s : Fin T.D → Fin T.N → E}
    (h : T.IsGoodSection E s) : (T.geomPts E (T.linSection E s)).Finite :=
  h.finiteEtale.finite.finite_subPts _

end Tuple

abbrev projTuple (M : ℕ) : Tuple ℚ where
  toLinSys := projSys ℚ M
  n := M + 1
  w := 1
  A _ := 1
  abelian₂ := 1
  bd := (ProjSpace.chart ℚ M (Fin.last M)).compl
  j₀ := 1
  th := secToPow (ProjSpace.coord ℚ M (Fin.last M)) 1

namespace projTuple

variable (M : ℕ)

theorem spans : (projTuple M).Spans := top_le_iff.1 fun u _ => by
  rw [pi_eq_sum_univ' u]
  refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, ?_⟩)
  funext j
  simp [Matrix.one_apply, Pi.single_apply]

theorem shortGenerators : (projTuple M).ShortGenerators := by
  refine ⟨fun u hu => ?_, fun k σ => ?_, le_rfl⟩
  · induction hu using Submodule.span_induction with
    | mem _ h => exact Submodule.subset_span h
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul c a _ ha =>
      obtain ⟨z, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective c
      rw [eq_intCast Rat.ringOfIntegersEquiv.symm z, Int.cast_smul_eq_zsmul]
      exact Submodule.smul_mem _ _ ha
  · simp [HermSys.normAt, frameNorm, Matrix.one_apply, apply_ite]

theorem isAdelic (hM : 1 ≤ M) : (projTuple M).IsAdelic := by
  have hl : nonzeroLocus (projTuple M).th = ProjSpace.chart ℚ M (Fin.last M) :=
    (nonzeroLocus_secToPow _ le_rfl).trans (ProjSpace.nonzeroLocus_coord ℚ M (Fin.last M))
  refine ⟨⟨⟨projSys.isVariety ℚ M hM, projSys.indep ℚ M, spans M, projSys.basePointFree ℚ M⟩, fun h => ?_⟩,
    ⟨projSys.birational ℚ M, projSys.noContract ℚ M _, le_rfl, fun h => ?_, fun y hy => hl ▸ hy⟩,
    fun σ => by simp, fun σ x => by simp [frameNorm], shortGenerators M⟩
  · exact (h.ge (Set.mem_univ (projSys.gen ℚ M))) (projSys.gen_mem ℚ M _)
  · have := hl.ge (projSys.gen_mem ℚ M _)
    rw [h] at this
    exact nonzeroLocus_secZero.le this

theorem isMetrized (hM : 1 ≤ M) : (projTuple M).IsMetrized :=
  (isAdelic M hM).isMetrized ((projSys.del_eq_one ℚ M).symm ▸ one_pos)

theorem exists_isHeight_line : ∃ h, (projTuple 1).IsHeight h :=
  ⟨_ / 2, 1, _, one_pos, (projSys.imageIdeal_eq_bot ℚ 1).symm ▸ Model.isChowForm_line ℚ, by
    rw [Nat.cast_one, mul_one, one_add_one_eq_two, mul_div_cancel₀ _ two_ne_zero]⟩

end projTuple

example : (projTuple 1).U ≠ ⊤ := fun h =>
  AmpleModel.coord_ne_top ℚ ((ProjSpace.nonzeroLocus_coord ℚ 1 1).trans
    ((Opens.compl_compl (ProjSpace.chart ℚ 1 1)).symm.trans h))

example : archSize ((2 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ![1, 1] = Real.sqrt 8 := by
  simp [archSize, Fin.sum_univ_two, Matrix.one_apply]; norm_num

example : (projTuple 2).theta 1 = 18 := by
  have h : (projTuple 2).del = 1 := projSys.del_eq_one ℚ 2
  rw [Tuple.theta, h]; norm_num

end GlobalTheory.Adelic
