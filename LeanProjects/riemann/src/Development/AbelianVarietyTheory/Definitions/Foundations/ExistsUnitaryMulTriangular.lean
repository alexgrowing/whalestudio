import Mathlib
import Formalism.SatakeDualWeyl.DualWeylRepApply
import Formalism.HarderNarasimhan.StatementPl
import Formalism.LocalRingCardinality.DataArith
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeHasBasisAtEveryFinitePlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActPMemLocPNabStdOfIsBasisAt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv

open MvPolynomial NumberField IsDedekindDomain MeasureTheory
open Formalism.GradedWeylDivisibility (dualWeyl rowAct initMinor lpMinor hw shapeDeg colW initW nuNext ssIdx)
open scoped Matrix ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.DualWeyl

variable {N : ℕ}

abbrev Pol (N : ℕ) (R : Type) [CommRing R] : Type := MvPolynomial (Fin N × Fin N) R

abbrev nabla (la : Fin N → ℕ) (R : Type) [CommRing R] : Submodule R (Pol N R) := dualWeyl R N N la

def size (la : Fin N → ℕ) : ℕ := ∑ i, la i

section Ring

variable {R S : Type} [CommRing R] [CommRing S]

def evalAt (y : Matrix (Fin N) (Fin N) R) : Pol N R →ₐ[R] R := aeval fun v => y v.1 v.2

def colAct (b : Matrix (Fin N) (Fin N) R) : Pol N R →ₐ[R] Pol N R :=
  aeval fun v => ∑ t : Fin N, X (v.1, t) * C (b t v.2)

def diagChar (la : Fin N → ℕ) (b : Matrix (Fin N) (Fin N) R) : R := ∏ i, b i i ^ la i

@[simp] theorem evalAt_X (y : Matrix (Fin N) (Fin N) R) (v : Fin N × Fin N) : evalAt y (X v) = y v.1 v.2 := by
  simp [evalAt]

theorem evalAt_rowAct (y g : Matrix (Fin N) (Fin N) R) (f : Pol N R) :
    evalAt y (rowAct R g f) = evalAt (g * y) f := by
  have : (evalAt y).comp (rowAct R g) = evalAt (g * y) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [rowAct, evalAt, Matrix.mul_apply]
  exact DFunLike.congr_fun this f

theorem evalAt_colAct (y b : Matrix (Fin N) (Fin N) R) (f : Pol N R) :
    evalAt y (colAct b f) = evalAt (y * b) f := by
  have : (evalAt y).comp (colAct b) = evalAt (y * b) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [colAct, evalAt, Matrix.mul_apply]
  exact DFunLike.congr_fun this f

theorem evalAt_map (φ : R →+* S) (y : Matrix (Fin N) (Fin N) R) (f : Pol N R) :
    evalAt (y.map φ) (map φ f) = φ (evalAt y f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evalAt]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, map_X, evalAt_X, Matrix.map_apply]

theorem map_colAct (φ : R →+* S) (b : Matrix (Fin N) (Fin N) R) (f : Pol N R) :
    map φ (colAct b f) = colAct (b.map φ) (map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [colAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp]
    simp [colAct]

theorem colAct_initMinor {s : ℕ} (I : Fin s → Fin N) (hs : s ≤ N) (b : Matrix (Fin N) (Fin N) R)
    (hb : b.BlockTriangular id) :
    colAct b (initMinor R I hs) = diagChar (initW N s) b • initMinor R I hs := by
  have hsum : ∀ (F : Fin N → Pol N R), (∀ t : Fin N, s ≤ t.val → F t = 0) →
      ∑ t, F t = ∑ q : Fin s, F (Fin.castLE hs q) := by
    intro F hF
    symm
    refine Finset.sum_of_injOn (Fin.castLE hs) (fun _ _ _ _ h => Fin.castLE_injective hs h)
      (fun _ _ => Finset.mem_univ _) ?_ (fun _ _ => rfl)
    intro t _ ht
    refine hF t ?_
    by_contra h
    exact ht ⟨⟨t.val, by omega⟩, by simp, by ext; simp⟩
  have hb' : (Matrix.of fun p q : Fin s => (C (b (Fin.castLE hs p) (Fin.castLE hs q)) : Pol N R)).BlockTriangular id := by
    intro p q hpq
    simp only [Matrix.of_apply]
    rw [hb (show id (Fin.castLE hs q) < id (Fin.castLE hs p) from hpq), map_zero]
  unfold initMinor
  rw [Formalism.GradedWeylDivisibility.algHom_det_of]
  have h1 : (Matrix.of fun p q : Fin s => colAct b (X (I p, Fin.castLE hs q))) =
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : Pol N R)) *
        (Matrix.of fun p q : Fin s => (C (b (Fin.castLE hs p) (Fin.castLE hs q)) : Pol N R)) := by
    ext1 p q
    simp only [Matrix.of_apply, Matrix.mul_apply, colAct, aeval_X]
    refine hsum _ fun t ht => ?_
    rw [hb (show id (Fin.castLE hs q) < id t from ?_), map_zero, mul_zero]
    have := q.2
    simp only [id, Fin.lt_def, Fin.val_castLE]
    omega
  rw [h1, Matrix.det_mul, Matrix.det_of_isUpperTriangular hb', smul_eq_C_mul, mul_comm]
  congr 1
  simp only [Matrix.of_apply, diagChar, map_prod, map_pow]
  symm
  refine (Finset.prod_of_injOn (Fin.castLE hs) (fun _ _ _ _ h => Fin.castLE_injective hs h)
      (fun _ _ => Finset.mem_univ _) ?_ (fun q _ => ?_)).symm
  · intro t _ ht
    have : ¬ t.val < s := fun h => ht ⟨⟨t.val, h⟩, by simp, by ext; simp⟩
    simp [initW, this]
  · simp [initW]

theorem colAct_of_mem [IsDomain R] {la : Fin N → ℕ} {f : Pol N R} (hf : f ∈ nabla la R)
    (b : Matrix (Fin N) (Fin N) R) (hb : b.BlockTriangular id) : colAct b f = diagChar la b • f := by
  unfold nabla at hf
  rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R N N la] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨K, sz, hsz, I, rfl, rfl⟩ := hx
    unfold Formalism.GradedWeylDivisibility.bideterminant
    rw [map_prod, ← Formalism.GradedWeylDivisibility.sum_initW_eq_shapeDeg]
    simp only [colAct_initMinor _ _ b hb]
    rw [Finset.prod_smul]
    congr 1
    simp only [diagChar, Finset.sum_apply]
    rw [Finset.prod_comm]
    simp only [Finset.prod_pow_eq_pow_sum]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul c x _ hx => rw [map_smul, hx, smul_comm]

theorem colAct_map_of_mem [IsDomain S] (φ : R →+* S) {la : Fin N → ℕ} {f : Pol N R} (hf : f ∈ nabla la R)
    (b : Matrix (Fin N) (Fin N) S) (hb : b.BlockTriangular id) :
    colAct b (map φ f) = diagChar la b • map φ f :=
  colAct_of_mem (Formalism.GradedWeylDivisibility.dualWeylMap R S φ N N la f hf) b hb

theorem coeff_colAct_diagonal (t : Fin N → R) (f : Pol N R) (m : Fin N × Fin N →₀ ℕ) :
    coeff m (colAct (Matrix.diagonal t) f) = (∏ s, t s ^ (Finsupp.weight (colW N N) m s)) * coeff m f := by
  classical
  have h1 : ∀ v : Fin N × Fin N,
      (∑ s : Fin N, X (v.1, s) * C (Matrix.diagonal t s v.2) : Pol N R) = C (t v.2) * X v := by
    intro v
    rw [Finset.sum_eq_single v.2]
    · simp [mul_comm]
    · intro s _ hs
      simp [Matrix.diagonal_apply_ne _ hs]
    · simp
  have h2 : ∀ (m : Fin N × Fin N →₀ ℕ) (a : R), colAct (Matrix.diagonal t) (monomial m a) =
      (∏ s, t s ^ (Finsupp.weight (colW N N) m s)) • monomial m a := by
    intro m a
    have h3 : (∏ s, t s ^ (Finsupp.weight (colW N N) m s)) = ∏ v ∈ m.support, t v.2 ^ m v := by
      simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, ← Finset.prod_pow_eq_pow_sum]
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [Finset.prod_eq_single v.2]
      · simp [colW]
      · intro s _ hs
        simp [colW, hs]
      · simp
    rw [h3, colAct, aeval_monomial, monomial_eq]
    simp only [h1, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, smul_eq_C_mul, map_prod, map_pow, algebraMap_eq]
    ring
  induction f using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [h2, coeff_smul, coeff_monomial]
    split_ifs with h
    · subst h; simp
    · simp
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, coeff_add, mul_add]

theorem mem_nabla_iff [IsDomain R] [Infinite R] {la : Fin N → ℕ} {f : Pol N R} :
    f ∈ nabla la R ↔ ∀ b : Matrix (Fin N) (Fin N) R, b.BlockTriangular id → (∀ i, b i i ≠ 0) →
      colAct b f = diagChar la b • f := by
  classical
  refine ⟨fun hf b hb _ => colAct_of_mem hf b hb, fun h => ?_⟩
  rw [Formalism.GradedWeylDivisibility.dualWeylPoint R N N la f]
  constructor
  · intro m hm
    have h1 : ∀ t : Fin N → R, ∏ s, t s ^ (Finsupp.weight (colW N N) m s + 1) = ∏ s, t s ^ (la s + 1) := by
      intro t
      by_cases ht : ∀ s, t s ≠ 0
      · have h2 := congrArg (coeff m) (h (Matrix.diagonal t) (Matrix.blockTriangular_diagonal t) (by simpa using ht))
        rw [coeff_colAct_diagonal, coeff_smul, smul_eq_mul] at h2
        have h3 := mul_right_cancel₀ hm h2
        simp only [pow_succ, Finset.prod_mul_distrib, h3, diagChar, Matrix.diagonal_apply_eq]
      · push Not at ht
        obtain ⟨s, hs⟩ := ht
        rw [Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs]),
          Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])]
    have h4 : (monomial (Finsupp.equivFunOnFinite.symm fun s => Finsupp.weight (colW N N) m s + 1) (1 : R)) =
        monomial (Finsupp.equivFunOnFinite.symm fun s => la s + 1) (1 : R) := by
      refine MvPolynomial.funext fun t => ?_
      rw [eval_monomial, eval_monomial, Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
      simpa using h1 t
    have h5 := Finsupp.equivFunOnFinite.symm.injective (monomial_left_injective one_ne_zero h4)
    funext s
    simpa using congrFun h5 s
  · intro l j hlj c
    have hb : (1 + Matrix.single l j c : Matrix (Fin N) (Fin N) R).BlockTriangular id := by
      intro p q hpq
      have hpq' : q < p := hpq
      rw [Matrix.add_apply, Matrix.one_apply_ne hpq'.ne', zero_add, Matrix.single_apply_of_ne]
      rintro ⟨rfl, rfl⟩
      exact absurd hlj hpq'.not_gt
    have hd : ∀ i, (1 + Matrix.single l j c : Matrix (Fin N) (Fin N) R) i i = 1 := by
      intro i
      rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply_of_ne, add_zero]
      rintro ⟨rfl, rfl⟩
      exact absurd hlj (lt_irrefl _)
    have h1 := h _ hb (fun i => by rw [hd]; exact one_ne_zero)
    have h2 : Formalism.GradedWeylDivisibility.colAdd R l j c = colAct (1 + Matrix.single l j c) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [Formalism.GradedWeylDivisibility.colAdd, colAct, aeval_X, Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib,
        Matrix.one_apply, Matrix.single_apply]
      by_cases hv : v.2 = j
      · subst hv
        simp [apply_ite C, mul_comm]
      · simp [apply_ite C, hv, Ne.symm hv]
    rw [h2, h1]
    simp [diagChar, hd]

end Ring

def width (la : Fin N → ℕ) : ℕ := Finset.univ.sup la

def colLen (la : Fin N → ℕ) (c : ℕ) : ℕ := (Finset.univ.filter fun i => c < la i).card

theorem colLen_le (la : Fin N → ℕ) (c : ℕ) : colLen la c ≤ N :=
  (Finset.card_filter_le _ _).trans (by simp)

abbrev Tableau (la : Fin N → ℕ) : Type := (c : Fin (width la)) → Fin (colLen la c) → Fin N

def IsStandard {la : Fin N → ℕ} (T : Tableau la) : Prop :=
  (∀ c, StrictMono (T c)) ∧
    ∀ (c c' : Fin (width la)), c ≤ c' → ∀ (p : ℕ) (h : p < colLen la c) (h' : p < colLen la c'),
      T c ⟨p, h⟩ ≤ T c' ⟨p, h'⟩

def StdTableau (la : Fin N → ℕ) : Type := {T : Tableau la // IsStandard T}

instance (la : Fin N → ℕ) : Finite (StdTableau la) := by unfold StdTableau; infer_instance

instance (la : Fin N → ℕ) : Fintype (StdTableau la) := Fintype.ofFinite _

def canon (la : Fin N → ℕ) : Tableau la := fun c => Fin.castLE (colLen_le la c)

theorem isStandard_canon (la : Fin N → ℕ) : IsStandard (canon la) :=
  ⟨fun _ => Fin.strictMono_castLE _, fun _ _ _ _ _ _ => le_rfl⟩

instance (la : Fin N → ℕ) : Inhabited (StdTableau la) := ⟨⟨canon la, isStandard_canon la⟩⟩

def bideterminant (la : Fin N → ℕ) (R : Type) [CommRing R] (T : Tableau la) : Pol N R :=
  Formalism.GradedWeylDivisibility.bideterminant R (fun c : Fin (width la) => colLen la c) (fun c => colLen_le la c) T

def extremal (la : Fin N → ℕ) (R : Type) [CommRing R] : Pol N R := hw R le_rfl la

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {la : Fin N → ℕ}

theorem extremal_mem (hla : Antitone la) : extremal la R ∈ nabla la R := Formalism.GradedWeylDivisibility.hwMem R N N le_rfl la hla

theorem evalAt_one_extremal : evalAt 1 (extremal la R) = 1 := by
  unfold extremal hw
  rw [map_prod]
  refine Finset.prod_eq_one fun s _ => ?_
  rw [map_pow, lpMinor, Formalism.GradedWeylDivisibility.algHom_det_of]
  have h : (Matrix.of fun p q : Fin (s.val + 1) => evalAt (1 : Matrix (Fin N) (Fin N) R)
      (X (Fin.castLE (by omega) p, Fin.castLE (by omega) q))) = 1 := by
    ext p q
    simp [Matrix.one_apply]
  rw [h, Matrix.det_one, one_pow]

theorem extremal_ne_zero [Nontrivial R] : extremal la R ≠ 0 := fun h => by
  have h1 := evalAt_one_extremal (R := R) (la := la)
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem nabla_ne_bot [Nontrivial R] (hla : Antitone la) : nabla la R ≠ ⊥ := fun h =>
  extremal_ne_zero (R := R) (la := la) (by simpa [h] using extremal_mem (R := R) hla)

end Ring

def rho (la : Fin N → ℕ) (R : Type) [CommRing R] : Representation R (Matrix (Fin N) (Fin N) R) (nabla la R) where
  toFun g := (rowAct R gᵀ).toLinearMap.restrict fun f hf => Formalism.GradedWeylDivisibility.dualWeylRowStable R N N la _ f hf
  map_one' := by
    refine LinearMap.ext fun f => Subtype.ext ?_
    change rowAct R (1 : Matrix (Fin N) (Fin N) R)ᵀ f.1 = f.1
    rw [Matrix.transpose_one, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
    rfl
  map_mul' g h := by
    refine LinearMap.ext fun f => Subtype.ext ?_
    change rowAct R (g * h)ᵀ f.1 = rowAct R gᵀ (rowAct R hᵀ f.1)
    rw [Matrix.transpose_mul, ← Formalism.GradedWeylDivisibility.rowActMul R N N]
    rfl

def rhoGL (la : Fin N → ℕ) (R : Type) [CommRing R] : Representation R (GL (Fin N) R) (nabla la R) :=
  (rho la R).comp (Units.coeHom _)

def baseChange (la : Fin N → ℕ) {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) :
    nabla la R →ₛₗ[φ] nabla la S where
  toFun f := ⟨map φ f.1, Formalism.GradedWeylDivisibility.dualWeylMap R S φ N N la f.1 f.2⟩
  map_add' f g := Subtype.ext (map_add _ _ _)
  map_smul' c f := Subtype.ext (by simp [smul_eq_C_mul])

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {la : Fin N → ℕ}

theorem coe_rho (g : Matrix (Fin N) (Fin N) R) (f : nabla la R) : (rho la R g f : Pol N R) = rowAct R gᵀ f := rfl

theorem coe_baseChange (φ : R →+* S) (f : nabla la R) : (baseChange la φ f : Pol N S) = map φ f.1 := rfl

theorem evalAt_rho (y g : Matrix (Fin N) (Fin N) R) (f : nabla la R) :
    evalAt y (rho la R g f : Pol N R) = evalAt (gᵀ * y) f := evalAt_rowAct _ _ _

theorem rho_one (f : nabla la R) : rho la R 1 f = f := by
  rw [map_one]; rfl

theorem rho_smul (t : R) (g : Matrix (Fin N) (Fin N) R) (f : nabla la R) :
    rho la R (t • g) f = t ^ size la • rho la R g f := by
  refine Subtype.ext ?_
  rw [coe_rho, Matrix.transpose_smul, GlobalTheory.NabStab.rowAct_smul t _ _ f.2.1]
  rfl

theorem rho_scalar (t : R) (f : nabla la R) : rho la R (t • 1) f = t ^ size la • f := by
  rw [rho_smul, rho_one]

theorem baseChange_rho (φ : R →+* S) (g : Matrix (Fin N) (Fin N) R) (f : nabla la R) :
    baseChange la φ (rho la R g f) = rho la S (g.map φ) (baseChange la φ f) := by
  refine Subtype.ext ?_
  rw [coe_baseChange, coe_rho, GlobalTheory.NabStab.map_rowAct, coe_rho, Matrix.transpose_map]
  rfl

end Ring

abbrev Idx (la : Fin N → ℕ) : Type := ssIdx N N la

instance (la : Fin N → ℕ) : Finite (Idx la) := (Formalism.GradedWeylDivisibility.sSIdxFinite N N la).to_subtype

instance (la : Fin N → ℕ) : Fintype (Idx la) := Fintype.ofFinite _

def intVec (la : Fin N → ℕ) : Idx la → Pol N ℤ := (Formalism.GradedWeylDivisibility.sSBasis ℤ N N la).choose

theorem intVec_spec (la : Fin N → ℕ) (K : Type) [Field K] [CharZero K] :
    LinearIndependent K (fun i => map (Int.castRingHom K) (intVec la i)) ∧
      Submodule.span K (Set.range fun i => map (Int.castRingHom K) (intVec la i)) = nabla la K := by
  have h := Formalism.GradedWeylDivisibility.nablaLKBasis ℤ K (algebraMap ℤ K).injective_int N N la (intVec la) _
    (Formalism.GradedWeylDivisibility.sSBasis ℤ N N la).choose_spec.1 1 (by simp)
  simpa [Formalism.GradedWeylDivisibility.ldlat_rowAct_one] using h

def basis (la : Fin N → ℕ) (K : Type) [Field K] [CharZero K] : Module.Basis (Idx la) K (nabla la K) :=
  (Module.Basis.span (intVec_spec la K).1).map (LinearEquiv.ofEq _ _ (intVec_spec la K).2)

theorem coe_basis (la : Fin N → ℕ) (K : Type) [Field K] [CharZero K] (i : Idx la) :
    (basis la K i : Pol N K) = map (Int.castRingHom K) (intVec la i) := by
  simp [basis, Module.Basis.span_apply]

instance (la : Fin N → ℕ) (K : Type) [Field K] [CharZero K] : FiniteDimensional K (nabla la K) :=
  Module.Finite.of_basis (basis la K)

def dim (la : Fin N → ℕ) : ℕ := Module.finrank ℂ (nabla la ℂ)

theorem dim_eq_card (la : Fin N → ℕ) : dim la = Fintype.card (Idx la) :=
  Module.finrank_eq_card_basis (basis la ℂ)

theorem dim_pos {la : Fin N → ℕ} (hla : Antitone la) : 0 < dim la := by
  have : Nontrivial (nabla la ℂ) := Submodule.nontrivial_iff_ne_bot.mpr (nabla_ne_bot hla)
  exact Module.finrank_pos

section Fields

variable {K L : Type} [Field K] [CharZero K] [Field L] [CharZero L] {la : Fin N → ℕ}

end Fields

abbrev UN (N : ℕ) : Type := Matrix.unitaryGroup (Fin N) ℂ

scoped instance measurableSpaceUN : MeasurableSpace (UN N) := borel _

scoped instance borelSpaceUN : BorelSpace (UN N) := ⟨rfl⟩

def haarU (N : ℕ) : Measure (UN N) := haarProb (UN N)

instance : (haarU N).IsHaarMeasure := haarProb_isHaarMeasure _

instance : IsProbabilityMeasure (haarU N) := haarProb_isProbabilityMeasure _

instance : (haarU N).IsMulRightInvariant := haarProb_isMulRightInvariant

def form (la : Fin N → ℕ) (f f' : Pol N ℂ) : ℂ :=
  (dim la : ℂ) * ∫ g : UN N, evalAt g.1 f * conj (evalAt g.1 f') ∂haarU N

def normSq (la : Fin N → ℕ) (f : Pol N ℂ) : ℝ :=
  (dim la : ℝ) * ∫ g : UN N, ‖evalAt g.1 f‖ ^ 2 ∂haarU N

def rhoU (la : Fin N → ℕ) : Representation ℂ (UN N) (nabla la ℂ) :=
  (rho la ℂ).comp (Matrix.unitaryGroup (Fin N) ℂ).subtype

section Metric

variable {la : Fin N → ℕ}

theorem rhoU_apply (u : UN N) : rhoU la u = rho la ℂ u.1 := rfl

theorem continuous_evalAt (f : Pol N ℂ) : Continuous fun y : Matrix (Fin N) (Fin N) ℂ => evalAt y f := by
  induction f using MvPolynomial.induction_on with
  | C a => simpa [evalAt] using continuous_const
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul, evalAt_X]
    exact hp.mul (continuous_apply_apply _ _)

theorem continuous_evalAt_coe (f : Pol N ℂ) : Continuous fun g : UN N => evalAt g.1 f :=
  (continuous_evalAt f).comp continuous_subtype_val

theorem integrable_mul_conj (f f' : Pol N ℂ) :
    Integrable (fun g : UN N => evalAt g.1 f * conj (evalAt g.1 f')) (haarU N) :=
  integrable_of_continuous_of_compactSpace _
    ((continuous_evalAt_coe f).mul (Complex.continuous_conj.comp (continuous_evalAt_coe f')))

theorem integrable_norm_sq (f : Pol N ℂ) : Integrable (fun g : UN N => ‖evalAt g.1 f‖ ^ 2) (haarU N) :=
  integrable_of_continuous_of_compactSpace _ ((continuous_evalAt_coe f).norm.pow 2)

theorem form_self (f : Pol N ℂ) : form la f f = normSq la f := by
  simp only [form, normSq, Complex.mul_conj', ← Complex.ofReal_pow, integral_complex_ofReal]
  push_cast
  rfl

theorem normSq_nonneg (f : Pol N ℂ) : 0 ≤ normSq la f :=
  mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun _ => by positivity)

theorem conj_form (f f' : Pol N ℂ) : conj (form la f f') = form la f' f := by
  simp only [form, map_mul, ← integral_conj, map_natCast, Complex.conj_conj, mul_comm]

theorem form_add_left (f₁ f₂ f' : Pol N ℂ) : form la (f₁ + f₂) f' = form la f₁ f' + form la f₂ f' := by
  simp only [form, map_add, add_mul]
  rw [integral_add (integrable_mul_conj _ _) (integrable_mul_conj _ _), mul_add]

theorem form_smul_left (c : ℂ) (f f' : Pol N ℂ) : form la (c • f) f' = c * form la f f' := by
  simp only [form, map_smul, smul_eq_mul, mul_assoc, integral_const_mul]
  ring

theorem form_add_right (f f₁ f₂ : Pol N ℂ) : form la f (f₁ + f₂) = form la f f₁ + form la f f₂ := by
  rw [← conj_form, form_add_left, map_add, conj_form, conj_form]

theorem form_smul_right (c : ℂ) (f f' : Pol N ℂ) : form la f (c • f') = conj c * form la f f' := by
  rw [← conj_form, form_smul_left, map_mul, conj_form]

theorem form_rowAct (u : UN N) (f f' : Pol N ℂ) : form la (rowAct ℂ u.1 f) (rowAct ℂ u.1 f') = form la f f' := by
  simp only [form, evalAt_rowAct]
  congr 1
  exact integral_mul_left_eq_self (μ := haarU N) (fun g : UN N => evalAt g.1 f * conj (evalAt g.1 f')) u

theorem transpose_mem_unitaryGroup {u : Matrix (Fin N) (Fin N) ℂ} (hu : u ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    uᵀ ∈ Matrix.unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff] at hu
  rw [Matrix.mem_unitaryGroup_iff']
  have h := congrArg Matrix.transpose hu
  rw [Matrix.transpose_mul, Matrix.transpose_one] at h
  exact h

theorem form_rhoU (u : UN N) (f f' : nabla la ℂ) :
    form la (rhoU la u f : Pol N ℂ) (rhoU la u f' : Pol N ℂ) = form la f f' :=
  form_rowAct ⟨u.1ᵀ, transpose_mem_unitaryGroup u.2⟩ _ _

theorem normSq_rhoU (u : UN N) (f : nabla la ℂ) : normSq la (rhoU la u f : Pol N ℂ) = normSq la f := by
  apply Complex.ofReal_injective
  rw [← form_self, ← form_self, form_rhoU]

theorem exists_unitary_mul_triangular (y : Matrix (Fin N) (Fin N) ℂ) :
    ∃ (u : UN N) (b : Matrix (Fin N) (Fin N) ℂ), b.BlockTriangular id ∧ y = u.1 * b := by
  let e := EuclideanSpace.basisFun (Fin N) ℂ
  let v : Fin N → EuclideanSpace ℂ (Fin N) := fun s => WithLp.toLp 2 fun a => y a s
  have h : Module.finrank ℂ (EuclideanSpace ℂ (Fin N)) = Fintype.card (Fin N) := by simp
  let o := InnerProductSpace.gramSchmidtOrthonormalBasis h v
  refine ⟨⟨e.toBasis.toMatrix o, e.toMatrix_orthonormalBasis_mem_unitary o⟩, o.toBasis.toMatrix v,
    InnerProductSpace.gramSchmidtOrthonormalBasis_inv_isUpperTriangular h v, ?_⟩
  change y = e.toBasis.toMatrix o.toBasis * o.toBasis.toMatrix v
  rw [Module.Basis.toMatrix_mul_toMatrix]
  ext a s
  simp [Module.Basis.toMatrix_apply, e, v]

theorem eq_zero_of_evalAt_unitary {f : Pol N ℂ} (hf : f ∈ nabla la ℂ) (h : ∀ g : UN N, evalAt g.1 f = 0) :
    f = 0 := by
  refine MvPolynomial.funext fun x => ?_
  obtain ⟨u, b, hb, hy⟩ := exists_unitary_mul_triangular (Matrix.of fun a s => x (a, s))
  have h1 : eval x f = evalAt (Matrix.of fun a s => x (a, s)) f := by
    simp [evalAt, aeval_eq_eval]
  rw [h1, hy, ← evalAt_colAct, colAct_of_mem hf b hb, map_smul, h u]
  simp

theorem normSq_pos {f : Pol N ℂ} (hf : f ∈ nabla la ℂ) (h0 : f ≠ 0) : 0 < normSq la f := by
  have : Nontrivial (nabla la ℂ) := ⟨⟨⟨f, hf⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩⟩
  have hd : 0 < dim la := Module.finrank_pos
  refine mul_pos (by exact_mod_cast hd) ?_
  obtain ⟨g, hg⟩ : ∃ g : UN N, evalAt g.1 f ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (eq_zero_of_evalAt_unitary hf h)
  exact Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := g)
    ((continuous_evalAt_coe f).norm.pow 2) (HasCompactSupport.of_compactSpace _) (fun k => by positivity)
    (by simpa using hg)

theorem normSq_le_dim {f : Pol N ℂ} (h : ∀ g : UN N, ‖evalAt g.1 f‖ ≤ 1) : normSq la f ≤ dim la := by
  have h1 : ∫ g : UN N, ‖evalAt g.1 f‖ ^ 2 ∂haarU N ≤ ∫ _ : UN N, (1 : ℝ) ∂haarU N :=
    integral_mono (integrable_norm_sq f) (integrable_const _) fun g => pow_le_one₀ (norm_nonneg _) (h g)
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h1
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) h1

end Metric

def Space (la : Fin N → ℕ) : Type := nabla la ℂ

instance (la : Fin N → ℕ) : AddCommGroup (Space la) := inferInstanceAs (AddCommGroup (nabla la ℂ))

instance (la : Fin N → ℕ) : Module ℂ (Space la) := inferInstanceAs (Module ℂ (nabla la ℂ))

instance (la : Fin N → ℕ) : FiniteDimensional ℂ (Space la) := inferInstanceAs (FiniteDimensional ℂ (nabla la ℂ))

def toSpace (la : Fin N → ℕ) : nabla la ℂ ≃ₗ[ℂ] Space la := LinearEquiv.refl ℂ _

@[reducible] def core (la : Fin N → ℕ) : InnerProductSpace.Core ℂ (Space la) where
  inner f f' := form la ((toSpace la).symm f').1 ((toSpace la).symm f).1
  conj_inner_symm f f' := conj_form _ _
  re_inner_nonneg f := by
    rw [form_self]
    exact normSq_nonneg _
  add_left f f' g := by
    simp only [map_add, Submodule.coe_add, form_add_right]
  smul_left f g c := by
    simp only [map_smul, Submodule.coe_smul, form_smul_right]
  definite f hf := by
    by_contra h
    have h1 : ((toSpace la).symm f).1 ≠ 0 := fun h2 => h (by
      rw [← (toSpace la).symm.map_eq_zero_iff]
      exact Subtype.ext h2)
    rw [form_self, Complex.ofReal_eq_zero] at hf
    exact (normSq_pos ((toSpace la).symm f).2 h1).ne' hf

instance (la : Fin N → ℕ) : NormedAddCommGroup (Space la) := (core la).toNormedAddCommGroup

instance (la : Fin N → ℕ) : InnerProductSpace ℂ (Space la) := InnerProductSpace.ofCore (core la).toCore

def rhoSpace (la : Fin N → ℕ) : Representation ℂ (UN N) (Space la) := rhoU la

section Space

variable {la : Fin N → ℕ}

theorem inner_toSpace (f f' : nabla la ℂ) : ⟪toSpace la f, toSpace la f'⟫_ℂ = form la f'.1 f.1 := rfl

theorem norm_toSpace_sq (f : nabla la ℂ) : ‖toSpace la f‖ ^ 2 = normSq la f.1 := by
  apply Complex.ofReal_injective
  rw [← form_self, ← inner_toSpace, inner_self_eq_norm_sq_to_K]
  simp

theorem finrank_space : Module.finrank ℂ (Space la) = dim la := rfl

theorem rhoSpace_toSpace (u : UN N) (f : nabla la ℂ) : rhoSpace la u (toSpace la f) = toSpace la (rhoU la u f) := rfl

theorem norm_rhoSpace (u : UN N) (v : Space la) : ‖rhoSpace la u v‖ = ‖v‖ := by
  obtain ⟨f, rfl⟩ := (toSpace la).surjective v
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), rhoSpace_toSpace, norm_toSpace_sq, norm_toSpace_sq, normSq_rhoU]

theorem continuous_of_span_dual {V T : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [TopologicalSpace T] (s : Set (Module.Dual ℂ V)) (hs : Submodule.span ℂ s = ⊤) (F : T → V)
    (h : ∀ l ∈ s, Continuous fun t => l (F t)) : Continuous F := by
  have hl : ∀ l : Module.Dual ℂ V, Continuous fun t => l (F t) := by
    intro l
    have hl : l ∈ Submodule.span ℂ s := hs ▸ Submodule.mem_top
    induction hl using Submodule.span_induction with
    | mem x hx => exact h x hx
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul c x _ hx => exact hx.const_smul c
  let b := Module.finBasis ℂ V
  have : F = fun t => ∑ i, b.coord i (F t) • b i := funext fun t => (b.sum_repr _).symm
  rw [this]
  exact continuous_finsetSum _ fun i _ => (hl _).smul continuous_const

def evSpace (la : Fin N → ℕ) (y : Matrix (Fin N) (Fin N) ℂ) : Module.Dual ℂ (Space la) :=
  (evalAt y).toLinearMap ∘ₗ (nabla la ℂ).subtype ∘ₗ (toSpace la).symm.toLinearMap

theorem evSpace_toSpace (y : Matrix (Fin N) (Fin N) ℂ) (f : nabla la ℂ) :
    evSpace la y (toSpace la f) = evalAt y f.1 := rfl

theorem span_evSpace : Submodule.span ℂ (Set.range fun g : UN N => evSpace la g.1) = ⊤ := by
  refine Submodule.span_eq_top_of_ne_zero fun z hz => ?_
  obtain ⟨f, rfl⟩ := (toSpace la).surjective z
  by_contra h
  push Not at h
  refine hz ?_
  rw [(toSpace la).map_eq_zero_iff]
  exact Subtype.ext (eq_zero_of_evalAt_unitary f.2 fun g => h _ ⟨g, rfl⟩)

theorem continuous_rhoSpace (v : Space la) : Continuous fun u : UN N => rhoSpace la u v := by
  obtain ⟨f, rfl⟩ := (toSpace la).surjective v
  refine continuous_of_span_dual _ span_evSpace _ ?_
  rintro _ ⟨y, rfl⟩
  simp only [rhoSpace_toSpace, evSpace_toSpace, rhoU_apply, evalAt_rho]
  have h : Continuous fun u : UN N => u.1ᵀ * y.1 :=
    (continuous_subtype_val (p := fun x => x ∈ Matrix.unitaryGroup (Fin N) ℂ)).matrix_transpose.matrix_mul
      continuous_const
  exact (continuous_evalAt f.1).comp h

end Space

def onBasis (la : Fin N → ℕ) : OrthonormalBasis (Idx la) ℂ (Space la) :=
  (stdOrthonormalBasis ℂ (Space la)).reindex (Fintype.equivFinOfCardEq (dim_eq_card la).symm).symm

def IsOrthoFrame (H X : Matrix (Fin N) (Fin N) ℂ) : Prop := Xᵀ * H * X.map conj = 1

def covFrame (la : Fin N → ℕ) (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Idx la) (Idx la) ℂ :=
  (basis la ℂ).toMatrix fun j => rho la ℂ X ((toSpace la).symm (onBasis la j))

def funFrame (la : Fin N → ℕ) (X : Matrix (Fin N) (Fin N) ℂ) : Matrix (Idx la) (Idx la) ℂ := covFrame la (X⁻¹)ᵀ

section Frames

variable {K : Type} [Field K] {la : Fin N → ℕ}

def covForm (la : Fin N → ℕ) (σ : K →+* ℂ) (X : Matrix (Fin N) (Fin N) ℂ) (f f' : nabla la K) : ℂ :=
  form la (rho la ℂ X⁻¹ (baseChange la σ f)).1 (rho la ℂ X⁻¹ (baseChange la σ f')).1

def covNormSq (la : Fin N → ℕ) (σ : K →+* ℂ) (X : Matrix (Fin N) (Fin N) ℂ) (f : nabla la K) : ℝ :=
  normSq la (rho la ℂ X⁻¹ (baseChange la σ f)).1

def funForm (la : Fin N → ℕ) (σ : K →+* ℂ) (X : Matrix (Fin N) (Fin N) ℂ) (f f' : nabla la K) : ℂ :=
  form la (rowAct ℂ X (map σ f.1)) (rowAct ℂ X (map σ f'.1))

def funNormSq (la : Fin N → ℕ) (σ : K →+* ℂ) (X : Matrix (Fin N) (Fin N) ℂ) (f : nabla la K) : ℝ :=
  normSq la (rowAct ℂ X (map σ f.1))

variable [NumberField K]

end Frames

section Lattices

open Formalism.L2.DIV (colLat IsBasisAt toK gLat)
open Formalism.HermitianLatticesTheory (localization₂)

def stdLat (la : Fin N → ℕ) (K : Type) [Field K] [NumberField K] : Submodule (𝓞 K) (nabla la K) :=
  ((nabla la (𝓞 K)).map (toK K _)).comap ((nabla la K).subtype.restrictScalars (𝓞 K))

variable {K : Type} [Field K] [NumberField K] {la : Fin N → ℕ}

def covLat (la : Fin N → ℕ) (L : Submodule (𝓞 K) (Fin N → K)) : Submodule (𝓞 K) (nabla la K) :=
  ⨅ (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin N) K) (_ : IsBasisAt w L B),
    (localization₂ w.asIdeal (stdLat la K)).comap ((rhoGL la K B⁻¹).restrictScalars (𝓞 K))

def funLat (la : Fin N → ℕ) (L : Submodule (𝓞 K) (Fin N → K)) : Submodule (𝓞 K) (nabla la K) :=
  ⨅ (w : HeightOneSpectrum (𝓞 K)) (B : GL (Fin N) K) (_ : IsBasisAt w L B),
    (localization₂ w.asIdeal (stdLat la K)).comap
      ((rho la K (B : Matrix (Fin N) (Fin N) K)ᵀ).restrictScalars (𝓞 K))

theorem baseChange_mem_stdLat (f : nabla la (𝓞 K)) : baseChange la (algebraMap (𝓞 K) K) f ∈ stdLat la K :=
  ⟨f.1, f.2, rfl⟩

theorem mem_stdLat {f : nabla la K} :
    f ∈ stdLat la K ↔ ∃ g : nabla la (𝓞 K), baseChange la (algebraMap (𝓞 K) K) g = f :=
  ⟨fun ⟨g, hg, h⟩ => ⟨⟨g, hg⟩, Subtype.ext h⟩, fun ⟨g, h⟩ => h ▸ baseChange_mem_stdLat g⟩

theorem mem_stdLat_iff_coeff {f : nabla la K} :
    f ∈ stdLat la K ↔ ∀ m, coeff m f.1 ∈ (algebraMap (𝓞 K) K).range := by
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [mem_stdLat]
  constructor
  · rintro ⟨g, rfl⟩ m
    exact ⟨coeff m g.1, by rw [coe_baseChange, coeff_map]⟩
  · intro h
    obtain ⟨g, hg⟩ : f.1 ∈ Set.range (map (algebraMap (𝓞 K) K)) := by
      rw [mem_range_map_iff_coeffs_subset]
      intro c hc
      obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp hc
      exact h m
    refine ⟨⟨g, mem_nabla_iff.mpr fun b hb _ => ?_⟩, Subtype.ext hg⟩
    apply map_injective _ hinj
    have h1 := colAct_of_mem f.2 (b.map (algebraMap (𝓞 K) K)) (hb.map _)
    rw [map_colAct, hg, h1, smul_eq_C_mul, smul_eq_C_mul, map_mul, hg, map_C]
    simp [diagChar]

theorem stdLat_eq_span : stdLat la K = Submodule.span (𝓞 K) (Set.range (basis la K)) := by
  apply le_antisymm
  · rintro f ⟨g, hg, hgf⟩
    have h : ∀ g ∈ nabla la (𝓞 K), ∀ f : nabla la K, toK K _ g = f.1 →
        f ∈ Submodule.span (𝓞 K) (Set.range (basis la K)) := by
      intro g hg
      unfold nabla at hg
      rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain] at hg
      have key : toK K _ g ∈ (Submodule.span (𝓞 K) (Set.range (basis la K))).map
          ((nabla la K).subtype.restrictScalars (𝓞 K)) := by
        induction hg using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨k, sz, hsz, I, hsh, rfl⟩ := hx
          have h1 : Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I ∈ Submodule.span ℤ (Set.range (intVec la)) := by
            rw [show Submodule.span ℤ (Set.range (intVec la)) = _ from
              (Formalism.GradedWeylDivisibility.sSBasis ℤ N N la).choose_spec.1.2.1, ← hsh]
            exact Formalism.GradedWeylDivisibility.bidetMem ℤ N N k sz hsz I
          rw [GlobalTheory.NabStab.toK_apply, Formalism.GradedWeylDivisibility.ldlat_map_bidet, ← Formalism.GradedWeylDivisibility.ldlat_map_bidet (Int.castRingHom K)]
          generalize Formalism.GradedWeylDivisibility.bideterminant ℤ sz hsz I = p at h1
          induction h1 using Submodule.span_induction with
          | mem x hx =>
            obtain ⟨i, rfl⟩ := hx
            exact ⟨basis la K i, Submodule.subset_span ⟨i, rfl⟩, coe_basis la K i⟩
          | zero => simp
          | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
          | smul c x _ hx => rw [map_zsmul]; exact zsmul_mem hx c
        | zero => simp
        | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
        | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
      rintro f hf
      obtain ⟨f', hf', h⟩ := key
      rwa [show f = f' from Subtype.ext (hf.symm.trans h.symm)]
    exact h g hg f hgf
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine mem_stdLat_iff_coeff.mpr fun m => ⟨(coeff m (intVec la i) : ℤ), ?_⟩
    rw [coe_basis, coeff_map]
    simp

theorem rho_mem_locP (w : HeightOneSpectrum (𝓞 K)) {g : Matrix (Fin N) (Fin N) K} {t : 𝓞 K}
    (ht : t ∈ w.asIdeal.primeCompl) {A : Matrix (Fin N) (Fin N) (𝓞 K)}
    (hA : A.map (algebraMap (𝓞 K) K) = algebraMap (𝓞 K) K t • g) {f : nabla la K}
    (hf : f ∈ localization₂ w.asIdeal (stdLat la K)) : rho la K g f ∈ localization₂ w.asIdeal (stdLat la K) := by
  obtain ⟨s, hs, hf⟩ := hf
  obtain ⟨p, hp⟩ := mem_stdLat.mp hf
  refine ⟨t ^ size la * s, Submonoid.mul_mem _ (Submonoid.pow_mem _ ht _) hs, mem_stdLat.mpr ⟨rho la _ A p, ?_⟩⟩
  rw [baseChange_rho, hA, hp, rho_smul, LinearMap.map_smul_of_tower, mul_smul, ← map_pow,
    IsScalarTower.algebraMap_smul]
  rfl

omit [NumberField K] in

theorem mem_colLat_iff (B : GL (Fin N) K) (x : Fin N → K) :
    x ∈ colLat B ↔ ∃ c : Fin N → 𝓞 K, (B : Matrix (Fin N) (Fin N) K) *ᵥ (fun j => (c j : K)) = x := by
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun c => Eq.congr_left ?_
  funext a
  simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]

theorem isLattice_colLat (B : GL (Fin N) K) : Submodule.IsLattice K (colLat B) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  unfold colLat
  rw [Submodule.span_span_of_tower]
  have h : LinearIndependent K (B : Matrix (Fin N) (Fin N) K).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr B.isUnit
  exact h.span_eq_top_of_card_eq_finrank' (by simp)

variable [StarRing K]

def baseHLat (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ) (L : Submodule (𝓞 K) (Fin N → K)) : Formalism.BasicNotions.HLat K where
  V := Fin N → K
  ι := Fin N
  b := Pi.basisFun K (Fin N)
  X := X
  L := L

def covHLat (la : Fin N → ℕ) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ) (L : Submodule (𝓞 K) (Fin N → K)) :
    Formalism.BasicNotions.HLat K where
  V := nabla la K
  ι := Idx la
  b := basis la K
  X := fun v => covFrame la (X v)
  L := covLat la L

def funHLat (la : Fin N → ℕ) (X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ) (L : Submodule (𝓞 K) (Fin N → K)) :
    Formalism.BasicNotions.HLat K where
  V := nabla la K
  ι := Idx la
  b := basis la K
  X := fun v => funFrame la (X v)
  L := funLat la L

variable {X : InfinitePlace K → Matrix (Fin N) (Fin N) ℂ} {L : Submodule (𝓞 K) (Fin N → K)}

end Lattices

example : width ![2, 1] = 2 ∧ colLen ![2, 1] 0 = 2 ∧ colLen ![2, 1] 1 = 1 ∧ size ![2, 1] = 3 := by decide

example (y : Matrix (Fin 2) (Fin 2) ℤ) : evalAt y (extremal ![1, 1] ℤ) = y 0 0 * y 1 1 - y 0 1 * y 1 0 := by
  simp [extremal, hw, nuNext, lpMinor, Fin.prod_univ_two, Matrix.det_fin_two]

example : extremal ![1, 0] ℤ = X (0, 0) := by
  simp [extremal, hw, nuNext, lpMinor, Fin.prod_univ_two]

example : (X (0, 1) : Pol 2 ℤ) ∉ nabla ![0, 1] ℤ := by
  intro h
  rw [nabla, Formalism.GradedWeylDivisibility.dualWeylNonDom ℤ 2 2 _ ⟨0, 1, by decide, by decide⟩] at h
  exact X_ne_zero _ ((Submodule.mem_bot ℤ).mp h)

example : (∃ T : Tableau ![1, 0], IsStandard T ∧ T ≠ canon _) ∧ ¬ IsStandard (la := ![1, 1]) fun _ _ => 0 := by
  refine ⟨⟨fun _ _ => 1, ⟨fun c p q hpq => ?_, fun _ _ _ _ _ _ => le_rfl⟩, fun h => ?_⟩, fun h => ?_⟩
  · exfalso
    revert c
    decide
  · revert h
    decide
  · have := h.1
    revert this
    decide

example : normSq ![1, 1] (extremal ![1, 1] ℂ) = dim ![1, 1] := by
  have h : ∀ g : UN 2, ‖evalAt g.1 (extremal ![1, 1] ℂ)‖ = 1 := fun g => by
    have h1 : evalAt g.1 (extremal ![1, 1] ℂ) = g.1.det := by
      simp [extremal, hw, nuNext, lpMinor, Fin.prod_univ_two, Matrix.det_fin_two]
    rw [h1]
    exact CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary g.2)
  simp [normSq, h]

end GlobalTheory.DualWeyl
