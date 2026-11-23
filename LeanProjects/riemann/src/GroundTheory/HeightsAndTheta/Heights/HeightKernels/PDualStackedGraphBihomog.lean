import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLead
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial NumberField

noncomputable section

namespace StackedGraphBihomogeneous

section Parts

variable {T : Type} [Fintype T]

def bideg (m : (Σ κ, stackedBlocks T κ) →₀ ℕ) : ℕ × ℕ :=
  (∑ t : T, m ⟨Sum.inl (), t⟩, ∑ t : T, m ⟨Sum.inr (), t⟩)

def bipart (f : MRing (stackedBlocks T)) (p : ℕ × ℕ) : MRing (stackedBlocks T) :=
  ∑ m ∈ f.support.filter (fun m => bideg m = p), monomial m (coeff m f)

theorem sum_bipart (f : MRing (stackedBlocks T)) : f = ∑ p ∈ f.support.image bideg, bipart f p := by
  classical
  unfold bipart
  rw [Finset.sum_fiberwise_of_maps_to (fun m hm => Finset.mem_image_of_mem _ hm)]
  exact (support_sum_monomial_coeff f).symm

theorem isMultiHomog_bipart (f : MRing (stackedBlocks T)) (p : ℕ × ℕ) :
    IsMultiHomog (bipart f p) (bidegree p.1 p.2) := by
  classical
  intro m hm κ
  obtain ⟨m', hm', hmm'⟩ := Finset.mem_biUnion.mp (support_sum hm)
  obtain rfl : m = m' := Finset.mem_singleton.mp (support_monomial_subset hmm')
  have hp : bideg m = p := (Finset.mem_filter.mp hm').2
  rcases κ with ⟨⟨⟩⟩ | ⟨⟨⟩⟩
  · exact congrArg Prod.fst hp
  · exact congrArg Prod.snd hp

def secW (s : Σ κ, stackedBlocks T κ) : ℕ := Sum.elim (fun _ => 0) (fun _ => 1) s.1

theorem sum_eq_bideg (m : (Σ κ, stackedBlocks T κ) →₀ ℕ) :
    ∑ s, m s = (bideg m).1 + (bideg m).2 := by
  rw [Fintype.sum_sigma, Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, bideg]
  rfl

theorem sum_secW_eq_bideg (m : (Σ κ, stackedBlocks T κ) →₀ ℕ) :
    ∑ s, secW s * m s = (bideg m).2 := by
  rw [Fintype.sum_sigma, Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, bideg, secW, Sum.elim_inl, Sum.elim_inr, zero_mul, one_mul,
    Finset.sum_const_zero, zero_add]
  rfl

end Parts

section Eval

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}

def formEvalFrac (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) :
    MRing (stackedBlocks T) →+* ProjField K i :=
  (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)).comp (stackedFormEval b b')

def biEval (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) :
    MRing (stackedBlocks T) →+* MvPolynomial Unit (MvPolynomial Unit (ProjField K i)) :=
  eval₂Hom (Int.castRingHom (MvPolynomial Unit (MvPolynomial Unit (ProjField K i))))
    fun s => C (C (formEvalFrac b b' (X s)) * X ()) * X () ^ secW s

theorem biEval_monomial [Fintype T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (m : (Σ κ, stackedBlocks T κ) →₀ ℕ) (c : ℤ) :
    biEval b b' (monomial m c) =
      C (C (formEvalFrac b b' (monomial m c)) * X () ^ (∑ s, m s)) * X () ^ (∑ s, secW s * m s) := by
  have hE : formEvalFrac b b' (monomial m c) = (c : ProjField K i) * ∏ s, formEvalFrac b b' (X s) ^ m s := by
    rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
    simp [map_pow]
  rw [hE, monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
  simp only [biEval, coe_eval₂Hom, eval₂_X, map_pow, mul_pow, Finset.prod_mul_distrib, ← pow_mul,
    Finset.prod_pow_eq_pow_sum, map_mul, map_prod, eq_intCast, map_intCast]
  ring

theorem formEvalFrac_first (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (t : T) : formEvalFrac b b' (X ⟨Sum.inl (), t⟩) = dualLatticeCoord b' ⟨(), t⟩ := by
  have h : (X ⟨Sum.inl (), t⟩ : MRing (stackedBlocks T)) = graphFirst t := rfl
  rw [formEvalFrac, RingHom.comp_apply, h, DualStackedExcLeadExample.stackedFormEval_first, dualLatticeCoord]

theorem formEvalFrac_second (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    {a : T → ℤ} (hb : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) (t : T) :
    formEvalFrac b b' (X ⟨Sum.inr (), t⟩) = (a t : ProjField K i) * dualLatticeCoord b' ⟨(), t⟩ := by
  have h : (X ⟨Sum.inr (), t⟩ : MRing (stackedBlocks T)) = graphSecond t := rfl
  rw [formEvalFrac, RingHom.comp_apply, h, DualStackedExcLeadExample.stackedFormEval_second, hb t,
    dualLatticeCoord, ← map_intCast (algebraMap (MvPolynomial (Fin i) K) (ProjField K i)), ← map_mul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, zsmul_eq_mul, map_mul, ← mul_assoc, map_intCast]

theorem biEval_eq_zero [Fintype T] [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T ℤ (dualLattice F')) {a : T → ℤ}
    (hb : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {f : MRing (stackedBlocks T)}
    (hf : f ∈ stackedGraph b' a) : biEval b b' f = 0 := by
  let Q : MRing (dualBlocks T) ⧸ dualIdeal b' →+* MvPolynomial Unit (ProjField K i) :=
    Ideal.Quotient.lift (dualIdeal b')
      (mConeMap (dualLatticeCoord b') : MRing (dualBlocks T) →+* MvPolynomial Unit (ProjField K i))
      (fun g hg => RingHom.mem_ker.mp hg)
  have hg : ∀ t : T, linForm (ι := dualBlocks T) (ι₂ := dualBlocks T) (stackedDiag a) ⟨(), t⟩ =
      C (a t) * X ⟨(), t⟩ := fun t => by
    simp [linForm, stackedDiag, apply_ite C, ite_mul, Finset.sum_ite_eq]
  have hcomp : (map Q).comp (graphMap (dualIdeal b') (linForm (stackedDiag a))) = biEval b b' := by
    apply MvPolynomial.ringHom_ext
    · intro n
      simp [biEval]
    · rintro ⟨(u | u), t⟩ <;> obtain ⟨⟩ := u
      · have h1 := formEvalFrac_first b b' t
        simp only [RingHom.comp_apply, graphMap, coe_eval₂Hom, eval₂_X, map_C, Q,
          Ideal.Quotient.lift_mk, biEval, secW, h1] at *
        simp [mConeMap]
      · have h2 := formEvalFrac_second b b' hb t
        simp only [RingHom.comp_apply, graphMap, coe_eval₂Hom, eval₂_X, map_mul, map_C, Q, hg t,
          Ideal.Quotient.lift_mk, biEval, secW, h2] at *
        simp [mConeMap, map_mul]
        ring
  have hf0 : graphMap (dualIdeal b') (linForm (stackedDiag a)) f = 0 := RingHom.mem_ker.mp hf
  rw [← hcomp, RingHom.comp_apply, hf0, map_zero]

end Eval

section Final

variable {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type} [Fintype T]
  [DecidableEq T]

theorem coeff_C_mul_X_pow_unit {R : Type*} [CommSemiring R] (r : R) (n e : ℕ) :
    coeff (Finsupp.single () e) (C r * X () ^ n : MvPolynomial Unit R) = if n = e then r else 0 := by
  rw [C_mul_X_pow_eq_monomial, coeff_monomial]
  by_cases h : n = e
  · simp [h]
  · rw [if_neg h, if_neg]
    intro h'
    exact h (by simpa using congrArg (fun g : Unit →₀ ℕ => g ()) h')

theorem stackedFormEval_bipart (b : Module.Basis T ℤ (dualLattice F))
    (b' : Module.Basis T ℤ (dualLattice F')) {a : T → ℤ}
    (hb : ∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) {f : MRing (stackedBlocks T)}
    (hf : f ∈ stackedGraph b' a) (p : ℕ × ℕ) : stackedFormEval b b' (bipart f p) = 0 := by
  apply IsFractionRing.injective (MvPolynomial (Fin i) K) (ProjField K i)
  rw [map_zero]
  change formEvalFrac b b' (bipart f p) = 0
  have h0 := biEval_eq_zero b b' hb hf
  rw [← support_sum_monomial_coeff f, map_sum] at h0
  simp_rw [biEval_monomial] at h0
  have h1 := congrArg (fun q => coeff (Finsupp.single () (p.1 + p.2)) (coeff (Finsupp.single () p.2) q)) h0
  simp only [coeff_sum, coeff_C_mul_X_pow_unit, apply_ite (coeff (Finsupp.single () (p.1 + p.2))),
    coeff_zero] at h1
  rw [← h1, bipart, map_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [sum_eq_bideg, sum_secW_eq_bideg]
  obtain ⟨d, e⟩ := p
  obtain ⟨d', e'⟩ := bideg m
  by_cases he : e' = e
  · subst he
    simp
  · simp [he]

end Final

end StackedGraphBihomogeneous

open StackedGraphBihomogeneous in

theorem DualStackedGraphBihomog.proof : DualStackedGraphBihomog.Statement := by
  intro K _ _ i F F' T _ _ b b' a hb f hf
  exact ⟨f.support.image bideg, bipart f, sum_bipart f,
    fun p _ => ⟨isMultiHomog_bipart f p, stackedFormEval_bipart b b' hb hf p⟩⟩

end

end GroundTheory.Heights₂.Heights
