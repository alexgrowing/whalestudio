import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualWeylWeightProjector

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.HighWt

namespace GlobalTheory.HighWtEmb

variable (O : Type) [CommRing O] (N : ℕ)

def genHom : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) :=
  aeval (fun v : Fin N × Fin N => ∑ b : Fin N, X (v.1, b) * C (X (b, v.2)))

theorem genHom_X (v : Fin N × Fin N) : genHom O N (X v) = ∑ b : Fin N, X (v.1, b) * C (X (b, v.2)) := aeval_X _ _

theorem genHom_C (c : O) : genHom O N (C c) = C (C c) := by
  rw [MvPolynomial.algHom_C]; rfl

section Weights

variable {O N} {M : Type} [AddCommMonoid M] (wx u : Fin N × Fin N → M)

def CoefHom (G : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)) (e : M) : Prop :=
  ∀ m, IsWeightedHomogeneous wx (coeff m G) (Finsupp.weight u m + e)

theorem CoefHom.mul {G G' : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)} {e e' : M}
    (h : CoefHom wx u G e) (h' : CoefHom wx u G' e') : CoefHom wx u (G * G') (e + e') := by
  intro m
  rw [coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun p hp => ?_
  have hp' : p.1 + p.2 = m := by simpa using hp
  rw [← hp', map_add, add_add_add_comm]
  exact (h p.1).mul (h' p.2)

theorem coefHom_monomial (d : Fin N × Fin N →₀ ℕ) (g : MvPolynomial (Fin N × Fin N) O) (e : M)
    (hg : IsWeightedHomogeneous wx g (Finsupp.weight u d + e)) : CoefHom wx u (monomial d g) e := by
  intro m
  rw [coeff_monomial]
  split_ifs with h
  · exact h ▸ hg
  · exact isWeightedHomogeneous_zero _ _ _

theorem coefHom_genHom_monomial (wf : Fin N × Fin N → M) (h : ∀ a b s, wx (b, s) = u (a, b) + wf (a, s))
    (d : Fin N × Fin N →₀ ℕ) (c : O) : CoefHom wx u (genHom O N (monomial d c)) (Finsupp.weight wf d) := by
  have hX : ∀ v, CoefHom wx u (genHom O N (X v)) (wf v) := by
    intro v m
    rw [genHom_X, coeff_sum]
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    rw [mul_comm, C_mul_X_eq_monomial]
    refine coefHom_monomial wx u _ _ _ ?_ m
    rw [Finsupp.weight_single, one_smul, ← h]
    exact isWeightedHomogeneous_X _ _ _
  induction d using Finsupp.induction_linear generalizing c with
  | zero =>
    rw [monomial_zero', genHom_C, map_zero]
    refine coefHom_monomial wx u 0 _ _ ?_
    rw [map_zero, add_zero]
    exact isWeightedHomogeneous_C _ _
  | add f g hf hg =>
    rw [← mul_one c, ← monomial_mul, map_mul, map_add]
    exact (hf c).mul wx u (hg 1)
  | single v n =>
    induction n generalizing c with
    | zero =>
      rw [Finsupp.single_zero, monomial_zero', genHom_C, map_zero]
      refine coefHom_monomial wx u 0 _ _ ?_
      rw [map_zero, add_zero]
      exact isWeightedHomogeneous_C _ _
    | succ n ih =>
      rw [Finsupp.single_add, ← mul_one c, ← monomial_mul, map_mul, map_add]
      refine (ih c).mul wx u ?_
      rw [Finsupp.weight_single, one_smul]
      exact hX v

theorem coefHom_genHom (wf : Fin N × Fin N → M) (h : ∀ a b s, wx (b, s) = u (a, b) + wf (a, s))
    (f : MvPolynomial (Fin N × Fin N) O) (e : M) (hf : IsWeightedHomogeneous wf f e) : CoefHom wx u (genHom O N f) e := by
  intro m
  rw [f.as_sum, map_sum, coeff_sum]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [← hf (mem_support_iff.1 hd)]
  exact coefHom_genHom_monomial wx u wf h d _ m

end Weights

theorem coeff_genHom_row (f : MvPolynomial (Fin N × Fin N) O) (m : Fin N × Fin N →₀ ℕ) :
    IsWeightedHomogeneous (rowW N N) (coeff m (genHom O N f)) (Finsupp.weight (colW N N) m) := by
  have := coefHom_genHom (rowW N N) (colW N N) 0 (fun a b s => by simp [rowW, colW]) f 0
    (fun d _ => by simp [Finsupp.weight_apply]) m
  rwa [add_zero] at this

theorem coeff_genHom_col (f : MvPolynomial (Fin N × Fin N) O) (ν : Fin N → ℕ) (hf : IsWeightedHomogeneous (colW N N) f ν)
    (m : Fin N × Fin N →₀ ℕ) : IsWeightedHomogeneous (colW N N) (coeff m (genHom O N f)) ν := by
  have := coefHom_genHom (colW N N) 0 (colW N N) (fun a b s => by simp [colW]) f ν hf m
  simpa [Finsupp.weight_apply] using this

theorem coeff_genHom_mem (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν)
    (m : Fin N × Fin N →₀ ℕ) : coeff m (genHom O N f) ∈ dualWeyl O N N ν := by
  rw [rowst_mem_dualWeyl_iff] at hf ⊢
  refine ⟨coeff_genHom_col O N f ν hf.1 m, fun l j hlj => ?_⟩
  let Φ : MvPolynomial (Option (Fin N × Fin N)) O →+* MvPolynomial (Fin N × Fin N) (MvPolynomial (Option (Fin N × Fin N)) O) :=
    eval₂Hom (C.comp C) fun o => Option.elim o (C (X none)) fun v => ∑ b : Fin N, X (v.1, b) * C (X (some (b, v.2)))
  have h1 : (map (colAddGen O (r := N) l j).toRingHom).comp (genHom O N).toRingHom = Φ.comp (colAddGen O l j).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [Φ, genHom_C]
    · intro v
      by_cases h : v.2 = j
      · simp [Φ, genHom_X, colAddGen, h, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_left_comm]
      · simp [Φ, genHom_X, colAddGen, h]
  have h2 : (map (rename (R := O) (some : Fin N × Fin N → Option (Fin N × Fin N))).toRingHom).comp (genHom O N).toRingHom =
      Φ.comp (rename some).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [Φ, genHom_C]
    · intro v; simp [Φ, genHom_X]
  have h3 := congrArg (coeff m) (RingHom.congr_fun h1 f)
  have h4 := congrArg (coeff m) (RingHom.congr_fun h2 f)
  simp only [RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h3 h4
  rw [h3, h4, hf.2 l j hlj]

theorem genHom_component (v : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) :
    genHom O N (weightedHomogeneousComponent (rowW N N) v f) = weightedHomogeneousComponent (rowW N N) v (genHom O N f) := by
  classical
  let Φ : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →ₐ[MvPolynomial (Fin N × Fin N) O]
      MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) :=
    aeval (fun v : Fin N × Fin N => ∑ b : Fin N, X (v.1, b) * C (X (b, v.2)))
  have h1 : Φ.toRingHom.comp (map C) = (genHom O N).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [Φ, genHom_C]
    · intro v; simp [Φ, genHom_X]
  have h2 : ∀ g, genHom O N g = Φ (map C g) := fun g => (RingHom.congr_fun h1 g).symm
  rw [h2, h2, ← algHom_weightedHomogeneousComponent Φ (rowW N N) (rowW N N)]
  · congr 1
    ext m
    simp only [coeff_map, coeff_weightedHomogeneousComponent]
    split_ifs <;> simp
  · intro u
    simp only [Φ, aeval_X]
    refine IsWeightedHomogeneous.sum _ _ _ fun b _ => ?_
    rw [mul_comm]
    exact (isWeightedHomogeneous_X _ (rowW N N) (u.1, b)).C_mul _

theorem sum_mul_weight_rowW (c : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    ∑ a, c a * Finsupp.weight (rowW N N) m a = ∑ v, c v.1 * m v := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [rowW, Pi.single_apply]

theorem sum_mul_weight_colW (c : Fin N → ℕ) (m : Fin N × Fin N →₀ ℕ) :
    ∑ a, c a * Finsupp.weight (colW N N) m a = ∑ v, c v.2 * m v := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finset.sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [colW, Pi.single_apply]

def expSet (ν : Fin N → ℕ) : Finset (Fin N × Fin N →₀ ℕ) := Finset.finsuppAntidiag Finset.univ (∑ a, ν a)

theorem support_genHom (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    (genHom O N f).support ⊆ expSet N ν := by
  intro m hm
  obtain ⟨d, hd⟩ := ne_zero_iff.1 (mem_support_iff.1 hm)
  have h1 := coeff_genHom_row O N f m hd
  have h2 := coeff_genHom_col O N f ν (rowst_mem_dualWeyl_iff.1 hf).1 m hd
  have h3 := sum_mul_weight_rowW N (fun _ => 1) d
  have h4 := sum_mul_weight_colW N (fun _ => 1) d
  have h5 := sum_mul_weight_colW N (fun _ => 1) m
  simp only [one_mul, h1, h2] at h3 h4 h5
  simp only [expSet, Finset.mem_finsuppAntidiag, Finset.subset_univ, and_true]
  rw [← h5, h3, h4]

theorem genHom_eq_sum (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    genHom O N f = ∑ m ∈ expSet N ν, monomial m (coeff m (genHom O N f)) := by
  conv_lhs => rw [(genHom O N f).as_sum]
  refine Finset.sum_subset (support_genHom O N ν f hf) fun m _ hm => ?_
  rw [notMem_support_iff.1 hm, map_zero]

def extHom {Z : Type} (β : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial Z O) :
    MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →+* MvPolynomial Z (MvPolynomial (Fin N × Fin N) O) :=
  eval₂Hom C fun v => map C (β (X v))

theorem extHom_monomial {Z : Type} (β : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial Z O) (m : Fin N × Fin N →₀ ℕ)
    (g : MvPolynomial (Fin N × Fin N) O) : extHom O N β (monomial m g) = map C (β (monomial m 1)) * C g := by
  rw [extHom, eval₂Hom_monomial, monomial_eq, mul_comm, C_1, one_mul]
  simp only [Finsupp.prod, map_prod, map_pow]

theorem extHom_genHom {Z : Type} (β : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial Z O) (ν : Fin N → ℕ)
    (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    extHom O N β (genHom O N f) = ∑ m ∈ expSet N ν, map C (β (monomial m 1)) * C (coeff m (genHom O N f)) := by
  conv_lhs => rw [genHom_eq_sum O N ν f hf]
  simp only [map_sum, extHom_monomial]

theorem extHom_id (G : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O)) : extHom O N (AlgHom.id O _) G = G := by
  have : extHom O N (AlgHom.id O _) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext <;> intro c <;> simp [extHom]
  rw [this]; rfl

theorem genHom_rowAct (A : Matrix (Fin N) (Fin N) O) (f : MvPolynomial (Fin N × Fin N) O) :
    genHom O N (rowAct O A f) = extHom O N (rowAct O A) (genHom O N f) := by
  have : (genHom O N).toRingHom.comp (rowAct O A).toRingHom = (extHom O N (rowAct O A)).comp (genHom O N).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [extHom, genHom_C]
    · intro v
      simp [extHom, genHom_X, genHom_C, rowAct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm
  exact RingHom.congr_fun this f

def unitHom (Z : Type) : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial Z O := aeval fun v => if v.1 = v.2 then 1 else 0

theorem extHom_unit (Z : Type) (f : MvPolynomial (Fin N × Fin N) O) : extHom O N (unitHom O N Z) (genHom O N f) = C f := by
  have : (extHom O N (unitHom O N Z)).comp (genHom O N).toRingHom = C := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [extHom, genHom_C]
    · intro v
      simp [extHom, genHom_X, unitHom, apply_ite]
  exact RingHom.congr_fun this f

def elemHom (l j : Fin N) : MvPolynomial (Fin N × Fin N) O →ₐ[O] MvPolynomial (Option (Fin N × Fin N)) O :=
  aeval fun v => (if v.1 = v.2 then 1 else 0) + if v = (l, j) then X none else 0

theorem extHom_colAddGen (l j : Fin N) (ν : Fin N → ℕ) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N ν) :
    extHom O N (colAddGen O l j) (genHom O N f) = ∑ p ∈ expSet N ν ×ˢ expSet N ν,
      map C (rename some (monomial p.1 1) * elemHom O N l j (monomial p.2 1)) * C (coeff p.2 (genHom O N (coeff p.1 (genHom O N f)))) := by
  let Θ : MvPolynomial (Fin N × Fin N) (MvPolynomial (Fin N × Fin N) O) →+*
      MvPolynomial (Option (Fin N × Fin N)) (MvPolynomial (Fin N × Fin N) O) :=
    eval₂Hom ((extHom O N (elemHom O N l j)).comp (genHom O N).toRingHom) fun v => X (some v)
  have : (extHom O N (colAddGen O l j)).comp (genHom O N).toRingHom = Θ.comp (genHom O N).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c; simp [extHom, genHom_C, Θ]
    · intro v
      have e1 : ∀ b, extHom O N (elemHom O N l j) (genHom O N (X (b, v.2))) =
          C (X (b, v.2)) + if b = l then X none * C (X (j, v.2)) else 0 := by
        intro b
        simp [extHom, genHom_X, elemHom, apply_ite (map C), add_mul, Finset.sum_add_distrib, ite_and]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [genHom_X]
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, map_mul, Θ, eval₂Hom_X', eval₂Hom_C, e1]
      have e2 : ∀ b, extHom O N (colAddGen O l j) (X (v.1, b)) =
          X (some (v.1, b)) + if b = j then X none * X (some (v.1, l)) else 0 := by
        intro b
        by_cases h : b = j <;> simp [extHom, colAddGen, h]
      simp only [e2]
      simp [extHom, mul_add, add_mul, Finset.sum_add_distrib]
      ring
  refine (RingHom.congr_fun this f).trans ?_
  show Θ (genHom O N f) = _
  conv_lhs => rw [genHom_eq_sum O N ν f hf]
  rw [map_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Θ, eval₂Hom_monomial, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [extHom_genHom O N _ ν _ (coeff_genHom_mem O N ν f hf m), Finset.sum_mul]
  refine Finset.sum_congr rfl fun m' _ => ?_
  have : map (C : O →+* MvPolynomial (Fin N × Fin N) O) (rename (some : Fin N × Fin N → _) (monomial m 1)) =
      m.prod fun i k => X (some i) ^ k := by
    rw [monomial_eq, C_1, one_mul]; simp only [Finsupp.prod, map_prod, map_pow, rename_X, map_X]
  rw [map_mul, this]
  ring

end GlobalTheory.HighWtEmb

end
