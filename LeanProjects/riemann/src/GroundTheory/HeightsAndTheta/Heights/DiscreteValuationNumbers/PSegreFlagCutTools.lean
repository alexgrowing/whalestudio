import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsSegreFlagCut
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairNumSectionCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial GenericProjClosureDivisor

noncomputable section

section Lift

variable {K : Type} {ι : K → Type} {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {M M' : ℕ} {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]

theorem liftPairDeg_sub (a b : K → ℤ) : liftPairDeg (a - b) = liftPairDeg a - liftPairDeg b := by
  funext o
  rcases o with _ | _ | k <;> simp [liftPairDeg]

theorem isMultiHomog_liftPairForm [DecidableEq K] {f : MRing ι O} {b : K → ℕ} (hf : IsMultiHomog f b) :
    IsMultiHomog (liftPairForm M M' f) (vdeg b) := by
  intro d hd
  obtain ⟨u, rfl, hu⟩ := coeff_rename_ne_zero _ f d hd
  have hb := hf hu
  rw [← hb]
  funext o
  have hσ : Function.Injective
      (fun p : Σ k, ι k => (⟨some (some p.1), p.2⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o)) := by
    rintro ⟨a, i⟩ ⟨a', i'⟩ h
    injection h with h1 h2
    injection h1 with h1
    injection h1 with h1
    subst h1
    exact Sigma.ext rfl h2
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum_mapDomain_index_inj hσ]
  rcases o with _ | _ | k <;> simp [Finsupp.sum, Finset.sum_apply, blockWeight, Pi.single_apply, vdeg]

theorem aeval_liftPairForm {y : (Σ k, ι k) → Ω} {pt : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    (hpt : ∀ p : Σ k, ι k, pt ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p)) (f : MRing ι O) :
    aeval pt (liftPairForm M M' f) = algebraMap Ω Φ (aeval y f) := by
  unfold liftPairForm
  have e : pt ∘ (fun p : Σ k, ι k => (⟨some (some p.1), p.2⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o)) =
      algebraMap Ω Φ ∘ y := funext hpt
  rw [aeval_rename, e, aeval_algebraMap_apply]

end Lift

section LiftIdeal

variable {K : Type} {ι : K → Type} {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {M M' : ℕ} {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]

theorem pointConeMap_liftPairForm {y : (Σ k, ι k) → Ω} {pt : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    (hpt : ∀ p : Σ k, ι k, pt ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p)) (f : MRing ι O) :
    pointConeMap O pt (liftPairForm M M' f) =
      rename (fun k : K => some (some k)) (MvPolynomial.map (algebraMap Ω Φ) (pointConeMap O y f)) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    simp only [liftPairForm, rename_C, pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, map_C]
    rw [IsScalarTower.algebraMap_apply O Ω Φ]
  | add p q hp hq =>
    simp only [liftPairForm, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p v hp =>
    simp only [liftPairForm, pointConeMap] at hp ⊢
    simp only [map_mul, rename_X, aeval_X, map_X, map_C, rename_C, hpt, hp]

theorem liftPairForm_mem_iff {y : (Σ k, ι k) → Ω} {pt : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    (hpt : ∀ p : Σ k, ι k, pt ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p)) (f : MRing ι O) :
    liftPairForm M M' f ∈ pointIdeal O pt ↔ f ∈ pointIdeal O y := by
  unfold pointIdeal
  rw [RingHom.mem_ker, RingHom.mem_ker]
  rw [pointConeMap_liftPairForm hpt]
  have hinj : Function.Injective (fun k : K => (some (some k) : Option (Option K))) :=
    fun a b h => Option.some_injective _ (Option.some_injective _ h)
  constructor
  · intro h
    have h' : MvPolynomial.map (algebraMap Ω Φ) (pointConeMap O y f) = 0 :=
      rename_injective _ hinj (by rw [h, map_zero])
    exact map_injective _ (algebraMap Ω Φ).injective (by rw [h', map_zero])
  · intro h
    rw [h, map_zero, map_zero]

theorem IsVerticalDivisor.liftPair [DecidableEq K] {y : (Σ k, ι k) → Ω} {pt : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ}
    (hpt : ∀ p : Σ k, ι k, pt ⟨some (some p.1), p.2⟩ = algebraMap Ω Φ (y p)) {ϖ : O} {b : K → ℤ}
    {f g : MRing ι O} (hD : IsVerticalDivisor (pointIdeal O y) ϖ b f g) :
    IsVerticalDivisor (pointIdeal O pt) ϖ (liftPairDeg b) (liftPairForm M M' f) (liftPairForm M M' g) := by
  obtain ⟨bf, bg, hbf, hbg, hb⟩ := hD.degrees
  refine IsVerticalDivisor.of_unit_off_special ⟨vdeg bf, vdeg bg, isMultiHomog_liftPairForm hbf,
    isMultiHomog_liftPairForm hbg, ?_⟩ (fun h => hD.num_not_mem ((liftPairForm_mem_iff hpt f).1 h))
    (fun h => hD.den_not_mem ((liftPairForm_mem_iff hpt g).1 h)) ?_
  · rw [← hb]
    funext o
    rcases o with _ | _ | k <;> simp [vdeg, liftPairDeg]
  · intro W hW hPW hrel hϖ
    let σ : MRing ι O →+* MRing (bundleIdx (bundleIdx ι M) M') O := (rename fun p : Σ k, ι k =>
      (⟨some (some p.1), p.2⟩ : Σ o, bundleIdx (bundleIdx ι M) M' o)).toRingHom
    have hσ : ∀ a, σ a = liftPairForm M M' a := fun _ => rfl
    have hW' : (W.comap σ).IsPrime := Ideal.comap_isPrime σ W
    have hPW' : pointIdeal O y ≤ W.comap σ := by
      intro a ha
      rw [Ideal.mem_comap, hσ]
      exact hPW ((liftPairForm_mem_iff hpt a).2 ha)
    have hrel' : IsRelevant (W.comap σ) := by
      intro k
      obtain ⟨i, hi⟩ := hrel (some (some k))
      refine ⟨i, ?_⟩
      rw [Ideal.mem_comap, hσ]
      simpa [liftPairForm] using hi
    have hϖ' : (C ϖ : MRing ι O) ∉ W.comap σ := by
      rw [Ideal.mem_comap, hσ]
      simpa [liftPairForm] using hϖ
    obtain ⟨u, v, hu, hv, h⟩ := hD.unit_off_special _ hW' hPW' hrel' hϖ'
    refine ⟨liftPairForm M M' u, liftPairForm M M' v, by rwa [← hσ, ← Ideal.mem_comap],
      by rwa [← hσ, ← Ideal.mem_comap], ?_⟩
    have e : liftPairForm M M' u * liftPairForm M M' f - liftPairForm M M' v * liftPairForm M M' g =
        liftPairForm M M' (u * f - v * g) := by
      simp only [liftPairForm, map_sub, map_mul]
    rw [e]
    exact (liftPairForm_mem_iff hpt _).2 h

end LiftIdeal

section Divisors

variable {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O]

theorem IsVerticalDivisor.restrict {P H : Ideal (MRing ι O)} {ϖ : O} {b : K → ℤ} {f g : MRing ι O}
    (hD : IsVerticalDivisor P ϖ b f g) (hPH : P ≤ H) (hf : f ∉ H) (hg : g ∉ H) :
    IsVerticalDivisor H ϖ b f g :=
  IsVerticalDivisor.of_unit_off_special hD.degrees hf hg fun W hW hHW hrel hϖ => by
    obtain ⟨u, v, hu, hv, h⟩ := hD.unit_off_special W hW (hPH.trans hHW) hrel hϖ
    exact ⟨u, v, hu, hv, hPH h⟩

variable [IsDomain O] [IsDiscreteValuationRing O] [Fintype K] [∀ k, Fintype (ι k)]

omit [DecidableEq K] in

theorem ratDiv_eq_of_sub_mem {P : Ideal (MRing ι O)} [P.IsPrime] {f g f' g' : MRing ι O} (hf : f ∉ P)
    (hg : g ∉ P) (hf' : f' ∉ P) (hg' : g' ∉ P) (h : f * g' - f' * g ∈ P) :
    ratDiv P f g = ratDiv P f' g' := by
  have e := divCycle_eq_of_sub_mem h
  rw [DivCycleMul.full O K ι P f g' ‹_› hf hg', DivCycleMul.full O K ι P f' g ‹_› hf' hg] at e
  funext W
  have eW := congrFun e W
  simp only [Pi.add_apply] at eW
  simp only [ratDiv]
  omega

end Divisors

section Flags

variable {Ω : Type*} [Field Ω] {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E] {Φ : Type*} [Field Φ]
  [Algebra Ω Φ]

theorem repr_flag_inv (w w' : Module.Basis (Fin N) Ω E) (hsame : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) :
    ∀ i j : Fin N, i < j → w'.repr (w i) j = 0 := by
  classical
  have hAB : w.toMatrix w' * w'.toMatrix w = 1 := w.toMatrix_mul_toMatrix_flip w'
  have hA : (w.toMatrix w').BlockTriangular id := by
    intro i j hji
    rw [Module.Basis.toMatrix_apply]
    exact hsame j i hji
  let _ := invertibleOfRightInverse _ _ hAB
  have hB : (w'.toMatrix w).BlockTriangular id := by
    have h := Matrix.blockTriangular_inv_of_blockTriangular hA
    rwa [Matrix.inv_eq_right_inv hAB] at h
  intro i j hij
  have h := hB hij
  rwa [Module.Basis.toMatrix_apply] at h

theorem repr_flag_diag (w w' : Module.Basis (Fin N) Ω E) (hsame : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0)
    (k : Fin N) : w.repr (w' k) k * w'.repr (w k) k = 1 := by
  classical
  have hAB : w.toMatrix w' * w'.toMatrix w = 1 := w.toMatrix_mul_toMatrix_flip w'
  have h := congrFun (congrFun hAB k) k
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single k] at h
  · simpa only [Module.Basis.toMatrix_apply] using h
  · intro i _ hik
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · rw [Module.Basis.toMatrix_apply, hsame i k hlt, zero_mul]
    · rw [Module.Basis.toMatrix_apply (e := w'), repr_flag_inv w w' hsame k i hgt, mul_zero]
  · simp

theorem flagLineCoord_flag (w w' e : Module.Basis (Fin N) Ω E)
    (hsame : ∀ i j : Fin N, i < j → w.repr (w' i) j = 0) (t : Fin N → Φ) (k : ℕ) (hk : k < N) :
    flagLineCoord w w e t (k + 1) ⟨k, hk⟩ =
      algebraMap Ω Φ (w.repr (w' ⟨k, hk⟩) ⟨k, hk⟩) * flagLineCoord w' w e t (k + 1) ⟨k, hk⟩ := by
  classical
  unfold flagLineCoord
  rw [Finset.sum_eq_single ⟨k, hk⟩, Finset.sum_eq_single ⟨k, hk⟩]
  · rw [Module.Basis.repr_self, Finsupp.single_eq_same, map_one, mul_one, ← mul_assoc,
      mul_comm (algebraMap Ω Φ _), mul_assoc, ← map_mul, repr_flag_diag w w' hsame, map_one, mul_one]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · rw [repr_flag_inv w w' hsame j ⟨k, hk⟩ hlt, map_zero, mul_zero]
    · have h0 : flagCoord w e t (k + 1) j = 0 := by
        unfold flagCoord
        rw [if_neg]
        exact fun h => absurd hgt (by rw [Fin.lt_def]; simp only; omega)
      rw [h0, zero_mul]
  · simp
  · intro j _ hj
    rw [Module.Basis.repr_self, Finsupp.single_apply, if_neg hj, map_zero, mul_zero]
  · simp

end Flags

section Slots

variable {K : Type} {ι : K → Type} {R : Type} [CommRing R] {M M' m : ℕ}

theorem closureForm_zero (h : MRing (bundleIdx (bundleIdx ι M) M') R) (F : Fin m → MRing ι R) :
    closureForm M M' h F (Fin.castAdd m 0) = h := by
  simp [closureForm]

theorem closureForm_natAdd (h : MRing (bundleIdx (bundleIdx ι M) M') R) (F : Fin m → MRing ι R) (j : Fin m) :
    closureForm M M' h F (Fin.natAdd 1 j) = liftPairForm M M' (F j) := by
  simp [closureForm]

theorem closureDeg_zero (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) :
    closureDeg ζ L (Fin.castAdd m 0) = ζ := by
  simp [closureDeg]

theorem closureDeg_natAdd (ζ : Option (Option K) → ℤ) (L : Fin m → K → ℤ) (j : Fin m) :
    closureDeg ζ L (Fin.natAdd 1 j) = liftPairDeg (L j) := by
  simp [closureDeg]

end Slots

section Numbers

variable {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O]

theorem cycEval_zero_fun (Z : Ideal (MRing ι O) → ℤ) : cycEval (fun _ => 0) Z = 0 := by
  simp [cycEval]

theorem cycEval_congr_cycle {n Z Z' : Ideal (MRing ι O) → ℤ} (h : ∀ W, Z W * n W = Z' W * n W) :
    cycEval n Z = cycEval n Z' := by
  unfold cycEval
  exact finsum_congr h

theorem cycEval_add_fun (n₁ n₂ Z : Ideal (MRing ι O) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => n₁ W + n₂ W) Z = cycEval n₁ Z + cycEval n₂ Z := by
  rw [cycEval_eq_sum hZ, cycEval_eq_sum hZ, cycEval_eq_sum hZ, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

theorem cycEval_sub_fun (n₁ n₂ Z : Ideal (MRing ι O) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => n₁ W - n₂ W) Z = cycEval n₁ Z - cycEval n₂ Z := by
  rw [cycEval_eq_sum hZ, cycEval_eq_sum hZ, cycEval_eq_sum hZ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun W _ => ?_
  ring

theorem eq_C_of_isHomogeneous_zero {σ : Type*} {A : MvPolynomial σ ℤ} (hA : A.IsHomogeneous 0) :
    A = C (A.coeff 0) := by
  classical
  ext μ
  rw [coeff_C]
  split_ifs with h
  · rw [h]
  · exact hA.coeff_eq_zero (by rwa [Ne, Finsupp.degree_eq_zero_iff, eq_comm])

theorem classNum_of_isHomogeneous_zero {σ : Type*} (z z' : σ → K → ℤ) {A : MvPolynomial σ ℤ}
    (hA : A.IsHomogeneous 0) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum z A Q W = classNum z' A Q W := by
  unfold classNum
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have h0 : μ = 0 := by
    by_contra hne
    exact (mem_support_iff.mp hμ) (hA.coeff_eq_zero (by rwa [Ne, Finsupp.degree_eq_zero_iff]))
  subst h0
  simp [classList]

variable [Fintype K] [∀ k, Fintype (ι k)]

theorem pairNum_congr_ratDiv {P : Ideal (MRing ι O)} {r : ℕ} {z z' : Fin r → K → ℤ}
    {F G F' G' : Fin r → MRing ι O} (h : ∀ i, ratDiv P (F i) (G i) = ratDiv P (F' i) (G' i))
    (Gs : Fin r → MvPolynomial (Fin r ⊕ Fin r) ℤ) (Q : List (K → ℤ)) :
    pairNum P z z' F G Gs Q = pairNum P z z' F' G' Gs Q := by
  unfold pairNum
  simp only [h]

theorem pairNum_single {P : Ideal (MRing ι O)} {r : ℕ} (z z' : Fin r → K → ℤ) (F G : Fin r → MRing ι O)
    (j : Fin r) (H : MvPolynomial (Fin r ⊕ Fin r) ℤ) (Q : List (K → ℤ)) :
    pairNum P z z' F G (Pi.single j H) Q = cycEval (fun W => classNum (Sum.elim z z') H Q W) (ratDiv P (F j) (G j)) := by
  unfold pairNum
  rw [Finset.sum_eq_single j]
  · rw [Pi.single_eq_same]
  · intro i _ hi
    rw [Pi.single_eq_of_ne hi]
    simp only [classNum_zero_poly]
    exact cycEval_zero_fun _
  · simp

theorem pairNum_mul_pairSum {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {e : ℕ} (hP : IsModelOver P (e + 1))
    {r : ℕ} (z z' : Fin r → K → ℤ) (fs gs : Fin r → MRing ι O)
    (hD : ∀ i, IsVerticalDivisor P ϖ (z i - z' i) (fs i) (gs i)) (a b : Fin r) {t : ℕ}
    {Bs : Fin r → MvPolynomial (Fin r ⊕ Fin r) ℤ} (hBs : ∀ i, (Bs i).IsHomogeneous t) (Q : List (K → ℤ))
    (hQ : e ≤ t + Q.length) :
    pairNum P z z' fs gs (fun i => (X (Sum.inr a) + X (Sum.inr b)) * Bs i) Q =
      pairNum P z z' fs gs Bs ((z' a + z' b) :: Q) := by
  unfold pairNum
  refine Finset.sum_congr rfl fun i _ => cycEval_congr_support fun W hW => ?_
  dsimp only
  rw [add_mul, classNum_add_poly, classNum_X_mul, classNum_X_mul, ← Finset.sum_add_distrib]
  unfold classNum
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have hlen : e ≤ (classList (Sum.elim z z') μ ++ Q).length := by
    rw [List.length_append, classList_length_of_mem_support _ (hBs i) hμ]
    exact hQ
  rw [vNumL_perm W List.perm_middle, vNumL_add_of_ratDiv_ne_zero hϖ hP (hD i) hW _ _ _ hlen]
  simp only [Sum.elim_inr]
  ring

end Numbers

end

end GroundTheory.Heights₂.Heights.NumbersDVR
