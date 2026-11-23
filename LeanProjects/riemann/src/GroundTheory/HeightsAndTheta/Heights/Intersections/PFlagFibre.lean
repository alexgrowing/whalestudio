import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagBundleSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.LinEmbedSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.FlagDimSt
import GroundTheory.HeightsAndTheta.Heights.Intersections.RelBaseChangeSt
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCauchyBinet
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Linear

variable {K : Type} {ι : K → Type} {N1 n : ℕ}

def flagFibreBlocksEquiv : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)) ≃ Fin (n - 1) where
  toFun k := match k with
    | ⟨.inl k, h⟩ => (h ⟨k, rfl⟩).elim
    | ⟨.inr j, _⟩ => j
  invFun j := ⟨.inr j, by rintro ⟨k, hk⟩; cases hk⟩
  left_inv k := by
    match k with
    | ⟨.inl k, h⟩ => exact (h ⟨k, rfl⟩).elim
    | ⟨.inr j, _⟩ => rfl
  right_inv _ := rfl

def flagCompound {F : Type} [Field F] (B : Matrix (Fin n) (Fin N1) F) :
    ∀ k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)),
      fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl k → PluckerBlocks n n (flagFibreBlocksEquiv k) → F
  | ⟨.inl k, h⟩ => (h ⟨k, rfl⟩).elim
  | ⟨.inr _, _⟩ => fun S S' => (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det

theorem fibreDeg_flag (a : K ⊕ Fin (n - 1) → ℤ) :
    fibreDeg Sum.inl a = (fun j => a (Sum.inr j)) ∘ (flagFibreBlocksEquiv (K := K) (n := n)) := by
  funext k
  match k with
  | ⟨.inl k, h⟩ => exact (h ⟨k, rfl⟩).elim
  | ⟨.inr _, _⟩ => rfl

theorem flagMinor_mul {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (B' : Matrix (Fin n) (Fin N1) R)
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    flagMinor (M * B') j S = ∑ S' : PluckerBlocks n n j,
      flagMinor M j S' * (B'.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det := by
  unfold flagMinor
  rw [Matrix.submatrix_mul M B' _ id _ Function.bijective_id, CauchyBinet.proof]
  rfl

end Linear

section Compound

variable {F : Type} [Field F] {N1 n : ℕ}

theorem exists_mul_eq_one (B : Matrix (Fin n) (Fin N1) F) (hB : LinearIndependent F B.row) :
    ∃ C : Matrix (Fin N1) (Fin n) F, B * C = 1 := by
  have hinj : Function.Injective (Matrix.vecMulLinear B) := Matrix.vecMul_injective_iff.2 hB
  obtain ⟨g, hg⟩ := (Matrix.vecMulLinear B).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨Matrix.of fun c b => g (Pi.single c 1) b, ?_⟩
  ext i b
  have hrow : Matrix.vecMulLinear B (Pi.single i 1) = B i := by
    ext c
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  have h1 := LinearMap.congr_fun hg (Pi.single i 1)
  rw [LinearMap.comp_apply, hrow, LinearMap.id_apply] at h1
  have h2 : ∑ c, B i c • (Pi.single c 1 : Fin N1 → F) = B i := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  calc (B * Matrix.of fun c b => g (Pi.single c 1) b) i b = ∑ c, B i c * g (Pi.single c 1) b := by
        simp [Matrix.mul_apply]
    _ = g (B i) b := by
        conv_rhs => rw [← h2]
        simp [map_sum, Finset.sum_apply, map_smul]
    _ = (1 : Matrix (Fin n) (Fin n) F) i b := by
        rw [h1, Matrix.one_apply, Pi.single_apply]
        exact if_congr eq_comm rfl rfl

theorem det_one_submatrix {m : ℕ} (S' S'' : {S : Finset (Fin n) // S.card = m}) :
    ((1 : Matrix (Fin n) (Fin n) F).submatrix (S'.1.orderEmbOfFin S'.2) (S''.1.orderEmbOfFin S''.2)).det =
      if S' = S'' then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.submatrix_one _ (S'.1.orderEmbOfFin S'.2).injective, Matrix.det_one]
  · have hsub : ¬ S'.1 ⊆ S''.1 := fun hs =>
      h (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [S'.2, S''.2])))
    obtain ⟨x, hx, hx'⟩ := Finset.not_subset.1 hsub
    have hr : x ∈ Set.range (S'.1.orderEmbOfFin S'.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨r, hr⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply_ne]
    intro he
    apply hx'
    rw [← hr, he]
    exact Finset.orderEmbOfFin_mem _ _ _

theorem compound_mul_eq {m : ℕ} (B : Matrix (Fin n) (Fin N1) F) (C : Matrix (Fin N1) (Fin n) F) (hBC : B * C = 1)
    (S' S'' : {S : Finset (Fin n) // S.card = m}) :
    ∑ S : {S : Finset (Fin N1) // S.card = m},
        (C.submatrix (S.1.orderEmbOfFin S.2) (S''.1.orderEmbOfFin S''.2)).det *
          (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det =
      if S' = S'' then 1 else 0 := by
  rw [← det_one_submatrix S' S'', ← hBC,
    Matrix.submatrix_mul B C _ id _ Function.bijective_id, CauchyBinet.proof]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem compound_injective {m : ℕ} (B : Matrix (Fin n) (Fin N1) F) (hB : LinearIndependent F B.row) :
    Function.Injective (Matrix.of fun (S : {S : Finset (Fin N1) // S.card = m})
      (S' : {S : Finset (Fin n) // S.card = m}) =>
        (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det).mulVec := by
  obtain ⟨C, hBC⟩ := exists_mul_eq_one B hB
  let D : Matrix {S : Finset (Fin n) // S.card = m} {S : Finset (Fin N1) // S.card = m} F :=
    Matrix.of fun S'' S => (C.submatrix (S.1.orderEmbOfFin S.2) (S''.1.orderEmbOfFin S''.2)).det
  have hD : D * (Matrix.of fun (S : {S : Finset (Fin N1) // S.card = m})
      (S' : {S : Finset (Fin n) // S.card = m}) =>
        (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det) = 1 := by
    ext S'' S'
    have hc : (if S'' = S' then (1 : F) else 0) = if S' = S'' then 1 else 0 := if_congr eq_comm rfl rfl
    rw [Matrix.mul_apply, Matrix.one_apply, hc, ← compound_mul_eq B C hBC S' S'']
    rfl
  intro x y hxy
  have := congrArg D.mulVec hxy
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD, Matrix.one_mulVec, Matrix.one_mulVec] at this

theorem flagCompound_injective {K : Type} {ι : K → Type} (B : Matrix (Fin n) (Fin N1) F)
    (hB : LinearIndependent F B.row) (k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1))) :
    Function.Injective (Matrix.of (flagCompound (ι := ι) B k)).mulVec := by
  match k with
  | ⟨.inl k, h⟩ => exact (h ⟨k, rfl⟩).elim
  | ⟨.inr j, _⟩ => exact compound_injective (m := j + 1) B hB

end Compound

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem fibreIdeal_flag (P : Ideal (MRing ι)) [hP : P.IsPrime] (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    fibreIdeal Sum.inl (flagGenFibre P hP B) =
      (flagIdealOver (FnField P) n).comap
        (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B)).toRingHom := by
  show RingHom.ker (aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)),
      fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl k =>
        algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P)))
          (flagMap P B (X ⟨q.1.1, q.2⟩))) :
      MRingOver (FnField P) (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl) →ₐ[FnField P]
        FractionRing (MvPolynomial (Fin n × Fin n) (FnField P))) = _
  have key : ∀ f, aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)),
      fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl k =>
        algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P)))
          (flagMap P B (X ⟨q.1.1, q.2⟩))) f =
      algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P)))
        (aeval (fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat (FnField P) n) q.1 q.2)
          (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B) f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [aeval_C, show (C a : MRingOver (FnField P) (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl)) =
        algebraMap (FnField P) _ a from rfl, AlgHom.commutes, AlgHom.commutes]
      exact IsScalarTower.algebraMap_apply _ _ _ a
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add, map_add]
    | mul_X p q hp =>
      rw [map_mul, hp, map_mul, map_mul, map_mul]
      congr 1
      rw [aeval_X, blockLinSubst, aeval_X]
      obtain ⟨⟨k, hk⟩, S⟩ := q
      match k, hk, S with
      | .inl k, h, _ => exact (h ⟨k, rfl⟩).elim
      | .inr j, h, S =>
        congr 1
        rw [flagMap, eval₂Hom_X']
        refine (flagMinor_mul (genMat (FnField P) n) (B.map C) j S).trans ?_
        simp only [map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]
        refine Finset.sum_congr rfl fun S' _ => ?_
        exact (mul_comm _ _).trans
          (congrArg (· * flagMinor (genMat (FnField P) n) j S') (RingHom.map_det C _).symm)
  ext f
  simp only [flagIdealOver, RingHom.mem_ker, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [key, map_eq_zero_iff _ (IsFractionRing.injective _ _)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem charZero_fnField (P : Ideal (MRing ι)) [P.IsPrime] (hP : IsHorizontal P) : CharZero (FnField P) := by
  refine charZero_of_inj_zero fun m hm => ?_
  have h1 : algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P (C (m : ℤ))) = 0 := by
    simpa using hm
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : (m : ℤ) ∈ P.comap (C : ℤ →+* MRing ι) := h1
  rw [hP, Ideal.mem_bot] at h2
  exact_mod_cast h2

theorem map_flagMinor (F F' : Type) [Field F] [Field F'] [Algebra F F'] (j : Fin (n - 1)) (S : PluckerBlocks n n j) :
    MvPolynomial.map (algebraMap F F') (flagMinor (genMat F n) j S) = flagMinor (genMat F' n) j S := by
  unfold flagMinor
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [genMat]

theorem flagIdealOver_map (hRel : RelBaseChange.Statement) (F F' : Type) [Field F] [Field F'] [Algebra F F'] :
    (flagIdealOver F n).map (MvPolynomial.map (algebraMap F F')) = flagIdealOver F' n := by
  unfold flagIdealOver
  rw [hRel F F']
  simp only [map_flagMinor]

end Fibre

theorem FlagFibre.proof
    (hEU : ∀ (K : Type) [Fintype K] (F : Type) [Field F] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hBC : ∀ (K : Type) [Fintype K] (F F' : Type) [Field F] [Field F'] [Algebra F F'] (ι : K → Type)
      [∀ k, Fintype (ι k)], BaseChangeStatement F F' ι)
    (hLin : LinEmbed.Statement) (hDim : FlagDim.Statement) (hRel : RelBaseChange.Statement) :
    FlagFibre.Statement := by
  intro K _ ι _ N1 t n P d c m B hP _ hB J₀ hJ₀
  have : P.IsPrime := hP.2.1.1
  have : CharZero (FnField P) := charZero_fnField P hP.2.2.1
  obtain ⟨J, hJ, -⟩ := hEU _ (FnField P) (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl)
  obtain ⟨J₁, hJ₁, -⟩ := hEU _ (FnField P) (PluckerBlocks n n)
  refine ⟨J, hJ, fun a => ?_⟩
  have hfib : fibreIdeal Sum.inl (flagGenFibre P hP.2.1.1 B) =
      (flagIdealOver (FnField P) n).comap
        (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B)).toRingHom :=
    fibreIdeal_flag P B
  have hdeg : (fun j => fibreDeg Sum.inl (a j)) =
      fun j => (fun j' => a j (Sum.inr j')) ∘ (flagFibreBlocksEquiv (K := K) (n := n)) :=
    funext fun j => fibreDeg_flag (a j)
  have h1 : J (fibreIdeal Sum.inl (flagGenFibre P hP.2.1.1 B)) (flagDim n) (fun j => fibreDeg Sum.inl (a j)) =
      J₁ (flagIdealOver (FnField P) n) (flagDim n) (fun j j' => a j (Sum.inr j')) := by
    rw [hfib, hdeg]
    exact hLin (FnField P) (Fin (n - 1)) _ (PluckerBlocks n n) _ flagFibreBlocksEquiv (flagCompound B)
      (flagCompound_injective B hB.1) J₁ J hJ₁ hJ _ _ _ (hDim _ n)
  rw [h1]
  have h2 := hBC _ ℚ (FnField P) (PluckerBlocks n n) J₀ J₁ hJ₀ hJ₁ (flagIdealQ n) (flagDim n)
    (fun j j' => a j (Sum.inr j')) (hDim ℚ n)
  have := flagIdealOver_isPrime (FnField P) n
  rw [h2, flagIdealQ_eq, flagIdealOver_map hRel, Ideal.minimalPrimes_eq_subsingleton_self,
    finsum_mem_singleton, inh_multAt_self]
  simp

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
