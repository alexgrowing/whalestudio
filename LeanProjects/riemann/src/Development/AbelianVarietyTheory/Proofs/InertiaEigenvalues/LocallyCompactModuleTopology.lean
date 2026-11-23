import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open Polynomial TensorProduct

noncomputable section

namespace GlobalTheory.JR.EtExist

variable (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def conjAlg [h : Unram F E] : E →ₐ[F] E :=
  { starRingEnd E with commutes' := fun x => h.star_fix x }

theorem conjAlg_apply [Unram F E] (y : E) : conjAlg F E y = star y := rfl

variable (K : Type) [CommRing K] [Algebra F K]

def conjT [Unram F E] : E ⊗[F] K →ₐ[F] E ⊗[F] K := Algebra.TensorProduct.map (conjAlg F E) (AlgHom.id F K)

theorem conjT_conjT [Unram F E] (z : E ⊗[F] K) : conjT F E K (conjT F E K z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [conjT, conjAlg_apply]
  | add a b ha hb => simp [ha, hb]

@[reducible] def starT [Unram F E] : StarRing (E ⊗[F] K) where
  star := conjT F E K
  star_involutive := conjT_conjT F E K
  star_mul a b := by
    change conjT F E K (a * b) = conjT F E K b * conjT F E K a
    rw [map_mul, mul_comm]
  star_add a b := map_add (conjT F E K) a b

theorem locallyCompact_moduleTopology [LocallyCompactSpace F] [Module.Finite F K] :
    @LocallyCompactSpace K (moduleTopology F K) := by
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  let b := (Module.finBasis F K).equivFun
  have h1 : Continuous b := IsModuleTopology.continuous_of_linearMap b.toLinearMap
  haveI : ContinuousAdd K := IsModuleTopology.toContinuousAdd F K
  have h2 : Continuous b.symm := IsModuleTopology.continuous_of_linearMap b.symm.toLinearMap
  let e : K ≃ₜ (Fin (Module.finrank F K) → F) := { b.toEquiv with continuous_toFun := h1, continuous_invFun := h2 }
  exact e.isClosedEmbedding.locallyCompactSpace

def ofAlgebra [h : Unram F E] [Module.Finite F K] [IsReduced K] : Et F E :=
  letI : TopologicalSpace K := moduleTopology F K
  haveI : IsModuleTopology F K := ⟨rfl⟩
  letI : TopologicalSpace (E ⊗[F] K) := moduleTopology F (E ⊗[F] K)
  letI : Algebra K (E ⊗[F] K) := Algebra.TensorProduct.rightAlgebra
  { K := K
    L := E ⊗[F] K
    trK := IsModuleTopology.isTopologicalRing F K
    lcK := haveI := h.lcF; locallyCompact_moduleTopology F K
    mK := borel K
    bK := @BorelSpace.mk _ _ (borel K) rfl
    stL := starT F E K
    mtL := ⟨rfl⟩
    mL := borel (E ⊗[F] K)
    bL := @BorelSpace.mk _ _ (borel (E ⊗[F] K)) rfl
    push := inferInstance
    star_K := fun x => by
      change conjT F E K (1 ⊗ₜ x) = 1 ⊗ₜ x
      simp [conjT]
    star_E := fun y => by
      change conjT F E K (y ⊗ₜ 1) = star y ⊗ₜ 1
      simp [conjT, conjAlg_apply] }

theorem exists_field [h : Unram F E] : ∃ A : Et F E, IsField A.K ∧ IsField A.L ∧ Module.finrank F A.K = 1 := by
  haveI := h.lcF
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [h.finrank_eq]; norm_num)
  exact ⟨{ K := F, L := E, mK := borel F, bK := @BorelSpace.mk _ _ (borel F) rfl, mL := borel E,
           bL := @BorelSpace.mk _ _ (borel E) rfl, mtL := isModuleTopologyOfFiniteDimensional,
           push := inferInstance, star_K := h.star_fix, star_E := fun _ => rfl },
    Field.toIsField F, Field.toIsField E, Module.finrank_self F⟩

theorem exists_isGen [Unram F E] (r : ℕ) (p : Fin r → F)
    (hs : (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]).Separable) : ∃ (A : Et F E) (τ : A.K), A.IsGen τ p := by
  set P : F[X] := X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) with hP
  have hlt : (∑ i, C (p i) * X ^ (i : ℕ) : F[X]).degree < r := degree_sum_fin_lt p
  have hm : P.Monic := monic_X_pow_add hlt
  have hd : P.natDegree = r := by
    have : P.degree = r := by
      rw [hP, degree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), degree_X_pow]
    exact natDegree_eq_of_degree_eq_some this
  let pb := AdjoinRoot.powerBasis' hm
  haveI : Module.Finite F (AdjoinRoot P) := pb.finite
  haveI : IsReduced (AdjoinRoot P) :=
    (Ideal.isRadical_iff_quotient_reduced _).1
      ((isRadical_iff_span_singleton).1 hs.squarefree.isRadical)
  refine ⟨ofAlgebra F E (AdjoinRoot P), AdjoinRoot.root P, ?_, ?_, ?_⟩
  · change LinearIndependent F (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ))
    have := pb.basis.linearIndependent.comp (Fin.cast (show r = pb.dim from hd.symm)) (Fin.cast_injective _)
    have e : (fun i : Fin r => AdjoinRoot.root P ^ (i : ℕ)) = pb.basis ∘ Fin.cast (show r = pb.dim from hd.symm) := by
      funext i
      rw [Function.comp_apply, pb.basis_eq_pow]
      rfl
    rw [e]; exact this
  · change Module.finrank F (AdjoinRoot P) = r
    rw [pb.finrank]; exact hd
  · change AdjoinRoot.root P ^ r + ∑ i, p i • AdjoinRoot.root P ^ (i : ℕ) = 0
    have := AdjoinRoot.aeval_eq (f := P) P
    rw [AdjoinRoot.mk_self] at this
    have h2 : aeval (AdjoinRoot.root P) (X ^ r + ∑ i, C (p i) * X ^ (i : ℕ) : F[X]) = 0 := this
    simp only [map_add, map_pow, map_sum, map_mul, aeval_X, aeval_C] at h2
    simpa only [Algebra.smul_def] using h2

theorem exists_et : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [GlobalTheory.JR.Unram F E],
    (∃ A : GlobalTheory.JR.Et F E, IsField A.K ∧ IsField A.L ∧ Module.finrank F A.K = 1) ∧
    ∀ (r : ℕ) (p : Fin r → F),
      (Polynomial.X ^ r + ∑ i, Polynomial.C (p i) * Polynomial.X ^ (i : ℕ) : Polynomial F).Separable →
      ∃ (A : GlobalTheory.JR.Et F E) (τ : A.K), A.IsGen τ p :=
  fun F E _ _ _ _ _ => ⟨exists_field F E, exists_isGen F E⟩

end GlobalTheory.JR.EtExist
