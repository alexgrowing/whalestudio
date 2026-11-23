import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open Matrix Polynomial GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms

namespace GlobalTheory.RegSS.CycAlg

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]

def lowPoly (c : n → A) : A[X] :=
  ∑ j, c j • (X : A[X]) ^ ((Fintype.equivFin n j : Fin (Fintype.card n)) : ℕ)

theorem aeval_lowPoly_mulVec (M : Matrix n n A) (v c : n → A) :
    aeval M (lowPoly c) *ᵥ v = krylov M v *ᵥ c := by
  funext i
  simp only [lowPoly, map_sum, map_smul, map_pow, aeval_X, Matrix.sum_mulVec, Matrix.smul_mulVec,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [krylov, Matrix.mulVec, dotProduct, Matrix.of_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_lowPoly (M : Matrix n n A) (p : A[X]) :
    ∃ c : n → A, p %ₘ M.charpoly = lowPoly c := by
  nontriviality A
  have h : (p %ₘ M.charpoly).degree < Fintype.card n := by
    rw [← Matrix.charpoly_degree_eq_dim M]
    exact degree_modByMonic_lt p M.charpoly_monic
  refine ⟨fun j => (p %ₘ M.charpoly).coeff (Fintype.equivFin n j), ?_⟩
  conv_lhs => rw [← Polynomial.sum_C_mul_X_pow_eq (p %ₘ M.charpoly),
    Polynomial.sum_fin _ (by simp) h |>.symm]
  rw [lowPoly, ← Equiv.sum_comp (Fintype.equivFin n)]
  simp [Polynomial.smul_eq_C_mul]

theorem charpoly_dvd {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) {p : A[X]}
    (hp : aeval M p *ᵥ v = 0) : M.charpoly ∣ p := by
  obtain ⟨c, hc⟩ := exists_lowPoly M p
  rw [Matrix.aeval_eq_aeval_mod_charpoly, hc, aeval_lowPoly_mulVec] at hp
  have h0 : c = 0 := by
    have := congrArg (fun w => (krylov M v)⁻¹ *ᵥ w) hp
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h] using this
  rw [← modByMonic_eq_zero_iff_dvd M.charpoly_monic, hc, h0]
  simp [lowPoly]

theorem exists_aeval {M : Matrix n n A} (l : genAlg M) :
    ∃ p : A[X], aeval M p = (l : Matrix n n A) := by
  exact (Algebra.adjoin_singleton_eq_range_aeval A M).le l.2

theorem coe_aeval_gen (M : Matrix n n A) (p : A[X]) :
    ((aeval (gen M) p : genAlg M) : Matrix n n A) = aeval M p :=
  (Polynomial.aeval_algHom_apply (genAlg M).val (gen M) p).symm

def actOn (M : Matrix n n A) (v : n → A) : genAlg M →ₗ[A] (n → A) where
  toFun l := (l : Matrix n n A) *ᵥ v
  map_add' a b := Matrix.add_mulVec _ _ _
  map_smul' c a := Matrix.smul_mulVec c (a : Matrix n n A) v

theorem actOn_bijective {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) :
    Function.Bijective (actOn M v) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun l hl => ?_, fun w => ?_⟩
  · obtain ⟨p, hp⟩ := exists_aeval l
    have hl' : aeval M p *ᵥ v = 0 := by rw [hp]; exact hl
    obtain ⟨q, rfl⟩ := charpoly_dvd h hl'
    refine Subtype.ext ?_
    rw [← hp, map_mul, Matrix.aeval_self_charpoly, zero_mul]; rfl
  · refine ⟨aeval (gen M) (lowPoly ((krylov M v)⁻¹ *ᵥ w)), ?_⟩
    change ((aeval (gen M) _ : genAlg M) : Matrix n n A) *ᵥ v = w
    rw [coe_aeval_gen, aeval_lowPoly_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h,
      Matrix.one_mulVec]

theorem aeval_gen_charpoly (M : Matrix n n A) : aeval (gen M) M.charpoly = 0 :=
  Subtype.ext (by rw [coe_aeval_gen, Matrix.aeval_self_charpoly]; rfl)

def toGen (M : Matrix n n A) : AdjoinRoot M.charpoly →ₐ[A] genAlg M :=
  AdjoinRoot.liftAlgHom M.charpoly (Algebra.ofId A _) (gen M) (aeval_gen_charpoly M)

theorem toGen_mk (M : Matrix n n A) (p : A[X]) :
    toGen M (AdjoinRoot.mk _ p) = aeval (gen M) p :=
  AdjoinRoot.liftAlgHom_mk _ _ _ _ p

theorem toGen_bijective {M : Matrix n n A} {v : n → A} (h : IsUnit (krylov M v).det) :
    Function.Bijective (toGen M) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun l => ?_⟩
  · obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [toGen_mk] at hx
    rw [AdjoinRoot.mk_eq_zero]
    refine charpoly_dvd h ?_
    rw [← coe_aeval_gen, hx]
    exact Matrix.zero_mulVec v
  · obtain ⟨p, hp⟩ := exists_aeval l
    exact ⟨AdjoinRoot.mk _ p, Subtype.ext (by rw [toGen_mk, coe_aeval_gen, hp])⟩

theorem cyclicAlgebra : GlobalTheory.RegSS.CyclicAlgebra := by
  intro A _ n _ _ M v h
  refine ⟨⟨AlgEquiv.ofBijective (toGen M) (toGen_bijective h), ?_⟩,
    ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective (actOn M v) (actOn_bijective h))⟩,
    actOn_bijective h⟩
  change toGen M (AdjoinRoot.mk _ X) = _
  rw [toGen_mk, aeval_X]

end GlobalTheory.RegSS.CycAlg
