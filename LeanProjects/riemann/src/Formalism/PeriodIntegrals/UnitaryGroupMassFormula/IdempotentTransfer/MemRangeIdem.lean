import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.HarderNarasimhan.FinalCor
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.TraceFormulaOfRankDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.ESMulESOfNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.CharacteristicPolynomialCompatibility
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.NormAtAddLe
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.DegGeOfInj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.FgOfLeL
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.DegTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.RankIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IdempotentTransfer.PerSAlg

noncomputable section

namespace PI.Dv.Tr

open PI.Dv Module NumberField

section VLevel

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

lemma mem_range_idem {V : Type} [AddCommGroup V] [Module K V] (f : Module.End K V) (hf : f * f = f) (x : V) :
    x ∈ LinearMap.range f ↔ f x = x := by
  constructor
  · rintro ⟨y, rfl⟩; rw [← Module.End.mul_apply, hf]
  · intro h; exact ⟨x, h⟩

variable (T : GoodSet K G) (s : T.S) (P0 P : Pair K G) (cB : MonoidAlgebra K G → K)
  (g h : Fin (nS T P s) → G)
  (hlift : ∀ a, eps P0 * a * eps P0 * eS T s = cB a • (eps P0 * eS T s))
  {V : Type} [AddCommGroup V] [Module K V] (ρ : Representation K G V)

include hlift in
lemma key_scalar (a : MonoidAlgebra K G) (y : V) (hy : y ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s))) :
    ρ.asAlgebraHom (eps P0 * a) y = cB a • y := by
  obtain ⟨z, rfl⟩ := hy
  rw [← Module.End.mul_apply, ← map_mul]
  have : eps P0 * a * (eps P0 * eS T s) = eps P0 * a * eps P0 * eS T s := by simp only [mul_assoc]
  rw [this, hlift, map_smul, LinearMap.smul_apply]

include hlift in
lemma inj_phi (hN : IsUnit (Matrix.of fun j i => cB (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i))))
    (y : Fin (nS T P s) → V) (hy : ∀ i, y i ∈ LinearMap.range (ρ.asAlgebraHom (eps P0 * eS T s)))
    (h0 : ∑ i, ρ.asAlgebraHom (eps P * MonoidAlgebra.of K G (g i)) (y i) = 0) : y = 0 := by
  apply unit_vec _ hN y
  intro j
  have := congrArg (ρ.asAlgebraHom (eps P0 * MonoidAlgebra.of K G (h j))) h0
  rw [map_sum, map_zero] at this
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Module.End.mul_apply, ← map_mul,
    show eps P0 * MonoidAlgebra.of K G (h j) * (eps P * MonoidAlgebra.of K G (g i)) =
      eps P0 * (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i)) by simp only [mul_assoc],
    key_scalar T s P0 cB hlift ρ _ _ (hy i)]
  rfl

include hlift in
lemma inj_psi (hM : M1 T P0) [FiniteDimensional K V]
    (hN : IsUnit (Matrix.of fun j i => cB (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i))))
    (x : V) (hx : x ∈ LinearMap.range (ρ.asAlgebraHom (eps P * eS T s)))
    (h0 : ∀ j, ρ.asAlgebraHom (eps P0 * MonoidAlgebra.of K G (h j)) x = 0) : x = 0 := by
  classical
  set E0 := ρ.asAlgebraHom (eps P0 * eS T s) with hE0
  set Ep := ρ.asAlgebraHom (eps P * eS T s) with hEp
  have hidem : ∀ Q : Pair K G, ρ.asAlgebraHom (eps Q * eS T s) * ρ.asAlgebraHom (eps Q * eS T s) =
      ρ.asAlgebraHom (eps Q * eS T s) := fun Q => by
    rw [← map_mul, mul_idem (eps_idem Q) (eS_idem T s) (eS_comm T s (eps Q)).symm]
  have he : ∀ y ∈ LinearMap.range E0, ρ.asAlgebraHom (eS T s) y = y := by
    rintro _ ⟨z, rfl⟩
    rw [hE0, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, ← eS_comm, mul_assoc, eS_idem]
  have hmemΦ : ∀ (y : Fin (nS T P s) → LinearMap.range E0),
      ∑ i, ρ.asAlgebraHom (eps P * MonoidAlgebra.of K G (g i)) ((y i : LinearMap.range E0) : V) ∈
        LinearMap.range Ep := by
    intro y
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [mem_range_idem Ep (hidem P)]
    conv_rhs => rw [← he _ (y i).2]
    rw [hEp, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    calc eps P * eS T s * (eps P * MonoidAlgebra.of K G (g i))
        = eps P * ((eps P * MonoidAlgebra.of K G (g i)) * eS T s) := by rw [mul_assoc, eS_comm]
      _ = (eps P * eps P) * MonoidAlgebra.of K G (g i) * eS T s := by simp only [mul_assoc]
      _ = eps P * MonoidAlgebra.of K G (g i) * eS T s := by rw [eps_idem]
  let Φ : (Fin (nS T P s) → LinearMap.range E0) →ₗ[K] LinearMap.range Ep :=
    { toFun := fun y => ⟨_, hmemΦ y⟩
      map_add' := by
        intro y z; apply Subtype.ext
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c y; apply Subtype.ext
        simp [Finset.smul_sum] }
  have hΦinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := congrArg Subtype.val hy
    have := inj_phi T s P0 P cB g h hlift ρ hN (fun i => ((y i : LinearMap.range E0) : V))
      (fun i => (y i).2) h1
    funext i
    apply Subtype.ext
    exact congrFun this i
  have hdim : finrank K (Fin (nS T P s) → LinearMap.range E0) = finrank K (LinearMap.range Ep) := by
    rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hEp,
      finrank_range_eps_mul_eS_eq_nS_mul T P0 P hM ρ s]
  have hΦsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hΦinj
  obtain ⟨y, hy⟩ := hΦsurj ⟨x, hx⟩
  have hxy : x = ∑ i, ρ.asAlgebraHom (eps P * MonoidAlgebra.of K G (g i)) ((y i : LinearMap.range E0) : V) :=
    (congrArg Subtype.val hy).symm
  have hsum0 : ∑ i, ρ.asAlgebraHom (eps P * MonoidAlgebra.of K G (g i)) ((y i : LinearMap.range E0) : V) = 0 := by

    have hz : (fun i => ((y i : LinearMap.range E0) : V)) = 0 := by
      apply unit_vec _ hN
      intro j
      have := h0 j
      rw [hxy, map_sum] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Module.End.mul_apply, ← map_mul,
        show eps P0 * MonoidAlgebra.of K G (h j) * (eps P * MonoidAlgebra.of K G (g i)) =
          eps P0 * (MonoidAlgebra.of K G (h j) * eps P * MonoidAlgebra.of K G (g i)) by simp only [mul_assoc],
        key_scalar T s P0 cB hlift ρ _ _ (y i).2]
      rfl
    have hzi : ∀ i, ((y i : LinearMap.range E0) : V) = 0 := fun i => congrFun hz i
    simp only [hzi, map_zero, Finset.sum_const_zero]
  rw [hxy, hsum0]

end VLevel

end PI.Dv.Tr
