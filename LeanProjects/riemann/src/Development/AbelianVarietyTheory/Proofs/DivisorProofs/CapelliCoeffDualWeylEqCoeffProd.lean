import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalPol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BranchingAdmissibleFacts
open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD GlobalTheory.CapelliLink

noncomputable section

namespace GlobalTheory.CapelliCoeffs

open Polynomial

def entry (O : Type) [CommRing O] (N : ℕ) (α : Equiv.Perm (Fin N)) (k : Fin N) :
    Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  C (FreeAlgebra.ι O (α k, k)) + if α k = k then X - C (((k : ℕ) : FreeAlgebra O (Fin N × Fin N))) else 0

def capPoly (O : Type) [CommRing O] (N : ℕ) : Polynomial (FreeAlgebra O (Fin N × Fin N)) :=
  ∑ α : Equiv.Perm (Fin N), (((Equiv.Perm.sign α : ℤˣ) : ℤ) : Polynomial (FreeAlgebra O (Fin N × Fin N))) *
    (List.ofFn (entry O N α)).prod

theorem ofFn_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] (ψ : M →+ M') : ∀ {m : ℕ} (g : Fin m → Module.End R M)
    (g' : Fin m → Module.End S M'), (∀ k x, ψ (g k x) = g' k (ψ x)) →
    ∀ x, ψ ((List.ofFn g).prod x) = (List.ofFn g').prod (ψ x)
  | 0, g, g', _, x => by simp
  | m + 1, g, g', h, x => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply,
      Module.End.mul_apply, h 0, ofFn_intertwine ψ (fun k => g k.succ) (fun k => g' k.succ) (fun k => h k.succ)]

theorem capDet_intertwine {R S M M' : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module S M'] {n : ℕ} (ψ : M →+ M') (E : Fin n → Fin n → Module.End R M)
    (E' : Fin n → Fin n → Module.End S M') (h : ∀ i j x, ψ (E i j x) = E' i j (ψ x)) (u : ℤ) (x : M) :
    ψ (Formalism.BranchingDeterminantCap.capDet E u x) = Formalism.BranchingDeterminantCap.capDet E' u (ψ x) := by
  unfold Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  refine ofFn_intertwine ψ _ _ (fun k y => ?_) x
  simp only [Formalism.BranchingDeterminantCap.bmF, LinearMap.sub_apply, map_sub, h]
  split_ifs
  · simp [Module.End.intCast_apply, map_zsmul]
  · simp

theorem capDet_dualWeyl_domain (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ)
    (hν : Antitone ν) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν) (u : ℤ) :
    Formalism.BranchingDeterminantCap.capDet (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1) u f =
      ((∏ j : Fin N, (u + ((j : ℕ) : ℤ) - (ν j : ℤ)) : ℤ) : O) • f := by
  let K := FractionRing O
  let φ : O →+* K := algebraMap O K
  have hφ : Function.Injective φ := IsFractionRing.injective O K
  have hg := Formalism.GradedWeylDivisibility.dualWeylMap O K φ N N ν f hf
  have h1 := GlobalTheory.BrCompare.capDet_dualWeyl (K := K) hν u hg
  have e : (fun i j => GlobalTheory.Mem.Gelf.rowE K N N i j) = fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1 := by
    funext a b
    exact LinearMap.ext fun P => (GlobalTheory.Mem.GelfCheck.rowE_eq_rowDiv K N N a b P).1
  rw [e] at h1
  have h2 := capDet_intertwine (MvPolynomial.map φ).toAddMonoidHom (fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1)
    (fun a b => Formalism.GradedWeylDivisibility.rowDivL K a b 1) (fun i j x => (Formalism.GradedWeylDivisibility.lclosedeq_rowDiv_map φ i j 1 x).symm) u f
  apply MvPolynomial.map_injective φ hφ
  have h3 := h2.trans h1
  simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe] at h3
  rw [h3, Int.cast_smul_eq_zsmul K, Int.cast_smul_eq_zsmul O, map_zsmul]

theorem eval_capPoly (O : Type) [CommRing O] (N : ℕ) {M : Type} [AddCommGroup M] [Module O M]
    (Φ : FreeAlgebra O (Fin N × Fin N) →ₐ[O] Module.End O M) (v : ℤ) (L : ℕ)
    (hL : (capPoly O N).natDegree < L) :
    ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) =
      ((-1 : ℤ) ^ N) • Formalism.BranchingDeterminantCap.capDet (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) := by
  have hc : ∀ a : Module.End O M, Commute ((RingHom.id _) a) (v : Module.End O M) :=
    fun a => (Int.cast_commute v a).symm
  let ev := Polynomial.eval₂RingHom' (RingHom.id (Module.End O M)) (v : Module.End O M) hc
  let Ψ := Polynomial.mapRingHom (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
  have key : ev (Ψ (capPoly O N)) = ∑ i ∈ Finset.range L, (v ^ i) • Φ ((capPoly O N).coeff i) := by
    show eval₂ (RingHom.id _) (v : Module.End O M) (map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M)
      (capPoly O N)) = _
    rw [eval₂_eq_sum_range' _ (lt_of_le_of_lt natDegree_map_le hL)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [coeff_map, RingHom.id_apply, ← Int.cast_pow, zsmul_eq_mul']
    rfl
  rw [← key]
  unfold capPoly Formalism.BranchingDeterminantCap.capDet Formalism.BranchingDeterminantCap.bmPi Formalism.BranchingDeterminantCap.bmM
  simp only [map_sum, map_mul, map_intCast, map_list_prod, List.map_ofFn, Finset.smul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have hev : ∀ p, ev p = p.eval₂ (RingHom.id _) (v : Module.End O M) := fun _ => rfl
  have hΨ : ∀ p, Ψ p = p.map (Φ : FreeAlgebra O (Fin N × Fin N) →+* Module.End O M) := fun _ => rfl
  have e : (List.ofFn fun k => ev (Ψ (entry O N α k))) =
      (List.ofFn fun k => Formalism.BranchingDeterminantCap.bmF (fun a b => Φ (FreeAlgebra.ι O (a, b))) (-v) k (α k) (id k)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext k
    rw [hev, hΨ]
    simp only [Function.comp_apply, entry, Formalism.BranchingDeterminantCap.bmF, id]
    split_ifs
    · simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval₂_add,
        Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.id_apply, map_natCast, RingHom.coe_coe, Polynomial.map_natCast,
        Polynomial.eval₂_natCast]
      push_cast
      abel
    · simp
  rw [show (⇑ev ∘ ⇑Ψ ∘ entry O N α) = fun k => ev (Ψ (entry O N α k)) from rfl, e, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul]
  push_cast
  exact (Int.cast_commute _ _).left_comm _

theorem coeff_eq_of_int (P : Type) [CommRing P] [IsDomain P] [CharZero P] (L : ℕ) (a b : ℕ → P)
    (h : ∀ v : ℤ, ∑ i ∈ Finset.range L, (v : P) ^ i * a i = ∑ i ∈ Finset.range L, (v : P) ^ i * b i) :
    ∀ i < L, a i = b i := by
  intro i hi
  let Q : Polynomial P := ∑ j ∈ Finset.range L, monomial j (a j - b j)
  have hQ : Q = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Int.cast_injective (α := P)))
    rintro _ ⟨v, rfl⟩
    have hv := h v
    simp only [Set.mem_setOf_eq, IsRoot, Q, eval_finset_sum, eval_monomial]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at hv
    rw [← hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have := congrArg (fun q : Polynomial P => q.coeff i) hQ
  simp only [Q, finset_sum_coeff, coeff_monomial, coeff_zero] at this
  rw [Finset.sum_eq_single i (fun j _ hj => if_neg hj) (fun h' => absurd (Finset.mem_range.2 hi) h'), if_pos rfl] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CapelliCoeffs

namespace GlobalTheory.CapelliCoeffs

open Polynomial

theorem capelli_coeff_dualWeyl : ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ),
    ∃ F : ℕ → FreeAlgebra O (Fin N × Fin N), ∀ ν : Fin N → ℕ, Antitone ν →
      ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N ν, ∀ k : ℕ,
        evalPol O N (F k) f = (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((ν a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • f := by
  intro O _ _ _ N
  refine ⟨fun k => (capPoly O N).coeff k, fun ν hν f hf k => ?_⟩
  set p : Polynomial ℤ := ∏ a : Fin N, (X + C (((ν a : ℤ) - (a : ℕ) : ℤ))) with hpdef
  set L := (capPoly O N).natDegree + N + 1 with hLdef
  have hp : p.natDegree ≤ N := by
    refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum fun a _ => (natDegree_X_add_C (((ν a : ℤ) - (a : ℕ) : ℤ))).le).trans ?_
    simp
  have hE : (fun a b => evalPol O N (FreeAlgebra.ι O (a, b))) = fun a b => Formalism.GradedWeylDivisibility.rowDivL O a b 1 := by
    funext a b
    simp [evalPol]
  by_cases hk : k < L
  · refine coeff_eq_of_int (MvPolynomial (Fin N × Fin N) O) L
      (fun i => evalPol O N ((capPoly O N).coeff i) f) (fun i => ((p.coeff i : ℤ) : O) • f) (fun v => ?_) k hk
    have hA := eval_capPoly O N (evalPol O N) v L (by omega)
    rw [hE] at hA
    have hB := capDet_dualWeyl_domain O N ν hν f hf (-v)
    have e1 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * evalPol O N ((capPoly O N).coeff i) f =
        (∑ i ∈ Finset.range L, (v ^ i) • evalPol O N ((capPoly O N).coeff i)) f := by
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, ← Int.cast_pow, ← zsmul_eq_mul]
    have e2 : ∑ i ∈ Finset.range L, ((v : MvPolynomial (Fin N × Fin N) O)) ^ i * (((p.coeff i : ℤ) : O) • f) =
        (p.eval v) • f := by
      rw [eval_eq_sum_range' (n := L) (by omega), Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Int.cast_pow, ← zsmul_eq_mul, Int.cast_smul_eq_zsmul, smul_smul, mul_comm]
    have e3 : p.eval v = (-1 : ℤ) ^ N * ∏ j : Fin N, (-v + ((j : ℕ) : ℤ) - (ν j : ℤ)) := by
      rw [hpdef, eval_prod]
      have : ((-1 : ℤ) ^ N) = ∏ _j : Fin N, (-1 : ℤ) := by simp
      rw [this, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [eval_add, eval_X, eval_C]
      ring
    rw [e1, e2, hA, LinearMap.smul_apply, hB, e3, Int.cast_smul_eq_zsmul, smul_smul]
  · have h1 : (capPoly O N).coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    have h2 : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    show evalPol O N ((capPoly O N).coeff k) f = _
    rw [h1, h2, map_zero]
    simp

end GlobalTheory.CapelliCoeffs
