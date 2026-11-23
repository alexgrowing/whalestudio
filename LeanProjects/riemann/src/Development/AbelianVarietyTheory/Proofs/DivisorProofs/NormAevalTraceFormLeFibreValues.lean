import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRootMapMinpolyIffExistsRingHomExtension

open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp

variable {K : Type} [Field K] {D : ℕ}

theorem ratR_zero_eq_closure (x : Fin (D + 1) → K) (h0 : x 0 ≠ 0) :
    ratR x 0 = Subring.closure (Set.range fun j : Fin D => x j.succ / x 0) := by
  refine le_antisymm (Subring.closure_le.2 ?_) (Subring.closure_mono ?_)
  · rintro _ ⟨j, rfl⟩
    refine Fin.cases ?_ (fun i => ?_) j
    · simp only [div_self h0]; exact Subring.one_mem _
    · exact Subring.subset_closure ⟨i, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.succ, rfl⟩

theorem ratR_zero_le_ratF (x : Fin (D + 1) → K) (h0 : x 0 ≠ 0) : ratR x 0 ≤ (ratF x).toSubring := by
  rw [ratR_zero_eq_closure x h0]
  exact Subring.closure_le.2 fun _ h => Subfield.subset_closure h

theorem exists_ringEquiv_ratR (x : Fin (D + 1) → K) (h0 : x 0 ≠ 0)
    (hind : AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0)) :
    ∃ e : MvPolynomial (Fin D) ℤ ≃+* ratR x 0, ∀ j, (e (X j) : K) = x j.succ / x 0 := by
  have hS : (Algebra.adjoin ℤ (Set.range fun j : Fin D => x j.succ / x 0)).toSubring = ratR x 0 := by
    rw [Algebra.adjoin_int, ratR_zero_eq_closure x h0]; rfl
  refine ⟨hind.aevalEquiv.toRingEquiv.trans (RingEquiv.subringCongr hS), fun j => ?_⟩
  have := hind.algebraMap_aevalEquiv (X j)
  rw [aeval_X] at this
  exact this

end GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

set_option maxHeartbeats 1000000 in

theorem norm_aeval_trace_le : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (B : Subring K) (hB : ∀ l, x l / x 0 ∈ B), (∀ b ∈ B, IsIntegral (ratR x 0) b) →
    ∀ (w : B) (T : MvPolynomial (Fin (D + 1)) ℤ),
    (Algebra.trace (ratF x) K (w : K) : K) = aeval (fun l => x l / x 0) T →
    ∀ (z : Fin (D + 1) → ℂ) (M : ℝ), z 0 = 1 →
    (∀ φ : B →+* ℂ, (∀ l, φ ⟨x l / x 0, hB l⟩ = z l) → ‖φ w‖ ≤ M) →
    ‖aeval z T‖ ≤ Module.finrank (ratF x) K * M := by
  intro K _ _ D x hx hind hfin B hB hint w T htr z M hz0 hM
  have h0 := hx 0
  have hAF := ratR_zero_le_ratF x h0
  have memA : ∀ l, x l / x 0 ∈ ratR x 0 := fun l => Subring.subset_closure ⟨l, rfl⟩
  have hAB : ratR x 0 ≤ B := Subring.closure_le.2 (by rintro _ ⟨l, rfl⟩; exact hB l)
  letI : Algebra (ratR x 0) (ratF x) := (Subring.inclusion hAF).toAlgebra
  letI : Algebra (ratR x 0) B := (Subring.inclusion hAB).toAlgebra
  haveI : IsScalarTower (ratR x 0) (ratF x) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower (ratR x 0) B K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨e, he⟩ := exists_ringEquiv_ratR x h0 hind
  haveI : UniqueFactorizationMonoid (ratR x 0) := e.toMulEquiv.uniqueFactorizationMonoid inferInstance
  have hinjF : Function.Injective (algebraMap (ratR x 0) (ratF x)) := Subring.inclusion_injective hAF
  have hinjB : Function.Injective (algebraMap (ratR x 0) B) := Subring.inclusion_injective hAB
  haveI : FaithfulSMul (ratR x 0) (ratF x) := (faithfulSMul_iff_algebraMap_injective _ _).2 hinjF
  haveI : IsFractionRing (ratR x 0) (ratF x) := by
    refine IsFractionRing.of_field _ _ fun y => ?_
    obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.1 y.2
    rw [← ratR_zero_eq_closure x h0] at ha hb
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, Subtype.ext (by rw [Subfield.coe_div]; exact hab.symm)⟩
  have hwint : IsIntegral (ratR x 0) (w : K) := hint w w.2
  have hmin : minpoly (ratF x) (w : K) = (minpoly (ratR x 0) (w : K)).map (algebraMap (ratR x 0) (ratF x)) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' (ratF x) hwint
  have hminB : minpoly (ratR x 0) w = minpoly (ratR x 0) (w : K) :=
    (minpoly.algHom_eq (IsScalarTower.toAlgHom (ratR x 0) B K) Subtype.val_injective w).symm
  haveI : Algebra.IsIntegral (ratR x 0) B :=
    ⟨fun b => (isIntegral_algHom_iff (IsScalarTower.toAlgHom (ratR x 0) B K) Subtype.val_injective).1 (hint b b.2)⟩
  set p := minpoly (ratR x 0) (w : K) with hp
  have hpm : p.Monic := minpoly.monic hwint

  obtain ⟨m, htr', hmdeg⟩ : ∃ m : ℕ, Algebra.trace (ratF x) K (w : K) = m * -(minpoly (ratF x) (w : K)).nextCoeff ∧
      m * (minpoly (ratF x) (w : K)).natDegree = Module.finrank (ratF x) K :=
    ⟨_, trace_eq_finrank_mul_minpoly_nextCoeff (ratF x) (w : K), by
      rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite (ratF x) (w : K)), mul_comm,
        Module.finrank_mul_finrank]⟩
  rw [hmin, hpm.natDegree_map] at hmdeg
  set c : ratR x 0 := m * -p.nextCoeff with hc
  have hcF : Algebra.trace (ratF x) K (w : K) = algebraMap (ratR x 0) (ratF x) c := by
    rw [htr', hmin, Polynomial.nextCoeff_map hinjF, hc, map_mul, map_neg, map_natCast]
  rw [hcF] at htr

  let a : Fin (D + 1) → ratR x 0 := fun l => ⟨x l / x 0, memA l⟩
  have hcT : c = aeval a T := by
    apply Subtype.val_injective
    refine htr.trans ?_
    have := AlgHom.congr_fun (MvPolynomial.comp_aeval a (ratR x 0).subtype.toIntAlgHom) T
    simp only [AlgHom.comp_apply] at this
    exact this.symm

  let ψ : ratR x 0 →+* ℂ := (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) fun j : Fin D => z j.succ).comp e.symm.toRingHom
  have hψ : ∀ l, ψ (a l) = z l := by
    intro l
    refine Fin.cases ?_ (fun j => ?_) l
    · have : a 0 = 1 := Subtype.ext (div_self h0)
      rw [this, map_one, hz0]
    · have : a j.succ = e (X j) := Subtype.ext (he j).symm
      rw [this]
      show MvPolynomial.eval₂Hom (Int.castRingHom ℂ) (fun j : Fin D => z j.succ) (e.symm (e (X j))) = _
      rw [RingEquiv.symm_apply_apply, eval₂Hom_X']
  have hψc : ψ c = aeval z T := by
    rw [hcT]
    have := AlgHom.congr_fun (MvPolynomial.comp_aeval a ψ.toIntAlgHom) T
    simp only [AlgHom.comp_apply] at this
    refine this.trans ?_
    rw [show (fun i => ψ.toIntAlgHom (a i)) = z from funext fun l => hψ l]

  set q := p.map ψ with hq
  have hqm : q.Monic := hpm.map ψ
  have hsum : q.nextCoeff = -q.roots.sum :=
    (IsAlgClosed.splits q).nextCoeff_eq_neg_sum_roots_of_monic hqm
  have hqn : q.nextCoeff = ψ p.nextCoeff :=
    Polynomial.nextCoeff_map_of_leadingCoeff_ne_zero ψ (by rw [hpm.leadingCoeff, map_one]; exact one_ne_zero)
  have hcard : q.roots.card = p.natDegree := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hpm.natDegree_map]
  have hroots : ∀ r ∈ q.roots, ‖r‖ ≤ M := by
    intro r hr
    have hr' : ((minpoly (ratR x 0) w).map ψ).IsRoot r := by
      rw [hminB]; exact (Polynomial.mem_roots hqm.ne_zero).1 hr
    obtain ⟨φ, hφ, hφw⟩ := (GlobalTheory.isRoot_map_minpoly_iff_exists_ringHom (ratR x 0) B hinjB w ψ r).1 hr'
    rw [← hφw]
    refine hM φ fun l => ?_
    rw [← hψ l, ← hφ]
    rfl
  have hval : aeval z T = (m : ℂ) * q.roots.sum := by
    rw [← hψc, hc, map_mul, map_neg, map_natCast, ← hqn, hsum, neg_neg]
  rw [hval, norm_mul, Complex.norm_natCast, ← hmdeg, Nat.cast_mul, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  refine (norm_multiset_sum_le _).trans ?_
  refine (Multiset.sum_le_card_nsmul _ M fun y hy => ?_).trans ?_
  · obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hy
    exact hroots r hr
  · rw [Multiset.card_map, hcard, nsmul_eq_mul]

end GlobalTheory.HSAmp
