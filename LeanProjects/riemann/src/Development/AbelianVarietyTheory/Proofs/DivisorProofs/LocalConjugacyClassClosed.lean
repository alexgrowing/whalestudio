import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMemIntV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinpolyEqOfAevalOfLinearIndependent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaDistributionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorRatAlgebraDecompFactorwise

open Polynomial
open scoped TensorProduct

namespace GlobalTheory.ClosedClass

section Alg

variable (S F B : Type) [Field S] [Algebra ℚ S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
  [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B]

noncomputable abbrev cen : S ⊗[ℚ] F →ₐ[S] S ⊗[ℚ] B :=
  Algebra.TensorProduct.map (AlgHom.id S S) (IsScalarTower.toAlgHom ℚ F B)

theorem eq_zero_of_isNilpotent (n : ℕ) (x₀ : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (c : Fin n → S ⊗[ℚ] F)
    (h : IsNilpotent (∑ j, cen S F B (c j) * ((1 : S) ⊗ₜ[ℚ] x₀) ^ (j : ℕ))) : c = 0 := by
  classical
  haveI hcz : CharZero S := charZero_of_injective_algebraMap (algebraMap ℚ S).injective
  obtain rfl : ‹Algebra ℚ S› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨ι, _, L, _, _, _, Φ, ψ, hΦ1, hΦ2⟩ := GlobalTheory.tensor_decomp_factorwise S F B
  have key : ∀ i (j : Fin n), ψ (c j) i = 0 := by
    intro i
    let K := L i
    let e : K ⊗[F] B := (1 : K) ⊗ₜ[F] x₀
    let hp : K[X] := ∑ j : Fin n, C (ψ (c j) i) * X ^ (j : ℕ)
    have hΦw : Φ (∑ j, cen S F B (c j) * ((1 : S) ⊗ₜ[ℚ] x₀) ^ (j : ℕ)) i = aeval e hp := by
      simp only [hp, map_sum, map_mul, map_pow, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hΦ2, hΦ1,
        aeval_C, aeval_X, e]
      rfl
    obtain ⟨m, hm⟩ := h
    have hnil : aeval e (hp ^ (m + 1)) = 0 := by
      rw [map_pow, ← hΦw, pow_succ]
      have := congrArg (fun w => w i) (congrArg Φ hm)
      simp only [map_pow, map_zero, Pi.pow_apply, Pi.zero_apply] at this
      rw [this, zero_mul]
    have hmin : minpoly K e = (minpoly F x₀).map (algebraMap F K) := GlobalTheory.SkNoFactor.minpoly_one_tmul K x₀
    have hd1 : minpoly K e ∣ hp ^ (m + 1) := minpoly.dvd K e hnil
    rw [hmin] at hd1
    have hd2 : (minpoly F x₀).map (algebraMap F K) ∣ hp :=
      (hsep.map.squarefree.dvd_pow_iff_dvd (Nat.succ_ne_zero m)).1 hd1
    have hdeglt : hp.degree < ((minpoly F x₀).map (algebraMap F K)).degree := by
      have h1 : hp.degree < n := Polynomial.degree_sum_fin_lt _
      rw [Polynomial.degree_map, Polynomial.degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite F x₀)), hdeg]
      exact h1
    have hz : hp = 0 := Polynomial.eq_zero_of_dvd_of_degree_lt hd2 hdeglt
    intro j
    have := congrArg (fun q : K[X] => q.coeff (j : ℕ)) hz
    simp only [hp, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
    rw [Finset.sum_eq_single j] at this
    · simpa using this
    · intro b _ hb
      rw [if_neg]
      exact fun h' => hb (Fin.ext h'.symm)
    · simp
  funext j
  apply ψ.injective
  funext i
  simp [key i j]

end Alg

end GlobalTheory.ClosedClass

namespace GlobalTheory.ClosedClass

section Conj

variable (S F B : Type) [Field S] [Algebra ℚ S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
  [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B]

noncomputable abbrev trL : S ⊗[ℚ] B →ₗ[S] S :=
  (LinearMap.trace S (S ⊗[ℚ] B)).comp (Algebra.lmul S (S ⊗[ℚ] B)).toLinearMap

theorem trL_conj (g : (S ⊗[ℚ] B)ˣ) (u : S ⊗[ℚ] B) :
    trL S B ((g : S ⊗[ℚ] B) * u * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B)) = trL S B u := by
  simp only [trL, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, map_mul]
  rw [LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

theorem cen_comm (z : S ⊗[ℚ] F) (y : S ⊗[ℚ] B) : Commute (cen S F B z) y := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul s f =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul s' b =>
      simp only [cen, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom']
      show (s ⊗ₜ[ℚ] algebraMap F B f) * (s' ⊗ₜ[ℚ] b) = (s' ⊗ₜ[ℚ] b) * (s ⊗ₜ[ℚ] algebraMap F B f)
      rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_comm s s',
        Algebra.commutes]
    | add a b ha hb => exact Commute.add_right ha hb
  | add a b ha hb => rw [map_add]; exact Commute.add_left ha hb

theorem exists_conj_of_traces [Algebra.IsCentral F B] [IsSimpleRing B] (n : ℕ) (hn : Module.finrank F B = n ^ 2)
    (x₀ : B) (hsep : (minpoly F x₀).Separable) (hdeg : (minpoly F x₀).natDegree = n) (y : S ⊗[ℚ] B)
    (hP : ∑ i ∈ Finset.range (n + 1), ((1 : S) ⊗ₜ[ℚ] algebraMap F B ((minpoly F x₀).coeff i)) * y ^ i = 0)
    (hT : ∀ (z : S ⊗[ℚ] F) (k : ℕ), trL S B (cen S F B z * y ^ k) =
      trL S B (cen S F B z * ((1 : S) ⊗ₜ[ℚ] x₀) ^ k)) :
    ∃ g : (S ⊗[ℚ] B)ˣ, (g : S ⊗[ℚ] B) * ((1 : S) ⊗ₜ[ℚ] x₀) = y * g := by
  classical
  haveI hcz : CharZero S := charZero_of_injective_algebraMap (algebraMap ℚ S).injective
  obtain rfl : ‹Algebra ℚ S› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  haveI : Module.Finite ℚ B := Module.Finite.trans F B
  refine GlobalTheory.SkNoFactor.exists_unit_conj_baseChange S F B n hn x₀ y hsep hdeg hP ?_
  intro c hc
  set e₀ : S ⊗[ℚ] B := (1 : S) ⊗ₜ[ℚ] x₀ with he₀
  let ev : S ⊗[ℚ] B → (S ⊗[ℚ] F)[X] →+* S ⊗[ℚ] B := fun u =>
    Polynomial.eval₂RingHom' (cen S F B).toRingHom u (fun a => cen_comm S F B a u)
  have hev : ∀ u (H : (S ⊗[ℚ] F)[X]), ev u H = ∑ k ∈ Finset.range (H.natDegree + 1), cen S F B (H.coeff k) * u ^ k := by
    intro u H
    show Polynomial.eval₂ _ u H = _
    rw [Polynomial.eval₂_eq_sum_range]
    rfl
  have htr : ∀ H : (S ⊗[ℚ] F)[X], trL S B (ev y H) = trL S B (ev e₀ H) := by
    intro H
    rw [hev, hev, map_sum, map_sum]
    exact Finset.sum_congr rfl fun k _ => hT _ k
  let R : (S ⊗[ℚ] F)[X] := ∑ j : Fin n, C (c j) * X ^ (j : ℕ)
  have hevR : ∀ u, ev u R = ∑ j : Fin n, cen S F B (c j) * u ^ (j : ℕ) := by
    intro u
    simp only [R, map_sum, map_mul, map_pow]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Polynomial.eval₂ _ u (C (c j)) * Polynomial.eval₂ _ u X ^ (j : ℕ) = _
    rw [Polynomial.eval₂_C, Polynomial.eval₂_X]
    rfl
  have hyR : ev y R = 0 := by rw [hevR]; exact hc
  set w := ev e₀ R with hw
  have hpow : ∀ k, 1 ≤ k → LinearMap.trace S (S ⊗[ℚ] B) ((Algebra.lmul S (S ⊗[ℚ] B) w) ^ k) = 0 := by
    intro k hk
    rw [← map_pow, hw, ← map_pow]
    have := htr (R ^ k)
    rw [map_pow, hyR, zero_pow (by omega), map_zero] at this
    exact this.symm
  obtain ⟨m, hm⟩ := GlobalTheory.UnipNormalTrace.isNilpotent_of_trace_pow_eq_zero _ hpow
  have hwn : IsNilpotent w := by
    refine ⟨m, ?_⟩
    have := congrArg (fun f : Module.End S (S ⊗[ℚ] B) => f 1) hm
    rw [← map_pow] at this
    simpa using this
  rw [hw, hevR] at hwn
  exact eq_zero_of_isNilpotent S F B n x₀ hsep hdeg c hwn

end Conj

end GlobalTheory.ClosedClass

namespace GlobalTheory.ClosedClass

section Top

variable (S F B : Type) [Field S] [Algebra ℚ S] [Field F] [Algebra ℚ F] [FiniteDimensional ℚ F] [Ring B]
  [Algebra F B] [Algebra ℚ B] [IsScalarTower ℚ F B] [FiniteDimensional F B]

theorem conj_val_pow (g e : (S ⊗[ℚ] B)ˣ) (i : ℕ) :
    (((g * e * g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B)) ^ i =
      (g : S ⊗[ℚ] B) * (e : S ⊗[ℚ] B) ^ i * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) := by
  rw [← Units.val_pow_eq_pow_val, conj_pow]
  simp [Units.val_pow_eq_pow_val]

theorem cen_mul_conj (z : S ⊗[ℚ] F) (g : (S ⊗[ℚ] B)ˣ) (u : S ⊗[ℚ] B) :
    cen S F B z * ((g : S ⊗[ℚ] B) * u * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B)) =
      (g : S ⊗[ℚ] B) * (cen S F B z * u) * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) := by
  rw [← mul_assoc, ← mul_assoc, (cen_comm S F B z g).eq, mul_assoc (g : S ⊗[ℚ] B)]

theorem one_tmul_eq_cen (f : F) : (1 : S) ⊗ₜ[ℚ] algebraMap F B f = cen S F B ((1 : S) ⊗ₜ[ℚ] f) := by
  simp [cen]

theorem isClosed_conjClass [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [Algebra.IsCentral F B]
    [IsSimpleRing B] (n : ℕ) (hn : Module.finrank F B = n ^ 2) (x₀ : B) (hsep : (minpoly F x₀).Separable)
    (hdeg : (minpoly F x₀).natDegree = n) (e : (S ⊗[ℚ] B)ˣ) (he : (e : S ⊗[ℚ] B) = (1 : S) ⊗ₜ[ℚ] x₀) :
    letI : TopologicalSpace (S ⊗[ℚ] B) := moduleTopology S (S ⊗[ℚ] B)
    IsClosed {y : (S ⊗[ℚ] B)ˣ | ∃ g : (S ⊗[ℚ] B)ˣ, y = g * e * g⁻¹} := by
  classical
  letI : TopologicalSpace (S ⊗[ℚ] B) := moduleTopology S (S ⊗[ℚ] B)
  haveI : IsModuleTopology S (S ⊗[ℚ] B) := ⟨rfl⟩
  haveI : Module.Finite ℚ B := Module.Finite.trans F B
  haveI : IsTopologicalRing (S ⊗[ℚ] B) := IsModuleTopology.isTopologicalRing S (S ⊗[ℚ] B)
  let Pv : S ⊗[ℚ] B → S ⊗[ℚ] B := fun y =>
    ∑ i ∈ Finset.range (n + 1), ((1 : S) ⊗ₜ[ℚ] algebraMap F B ((minpoly F x₀).coeff i)) * y ^ i
  have hPe : Pv (e : S ⊗[ℚ] B) = 0 := by
    have h0 : Polynomial.aeval x₀ (minpoly F x₀) = 0 := minpoly.aeval F x₀
    rw [Polynomial.aeval_eq_sum_range, hdeg] at h0
    have h1 := congrArg (fun b : B => (1 : S) ⊗ₜ[ℚ] b) h0
    simp only [TensorProduct.tmul_zero, TensorProduct.tmul_sum] at h1
    rw [← h1]
    simp only [Pv, he]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  let b := Module.finBasis S (S ⊗[ℚ] B)
  have hset : {y : (S ⊗[ℚ] B)ˣ | ∃ g : (S ⊗[ℚ] B)ˣ, y = g * e * g⁻¹} =
      (⋂ i, {y : (S ⊗[ℚ] B)ˣ | b.coord i (Pv (y : S ⊗[ℚ] B)) = 0}) ∩
      ⋂ (z : S ⊗[ℚ] F) (k : ℕ), {y : (S ⊗[ℚ] B)ˣ | trL S B (cen S F B z * (y : S ⊗[ℚ] B) ^ k) =
        trL S B (cen S F B z * (e : S ⊗[ℚ] B) ^ k)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨g, rfl⟩
      have hPy : Pv ((g * e * g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) = 0 := by
        have : Pv ((g * e * g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) =
            (g : S ⊗[ℚ] B) * Pv (e : S ⊗[ℚ] B) * ((g⁻¹ : (S ⊗[ℚ] B)ˣ) : S ⊗[ℚ] B) := by
          simp only [Pv, conj_val_pow, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [one_tmul_eq_cen, cen_mul_conj]
        rw [this, hPe, mul_zero, zero_mul]
      refine ⟨fun i => by rw [hPy, map_zero], fun z k => ?_⟩
      rw [conj_val_pow, cen_mul_conj, trL_conj]
    · rintro ⟨hP, hT⟩
      have hP' : Pv (y : S ⊗[ℚ] B) = 0 := by
        apply b.forall_coord_eq_zero_iff.1
        exact hP
      rw [he] at hT
      obtain ⟨g, hg⟩ := exists_conj_of_traces S F B n hn x₀ hsep hdeg (y : S ⊗[ℚ] B) hP' hT
      refine ⟨g, Units.ext ?_⟩
      rw [Units.val_mul, Units.val_mul, he, hg, mul_assoc, Units.mul_inv, mul_one]
  rw [hset]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun z => isClosed_iInter fun k => ?_)
  · have hc : Continuous fun y : (S ⊗[ℚ] B)ˣ => b.coord i (Pv (y : S ⊗[ℚ] B)) := by
      refine (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp ?_
      exact continuous_finset_sum _ fun j _ => continuous_const.mul (Units.continuous_val.pow j)
    exact isClosed_eq hc continuous_const
  · have hc : Continuous fun y : (S ⊗[ℚ] B)ˣ => trL S B (cen S F B z * (y : S ⊗[ℚ] B) ^ k) :=
      (IsModuleTopology.continuous_of_linearMap (trL S B)).comp
        (continuous_const.mul (Units.continuous_val.pow k))
    exact isClosed_eq hc continuous_const

end Top

end GlobalTheory.ClosedClass

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

namespace GlobalTheory.OrbFinAf

end GlobalTheory.OrbFinAf
