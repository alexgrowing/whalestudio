import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalPairSplitSumStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycNumIntAndComb
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberLinearStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.DivisorCycleSubstitutionStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleNumberRenameStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

noncomputable section

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem divCycle_support_finite (P : Ideal (MRing ι O)) (f : MRing ι O) :
    (Function.support (divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  by_contra h
  apply hW
  simp [divCycle, h]

theorem C_not_mem {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {a : O} (ha : a ≠ 0) :
    (C a : MRing ι O) ∉ P := by
  intro h
  have h' : a ∈ P.comap (C : O →+* MRing ι O) := h
  rw [hP.noTorsion] at h'
  exact ha (by simpa using h')

theorem laNum_eq (P : Ideal (MRing ι O)) (a : O) {r : ℕ} (x : Fin r → K → ℤ) (k : ℕ)
    (Q : List (K → ℤ)) :
    ((laNum P a x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum (divCycle P (C a)) x (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1)) Q := by
  have h := (cycNum_int_and_comb O K ι (Fin r) x Q).1 (divCycle P (C a))
    (divCycle_support_finite P (C a)) (psum (Fin r) ℤ (k - 1))
  have e : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin r) ℤ (k - 1)) =
      ∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ (k - 1) := by
    simp [psum, map_sum]
  rw [e] at h
  rw [h, laNum]
  push_cast
  rfl

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ]

theorem liePs_inl (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inl τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j => (τ, Fin.castAdd j' i))
        (∑ i : Fin j, (X i : MvPolynomial (Fin j) ℝ) ^ m) := by
  simp only [liePs, map_sum, map_pow, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  simp

theorem liePs_inr (j j' m : ℕ) (τ : Ψ) :
    (liePs (N := j + j') j m (Sum.inr τ) : MvPolynomial (Ψ × Fin (j + j')) ℝ) =
      rename (fun i : Fin j' => (τ, Fin.natAdd j i))
        (∑ i : Fin j', (-(X i : MvPolynomial (Fin j') ℝ)) ^ m) := by
  simp only [liePs, map_sum, map_pow, map_neg, rename_X, Finset.sum_filter, Fin.sum_univ_add]
  have h0 : ∀ x : Fin j, ¬ j ≤ (x : ℕ) := fun x => not_le.2 x.2
  simp [h0]

theorem cycNum_neg {ϖ : O} (hϖ : Irreducible ϖ) {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d)
    {a : O} (ha : a ≠ 0) {r : ℕ} (cls : Fin r → K → ℤ) (m : ℕ) (Q : List (K → ℤ))
    (hQ : m + Q.length = d) :
    cycNum (divCycle P (C a)) (fun i => -cls i) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) Q =
      cycNum (divCycle P (C a)) cls (∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m) Q := by
  have hC : IsMultiHomog (C a : MRing ι O) (0 : K → ℕ) := isWeightedHomogeneous_C _ a
  have hH : (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m).IsHomogeneous m :=
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_X ℝ i).pow m
  have h := (GlobalTheory.T.divisor_cycle_substitution O ϖ hϖ K ι P d hP 0 0 (C a) (C a) hC hC (C_not_mem hP ha) (C_not_mem hP ha)
    (Fin r) (Fin r) cls (fun t i => if t = i then -1 else 0) _ m hH Q hQ).2
  have e1 : (fun t : Fin r => ∑ i, (if t = i then (-1 : ℤ) else 0) • cls i) = fun i => -cls i := by
    funext t
    simp
  have e2 : aeval (fun t : Fin r => ∑ i, (C (((if t = i then (-1 : ℤ) else 0 : ℤ)) : ℝ) * X i :
      MvPolynomial (Fin r) ℝ)) (∑ i : Fin r, (X i : MvPolynomial (Fin r) ℝ) ^ m) =
      ∑ i : Fin r, (-(X i : MvPolynomial (Fin r) ℝ)) ^ m := by
    simp [map_sum, apply_ite]
  rw [e1, e2] at h
  exact h

end

end GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3

namespace GlobalTheory.CompanionTheory.Ar.Num

open GlobalTheory.CompanionTheory.Ar.Num.FlagLocalM3 in

theorem flag_m3_of_local_m3 : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (p : ℕ), (p : O) ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (j j' : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair ι O (Ψ × Fin (j + j'))) (lie : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j) (fun _ : Ψ => j')) σ))) (om : ∀ σ, LocPair ι O (Fin ((Sum.elim (fun _ : Ψ => j') (fun _ : Ψ => j)) σ))), (∀ τ, lie (Sum.inl τ) = T.comp fun i : Fin j => (τ, Fin.castAdd j' i)) → (∀ τ, om (Sum.inl τ) = T.comp fun i : Fin j' => (τ, Fin.natAdd j i)) → (∀ τ k Q, Q.length + k = d + 1 → laNum P (p : O) (lie (Sum.inr τ)).x k Q = laNum P (p : O) (fun i : Fin j' => -T.x (τ, Fin.natAdd j i)) k Q) → LabelChernComparison P d p φ lie om → FlagChernComparison P d p j φ T := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP p hp Ψ _ _ j j' φ T lie om hl ho hr hM τ k hk Q hQ
  set Z := divCycle P (C (p : O)) with hZ
  have hm : k - 1 + Q.length = d := by omega

  have hlab : ∀ τ' : Ψ ⊕ Ψ, ((laNum P (p : O) (lie τ').x k Q : ℤ) : ℝ) =
      (k : ℝ) * cycNum Z T.x (liePs j (k - 1) τ') Q := by
    rintro (t | t)
    · have e : (lie (Sum.inl t)).x = fun i : Fin j => T.x (t, Fin.castAdd j' i) := by
        rw [hl t]; rfl
      have e' : ((laNum P (p : O) (lie (Sum.inl t)).x k Q : ℤ) : ℝ) =
          ((laNum P (p : O) (fun i : Fin j => T.x (t, Fin.castAdd j' i)) k Q : ℤ) : ℝ) :=
        congrArg (fun y : Fin j → K → ℤ => ((laNum P (p : O) y k Q : ℤ) : ℝ)) e
      rw [e', laNum_eq, liePs_inl, (GlobalTheory.T.cycle_number_rename).1 O K ι _ _ _ Z T.x]
      rfl
    · rw [hr t k Q hQ, laNum_eq, cycNum_neg hϖ hP hp _ _ Q hm, liePs_inr,
        (GlobalTheory.T.cycle_number_rename).1 O K ι _ _ _ Z T.x]
      rfl
  have hL := hM k hk Q hQ (Sum.inl τ)
  have e1 : (lie (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j) => L.ck P k Q) (hl τ)
  have e2 : (om (Sum.inl τ)).ck P k Q = (T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q :=
    congrArg (fun L : LocPair ι O (Fin j') => L.ck P k Q) (ho τ)
  have hadd := GlobalTheory.T.local_pair_split_sum O K ι j j' (T.comp fun i : Fin (j + j') => (τ, i)) P k Q
  have hlin := GlobalTheory.T.cycle_number_linear O K ι (Ψ × Fin (j + j')) Z T.x Q
  rw [e1, e2] at hL
  have hleft : (((T.comp fun i : Fin (j + j') => (τ, i)).ck P k Q : ℤ) : ℝ) =
      (((T.comp fun i : Fin j => (τ, Fin.castAdd j' i)).ck P k Q : ℤ) : ℝ) +
      (((T.comp fun i : Fin j' => (τ, Fin.natAdd j i)).ck P k Q : ℤ) : ℝ) := by
    rw [hadd]
    push_cast
    rfl
  rw [hleft, hL, bracket]
  rw [hlin.2.1, hlin.2.2.1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ' _ => ?_
  rw [hlin.2.1, hlab τ']
  ring

end GlobalTheory.CompanionTheory.Ar.Num
