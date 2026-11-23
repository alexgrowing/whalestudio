import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor

open MvPolynomial
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section Ten

variable {K : Type} [Field K] [StarRing K] {ι : Type} {n : ℕ}

omit [StarRing K] in
theorem fk_blockEmb_X (τ : ι) (v : Fin n × Fin n) :
    Formalism.GradedWeylDivisibility.blockEmb K τ (X v) = (X (τ, v) : MvPolynomial (ι × Fin n × Fin n) K) := by
  simp [Formalism.GradedWeylDivisibility.blockEmb]

omit [StarRing K] in
theorem fk_blockEmb_C (τ : ι) (a : K) :
    Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ (C a) = (C a : MvPolynomial (ι × Fin n × Fin n) K) := by
  simp [Formalism.GradedWeylDivisibility.blockEmb]

omit [StarRing K] in
theorem fk_pderiv_blockEmb (τ : ι) (v : Fin n × Fin n) (g : MvPolynomial (Fin n × Fin n) K) :
    pderiv (τ, v) (Formalism.GradedWeylDivisibility.blockEmb K τ g) = Formalism.GradedWeylDivisibility.blockEmb K τ (pderiv v g) := by
  unfold Formalism.GradedWeylDivisibility.blockEmb
  exact pderiv_rename (fun a b hab => by simpa using hab) v g

omit [StarRing K] in
theorem fk_pderiv_blockEmb_ne {τ τ' : ι} (h : τ ≠ τ') (v : Fin n × Fin n) (g : MvPolynomial (Fin n × Fin n) K) :
    pderiv (τ, v) (Formalism.GradedWeylDivisibility.blockEmb K τ' g) = 0 := by
  classical
  unfold Formalism.GradedWeylDivisibility.blockEmb
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p w hp => simp [Derivation.leibniz, hp, pderiv_X, Pi.single_apply, Prod.ext_iff, Ne.symm h]

theorem fk_fock_right (τ : ι) (P Q : MvPolynomial (ι × Fin n × Fin n) K) (hP : ∀ v, pderiv (τ, v) P = 0)
    (g : MvPolynomial (Fin n × Fin n) K) :
    fockL P (Formalism.GradedWeylDivisibility.blockEmb K τ g * Q) = constantCoeff g * fockL P Q := by
  classical
  induction g using MvPolynomial.induction_on with
  | C a => rw [fk_blockEmb_C, ← smul_eq_C_mul, map_smul, smul_eq_mul, constantCoeff_C]
  | add p q hp hq => rw [map_add, add_mul, map_add, hp, hq, map_add, add_mul]
  | mul_X p v _ =>
    rw [map_mul (Formalism.GradedWeylDivisibility.blockEmb K τ), fk_blockEmb_X, mul_comm _ (X (τ, v)), mul_assoc, ← fockL_pderiv_X, hP, map_zero,
      LinearMap.zero_apply, map_mul constantCoeff, constantCoeff_X, mul_zero, zero_mul]

theorem fk_fock_mul (τ : ι) (P P' : MvPolynomial (ι × Fin n × Fin n) K) (hP : ∀ v, pderiv (τ, v) P = 0)
    (hP' : ∀ v, pderiv (τ, v) P' = 0) (f g : MvPolynomial (Fin n × Fin n) K) :
    fockL (Formalism.GradedWeylDivisibility.blockEmb K τ f * P) (Formalism.GradedWeylDivisibility.blockEmb K τ g * P') = fockL f g * fockL P P' := by
  classical
  induction f using MvPolynomial.induction_on generalizing g with
  | C a =>
    rw [fk_blockEmb_C, ← smul_eq_C_mul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, fk_fock_right τ P P' hP,
      fockL_C_left, smul_eq_mul, starRingEnd_apply, mul_assoc]
  | add p q hp hq =>
    rw [map_add, add_mul, map_add, LinearMap.add_apply, hp, hq, map_add, LinearMap.add_apply, add_mul]
  | mul_X p v hp =>
    rw [map_mul (Formalism.GradedWeylDivisibility.blockEmb K τ), fk_blockEmb_X, mul_comm _ (X (τ, v)), mul_assoc, fockL_X_pderiv, Derivation.leibniz, hP',
      smul_zero, zero_add, fk_pderiv_blockEmb, smul_eq_mul, mul_comm P', hp, mul_comm p, fockL_X_pderiv]

theorem fk_fock_prod (s : Finset ι) (f g : ι → MvPolynomial (Fin n × Fin n) K) :
    fockL (∏ τ ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) (∏ τ ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ (g τ)) =
      ∏ τ ∈ s, fockL (f τ) (g τ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [← C_1, fockL_C_left]
    simp
  | insert τ s hτ ih =>
    have hz : ∀ (h : ι → MvPolynomial (Fin n × Fin n) K) (v : Fin n × Fin n),
        pderiv (τ, v) (∏ τ' ∈ s, Formalism.GradedWeylDivisibility.blockEmb K τ' (h τ')) = 0 := by
      intro h v
      refine Finset.prod_induction _ (fun P => pderiv (τ, v) P = 0) ?_ ?_ ?_
      · intro a b ha hb
        rw [Derivation.leibniz, ha, hb, smul_zero, smul_zero, add_zero]
      · exact (pderiv (τ, v)).map_one_eq_zero
      · intro τ' hτ'
        exact fk_pderiv_blockEmb_ne (fun e : τ = τ' => hτ (by rw [e]; exact hτ')) v _
    rw [Finset.prod_insert hτ, Finset.prod_insert hτ, Finset.prod_insert hτ, fk_fock_mul τ _ _ (hz f) (hz g), ih]

end Ten

theorem fockSymTensor_holds : FockSTen := by
  intro K _ _ ι _ n f g
  exact fk_fock_prod Finset.univ f g

theorem pairingExtremal_holds : PairExtremal := pairExtremal_of fockSymTensor_holds extNormPos

section Rat

variable {K : Type} [Field K] (K0 : Subfield K)

theorem fk_coeff_mem {σ : Type} {P : MvPolynomial σ K} (hP : P ∈ (map (σ := σ) K0.subtype).range) (m : σ →₀ ℕ) :
    coeff m P ∈ K0 := by
  obtain ⟨Q, rfl⟩ := hP
  rw [MvPolynomial.coeff_map]
  exact (coeff m Q).2

theorem fk_int_mem {σ : Type} (P : MvPolynomial σ ℤ) :
    map (Int.castRingHom K) P ∈ (map (σ := σ) K0.subtype).range := by
  refine ⟨map (Int.castRingHom K0) P, ?_⟩
  rw [MvPolynomial.map_map, RingHom.ext_int (K0.subtype.comp (Int.castRingHom K0)) (Int.castRingHom K)]

theorem fk_C_mem {σ : Type} {a : K} (ha : a ∈ K0) : (C a : MvPolynomial σ K) ∈ (map (σ := σ) K0.subtype).range :=
  ⟨C ⟨a, ha⟩, by simp⟩

theorem fk_X_mem {σ : Type} (v : σ) : (X v : MvPolynomial σ K) ∈ (map (σ := σ) K0.subtype).range :=
  ⟨X v, map_X _ _⟩

theorem fk_blockAct_mem {ι : Type} [Fintype ι] {n : ℕ} (U : ι → Matrix (Fin n) (Fin n) K) (hU : ∀ τ a b, U τ a b ∈ K0)
    {P : MvPolynomial (ι × Fin n × Fin n) K} (hP : P ∈ (map (σ := ι × Fin n × Fin n) K0.subtype).range) :
    Formalism.GradedWeylDivisibility.blockAct K U P ∈ (map (σ := ι × Fin n × Fin n) K0.subtype).range := by
  obtain ⟨Q, rfl⟩ := hP
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [map_C, algHom_C]
    exact fk_C_mem K0 a.2
  | add p q hp hq =>
    rw [map_add (map K0.subtype), map_add]
    exact add_mem hp hq
  | mul_X p v hp =>
    rw [map_mul (map K0.subtype), map_X, map_mul, blockAct_X]
    exact mul_mem hp (sum_mem fun b _ => mul_mem (fk_C_mem K0 (hU _ _ _)) (fk_X_mem K0 _))

theorem fk_det_mem {n : ℕ} (G : Matrix (Fin n) (Fin n) K) (hG : ∀ a b, G a b ∈ K0) : G.det ∈ K0 := by
  let G0 : Matrix (Fin n) (Fin n) K0 := fun a b => ⟨G a b, hG a b⟩
  have hG0 : G = G0.map K0.subtype := by
    ext a b
    rfl
  rw [hG0, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (G0.det).2

theorem fk_fock_mem [StarRing K] {σ : Type} (P : MvPolynomial σ ℤ) {Q : MvPolynomial σ K}
    (hQ : Q ∈ (map (σ := σ) K0.subtype).range) : fockS (map (Int.castRingHom K) P) Q ∈ K0 := by
  unfold fockS
  refine sum_mem fun m _ => mul_mem (mul_mem ?_ (fk_coeff_mem K0 hQ m)) (natCast_mem K0 _)
  rw [coeff_map, eq_intCast, star_intCast]
  exact intCast_mem K0 _

theorem fk_extNorm_mem [StarRing K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) : extNorm K lam ∈ K0 := by
  unfold extNorm
  refine prod_mem fun τ _ => ?_
  rw [← map_extremal (Int.castRingHom K)]
  exact fk_fock_mem K0 _ (fk_int_mem K0 _)

theorem fk_gramTw_mem {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K)
    (hG : ∀ τ a b, G τ a b ∈ K0) : gramTw lam G ∈ K0 := by
  unfold gramTw
  exact prod_mem fun τ _ => zpow_mem (fk_det_mem K0 _ (hG τ)) _

theorem fk_descent {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ K) (hv : LinearIndependent K v)
    (hv0 : ∀ i, v i ∈ (map (σ := σ) K0.subtype).range) (c : κ → K)
    (hx : ∑ i, c i • v i ∈ (map (σ := σ) K0.subtype).range) (i : κ) : c i ∈ K0 := by
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K0 K)
    (LinearMap.ker_eq_bot.mpr (algebraMap K0 K).injective)
  have hπ' : ∀ a : K0, π (a : K) = a := fun a => congrArg (fun φ : K0 →ₗ[K0] K0 => φ a) hπ
  have hmul : ∀ (a : K0) (z : K), π (z * (a : K)) = π z * a := by
    intro a z
    have : z * (a : K) = a • z := by rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  have key : ∑ i, (c i - (π (c i) : K)) • v i = 0 := by
    ext m
    rw [coeff_sum, coeff_zero]
    simp only [coeff_smul, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have h1 : coeff m (∑ i, c i • v i) = ∑ i, c i * coeff m (v i) := by
      rw [coeff_sum]
      simp only [coeff_smul, smul_eq_mul]
    have h2 : ((π (coeff m (∑ i, c i • v i)) : K0) : K) = coeff m (∑ i, c i • v i) :=
      congrArg (fun a : K0 => (a : K)) (hπ' ⟨_, fk_coeff_mem K0 hx m⟩)
    rw [← h1, ← h2, h1, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hmul ⟨_, fk_coeff_mem K0 (hv0 i) m⟩ (c i)
    simp only at this
    rw [this]
    rfl
  have := (Fintype.linearIndependent_iff.mp hv) _ key i
  rw [sub_eq_zero] at this
  rw [this]
  exact (π (c i)).2

end Rat

theorem pairingRational_holds : PairRat := by
  intro K _ _ ι _ n lam K0 G hG i j
  obtain ⟨Pi, hPi⟩ := bVVfun_int K lam i
  obtain ⟨Pj, hPj⟩ := bVVfun_int K lam j
  rw [pairK_apply, pairP_apply, bVV_coe, bVV_coe, fockL_apply, hPi, hPj]
  refine mul_mem (div_mem (fk_gramTw_mem K0 lam G hG) (fk_extNorm_mem K0 lam)) (fk_fock_mem K0 _ ?_)
  exact fk_blockAct_mem K0 _ (fun τ a b => hG τ b a) (fk_int_mem K0 _)

theorem actionRational_holds : ActRat := by
  intro K _ ι _ n lam K0 g hg i j
  obtain ⟨Pj, hPj⟩ := bVVfun_int K lam j
  refine fk_descent K0 (bVVfun K lam) (bVVfun_spec K lam).1 (fun k => ?_)
    (fun k => (bVV K lam).repr (rhoK lam g (bVV K lam j)) k) ?_ i
  · obtain ⟨Pk, hPk⟩ := bVVfun_int K lam k
    rw [hPk]
    exact fk_int_mem K0 _
  · have h1 : ∑ k, (bVV K lam).repr (rhoK lam g (bVV K lam j)) k • bVVfun K lam k =
        actP lam g (bVVfun K lam j) := by
      have h := congrArg (fun x : VV K lam => (x : Pol K ι n)) ((bVV K lam).sum_repr (rhoK lam g (bVV K lam j)))
      simp only [rhoK_coe, bVV_coe, Submodule.coe_sum, Submodule.coe_smul] at h
      exact h
    rw [h1, hPj, actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply, smul_eq_C_mul]
    refine mul_mem (fk_C_mem K0 ?_) (fk_blockAct_mem K0 _ (fun τ a b => hg τ b a) (fk_int_mem K0 _))
    rw [detTw_eq]
    exact prod_mem fun τ _ => zpow_mem (fk_det_mem K0 _ (hg τ)) _

end Formalism.L2.DIV
