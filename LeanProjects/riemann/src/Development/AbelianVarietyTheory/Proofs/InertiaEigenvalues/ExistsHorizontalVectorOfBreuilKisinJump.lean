import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EzpowMulEzpowNeg

noncomputable section

open PowerSeries Matrix GlobalTheory.BK GlobalTheory.BKGal.JumpDR

namespace GlobalTheory.BKGal.JumpDR.Horiz

theorem const_mem_of_stable {R κ : Type} [CommRing R] (hR : ∀ n : ℕ, IsUnit ((n + 1 : ℕ) : R))
    (Λ : Submodule R⟦X⟧ (κ → R⟦X⟧)) (α : ℕ) (hα : ∀ h : κ → R⟦X⟧, (X : R⟦X⟧) ^ α • h ∈ Λ)
    (hθ : ∀ v ∈ Λ, (fun k => X * PowerSeries.derivative R (v k)) ∈ Λ) {v : κ → R⟦X⟧} (hv : v ∈ Λ) :
    (fun k => C (constantCoeff (v k))) ∈ Λ := by
  set c : κ → R⟦X⟧ := fun k => C (constantCoeff (v k))
  have key (m : ℕ) : ∃ h : κ → R⟦X⟧, c + (X : R⟦X⟧) ^ (m + 1) • h ∈ Λ := by
    induction m with
    | zero =>
      refine ⟨fun k => PowerSeries.mk fun n => coeff (n + 1) (v k), ?_⟩
      convert hv using 1
      funext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add, pow_one, c]
      rw [add_comm]
      exact (PowerSeries.eq_X_mul_shift_add_const (v k)).symm
    | succ m ih =>
      obtain ⟨h, hh⟩ := ih
      obtain ⟨u, hu⟩ := (hR m).exists_left_inv
      refine ⟨fun k => -(C u * PowerSeries.derivative R (h k)), ?_⟩
      convert Λ.sub_mem hh (Λ.smul_mem (C u) (hθ _ hh)) using 1
      funext k
      have hu' : (C u : R⟦X⟧) * ((m : R⟦X⟧) + 1) = 1 := by
        have := congrArg (C (R := R)) hu
        simpa using this
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, c, map_add, derivative_C,
        Derivation.leibniz, Derivation.leibniz_pow, derivative_X, nsmul_eq_mul, Nat.add_sub_cancel]
      push_cast
      linear_combination (X ^ (m + 1) * h k) * hu'
  obtain ⟨h, hh⟩ := key α
  have := Λ.sub_mem hh (hα ((X : R⟦X⟧) • h))
  rwa [smul_smul, ← pow_succ, add_sub_cancel_right] at this

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  {l e a : ℕ} [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [CompleteSpace K]
  {ι : Type} [Fintype ι] [DecidableEq ι]

variable (O K l e) in
theorem exists_Ehat_eq : ∃ w : (AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K)))⟦X⟧,
    AhatEq.equivAhat O K l e X = Ehat O K l e * AhatEq.equivAhat O K l e w := by
  have h1 : AhatEq.equivAhat O K l e (AhatEq.taylor _ (Polynomial.X ^ e + Polynomial.C (l : K))) =
      Ehat O K l e :=
    (AhatEq.toAhat_taylor O K l e _).trans (congrArg _ (AhatEq.incl_E O K l e))
  have hX := AhatEq.associated_taylor (AhatEq.separable_E K l e)
  obtain ⟨w, hw⟩ := hX.dvd
  exact ⟨w, by rw [← h1, ← map_mul, ← hw]⟩

variable (O K l e) in
theorem isUnit_uhat : IsUnit (uhat O K l e) := by
  have h1 : AhatEq.equivAhat O K l e (C (AdjoinRoot.root _) + X) = uhat O K l e := by
    have := AhatEq.toAhat_taylor O K l e Polynomial.X
    rw [AhatEq.taylor, AhatEq.incl, Polynomial.aeval_X, Polynomial.aeval_X] at this
    exact this
  rw [← h1]
  refine IsUnit.map _ ?_
  rw [isUnit_iff_constantCoeff, map_add, constantCoeff_C, constantCoeff_X, add_zero]
  have h2 : (AdjoinRoot.root (Polynomial.X ^ e + Polynomial.C (l : K))) ^ e =
      algebraMap K _ (-(l : K)) := by
    have := AdjoinRoot.mk_self (f := Polynomial.X ^ e + Polynomial.C (l : K))
    rw [map_add, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at this
    rw [map_neg, eq_neg_iff_add_eq_zero]
    exact this
  refine (isUnit_pow_iff (NeZero.ne e)).1 ?_
  rw [h2]
  exact IsUnit.map _ (IsUnit.mk0 _ (neg_ne_zero.2 (l_ne_zero l)))

theorem equivAhat_derivative (x : (AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K)))⟦X⟧) :
    AhatEq.equivAhat O K l e (PowerSeries.derivative _ x) = dHat O K l e (AhatEq.equivAhat O K l e x) :=
  AhatEq.toAhat_derivative O K l e x

theorem NHatE_algebraMap (x : Ahat O K l e) :
    NHatE O K l e (algebraMap _ _ x) = algebraMap _ _ (uhat O K l e * dHat O K l e x) := by
  rw [NHatE, Derivation.smul_apply, dHatE_algebraMap, smul_eq_mul, map_mul]

theorem exists_denom {σ : Type} [Finite σ] (f : σ → AhatE O K l e) :
    ∃ α : ℕ, ∀ s, ∃ x : Ahat O K l e,
      algebraMap _ _ x = algebraMap (Ahat O K l e) (AhatE O K l e) (Ehat O K l e ^ α) * f s := by
  obtain ⟨⟨_, α, rfl⟩, h⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers (Ehat O K l e)) f
  exact ⟨α, fun s => by
    obtain ⟨x, hx⟩ := h s
    exact ⟨x, hx.trans (Algebra.smul_def _ _)⟩⟩

theorem mul_derivation_pow {F B : Type} [CommRing F] [CommRing B] [Algebra F B] (D : Derivation F B B)
    (s : B) (n : ℕ) : s * D (s ^ n) = n * s ^ n * D s := by
  rw [Derivation.leibniz_pow]
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel, nsmul_eq_mul, smul_eq_mul]
    ring

theorem stable_EN {κ : Type} [Fintype κ] (Ξ : κ → ι → AhatE O K l e) (Γ : ι → ι → AhatE O K l e)
    (hΓ : ∀ j i, ∃ γ : Ahat O K l e, algebraMap _ _ γ = algebraMap _ _ (Ehat O K l e) * Γ j i)
    (hΞ : ∀ k i, NHatE O K l e (Ξ k i) + ∑ j, Ξ k j * Γ j i = 0) (N p : ℕ) (g : κ → Ahat O K l e)
    (hg : ∀ i, ∃ x : Ahat O K l e, algebraMap _ (AhatE O K l e) (Ehat O K l e ^ p * x) =
      algebraMap _ _ (Ehat O K l e ^ N) * ∑ k, algebraMap _ _ (g k) * Ξ k i) (i : ι) :
    ∃ x : Ahat O K l e, algebraMap _ (AhatE O K l e) (Ehat O K l e ^ p * x) =
      algebraMap _ _ (Ehat O K l e ^ N) *
        ∑ k, algebraMap _ _ (Ehat O K l e * (uhat O K l e * dHat O K l e (g k))) * Ξ k i := by
  choose γ hγ using hΓ
  choose x hx using hg
  set φ := algebraMap (Ahat O K l e) (AhatE O K l e)
  set w : ι → AhatE O K l e := fun i => ∑ k, φ (g k) * Ξ k i with hw
  set s := φ (Ehat O K l e) with hs
  set ν := uhat O K l e * dHat O K l e (Ehat O K l e)
  have hν : NHatE O K l e s = φ ν := NHatE_algebraMap _
  have h1 : ∑ k, φ (Ehat O K l e * (uhat O K l e * dHat O K l e (g k))) * Ξ k i =
      s * (NHatE O K l e (w i) + ∑ j, w j * Γ j i) := by
    have h2 : ∑ j, w j * Γ j i = ∑ k, φ (g k) * ∑ j, Ξ k j * Γ j i := by
      simp only [hw, Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    rw [h2, hw, map_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, NHatE_algebraMap, map_mul]
    linear_combination (-(s * φ (g k))) * hΞ k i
  have hx' (j) : s ^ p * φ (x j) = s ^ N * w j := by
    have := hx j
    rwa [map_mul, map_pow, map_pow] at this
  have h3 := congrArg (fun t => s * NHatE O K l e t) (hx' i)
  simp only [Derivation.leibniz, smul_eq_mul] at h3
  rw [NHatE_algebraMap] at h3
  have h4 := mul_derivation_pow (NHatE O K l e) s p
  have h5 := mul_derivation_pow (NHatE O K l e) s N
  rw [hν] at h4 h5
  have h6 : s ^ N * (s * ∑ j, w j * Γ j i) = s ^ p * φ (∑ j, x j * γ j i) := by
    rw [map_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, hγ]
    linear_combination (-(s * Γ j i)) * hx' j
  refine ⟨Ehat O K l e * (uhat O K l e * dHat O K l e (x i)) + ((p : Ahat O K l e) - N) * ν * x i +
    ∑ j, x j * γ j i, ?_⟩
  rw [h1, map_mul, map_pow, map_pow, map_add, map_add, map_mul, map_mul, map_mul φ _ (x i), map_mul φ _ ν, map_sub, map_natCast,
    map_natCast, ← hs]
  rw [map_mul] at h3
  linear_combination h3 - h6 - φ (x i) * h4 + w i * h5 - N * φ ν * hx' i

theorem grading [NeZero a] (P : PhiMod O K l e a ι) (hP : ∀ m ∈ P.M, P.EN m ∈ P.Man) (i : ℤ)
    (g : Fin (Fintype.card ι) → ZMod a → Ahat O K l e)
    (hg : InEhat O K l e i (hsum P g (xiVec P))) :
    InEhat O K l e i (hsum P (fun k => kLift O (fun τ => cterm O K l e (g k τ))) (xiVec P)) := by
  obtain ⟨N, hN, hg⟩ := hg
  refine ⟨N, hN, fun τ => ?_⟩
  set p := (i + N).toNat
  set ψ := AhatEq.equivAhat O K l e
  set φ := algebraMap (Ahat O K l e) (AhatE O K l e)
  set Ξ : Fin (Fintype.card ι) → ι → AhatE O K l e := fun k => P.hatTot (xiVec P k) τ
  have hb (j : ι) : E K l e • P.conn (bas j) ∈ P.Mext (Rpi O K l e) := hP _ (P.bas_mem_M j)
  have hb' (j : ι) : P.conn (bas j) ∈ P.Mext (RpiE O K l e) :=
    P.mem_Mext_invE_of_mem_divE (n := 1) (by rw [pow_one]; exact hb j)
  have hΓ (j i : ι) : ∃ γ : Ahat O K l e, φ γ = φ (Ehat O K l e) * P.hatTot (P.conn (bas j)) τ i := by
    refine ⟨toHat O K l e ⟨_, mem_tot.1 (hb j) τ i⟩, ?_⟩
    rw [← hat_coe_Rpi]
    have := hat_E_pow_mul (O := O) l e 1 (mem_tot.1 (hb' j) τ i)
    rw [pow_one, pow_one] at this
    exact this
  have hΞ (k) (i : ι) : NHatE O K l e (Ξ k i) + ∑ j, Ξ k j * P.hatTot (P.conn (bas j)) τ i = 0 := by
    have hv : xiVec P k ∈ P.Mext (RpiE O K l e) := mem_tot.2 fun τ i => by
      rw [xiVec_apply]; exact xiMat_mem_RpiE P τ i _
    have h1 := congrFun (congrFun (P.hatTot_conn hb' hv) τ) i
    rw [xiVec, P.conn_xi] at h1
    exact h1.symm.trans ((hat_coe l e 0).trans (map_zero _))
  obtain ⟨α, hα⟩ := exists_denom (fun q : Fin (Fintype.card ι) × ι => Ξ q.1 q.2)
  choose ξ hξ using hα
  obtain ⟨w, hw⟩ := exists_Ehat_eq O K l e
  obtain ⟨u', hu'⟩ := (isUnit_uhat O K l e).exists_left_inv
  let Λ : Submodule (AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K)))⟦X⟧
      (Fin (Fintype.card ι) → (AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : K)))⟦X⟧) :=
    { carrier := {v | ∀ i, ∃ x : Ahat O K l e, φ (Ehat O K l e ^ p * x) =
        φ (Ehat O K l e ^ N) * ∑ k, φ (ψ (v k)) * Ξ k i}
      add_mem' := fun {v v'} hv hv' i => by
        obtain ⟨x, hx⟩ := hv i
        obtain ⟨x', hx'⟩ := hv' i
        refine ⟨x + x', ?_⟩
        simp only [mul_add, map_add, hx, hx', Pi.add_apply, add_mul, Finset.sum_add_distrib]
      zero_mem' := fun i => ⟨0, by simp⟩
      smul_mem' := fun c v hv i => by
        obtain ⟨x, hx⟩ := hv i
        refine ⟨ψ c * x, ?_⟩
        rw [mul_left_comm, map_mul, hx, mul_left_comm, Finset.mul_sum]
        simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc] }
  have hmem : (fun k => ψ.symm (g k τ)) ∈ Λ := fun i => by
    simp only [AlgEquiv.apply_symm_apply]
    exact hg τ i
  refine const_mem_of_stable (fun n => ?_) Λ (α + p) (fun h i => ?_) (fun v hv => ?_) hmem
  · rw [← map_natCast (algebraMap K _)]
    exact IsUnit.map (algebraMap K _) (IsUnit.mk0 _ (natCast_ne_zero' (K := K) l n.succ_ne_zero))
  · refine ⟨Ehat O K l e ^ N * ψ w ^ (α + p) * ∑ k, ψ (h k) * ξ (k, i), ?_⟩
    have hξ' (k) : φ (ξ (k, i)) = φ (Ehat O K l e) ^ α * Ξ k i := (hξ (k, i)).trans (by rw [map_pow])
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_sum, map_pow, Finset.mul_sum, hξ']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ψ X = _ from hw, map_mul]
    ring
  · have h1 : (fun k => ψ.symm (Ehat O K l e * (uhat O K l e * dHat O K l e (ψ (v k))))) ∈ Λ :=
      fun i => by
        simpa only [AlgEquiv.apply_symm_apply] using stable_EN Ξ _ hΓ hΞ N p (fun k => ψ (v k)) hv i
    convert Λ.smul_mem (w * ψ.symm u') h1 using 1
    funext k
    apply ψ.injective
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.apply_symm_apply]
    rw [show ψ X = _ from hw, show ψ (PowerSeries.derivative _ (v k)) = _ from equivAhat_derivative (v k)]
    linear_combination (-(Ehat O K l e * ψ w * dHat O K l e (ψ (v k)))) * hu'

theorem exists_eq_cterm_add (x : Ahat O K l e) :
    ∃ r : Ahat O K l e, x = AhatEq.equivAhat O K l e (C (cterm O K l e x)) + Ehat O K l e * r := by
  obtain ⟨w, hw⟩ := exists_Ehat_eq O K l e
  obtain ⟨v, rfl⟩ := (AhatEq.equivAhat O K l e).surjective x
  refine ⟨AhatEq.equivAhat O K l e (w * PowerSeries.mk fun n => coeff (n + 1) v), ?_⟩
  rw [cterm, AlgEquiv.symm_apply_apply, map_mul, ← mul_assoc, ← hw, ← map_mul, ← map_add]
  exact congrArg _ ((PowerSeries.eq_X_mul_shift_add_const v).trans (add_comm _ _))

theorem hat_mulVec {Y : Matrix ι ι K⟦X⟧} (hY : ∀ i j, Y i j ∈ RpiE O K l e) {m : ι → K⟦X⟧}
    (hm : ∀ j, m j ∈ Rpi O K l e) (i : ι) :
    hat O l e ((Y *ᵥ m) i) =
      ∑ j, hat O l e (Y i j) * algebraMap _ _ (toHat O K l e ⟨m j, hm j⟩) := by
  have : (Y *ᵥ m) i = ((∑ j, ⟨Y i j, hY i j⟩ * ⟨m j, le_away _ _ (hm j)⟩ : RpiE O K l e) : K⟦X⟧) := by
    simp [Matrix.mulVec, dotProduct]
  rw [this, hat_coe, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, hat_of_mem l e (hY i j),
    toHatE_eq l e (f := ⟨m j, le_away _ _ (hm j)⟩) (g := ⟨m j, hm j⟩) rfl]

theorem Ezpow_mul_mem {j : ℤ} {N : ℕ} (hN : 0 ≤ j + N) {f : K⟦X⟧} (hf : f ∈ invE l e (invL l (A O K)))
    {x : Ahat O K l e} (hx : algebraMap _ (AhatE O K l e) (Ehat O K l e ^ (j + N).toNat * x) =
      algebraMap _ _ (Ehat O K l e ^ N) * hat O l e f) :
    Ezpow K l e (-j) * f ∈ invL l (A O K) := by
  set p := (j + N).toNat
  have h1 : E K l e ^ p * (Ezpow K l e (-j) * f) = E K l e ^ N * f := by
    rw [← mul_assoc, ← Ezpow_natCast, ← Ezpow_natCast, ← Ezpow_add]
    congr 2
    omega
  have hf' : f ∈ RpiE O K l e := invE_le_RpiE l e (invL_A_le_Rpi l e) hf
  obtain ⟨n, hn⟩ := hf
  rw [coe_EIn] at hn
  have h2 : E K l e ^ (n + p) * (Ezpow K l e (-j) * f) ∈ invL l (A O K) := by
    rw [pow_add, mul_assoc, h1, mul_left_comm]
    exact mul_mem (pow_mem (E_mem l e _) N) hn
  have h3 : Ezpow K l e (-j) * f ∈ RpiE O K l e := ⟨n + p, invL_A_le_Rpi l e h2⟩
  refine mem_invL_A_of_E_pow_mul l e _ ((hat_mem_range_iff l e h3).1 ⟨x, ?_⟩) h2
  rw [← hat_E_pow_mul l e N hf', ← h1, hat_E_pow_mul l e p h3, map_mul, map_pow] at hx
  exact ((IsLocalization.Away.algebraMap_isUnit (Ehat O K l e)).pow p).mul_left_cancel hx

theorem mem_invE_of_mem_ext (P : PhiMod O K l e a ι) {y : Vec K a ι} (hy : y ∈ P.ext (invL l (A O K)))
    (τ : ZMod a) (j : ι) : y τ j ∈ invE l e (invL l (A O K)) := by
  obtain ⟨m, hm, hv⟩ := P.mem_extc.1 (mem_tot.1 hy τ)
  rw [hv]
  exact Subalgebra.sum_mem _ fun k _ => mul_mem
    (away_mono (le_away _ _) rfl (P.mx_mem τ j k)) (le_away _ _ (hm k))

theorem xiVec_mem_Lk [NeZero a] (P : PhiMod O K l e a ι) (k : Fin (Fintype.card ι)) :
    xiVec P k ∈ P.ext (Rpi O K l e) :=
  (xiExt_mem_Lk_iff O K l e a ι P (1 / e) (one_div_lt l e) (cst (dvec K a (idx ι k)))).2
    (mem_tot.2 fun τ i => by
      simp only [cst_apply, dvec]
      exact PowerSeries.isRestricted_C _ _)

theorem not_next [NeZero a] (P : PhiMod O K l e a ι) (i : ℤ) {y : Vec K a ι}
    (hy : y ∈ P.ext (invL l (A O K))) (h : InEhat O K l e (i + 1) (constPart P y)) :
    y ∈ P.filL (i + 1) := by
  obtain ⟨N, hN, h⟩ := h
  set p := (i + 1 + N).toNat
  set φ := algebraMap (Ahat O K l e) (AhatE O K l e)
  choose x hx using h
  choose r hr using fun k τ => exists_eq_cterm_add (coordHat P y k τ)
  choose m hm hv using fun k τ => P.mem_extc.1 (mem_tot.1 (xiVec_mem_Lk P k) τ)
  have hX (τ i j) : P.mx τ i j ∈ RpiE O K l e := invE_A_le_RpiE l e (P.mx_mem τ i j)
  obtain ⟨α, hα⟩ := exists_denom (fun q : ZMod a × ι × ι => hat O l e (P.mx q.1 q.2.1 q.2.2))
  choose μ hμ using hα
  choose ρ s hρ using fun τ j => exists_eq_algebraMap_add_pow_mul (EIn l e (invL l (A O K))) (α + p)
    (∑ k, r k τ * toHat O K l e ⟨m k τ j, hm k τ j⟩)
  set z : Vec K a ι := fun τ => P.mx τ *ᵥ fun j => (ρ τ j : K⟦X⟧)
  have hz : z ∈ P.ext (invL l (A O K)) :=
    mem_tot.2 fun τ => P.mem_extc.2 ⟨_, fun j => (ρ τ j).2, rfl⟩
  have hEz : E K l e • z ∈ P.ext (invL l (A O K)) := Submodule.smul_mem _ (EIn l e (invL l (A O K))) hz
  have hyz : y - E K l e • z ∈ P.ext (invL l (A O K)) := sub_mem hy hEz
  rw [← sub_add_cancel y (E K l e • z)]
  refine add_mem (Submodule.mem_sup_left ⟨hyz, ?_⟩) (Submodule.mem_sup_right ?_)
  swap
  · rw [mem_shiftE, smul_smul, mul_comm]
    have := E_pow_mul_Ezpow_neg (K := K) l e 1
    rw [pow_one, Nat.cast_one] at this
    rwa [this, one_smul]
  refine mem_tot.2 fun τ j => Ezpow_mul_mem hN (mem_invE_of_mem_ext P hyz τ j)
    (x := x τ j + Ehat O K l e ^ (N + 1) * ∑ j', μ (τ, j, j') * s τ j') ?_
  have hR {v : Vec K a ι} (hv : v ∈ P.ext (invL l (A O K))) : v τ j ∈ RpiE O K l e :=
    invE_le_RpiE l e (invL_A_le_Rpi l e) (mem_invE_of_mem_ext P hv τ j)
  have h1 : hat O l e ((y - E K l e • z) τ j) =
      P.hatTot y τ j - φ (Ehat O K l e) * hat O l e (z τ j) := by
    have := hat_E_pow_mul (O := O) l e 1 (hR hz)
    rw [pow_one, pow_one] at this
    rw [← this]
    exact hat_sub l e (hR hy) (hR hEz)
  have h2 : hat O l e (z τ j) = ∑ j', hat O l e (P.mx τ j j') * φ (ofAl O K l e (ρ τ j')) := by
    rw [hat_mulVec (hX τ) (fun j => invL_A_le_Rpi l e (ρ τ j).2)]
    exact Finset.sum_congr rfl fun j' _ => by rw [toHat_eq_ofAl l e (g := ρ τ j') rfl]
  have h3 : P.hatTot y τ j = constPart P y τ j + φ (Ehat O K l e) *
      ∑ j', hat O l e (P.mx τ j j') * φ (∑ k, r k τ * toHat O K l e ⟨m k τ j', hm k τ j'⟩) := by
    rw [hatTot_eq_hsum P (xiExt_symm_mem P hy), constPart, hsum, hsum]
    simp only [map_sum, Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h4 : P.hatTot (xiVec P k) τ j =
        ∑ j', hat O l e (P.mx τ j j') * φ (toHat O K l e ⟨m k τ j', hm k τ j'⟩) := by
      rw [← hat_mulVec (hX τ) (hm k τ), ← hv]
      rfl
    conv_lhs => rw [hr k τ, map_add, add_mul]
    congr 1
    rw [h4, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [map_mul, map_mul]
    ring
  have h5 : ∑ j', hat O l e (P.mx τ j j') * φ (∑ k, r k τ * toHat O K l e ⟨m k τ j', hm k τ j'⟩) =
      hat O l e (z τ j) + φ (Ehat O K l e) ^ p * φ (∑ j', μ (τ, j, j') * s τ j') := by
    rw [h2, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j' _ => ?_
    have h6 : φ (μ (τ, j, j')) = φ (Ehat O K l e) ^ α * hat O l e (P.mx τ j j') :=
      (hμ (τ, j, j')).trans (by rw [map_pow])
    have h7 : ∑ k, r k τ * toHat O K l e ⟨m k τ j', hm k τ j'⟩ =
      ofAl O K l e (ρ τ j') + Ehat O K l e ^ (α + p) * s τ j' := hρ τ j'
    rw [h7, map_add, map_mul, map_mul, map_pow, h6]
    ring
  have h8 := hx τ j
  rw [h1, h3, h5, mul_add, map_add, h8]
  simp only [map_mul, map_pow]
  ring

end GlobalTheory.BKGal.JumpDR.Horiz

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.JumpDR.Horiz

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι), (∀ m ∈ P.M, P.EN m ∈ P.Man) → ∀ i ∈ P.jumps, ∃ (n : ℕ) (d : Fin n → P.D) (c : Fin n → ZMod a → AdjoinRoot (Polynomial.X ^ e + Polynomial.C (l : ↥LL.1))), (∀ k, P.xi (d k) ∈ P.MMl) ∧ GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e i (GlobalTheory.BKGal.JumpDR.hsum P (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) (fun k => P.xi (d k))) ∧ ¬ GlobalTheory.BKGal.JumpDR.InEhat ↥(OL LL) ↥LL.1 l e (i + 1) (GlobalTheory.BKGal.JumpDR.hsum P (fun k => GlobalTheory.BKGal.JumpDR.kLift ↥(OL LL) (c k)) (fun k => P.xi (d k))) := by
  intro l _ a e _ _ LL _ _ _ ι _ _ P hP i hi
  obtain ⟨y, hyL, hyM, hy⟩ := exists_of_mem_jumps P hi
  refine ⟨Fintype.card ι, fun k => dvec _ a (idx ι k),
    fun k τ => cterm _ _ l e (coordHat P y k τ), fun k => xiVec_mem_MMl P k, ?_, ?_⟩
  · have h1 := inEhat_hatTot P hyM
    rw [hatTot_eq_hsum P (xiExt_symm_mem P hyL)] at h1
    exact grading P hP i _ h1
  · exact fun h => hy (not_next P i hyL h)

end GlobalTheory.BKGal.JumpDR.Horiz
