import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.RightSub

open Formalism.BasicNotions UpperTheory.TP.RP MvPolynomial

namespace UpperTheory.TP.RP

private theorem rightSub_xv {n d : ℕ} (g : Matrix (Fin d) (Fin d) ℂ) (b : Fin n) (c : Fin d) :
    rightSub g (xv b c) = ∑ a, C (g a c) * xv b a := by
  simp only [rightSub, xv, aeval_X]

private noncomputable def sSub (n d : ℕ) : MvPolynomial (Fin d × Fin d) ℂ →ₐ[ℂ] PP n d :=
  aeval fun v => if hv : (v.2 : ℕ) < n then xv ⟨v.2, hv⟩ v.1 else 0

private theorem sSub_X {n d : ℕ} (a b : Fin d) :
    sSub n d (X (a, b)) = if hv : (b : ℕ) < n then xv ⟨b, hv⟩ a else 0 := by
  simp only [sSub, aeval_X]

private theorem sSub_rowAct {n d : ℕ} (g : Matrix (Fin d) (Fin d) ℂ)
    (f : MvPolynomial (Fin d × Fin d) ℂ) :
    sSub n d (Formalism.GradedWeylDivisibility.rowAct ℂ g.transpose f) = rightSub g (sSub n d f) := by
  have e : (sSub n d).comp (Formalism.GradedWeylDivisibility.rowAct ℂ g.transpose) = (rightSub g).comp (sSub n d) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, b⟩
    simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowAct, aeval_X, map_sum, map_mul, Matrix.transpose_apply,
      algHom_C, sSub_X]
    by_cases hb : (b : ℕ) < n
    · simp [hb, rightSub_xv, algebraMap_eq]
    · simp [hb]
  exact DFunLike.congr_fun e f

private theorem sSub_lp {n d s : ℕ} (hd : s ≤ d) (hn : s ≤ n) :
    sSub n d (Formalism.GradedWeylDivisibility.lpMinor ℂ s hd hd) = ofTall (Formalism.GradedWeylDivisibility.lpMinor ℂ s hd hn) := by
  unfold Formalism.GradedWeylDivisibility.lpMinor
  rw [AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext p q
  have hq : ((Fin.castLE hn q : Fin n) : ℕ) = q := rfl
  simp [sSub_X, ofTall, xv, show (q : ℕ) < n by omega]
  rfl

private noncomputable def dTop {n d : ℕ} (h : n ≤ d) : PP n d :=
  ofTall (Formalism.GradedWeylDivisibility.lpMinor ℂ n h le_rfl)

private theorem rightSub_dTop {d : ℕ} (g : Matrix (Fin d) (Fin d) ℂ) :
    rightSub g (dTop (le_refl d)) = C g.det * dTop (le_refl d) := by
  have hM : dTop (le_refl d) = (Matrix.of fun p q : Fin d => (xv q p : PP d d)).det := by
    unfold dTop Formalism.GradedWeylDivisibility.lpMinor
    rw [AlgHom.map_det]
    congr 1
    ext p q
    simp [ofTall, xv]
  rw [hM, AlgHom.map_det]
  have e : (rightSub g).mapMatrix (Matrix.of fun p q : Fin d => (xv q p : PP d d)) =
      (g.map C).transpose * Matrix.of fun p q : Fin d => (xv q p : PP d d) := by
    ext1 p q
    simp [Matrix.mul_apply, rightSub_xv]
  rw [e, Matrix.det_mul, Matrix.det_transpose]
  congr 1
  exact (RingHom.map_det (C : ℂ →+* PP d d) g).symm

private theorem hw_lt {n d : ℕ} (h : n ≤ d) (hlt : n < d) (ν : Fin d → ℕ) (μ : Fin n → ℕ)
    (hν : ∀ k : Fin d, ν k = if hk : (k : ℕ) < n then μ ⟨k, hk⟩ else 0) :
    sSub n d (Formalism.GradedWeylDivisibility.hw ℂ le_rfl ν) = joint h μ := by
  unfold joint Formalism.GradedWeylDivisibility.hw
  rw [map_prod, map_prod]
  symm
  apply Fintype.prod_of_injective (Fin.castLE h) (Fin.castLE_injective h)
  · intro i hi
    have hin : ¬ (i : ℕ) < n := fun hh => hi ⟨⟨i, hh⟩, Fin.ext rfl⟩
    have : ν i = 0 := by rw [hν]; simp [hin]
    rw [this]
    simp
  · intro k
    have hk1 : (k : ℕ) + 1 ≤ n := k.2
    rw [map_pow, map_pow]
    have e1 := sSub_lp (n := n) (d := d) (s := (k : ℕ) + 1) (by omega) hk1
    have a : ν (Fin.castLE h k) = μ k := by rw [hν]; simp
    have b : Formalism.GradedWeylDivisibility.nuNext ν (Fin.castLE h k) = Formalism.GradedWeylDivisibility.nuNext μ k := by
      unfold Formalism.GradedWeylDivisibility.nuNext
      by_cases hk : (k : ℕ) + 1 < n
      · simp [hk, show (k : ℕ) + 1 < d by omega, hν]
      · simp [hk, show (k : ℕ) + 1 < d by omega, hν]
    rw [a, b]
    exact congrArg (· ^ _) e1.symm

private theorem hw_eq {d : ℕ} (ν μ : Fin d → ℕ) (t : ℕ) (hν : ∀ k, ν k + t = μ k)
    (hl : ∀ k : Fin d, (k : ℕ) + 1 = d → ν k = 0) :
    sSub d d (Formalism.GradedWeylDivisibility.hw ℂ le_rfl ν) * dTop (le_refl d) ^ t = joint (le_refl d) μ := by
  rcases d with _ | m
  · simp [joint, Formalism.GradedWeylDivisibility.hw, dTop, Formalism.GradedWeylDivisibility.lpMinor]
  · unfold joint Formalism.GradedWeylDivisibility.hw
    have f : ∀ k : Fin (m + 1), sSub (m + 1) (m + 1) (Formalism.GradedWeylDivisibility.lpMinor ℂ ((k : ℕ) + 1) (by omega) (by omega)) =
        ofTall (Formalism.GradedWeylDivisibility.lpMinor ℂ ((k : ℕ) + 1) (by omega) (by omega)) := fun k => sSub_lp _ (by omega)
    rw [map_prod, map_prod]
    simp only [map_pow, f]
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    have e_last : ν (Fin.last m) = 0 := hl _ (by simp)
    have n_last : ∀ ξ : Fin (m + 1) → ℕ, Formalism.GradedWeylDivisibility.nuNext ξ (Fin.last m) = 0 := fun ξ => by
      simp [Formalism.GradedWeylDivisibility.nuNext]
    have e_cs : ∀ k : Fin m, ν k.castSucc - Formalism.GradedWeylDivisibility.nuNext ν k.castSucc =
        μ k.castSucc - Formalism.GradedWeylDivisibility.nuNext μ k.castSucc := by
      intro k
      unfold Formalism.GradedWeylDivisibility.nuNext
      have hk : (k.castSucc : ℕ) + 1 < m + 1 := by simp
      rw [dif_pos hk, dif_pos hk]
      have h1 := hν k.castSucc
      have h2 := hν ⟨(k.castSucc : ℕ) + 1, hk⟩
      omega
    have hμl : μ (Fin.last m) = t := by
      have := hν (Fin.last m)
      omega
    simp only [e_cs, e_last, n_last, hμl, Nat.zero_sub, Nat.sub_zero, pow_zero, mul_one]
    rfl

end UpperTheory.TP.RP

theorem UpperTheory.TP.RP.exists_act2_equivariant_nablaSq_map_hitting_joint :
    ∀ {n d : ℕ} (h : n ≤ d) (lam' : DomWeight d) (c : ℤ) (μ : Fin n → ℕ),
      (∀ k : Fin d, lam'.w k = (if hk : (k : ℕ) < n then (μ ⟨k, hk⟩ : ℤ) else 0) + c) →
      ∃ i : nablaSq ℂ d lam' →ₗ[ℂ] PP n d, (∀ g x, i (GlobalTheory.Branching.sqRep ℂ d lam' g x) = act2 c g (i x)) ∧ ∃ x₀, i x₀ = joint h μ := by
  intro n d h lam' c μ hμ
  have hanti : Antitone lam'.natW := fun i j hij => by
    have := lam'.anti hij
    simp only [DomWeight.natW]
    omega
  have key : (∀ g : GL (Fin d) ℂ, C (detPow ℂ d g lam'.detShift) * dTop h ^ (lam'.detShift - c).toNat =
        C (detPow ℂ d g c) * (rightSub g.1 (dTop h)) ^ (lam'.detShift - c).toNat) ∧
      sSub n d (Formalism.GradedWeylDivisibility.hw ℂ le_rfl lam'.natW) * dTop h ^ (lam'.detShift - c).toNat = joint h μ := by
    rcases h.lt_or_eq with hlt | rfl
    · have hs : lam'.detShift = c := by
        have h0 : 0 < d := by omega
        simp only [DomWeight.detShift, dif_pos h0]
        rw [hμ]
        simp [show ¬ (d - 1 < n) by omega]
      rw [hs]
      refine ⟨fun g => by simp, ?_⟩
      simp only [sub_self, Int.toNat_zero, pow_zero, mul_one]
      apply hw_lt h hlt
      intro k
      simp only [DomWeight.natW, hs]
      rw [hμ]
      split_ifs <;> simp
    · have hμ' : ∀ k, lam'.w k = (μ k : ℤ) + c := fun k => by rw [hμ, dif_pos k.2]
      have hsh : ∀ h0 : 0 < n, lam'.detShift = (μ ⟨n - 1, by omega⟩ : ℤ) + c := fun h0 => by
        simp only [DomWeight.detShift, dif_pos h0, hμ']
      refine ⟨fun g => ?_, ?_⟩
      · rw [rightSub_dTop, mul_pow, ← C_pow, ← mul_assoc, ← C_mul]
        congr 2
        rcases Nat.eq_zero_or_pos n with rfl | h0
        · have : Matrix.GeneralLinearGroup.det g = 1 := Units.ext (by simp)
          simp [detPow, this]
        · have e : lam'.detShift = c + ((lam'.detShift - c).toNat : ℤ) := by
            have := hsh h0
            omega
          have e2 : g.1.det = ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) := by simp
          conv_lhs => rw [e]
          rw [e2]
          simp only [detPow, zpow_add, zpow_natCast, Units.val_mul, Units.val_pow_eq_pow_val]
      · apply hw_eq
        · intro k
          have h0 : 0 < n := by have := k.2; omega
          have h1 := hsh h0
          have h2 := lam'.anti (show k ≤ ⟨n - 1, by omega⟩ from Fin.le_def.mpr (by have := k.2; simp only; omega))
          rw [hμ', hμ'] at h2
          simp only [DomWeight.natW, hμ']
          omega
        · intro k hk
          have h0 : 0 < n := by omega
          have e : (⟨n - 1, by omega⟩ : Fin n) = k := Fin.ext (by simp; omega)
          simp [DomWeight.natW, DomWeight.detShift, h0, e]
  refine ⟨(LinearMap.mulRight ℂ (dTop h ^ (lam'.detShift - c).toNat)) ∘ₗ (sSub n d).toLinearMap ∘ₗ
    (nablaSq ℂ d lam').subtype, ?_, ⟨_, Formalism.GradedWeylDivisibility.hwMem ℂ d d le_rfl _ hanti⟩, ?_⟩
  · intro g x
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Submodule.subtype_apply,
      AlgHom.toLinearMap_apply, GlobalTheory.Branching.sqRep_coe, sqAct, act2, LinearMap.smul_apply]
    rw [map_smul, sSub_rowAct, map_mul, map_pow, smul_eq_C_mul, smul_eq_C_mul]
    linear_combination rightSub g.1 (sSub n d x) * key.1 g
  · exact key.2
