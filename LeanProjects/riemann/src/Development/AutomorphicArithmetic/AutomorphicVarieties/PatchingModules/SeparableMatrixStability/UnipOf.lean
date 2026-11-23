import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.MapEta

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem cast_zero (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Finite K] [Algebra ℤ_[l] K] : (l : K) = 0 := by
  have hni : ¬ Function.Injective (algebraMap ℤ_[l] K) := by
    haveI : Infinite ℤ_[l] := Infinite.of_injective (Nat.cast : ℕ → ℤ_[l]) Nat.cast_injective
    exact not_injective_infinite_finite _
  have hker : RingHom.ker (algebraMap ℤ_[l] K) ≠ ⊥ := by
    intro h
    exact hni ((RingHom.injective_iff_ker_eq_bot _).2 h)
  obtain ⟨e, he⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (l : ℤ_[l]) ^ e ∈ RingHom.ker (algebraMap ℤ_[l] K) := by
    rw [he]
    exact Ideal.subset_span rfl
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact pow_eq_zero_iff'.mp hmem |>.1

private theorem key (l : ℕ) [Fact l.Prime] (K : Type) [Field K] (hl : (l : K) = 0) (n : ℕ)
    (P : Matrix (Fin n) (Fin n) (PowerSeries K))
    (hP : P.charpoly.map (PowerSeries.constantCoeff : PowerSeries K →+* K) = (Polynomial.X - 1) ^ n) (m : ℕ) :
    ∃ e : ℕ, ∀ i j, (P ^ l ^ e - 1) i j ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ m} := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun i => i.elim0⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : CharP K l := (CharP.charP_iff_prime_eq_zero (Fact.out : l.Prime)).2 hl
  haveI : CharP (PowerSeries K) l :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective l
  set I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X} with hI
  have hmul : ∀ (A B : Matrix (Fin n) (Fin n) (PowerSeries K)) (J J' : Ideal (PowerSeries K)),
      (∀ i j, A i j ∈ J) → (∀ i j, B i j ∈ J') → ∀ i j, (A * B) i j ∈ J * J' := by
    intro A B J J' hA hB i j
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_mul (hA i k) (hB k j)
  have hpow : ∀ (A : Matrix (Fin n) (Fin n) (PowerSeries K)) (J : Ideal (PowerSeries K)),
      (∀ i j, A i j ∈ J) → ∀ k : ℕ, ∀ i j, (A ^ k) i j ∈ J ^ k := by
    intro A J hA k
    induction k with
    | zero => intro i j; simp
    | succ k ih =>
      intro i j
      rw [pow_succ, pow_succ]
      exact hmul _ _ _ _ ih hA i j
  set d := P.charpoly - (Polynomial.X - 1) ^ n with hd
  have hdmap : d.map (PowerSeries.constantCoeff : PowerSeries K →+* K) = 0 := by
    rw [hd, Polynomial.map_sub, hP, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_one, sub_self]
  have hdc : ∀ k, d.coeff k ∈ I := by
    intro k
    rw [hI, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    have := congrArg (fun q => Polynomial.coeff q k) hdmap
    simpa [Polynomial.coeff_map] using this
  have hev : Polynomial.aeval P d = -(P - 1) ^ n := by
    rw [hd, map_sub, Matrix.aeval_self_charpoly, map_pow, map_sub, Polynomial.aeval_X, map_one,
      zero_sub]
  have hA : ∀ i j, (Polynomial.aeval P d) i j ∈ I := by
    intro i j
    rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply]
    exact Ideal.sum_mem _ fun k _ => by
      rw [Matrix.smul_apply, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (hdc k)
  have hQ : ∀ i j, ((P - 1) ^ n) i j ∈ I := by
    intro i j
    have h1 : (P - 1) ^ n = -(Polynomial.aeval P d) := by rw [hev, neg_neg]
    rw [h1, Matrix.neg_apply]
    exact I.neg_mem (hA i j)
  refine ⟨n * m, fun i j => ?_⟩
  have hle : n * m ≤ l ^ (n * m) := (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
  have hsub : P ^ l ^ (n * m) - 1 = (P - 1) ^ l ^ (n * m) := by
    rw [sub_pow_char_pow_of_commute l (n * m) (Commute.one_right P), one_pow]
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hle
  rw [hsub, hr, pow_add, pow_mul]
  have h2 := hmul (((P - 1) ^ n) ^ m) ((P - 1) ^ r) (I ^ m) ⊤ (hpow _ _ hQ m)
    (fun a b => Submodule.mem_top (x := ((P - 1) ^ r) a b)) i j
  rwa [Ideal.mul_top, hI, Ideal.span_singleton_pow] at h2

theorem UpperTheory.V.Pa.unip_of :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n) (H : Subgroup F.Γ), (∀ h : F.G₀, (h : F.Γ) ∈ H → (mat x.ρ h).charpoly.map (PowerSeries.constantCoeff : x.A →+* x.K) = (Polynomial.X - 1) ^ n) → x.UnipOn H := by
  intro l _ F n x H hH m h hh
  obtain ⟨e, he⟩ := key l x.K (cast_zero l x.K) n (mat x.ρ h) (hH h hh) m
  exact ⟨e, fun i j => by rw [map_pow]; exact he i j⟩
