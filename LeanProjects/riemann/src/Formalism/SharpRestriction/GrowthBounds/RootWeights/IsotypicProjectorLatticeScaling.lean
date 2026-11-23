import Formalism.SharpRestriction.GrowthBounds.RootWeights.IsotypicProjectorSelfAdjoint

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

theorem monomial_exponent_le_multidegree {ι : Type*} {n : ℕ} (m : ι × Fin n →₀ ℕ) (l : ι) (a : Fin n) : m (l, a) ≤ multideg m l := by
  exact Finset.single_le_sum (f := fun c => m (l, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem polynomial_weight_difference_le {ι : Type*} [Fintype ι] {n : ℕ} (LL : Letters ι) (S : Set ι) (d : ι → ℕ)
    (m m' : ι × Fin n →₀ ℕ) (hm : ∀ i, multideg m i = d i) (hm' : ∀ i, multideg m' i = d i) (a b : Fin n) :
    wtS LL S m a - wtS LL S m' b ≤ (degIn d S : ℤ) := by
  unfold wtS degIn
  rw [← Finset.sum_sub_distrib]
  push_cast
  refine Finset.sum_le_sum fun l _ => ?_
  have h1 := monomial_exponent_le_multidegree m l a
  have h2 := monomial_exponent_le_multidegree m' l b
  rw [hm l] at h1
  rw [hm' l] at h2
  split_ifs <;> omega

theorem prime_pow_smul_cast {O : Type} [CommRing O] [IsDomain O] {σ : Type} (p k : ℕ) (y : MvPolynomial σ (KK O)) :
    ((p : O) ^ k) • y = ((p : KK O) ^ k) • y := by
  rw [← algebraMap_smul (KK O) ((p : O) ^ k) y, map_pow, map_natCast]

theorem isotypic_projector_lattice_scaling (D : Formalism.BasicNotions.D7) (hDom : HighestWeightDominant) (hRes : SubrepRestrictionRep) (hPol : PolynomialGLRepresentation) (h13 : IsotypicProjectorTheoremField D)
    (p n' : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (S0 : UniformizedDVR p O)
    (hG : AdmissibleDVR p n' O) [CharZero (KK O)] (n : ℕ) (ι : Type) [Fintype ι] (LL : Letters ι) (S : Set ι)
    (d : ι → ℕ) (lam : Fin n → ℤ) (e : Module.End (KK O) (MvPolynomial (ι × Fin n) (KK O)))
    (he : IsIsoProj (glOps (KK O) n LL S) lam e) :
    (∀ F ∈ Pol (KK O) n d, e F ∈ Pol (KK O) n d) ∧
    ∀ L : Submodule O (MvPolynomial (ι × Fin n) (KK O)),
      (∀ u ∈ UZgens (glOps (KK O) n LL S), ∀ F ∈ L, u F ∈ L) → (latticeMultidegreePart L d).FG →
      MQ (K := KK O) (latticeMultidegreePart L d) = ⊤ →
      ∀ F ∈ Pol (KK O) n d, F ∈ L →
        ((p : KK O) ^ (N0 n * Nat.log p (2 * degIn d S + n - 1))) • e F ∈ L := by
  obtain ⟨hRep, -, -, hStab, hFD, hWt, -⟩ := hPol (KK O) ι n LL
  have hStabS : ∀ a b, ∀ x ∈ Pol (KK O) n d, glOps (KK O) n LL S a b x ∈ Pol (KK O) n d :=
    fun a b x hx => hStab S d a b x hx
  obtain ⟨hResRep, hResWt, hResDiv, hResBin, hResProj, hResZero⟩ :=
    hRes (KK O) (MvPolynomial (ι × Fin n) (KK O)) n (glOps (KK O) n LL S) (hRep S) (Pol (KK O) n d) hStabS
  obtain ⟨e', he'P, he'eq⟩ := hResProj lam e he
  have hPres : ∀ F ∈ Pol (KK O) n d, e F ∈ Pol (KK O) n d := by
    intro F hF
    have h := (e' ⟨F, hF⟩).2
    rwa [he'eq ⟨F, hF⟩] at h
  refine ⟨hPres, ?_⟩
  intro L hLst hFG hMQ F hF hFL
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hid : e F = F := by
      by_cases h0 : F = 0
      · rw [h0, map_zero]
      · apply he.1
        apply Submodule.subset_span
        refine ⟨1, Submonoid.one_mem _, F, ⟨h0, ?_, fun a => a.elim0⟩, by simp⟩
        simp [weightSp]
    rw [hid]
    simpa [N0] using hFL
  · have : NeZero n := ⟨hn.ne'⟩
    have : FiniteDimensional (KK O) (Pol (KK O) n d) := hFD d

    have hwt : ∀ (mu : Fin n → ℤ) (x : Pol (KK O) n d), x ≠ 0 →
        x ∈ weightSp (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) mu →
        ∃ m : ι × Fin n →₀ ℕ, (∀ i, multideg m i = d i) ∧ wtS LL S m = mu := by
      intro mu x hx0 hx
      have hxV := (hResWt mu x).mp hx
      have hne : (x : MvPolynomial (ι × Fin n) (KK O)) ≠ 0 := by simpa using hx0
      obtain ⟨m, hm⟩ : (x : MvPolynomial (ι × Fin n) (KK O)).support.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (by rwa [Ne, MvPolynomial.support_eq_empty])
      refine ⟨m, ?_, hWt S mu _ hxV m hm⟩
      have hx2 : (x : MvPolynomial (ι × Fin n) (KK O)) ∈
          MvPolynomial.restrictSupport (KK O) {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := x.2
      exact (show ((x : MvPolynomial (ι × Fin n) (KK O)).support : Set (ι × Fin n →₀ ℕ)) ⊆
        {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} from hx2) hm
    by_cases hhw : ∃ v : Pol (KK O) n d,
        IsHWV (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) lam v
    · have hdom : Dominant lam := by
        obtain ⟨v, hv⟩ := hhw
        exact hDom (KK O) (Pol (KK O) n d) n _ hResRep lam v hv
      have hWtBound : ellWt lam ≤ degIn d S := by
        obtain ⟨v, hv⟩ := hhw
        obtain ⟨m, hmd, hmw⟩ := hwt lam v hv.1 hv.2.1
        have h := polynomial_weight_difference_le LL S d m m hmd hmd 0 (lastIdx n)
        rw [hmw] at h
        unfold ellWt
        omega
      have hEllBound : ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤ ≤ degIn d S := by
        unfold ellOf
        apply csSup_le'
        rintro k ⟨mu, hmu, nu, hnu, a, b, hab, hk⟩
        obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp (by simpa [wtsOf] using hmu)
        obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp (by simpa [wtsOf] using hnu)
        obtain ⟨m, hmd, hmw⟩ := hwt mu x hx0 hx
        obtain ⟨m', hmd', hmw'⟩ := hwt nu y hy0 hy
        have e1 := congrFun hk a
        have e2 := congrFun hk b
        simp [rootW, hab, Ne.symm hab] at e1 e2
        have d1 := polynomial_weight_difference_le LL S d m m hmd hmd a b
        have d2 := polynomial_weight_difference_le LL S d m' m' hmd' hmd' b a
        rw [hmw] at d1
        rw [hmw'] at d2
        omega
      have hLat : UZLattice (O := O) (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS)
          (latticeMultidegreePart L d) := by
        refine ⟨?_, hFG⟩
        intro u hu x hx
        rw [latticeMultidegreePart, Submodule.mem_comap] at hx ⊢
        rcases hu with ⟨a, b, k, hab, rfl⟩ | ⟨a, k, rfl⟩
        · change ((divPowE _ a b k x : Pol (KK O) n d) : MvPolynomial (ι × Fin n) (KK O)) ∈ L
          rw [hResDiv a b k x]
          exact hLst _ (Or.inl ⟨a, b, k, hab, rfl⟩) _ hx
        · change ((binomE _ a k x : Pol (KK O) n d) : MvPolynomial (ι × Fin n) (KK O)) ∈ L
          rw [hResBin a k x]
          exact hLst _ (Or.inr ⟨a, k, rfl⟩) _ hx
      have key := h13 p n' O S0 hG n (Pol (KK O) n d) _ hResRep (latticeMultidegreePart L d) hLat hMQ {lam}
        (by simpa using hdom) (fun _ => e') (by simpa using he'P) ⟨F, hF⟩ hFL
      simp only [Finset.sup_singleton, Finset.sum_singleton, hMQ] at key
      rw [latticeMultidegreePart, Submodule.mem_comap] at key
      have key' : ((p : O) ^ (N0 n * deF p n (ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤
          + ellWt lam))) • e F ∈ L := by
        simpa [he'eq] using key
      have hle : N0 n * deF p n (ellOf (restrictStableOperators (glOps (KK O) n LL S) (Pol (KK O) n d) hStabS) ⊤ + ellWt lam)
          ≤ N0 n * Nat.log p (2 * degIn d S + n - 1) := by
        unfold deF
        exact Nat.mul_le_mul_left _ (Nat.log_mono_right (by omega))
      obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hle
      rw [hj, ← prime_pow_smul_cast p _ (e F), pow_add, mul_comm, mul_smul]
      exact L.smul_mem _ key'
    · have h0 : e F = 0 := hResZero lam e he hhw F hF
      rw [h0, smul_zero]
      exact L.zero_mem

end Formalism.MainNotions.G.GLWeightTheory
