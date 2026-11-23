import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.BlockMatrixPlaces.BlockDiagonalOrdinaryGSpRep

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Bl

private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha y _ i => ?_) (fun a b ha hb i => ?_)
    · exact J.mul_mem_right _ ha
    · exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R] (r : ℕ) :
    IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have key : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := fun i =>
    IsPrecomplete.prec' (I := I) (fun n => f n i) fun {m n} hmn => by
      have h := hf hmn
      rw [SModEq.sub_mem, mem_smul_top_pi] at h
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      exact h i
  choose L hL using key
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, mem_smul_top_pi]
  intro i
  have h := hL i n
  rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  obtain ⟨r, π, hπ⟩ := Module.Finite.exists_fin' R M
  haveI := isPrecomplete_pi I r
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.map_surjective I hπ y
  obtain ⟨w, rfl⟩ := AdicCompletion.of_surjective I (Fin r → R) z
  exact ⟨π w, (AdicCompletion.map_of I π w).symm⟩

private theorem lift_seq {A : Type} [CommRing A] [IsLocalRing A] {T : Type} [AddCommGroup T] [Module A T]
    [IsPrecomplete (maximalIdeal A) T] (x : ∀ n, T ⧸ lev A T n) (hx : ∀ n, redn A T n (x (n + 1)) = x n) :
    ∃ L : T, ∀ n, (lev A T n).mkQ L = x n := by
  choose f hf using fun n => (lev A T n).mkQ_surjective (x n)
  have h1 : ∀ n, f n - f (n + 1) ∈ lev A T n := fun n => by
    rw [← Submodule.Quotient.eq]
    have := hx n
    rw [← hf (n + 1), redn_mk, ← hf n] at this
    exact this.symm
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ lev A T m := fun m n hmn => by
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h3 : lev A T n ≤ lev A T m := Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)
      simpa using (lev A T m).add_mem ih (h3 (h1 n))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := maximalIdeal A) f fun {m n} hmn => SModEq.sub_mem.2 (h2 m n hmn)
  exact ⟨L, fun n => Eq.trans (SModEq.def.1 (hL n).symm) (hf n)⟩

private theorem mem_of_lev {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {T : Type} [AddCommGroup T]
    [Module A T] [Module.Finite A T] (P : Submodule A T) (x : T)
    (hx : ∀ n, (lev A T n).mkQ x ∈ P.map (lev A T n).mkQ) : x ∈ P := by
  rw [← Submodule.Quotient.mk_eq_zero]
  refine IsHausdorff.haus' (I := maximalIdeal A) _ fun n => ?_
  obtain ⟨p, hp, e⟩ := hx n
  have e' : p - x ∈ lev A T n := (Submodule.Quotient.eq _).1 e
  have h1 : P.mkQ (p - x) ∈ (lev A T n).map P.mkQ := Submodule.mem_map_of_mem e'
  rw [Submodule.map_smul'', map_sub, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero P).2 hp, zero_sub,
    neg_mem_iff] at h1
  rw [SModEq.zero]
  exact Submodule.smul_mono le_rfl le_top h1

private theorem eq_of_lev {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {T : Type} [AddCommGroup T]
    [Module A T] [Module.Finite A T] (x y : T)
    (hx : ∀ n, (lev A T n).mkQ x = (lev A T n).mkQ y) : x = y := by
  rw [← sub_eq_zero, ← Submodule.mem_bot A]
  refine mem_of_lev ⊥ _ fun n => ?_
  rw [map_sub, hx n, sub_self]
  exact zero_mem _

theorem UpperTheory.V.Ws.Bl.limit :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (T : Type) [AddCommGroup T] [Module A T] [Module.Finite A T] [Module.Free A T] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (ρ : Representation A Γ T) (c : Γ) (N : Set Γ) (H : Subgroup Γ) (P : Submodule A T), IsAdicComplete (maximalIdeal A) A → ∀ (z : ∀ n, Γ → T ⧸ lev A T n) (y : ∀ n, T ⧸ lev A T n), (∀ n, IsZn ρ c N H P n (z n) (y n)) → (∀ n g, redn A T n (z (n + 1) g) = z n g) → (∀ n, redn A T n (y (n + 1)) = y n) → Prim (z 1) →
          ∃ (z' : Γ → T) (y' : T), IsZT ρ c N H P z' y' ∧ z' ≠ 0 := by
  intro A _ _ _ T _ _ _ _ Γ _ _ ρ c N H P hA z y hZ hz hy hP
  haveI : IsPrecomplete (maximalIdeal A) T := isPrecomplete_finite _
  choose z' hz' using fun g => lift_seq (fun n => z n g) fun n => hz n g
  obtain ⟨y', hy'⟩ := lift_seq y hy
  refine ⟨z', y', ⟨fun n => ?_, fun g h => ?_, ?_, fun g hg => ?_, fun h hh => ?_⟩, ?_⟩
  · simp only [hz']
    exact (hZ n).lc
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [map_add, ← modRep_mk, hz', hz', hz']
    exact (hZ n).coc g h
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [hz', map_zero]
    exact (hZ n).cz
  · refine eq_of_lev (A := A) _ _ fun n => ?_
    rw [hz', map_zero]
    exact (hZ n).kill g hg
  · refine mem_of_lev P _ fun n => ?_
    rw [map_sub, map_sub, ← modRep_mk, hz', hy']
    exact (hZ n).loc h hh
  · rintro rfl
    obtain ⟨g, hg⟩ := hP
    apply hg
    rw [← hz' g 1, Pi.zero_apply, map_zero]
    exact zero_mem _
