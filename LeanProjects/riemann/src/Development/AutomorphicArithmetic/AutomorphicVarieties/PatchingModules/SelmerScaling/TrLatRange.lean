import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrVr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.AdjoinNilFinite
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem trLat_range {A B R : Type} [CommRing A] [CommRing B] [CommRing R] [Algebra A R] [IsNoetherianRing B]
    (φ : B →+* R) (f : B →+* A) (J : Ideal R) (N : ℕ) (hJ : J ^ N = ⊥)
    (h1 : ∀ a, ∃ b, φ b = algebraMap A R a ∧ f b = a) (h2 : ∀ b, φ b - algebraMap A R (f b) ∈ J) :
    ∃ M : Subalgebra A R, (Subalgebra.toSubmodule M).FG ∧ ∀ b, φ b ∈ M := by
  classical
  obtain ⟨r, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (RingHom.ker f))
  have hgJ : ∀ i, φ (g i) ∈ J := by
    intro i
    have : g i ∈ RingHom.ker f := hg ▸ Submodule.subset_span ⟨i, rfl⟩
    have h := h2 (g i)
    rwa [(RingHom.mem_ker.1 this), map_zero, sub_zero] at h
  refine ⟨Algebra.adjoin A (Set.range fun i => φ (g i)), ?_, ?_⟩
  · refine fg_adjoin_of_finite (Set.finite_range _) ?_
    rintro _ ⟨i, rfl⟩
    have : φ (g i) ^ N = 0 := by
      have := Ideal.pow_mem_pow (hgJ i) N
      rwa [hJ, Ideal.mem_bot] at this
    exact ⟨Polynomial.X ^ N, Polynomial.monic_X_pow N, by simpa using this⟩
  · have key : ∀ k : ℕ, ∀ b, ∃ m ∈ Algebra.adjoin A (Set.range fun i => φ (g i)), φ b - m ∈ J ^ k := by
      intro k
      induction k with
      | zero => intro b; exact ⟨0, zero_mem _, by simp⟩
      | succ k ih =>
        intro b
        obtain ⟨b', hb', hf⟩ := h1 (f b)
        have hq : b - b' ∈ Submodule.span B (Set.range g) := by
          rw [hg, RingHom.mem_ker, map_sub, hf, sub_self]
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).1 hq
        choose m hm hm' using ih
        refine ⟨algebraMap A R (f b) + ∑ i, m (c i) * φ (g i), ?_, ?_⟩
        · refine add_mem (Subalgebra.algebraMap_mem _ _) (sum_mem fun i _ => mul_mem (hm _) ?_)
          exact Algebra.subset_adjoin ⟨i, rfl⟩
        · have e : φ b - (algebraMap A R (f b) + ∑ i, m (c i) * φ (g i)) = ∑ i, (φ (c i) - m (c i)) * φ (g i) := by
            have := congrArg φ hc
            rw [map_sub, map_sum, hb'] at this
            simp only [smul_eq_mul, map_mul] at this
            simp only [sub_mul, Finset.sum_sub_distrib]
            linear_combination -this
          rw [e, pow_succ]
          exact sum_mem fun i _ => Ideal.mul_mem_mul (hm' _) (hgJ i)
    intro b
    obtain ⟨m, hm, h⟩ := key N b
    rw [hJ, Ideal.mem_bot, sub_eq_zero] at h
    rwa [h]

private theorem trLat_pow {A B R : Type} [CommRing A] [CommRing B] [CommRing R] [Algebra A R] [IsLocalRing A]
    [IsLocalRing B] (t : A) (ht : maximalIdeal A ≤ Ideal.span {t})
    (φ : B →+* R) (f : B →+* A) (J : Ideal R) (N : ℕ) (hJ : J ^ N = ⊥)
    (h1 : Function.Surjective f) (h2 : ∀ b, φ b - algebraMap A R (f b) ∈ J) (M : Subalgebra A R) (hM : ∀ b, φ b ∈ M) (j : ℕ) :
    ∀ b ∈ maximalIdeal B ^ (j + N), ∃ y ∈ M, φ b = t ^ j • y := by
  haveI : IsLocalHom f := IsLocalHom.of_surjective f h1
  let φ' : B →+* M := φ.codRestrict M hM
  let J' : Ideal M := J.comap M.val.toRingHom
  have hJ' : J' ^ N = ⊥ := by
    refine le_bot_iff.1 ((Ideal.le_comap_pow _ N).trans ?_)
    rw [hJ]
    intro y hy
    rw [Ideal.mem_comap, Ideal.mem_bot] at hy
    exact Ideal.mem_bot.2 (Subtype.ext hy)
  have hle : (maximalIdeal B).map φ' ≤ Ideal.span {algebraMap A M t} ⊔ J' := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (ht (map_nonunit f b hb))
    rw [Ideal.mem_comap]
    have e : φ' b = algebraMap A M a * algebraMap A M t + (φ' b - algebraMap A M (f b)) := by
      rw [← map_mul, ha]; ring
    rw [e]
    exact add_mem (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
      (Ideal.mem_sup_right (h2 b))
  intro b hb
  have h3 : φ' b ∈ ((maximalIdeal B).map φ') ^ (j + N) := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hb
  have h4 := Ideal.sup_pow_add_le_pow_sup_pow (Ideal.pow_right_mono hle _ h3)
  rw [hJ', sup_bot_eq, Ideal.span_singleton_pow] at h4
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h4
  refine ⟨y, y.2, ?_⟩
  have := congrArg Subtype.val hy
  rw [Algebra.smul_def, map_pow, mul_comm]
  simpa [φ'] using this.symm

private theorem trLat_mul {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (M : Subalgebra A R) (E : Submodule A R) :
    (∀ y ∈ M, ∀ z ∈ Subalgebra.toSubmodule M * E, y * z ∈ Subalgebra.toSubmodule M * E) ∧
      E ≤ Subalgebra.toSubmodule M * E := by
  refine ⟨fun y hy z hz => ?_, fun z hz => ?_⟩
  · have : y * z ∈ Subalgebra.toSubmodule M * (Subalgebra.toSubmodule M * E) := Submodule.mul_mem_mul hy hz
    rwa [← mul_assoc, M.isIdempotentElem_toSubmodule.eq] at this
  · have : 1 * z ∈ Subalgebra.toSubmodule M * E := Submodule.mul_mem_mul M.one_mem hz
    rwa [one_mul] at this

theorem UpperTheory.V.Pa.trLat :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] [Algebra S.x.A R] [IsScalarTower S.x.A S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → ∃ M : Subalgebra S.x.A R, Module.Finite S.x.A M ∧ (∀ b : S.B, θ (algebraMap S.B S.U.AA b) ∈ M) ∧ (∀ g i j, θ (S.U.vr g i j) ∈ M) ∧ (∀ j : ℕ, ∃ j' : ℕ, ∀ b ∈ maximalIdeal S.B ^ j', ∃ y ∈ M, θ (algebraMap S.B S.U.AA b) = S.x.t ^ j • y) ∧ ∃ P : Submodule S.x.A R, P.FG ∧ (∀ p ∈ S.U.P, ∀ i j, θ (p i j) ∈ P) ∧ ∀ y ∈ M, ∀ z ∈ P, y * z ∈ P := by
  intro l _ S R _ _ _ _ e θ T
  classical
  obtain ⟨N, hN⟩ := T.nil
  haveI : Nontrivial R := e.toRingHom.domain_nontrivial
  haveI : IsNoetherianRing S.B := inferInstance
  let φ : S.B →+* R := θ.comp (algebraMap S.B S.U.AA)
  have hφ : ∀ b, φ b = θ (algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh b)) := fun b => by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have heA : ∀ a : S.x.A, e (algebraMap S.x.A R a) = algebraMap S.x.A S.F a := fun a => by
    rw [IsScalarTower.algebraMap_apply S.x.A S.F R, AlgHom.commutes]; rfl
  have h1 : ∀ a, ∃ b, φ b = algebraMap S.x.A R a ∧ S.P.f.toRingHom b = a := by
    intro a
    obtain ⟨o, b, ho, hb⟩ := S.oo_A a
    refine ⟨b, ?_, hb⟩
    rw [hφ, ← ho, T.oo, ho, S.rF_f, hb, ← IsScalarTower.algebraMap_apply]
  have h2 : ∀ b, φ b - algebraMap S.x.A R (S.P.f.toRingHom b) ∈ RingHom.ker e := by
    intro b
    have := ((prAdd l S).2.1 (algebraMap S.B S.Bh b) 0).1
    rw [Submodule.coe_zero, add_zero] at this
    rw [RingHom.mem_ker, map_sub, heA, hφ, T.res, this, S.rF_f, sub_eq_zero]
    rfl
  obtain ⟨M0, hM0, hM0'⟩ := trLat_range φ S.P.f.toRingHom (RingHom.ker e) N hN h1 h2
  obtain ⟨r, p, hp⟩ := Submodule.fg_iff_exists_fin_generating_family.1 S.U.ker_le_span_sub_sup_map
  let E : Submodule S.x.A R := Submodule.span S.x.A (Set.range fun q : Fin r × Fin S.n × Fin S.n => θ (p q.1 q.2.1 q.2.2))
  have hE : E.FG := Submodule.fg_span (Set.finite_range _)
  have hP : ∀ M : Subalgebra S.x.A R, (∀ b, φ b ∈ M) → ∀ z ∈ S.U.P, ∀ i j, θ (z i j) ∈ Subalgebra.toSubmodule M * E := by
    intro M hM z hz i j
    rw [← hp] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨k, rfl⟩ := hz
      exact (trLat_mul M E).2 (Submodule.subset_span ⟨(k, i, j), rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_apply, map_add]; exact add_mem hx hy
    | smul b x _ hx =>
      rw [Matrix.smul_apply, Algebra.smul_def, map_mul]
      exact (trLat_mul M E).1 _ (hM b) _ hx
  let Q : Submodule S.x.A R := Subalgebra.toSubmodule M0 ⊔ Subalgebra.toSubmodule M0 * E
  have hQ : Q.FG := hM0.sup (hM0.mul hE)
  let P0 : Submodule S.x.A R := Q ⊓ ((1 : Submodule S.x.A R) ⊔ (RingHom.ker e).restrictScalars S.x.A)
  have hP0 : P0.FG := hQ.of_le inf_le_left
  have hmem : ∀ y ∈ Q, ∀ a : S.x.A, y - algebraMap S.x.A R a ∈ RingHom.ker e → y ∈ P0 := by
    intro y hy a ha
    refine ⟨hy, Submodule.mem_sup.2 ⟨algebraMap S.x.A R a, Submodule.mem_one.2 ⟨a, rfl⟩, _, ha, by ring⟩⟩
  have hnil : ∀ y ∈ P0, ∃ a : S.x.A, IsNilpotent (y - algebraMap S.x.A R a) := by
    intro y hy
    obtain ⟨u, hu, z, hz, rfl⟩ := Submodule.mem_sup.1 hy.2
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 hu
    refine ⟨a, N, ?_⟩
    have := Ideal.pow_mem_pow (I := RingHom.ker e) hz N
    rw [hN, Ideal.mem_bot] at this
    rwa [add_sub_cancel_left]
  have hfin := (adjoin_nil_finite P0 hP0 hnil).1
  have hB : ∀ b, φ b ∈ Algebra.adjoin S.x.A (P0 : Set R) := fun b =>
    Algebra.subset_adjoin (hmem _ (Submodule.mem_sup_left (hM0' b)) _ (h2 b))
  refine ⟨Algebra.adjoin S.x.A (P0 : Set R), hfin, hB, fun g i j => ?_, fun j => ⟨j + N, ?_⟩,
    Subalgebra.toSubmodule (Algebra.adjoin S.x.A (P0 : Set R)) * E, (Module.Finite.iff_fg.1 hfin).mul hE, hP _ hB,
    (trLat_mul _ E).1⟩
  · refine Algebra.subset_adjoin (hmem _ (Submodule.mem_sup_right (hP M0 hM0' _ (S.U.vr_mem g) i j))
      (mat S.x.ρ (S.h.p₀ g) i j) ?_)
    rw [RingHom.mem_ker, map_sub, heA, T.res, (prVr l S g i j).1, sub_eq_zero]
    rfl
  · exact trLat_pow S.x.t PowerSeries.maximalIdeal_eq_span_X.le φ S.P.f.toRingHom (RingHom.ker e) N hN
      (fun a => (h1 a).imp fun _ h => h.2) h2 _ hB j
