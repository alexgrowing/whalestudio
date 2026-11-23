import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.TrLatRange
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem krull_sub {A R : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [Algebra A R]
    (M : Subalgebra A R) [Module.Finite A M] (t : A) (ht : t ∈ maximalIdeal A) (d : R)
    (h : ∀ j : ℕ, ∃ y ∈ M, d = t ^ j • y) : d = 0 := by
  have hI : Ideal.span {t} ≠ ⊤ := fun h1 =>
    (mem_maximalIdeal t).1 ht (Ideal.span_singleton_eq_top.1 h1)
  obtain ⟨y0, hy0, hd0⟩ := h 0
  have hdM : d ∈ M := by simpa [hd0] using hy0
  have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M) (Ideal.span {t}) hI
  have hmem : (⟨d, hdM⟩ : M) ∈ (⨅ i : ℕ, (Ideal.span {t}) ^ i • ⊤ : Submodule A M) := by
    rw [Submodule.mem_iInf]
    intro j
    obtain ⟨y, hy, hd⟩ := h j
    have e : (⟨d, hdM⟩ : M) = t ^ j • (⟨y, hy⟩ : M) := Subtype.ext hd
    rw [e, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  rw [key, Submodule.mem_bot] at hmem
  exact congrArg Subtype.val hmem

private theorem f_local {O B K : Type} [CommRing O] [CommRing B] [IsLocalRing B] [Algebra O B] [Field K] [Algebra O K]
    (hs : Function.Surjective (algebraMap O K)) (f : B →ₐ[O] PowerSeries K) (j : ℕ) (b : B)
    (hb : b ∈ maximalIdeal B ^ j) : ∃ c, f b = PowerSeries.X ^ j * c := by
  set φ : B →+* K := PowerSeries.constantCoeff.comp f.toRingHom with hφdef
  have hφ : Function.Surjective φ := fun k => by
    obtain ⟨o, rfl⟩ := hs k
    exact ⟨algebraMap O B o, by simp [φ, PowerSeries.algebraMap_apply]⟩
  have hker : RingHom.ker φ = maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective φ hφ)
  have hm : Ideal.map f (maximalIdeal B) ≤ Ideal.span {PowerSeries.X} := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [← hker, RingHom.mem_ker] at hy
    rw [Ideal.mem_comap, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    exact hy
  have hfb : f b ∈ Ideal.span {(PowerSeries.X : PowerSeries K) ^ j} := by
    rw [← Ideal.span_singleton_pow]
    refine Ideal.pow_right_mono hm j ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem f hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hfb
  exact ⟨c, by rw [← hc, mul_comm]⟩

theorem UpperTheory.V.Pa.trConst :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ (R : Type) [CommRing R] [Algebra S.F R] (e : R →ₐ[S.F] S.F) (θ : S.U.AA →+* R), S.Test R e θ → (∀ b ∈ pairVals S.u ∪ {b | ∃ j i, b = S.P.U j i ∨ b = S.P.y j i} ∪ {S.P.s}, θ (algebraMap S.B S.U.AA b) = algebraMap S.F R (algebraMap S.x.A S.F (S.P.f b))) → ∀ b : S.Bh, θ (algebraMap S.Bh S.U.AA b) = algebraMap S.F R (S.rF b) := by
  intro l _ S R _ _ e θ hT hgen b
  letI : Algebra S.x.A R := ((algebraMap S.F R).comp (algebraMap S.x.A S.F)).toAlgebra
  haveI : IsScalarTower S.x.A S.F R := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨M, hMfin, -, -, hMj, -⟩ := trLat l S R e θ hT
  have htow : ∀ y : S.B, algebraMap S.B S.U.AA y = algebraMap S.Bh S.U.AA (algebraMap S.B S.Bh y) :=
    fun y => by first | rfl | exact IsScalarTower.algebraMap_apply _ _ _ _
  set ψ1 : S.B →+* R := θ.comp (algebraMap S.B S.U.AA) with hψ1
  set ψ2 : S.B →+* R :=
    (algebraMap S.F R).comp ((algebraMap S.x.A S.F).comp S.P.f.toRingHom) with hψ2
  have hO : ∀ c : S.O, ψ1 (algebraMap S.O S.B c) = ψ2 (algebraMap S.O S.B c) := by
    intro c
    obtain ⟨o, ho⟩ := S.oo_O c
    have h1 := hT.oo o
    rw [ho] at h1
    show θ (algebraMap S.B S.U.AA _) = algebraMap S.F R (algebraMap S.x.A S.F (S.P.f _))
    rw [htow, h1, S.rF_f]
  have hadj : ∀ a ∈ Algebra.adjoin S.O
      (pairVals S.u ∪ {b | ∃ j i, b = S.P.U j i ∨ b = S.P.y j i} ∪ {S.P.s}), ψ1 a = ψ2 a := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem y hy => exact hgen y hy
    | algebraMap c => exact hO c
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]
  have ht : S.x.t ∈ maximalIdeal S.x.A := by
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hB : ∀ y : S.B, ψ1 y = ψ2 y := by
    intro y
    refine sub_eq_zero.1 (krull_sub M S.x.t ht (ψ1 y - ψ2 y) ?_)
    intro j
    obtain ⟨j', hj'⟩ := hMj j
    obtain ⟨a, ha, hya⟩ := S.P.gen (max j j') y
    have hm' : y - a ∈ maximalIdeal S.B ^ j' := Ideal.pow_le_pow_right (le_max_right _ _) hya
    have hm : y - a ∈ maximalIdeal S.B ^ j := Ideal.pow_le_pow_right (le_max_left _ _) hya
    obtain ⟨z, hz, hze⟩ := hj' (y - a) hm'
    obtain ⟨c, hc⟩ := f_local S.P.surj S.P.f j (y - a) hm
    refine ⟨z - algebraMap S.x.A R c, M.sub_mem hz (M.algebraMap_mem c), ?_⟩
    have e1 : ψ1 y - ψ2 y = ψ1 (y - a) - ψ2 (y - a) := by
      rw [map_sub, map_sub, hadj a ha]
      ring
    rw [e1, smul_sub, ← hze]
    congr 1
    show algebraMap S.F R (algebraMap S.x.A S.F (S.P.f (y - a))) = _
    rw [hc, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    simp [map_mul, map_pow]
  obtain ⟨N, hN⟩ := hT.nil
  have hker : ∀ m ∈ maximalIdeal S.Bh, e (θ (algebraMap S.Bh S.U.AA m)) = 0 := by
    intro m hm
    have hp : S.pr0 (algebraMap S.Bh S.U.AA m) = m := by
      simpa using ((prAdd l S).2.1 m 0).1
    rw [hT.res, hp]
    have hm2 : m ∈ RingHom.ker S.rF := by rw [S.rF_ker]; exact hm
    exact (RingHom.mem_ker).1 hm2
  have hkill : ∀ m ∈ maximalIdeal S.Bh ^ N, θ (algebraMap S.Bh S.U.AA m) = 0 := by
    intro m hm
    have h1 : Ideal.map (θ.comp (algebraMap S.Bh S.U.AA)) (maximalIdeal S.Bh) ≤ RingHom.ker e := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact (RingHom.mem_ker).2 (hker y hy)
    have h2 : θ.comp (algebraMap S.Bh S.U.AA) m ∈ RingHom.ker e ^ N := by
      refine Ideal.pow_right_mono h1 N ?_
      rw [← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ hm
    rw [hN, Ideal.mem_bot] at h2
    exact h2
  have hmax : ∀ m ∈ maximalIdeal S.Bh, θ (algebraMap S.Bh S.U.AA m) = 0 := by
    intro m hm
    obtain ⟨a, s, hs, hsa⟩ := S.cpl.dense N m
    have e1 := hkill _ hsa
    simp only [map_sub, map_mul, sub_eq_zero, ← htow] at e1
    have e2 : ψ2 s * θ (algebraMap S.Bh S.U.AA m) = ψ2 a := by
      rw [← hB, ← hB]
      exact e1
    set u := algebraMap S.x.A S.F (S.P.f s) with hudef
    have hu : u ≠ 0 := fun h0 =>
      hs ((RingHom.mem_ker).2 (IsFractionRing.injective S.x.A S.x.Fr (h0.trans (map_zero _).symm)))
    have e3 : θ (algebraMap S.Bh S.U.AA m) =
        algebraMap S.F R (u⁻¹ * algebraMap S.x.A S.F (S.P.f a)) := by
      calc θ (algebraMap S.Bh S.U.AA m)
          = algebraMap S.F R (u⁻¹ * u) * θ (algebraMap S.Bh S.U.AA m) := by
            rw [inv_mul_cancel₀ hu, map_one, one_mul]
        _ = _ := by
            rw [map_mul, mul_assoc, map_mul]
            exact congrArg _ e2
    have e4 := hker m hm
    rw [e3, AlgHom.commutes] at e4
    have e5 : u⁻¹ * algebraMap S.x.A S.F (S.P.f a) = 0 := e4
    rw [e3, e5, map_zero]
  obtain ⟨o, ho⟩ := S.oo_surj (S.rF b)
  simp only [RingHom.comp_apply] at ho
  have hm : b - algebraMap S.OO S.Bh o ∈ maximalIdeal S.Bh := by
    rw [← S.rF_ker, RingHom.mem_ker, map_sub, ho, sub_self]
  have hb := hmax _ hm
  rw [map_sub, map_sub, sub_eq_zero, hT.oo o, ho] at hb
  exact hb
