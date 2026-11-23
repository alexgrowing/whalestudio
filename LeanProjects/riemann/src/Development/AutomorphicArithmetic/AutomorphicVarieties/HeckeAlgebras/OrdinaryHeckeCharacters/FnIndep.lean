import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter

open IsLocalRing Matrix UpperTheory.V.Hi

theorem UpperTheory.V.Hi.fnIndep :
    ∀ (O Ω S ι : Type) [CommRing O] [IsDomain O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ∀ (m : ℕ) (v : ι → S → Fin m → O), LinearIndependent O v → LinearIndependent Ω fun i s j => algebraMap O Ω (v i s j) := by
  intro O Ω S ι _ _ _ _ hinj m v hv
  classical
  letI : Algebra (FractionRing O) Ω := (IsFractionRing.lift hinj).toAlgebra
  have htow : ∀ x : O, algebraMap O Ω x =
      algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) x) :=
    fun x => (IsFractionRing.lift_algebraMap hinj x).symm
  have hu : LinearIndependent (FractionRing O)
      (fun i s j => algebraMap O (FractionRing O) (v i s j)) := by
    rw [← LinearIndependent.iff_fractionRing O (FractionRing O)]
    have hf : Function.Injective
        (((Algebra.linearMap O (FractionRing O)).compLeft (Fin m)).compLeft S) := by
      intro a c hac
      funext s j
      exact IsFractionRing.injective O (FractionRing O) (congrFun (congrFun hac s) j)
    exact hv.map' _ (LinearMap.ker_eq_bot.mpr hf)
  let b := Module.Free.chooseBasis (FractionRing O) Ω
  rw [linearIndependent_iff'] at hu ⊢
  intro s g hg i hi
  refine b.ext_elem fun k => ?_
  rw [map_zero, Finsupp.zero_apply]
  refine hu s (fun i => b.repr (g i) k) ?_ i hi
  funext x y
  have h := congrFun (congrFun hg x) y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h ⊢
  have h2 := congrArg (fun z => b.repr z k) h
  simp only [map_sum, map_zero, Finsupp.coe_finset_sum, Finset.sum_apply,
    Finsupp.zero_apply] at h2
  rw [← h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : g i * algebraMap (FractionRing O) Ω (algebraMap O (FractionRing O) (v i x y)) =
      algebraMap O (FractionRing O) (v i x y) • g i := by
    rw [Algebra.smul_def, mul_comm]
  rw [htow, e, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
