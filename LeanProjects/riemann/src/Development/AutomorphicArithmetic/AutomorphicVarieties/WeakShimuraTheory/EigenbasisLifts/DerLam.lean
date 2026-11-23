import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.IsTanZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DerZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.DerHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem derLam_dense {O : Type} [CommRing O] [IsLocalRing O] {σ : Type} [Finite σ] (n : ℕ)
    (a : MvPowerSeries σ O) :
    ∃ b ∈ Algebra.adjoin O (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)),
      a - b ∈ maximalIdeal (MvPowerSeries σ O) ^ n := by
  have hX : ∀ i : σ, (AlgHom.id O (MvPowerSeries σ O)) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries σ O) := by
    intro i
    rw [AlgHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have key := GlobalTheory.algHom_sub_aeval_truncTotal_mem (AlgHom.id O (MvPowerSeries σ O)) hX n a
  simp only [AlgHom.id_apply] at key
  refine ⟨_, ?_, key⟩
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨_, rfl⟩

private theorem ptDer_eq_zero_of_vanish_on_X {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ)
    (x : MvPowerSeries (Fin N) c.O →ₐ[c.O] PadicAlgCl l)
    (D : MvPowerSeries (Fin N) c.O →ₗ[c.O] PadicAlgCl l) (hD : D ∈ PtDer x (PadicAlgCl l))
    (h0 : ∀ i, D (MvPowerSeries.X i) = 0) (a : MvPowerSeries (Fin N) c.O) : D a = 0 := by
  have hmul : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have h1 : D 1 = 0 := by
    have h := hmul 1 1
    simp only [mul_one, map_one, one_smul] at h
    linear_combination (-1 : PadicAlgCl l) * h
  let y : MvPowerSeries (Fin N) c.O →ₐ[c.O] DualNumber (PadicAlgCl l) :=
    { toFun := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (D f)
      map_one' := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h1]
      map_mul' := by
        intro f g
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
            add_zero, zero_add, hmul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
          ring
      map_zero' := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp
      map_add' := by
        intro f g
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp <;> ring
      commutes' := by
        intro r
        refine TrivSqZeroExt.ext ?_ ?_
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
            AlgHom.commutes]
          rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r]
          rfl
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
          rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r, map_smul, h1,
            smul_zero]
          show (0 : PadicAlgCl l) = r • (0 : PadicAlgCl l)
          rw [smul_zero] }
  haveI := co_mvps c.O c.O (Fin N)
  have key := derZero c (MvPowerSeries (Fin N) c.O) y (Set.range MvPowerSeries.X)
    (fun n b => derLam_dense n b) (by rintro _ ⟨i, rfl⟩; simp [y, h0]) a
  simpa [y] using key

theorem UpperTheory.V.Ws.Eb.derLam :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (x : MvPowerSeries (Fin N) c.O →ₐ[c.O] PadicAlgCl l), Module.rank (PadicAlgCl l) (PtDer x (PadicAlgCl l)) ≤ N := by
  intro l _ c N x
  let Φ : PtDer x (PadicAlgCl l) →ₗ[PadicAlgCl l] (Fin N → PadicAlgCl l) :=
    { toFun := fun D i => (D : MvPowerSeries (Fin N) c.O →ₗ[c.O] PadicAlgCl l) (MvPowerSeries.X i)
      map_add' := by
        intro D D'
        rfl
      map_smul' := by
        intro k D
        rfl }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro D hD
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact ptDer_eq_zero_of_vanish_on_X c N x D D.2 (fun i => congrFun hD i) a
  calc Module.rank (PadicAlgCl l) (PtDer x (PadicAlgCl l))
      ≤ Module.rank (PadicAlgCl l) (Fin N → PadicAlgCl l) := LinearMap.rank_le_of_injective Φ hinj
    _ = N := by simp
