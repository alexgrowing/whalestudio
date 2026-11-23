import Mathlib

namespace GroundTheory.Global

open IsDedekindDomain NumberField

noncomputable section

namespace SemiLocal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (L) in

abbrev PlacesOver (v : HeightOneSpectrum (𝓞 K)) : Type _ :=
  {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal}

instance (v : HeightOneSpectrum (𝓞 K)) (w : PlacesOver L v) : w.1.asIdeal.LiesOver v.asIdeal :=
  w.2

variable (L) in

def placesOverEquiv (v : HeightOneSpectrum (𝓞 K)) :
    PlacesOver L v ≃ v.asIdeal.primesOver (𝓞 L) where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun P := ⟨⟨P.1, P.2.1, (have := P.2.2; Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P.1)⟩, P.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (v : HeightOneSpectrum (𝓞 K)) : Fintype (PlacesOver L v) :=
  Fintype.ofEquiv _ (placesOverEquiv L v).symm

section Map

variable (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

def completionMap : v.adicCompletion K →+* w.adicCompletion L :=
  (HeightOneSpectrum.adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w).continuous).comp
      (HeightOneSpectrum.adicCompletion.equiv K v).toRingHom

theorem continuous_completionMap : Continuous (completionMap v w) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion L w).comp <|
    UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v)

theorem completionMap_algebraMap (x : K) :
    completionMap v w (algebraMap K (v.adicCompletion K) x) =
      algebraMap K (w.adicCompletion L) x := by
  apply HeightOneSpectrum.adicCompletion.ext
  change UniformSpace.Completion.map _
      ((algebraMap K (WithVal (v.valuation K)) x : WithVal _) :
        UniformSpace.Completion (WithVal (v.valuation K))) =
    ((algebraMap K (WithVal (w.valuation L)) x : WithVal _) :
        UniformSpace.Completion (WithVal (w.valuation L)))
  rw [UniformSpace.Completion.map_coe
    (HeightOneSpectrum.uniformContinuous_algebraMap_liesOver (K := K) L v w)]
  rfl

theorem valued_completionMap (x : v.adicCompletion K) :
    Valued.v (completionMap v w x) = Valued.v x ^ w.asIdeal.ramificationIdx (𝓞 K) := by
  set e := w.asIdeal.ramificationIdx (𝓞 K) with he
  have he0 : e ≠ 0 := (Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)).ne'
  have hK : ∀ k : K, Valued.v (completionMap v w (algebraMap K _ k)) =
      Valued.v (algebraMap K (v.adicCompletion K) k) ^ e := by
    intro k
    rw [completionMap_algebraMap, IsScalarTower.algebraMap_apply K L (w.adicCompletion L),
      HeightOneSpectrum.algebraMap_adicCompletion, HeightOneSpectrum.algebraMap_adicCompletion]
    simp only [Function.comp_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    rw [he, ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
      HeightOneSpectrum.valuation_liesOver L v w]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  have hclosed : IsClosed
      {x : v.adicCompletion K | Valued.v (completionMap v w x) = Valued.v x ^ e} := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro x0 hx0
    have h0 : x0 ≠ 0 := by
      rintro rfl
      simp [zero_pow he0] at hx0
    have h1 : Valued.v x0 ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    have h2 : Valued.v (completionMap v w x0) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 ((map_ne_zero_iff _ (completionMap v w).injective).2 h0)
    filter_upwards [Valued.locally_const h1,
      (continuous_completionMap v w).continuousAt.preimage_mem_nhds (Valued.locally_const h2)]
      with x hx hx'
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_compl_iff] at hx hx' hx0 ⊢
    rwa [hx, hx']
  exact (HeightOneSpectrum.denseRange_algebraMap K v).induction_on x hclosed hK

scoped instance algebraCompletion : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionMap v w).toAlgebra

theorem algebraMap_completion_eq :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = completionMap v w := rfl

scoped instance : IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ (completionMap_algebraMap v w x).symm

scoped instance : ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) where
  continuous_smul := ((continuous_completionMap v w).comp continuous_fst).mul continuous_snd

end Map

end SemiLocal

end

end GroundTheory.Global
