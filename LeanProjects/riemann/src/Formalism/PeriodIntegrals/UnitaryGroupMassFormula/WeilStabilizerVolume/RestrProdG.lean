import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProdSt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.PosNear
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensFibV

noncomputable section

namespace PI.VolStabW.RestrProdG

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct

section Maps

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S]

theorem map_sigR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) (z : R ⊗[F] E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (sigR R σ z) =
      sigR S σ (Algebra.TensorProduct.map f (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem map_inclR (f : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR, Algebra.TensorProduct.map_tmul]

theorem map_gramR (f : R →ₐ[F] S) (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (x y : Fin n) :
    Algebra.TensorProduct.map f (AlgHom.id F E) (gramR R σ J X x y) =
      gramR S σ J (fun x i => Algebra.TensorProduct.map f (AlgHom.id F E) (X x i)) x y := by
  simp only [gramR, hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, map_sigR,
    map_inclR]

end Maps

theorem t2_tensor_product {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by
  let b := Module.finBasis F E
  refine T2Space.of_injective_continuous
    (f := fun y : R ⊗[F] E => fun k => PositiveNearLattice.crd b R y k) ?_
    (continuous_pi fun k => PositiveNearLattice.continuous_crd b R k)
  intro y y' h
  have h' : ∀ k, PositiveNearLattice.crd b R y k = PositiveNearLattice.crd b R y' k := fun k => congrFun h k
  rw [PositiveNearLattice.eq_sum_crd b R y, PositiveNearLattice.eq_sum_crd b R y']
  simp only [h']

theorem rpGram_holds : RPGram := by
  intro F E _ _ _ _ _ σ M J a T
  let b := Module.finBasis F E
  refine ⟨?_, ?_, fun v => ?_, ?_⟩
  · have : T2Space (AF F ⊗[F] E) := t2_tensor_product (AF F)
    have : T2Space (Matrix (Fin a) (Fin a) (AF F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → AF F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (AF F) σ J)).isOpen_compl.measurableSet
  · have : T2Space (Ainf F ⊗[F] E) := t2_tensor_product (Ainf F)
    have : T2Space (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Ainf F ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Ainf F) σ J)).measurableSet
  · have : LocallyCompactSpace (Fv F v) := locallyCompact_Fv F v
    have : T2Space (Fv F v ⊗[F] E) := t2_tensor_product (Fv F v)
    have : T2Space (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (T2Space (Fin a → Fin a → Fv F v ⊗[F] E))
    exact (isClosed_singleton.preimage (continuous_gramR (Fv F v) σ J)).measurableSet
  · intro X hI hV
    have key : ∀ w w' : AF F ⊗[F] E,
        Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w =
          Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) w' →
        (∀ v, Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w) =
          Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)
            (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) w')) → w = w' := by
      intro w w' h1 h2
      rw [PositiveNearLattice.eq_sum_crd b (AF F) w, PositiveNearLattice.eq_sum_crd b (AF F) w']
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      have e1 := congrArg (fun u => PositiveNearLattice.crd b (Ainf F) u k) h1
      simp only [PositiveNearLattice.crd_map] at e1
      refine Prod.ext e1 (FiniteAdeleRing.ext (K := F) fun v => ?_)
      have e2 := congrArg (fun u => PositiveNearLattice.crd b (Fv F v) u k) (h2 v)
      simp only [PositiveNearLattice.crd_map] at e2
      exact e2
    funext x y
    refine key _ _ ?_ fun v => ?_
    · rw [map_gramR, Matrix.map_apply, map_inclR]
      exact congrFun (congrFun hI x) y
    · rw [map_gramR, map_gramR, Matrix.map_apply, map_inclR, map_inclR]
      exact congrFun (congrFun (hV v) x) y

end PI.VolStabW.RestrProdG
