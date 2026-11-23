import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.MeasInfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement

noncomputable section

open NumberField Matrix Formalism.L2.SG.AdBridge
open scoped TensorProduct Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.MainNotions.S (AutInst uMat)

namespace Formalism.L2.SG.Pf.MeasInfW

variable (I : AutInst)

abbrev TI : Type := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F ⊗[I.F] I.E

def evI (v : InfinitePlace I.F) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F →+* ℂ :=
  (InfinitePlace.Completion.extensionEmbedding v).comp
    (Pi.evalRingHom (fun w : InfinitePlace I.F => w.Completion) v)

theorem evI_apply (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) :
    evI I v a = InfinitePlace.Completion.extensionEmbedding v (a v) := rfl

theorem evI_algebraMap (v : InfinitePlace I.F) (a : I.F) :
    evI I v (algebraMap I.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) a) = v.embedding a := by
  change InfinitePlace.Completion.extensionEmbedding v (algebraMap I.F v.Completion a) = _
  exact InfinitePlace.Completion.extensionEmbedding_coe v ((WithAbs.equiv v.1).symm a)

def thI (v : InfinitePlace I.F) : TI I →+* ℂ :=
  letI : Algebra I.F ℂ := v.embedding.toAlgebra
  (Algebra.TensorProduct.lift
    ({ evI I v with commutes' := fun a => evI_algebraMap I v a } :
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F →ₐ[I.F] ℂ)
    ({ I.φ v with commutes' := I.φ_over v } : I.E →ₐ[I.F] ℂ)
    (fun _ _ => Commute.all _ _)).toRingHom

theorem thI_tmul (v : InfinitePlace I.F) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (x : I.E) :
    thI I v (a ⊗ₜ[I.F] x) = evI I v a * I.φ v x := by
  simp [thI]

def kap : TT I →+* TI I := Formalism.L2.SG.Measures.tensMap (E := I.E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA I.F)

theorem kap_tmul (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (x : I.E) : kap I (a ⊗ₜ[I.F] x) = a.1 ⊗ₜ[I.F] x := by
  simp [kap, Formalism.L2.SG.Measures.tensMap]
  rfl

theorem thI_kap (v : InfinitePlace I.F) (y : TT I) : thI I v (kap I y) = thetaV I v y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [kap_tmul, thI_tmul, thetaV_tmul]; rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem kap_surj (y : TI I) : ∃ y0 : TT I, kap I y0 = y ∧ tauF I y0 = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp, by simp⟩
  | tmul a x =>
    let a0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F := (a, 0)
    refine ⟨a0 ⊗ₜ[I.F] x, kap_tmul I a0 x, ?_⟩
    rw [tauF_tmul]
    exact TensorProduct.tmul_zero _ _
  | add x y hx hy =>
    obtain ⟨x0, hx0, hx1⟩ := hx
    obtain ⟨y0, hy0, hy1⟩ := hy
    exact ⟨x0 + y0, by rw [map_add, hx0, hy0], by rw [map_add, hx1, hy1, add_zero]⟩

theorem thI_inj (y : TI I) (h : ∀ v, thI I v y = 0) : y = 0 := by
  obtain ⟨y0, rfl, hτ⟩ := kap_surj I y
  have : y0 = 0 := TT_ext I y0 (fun v => by rw [← thI_kap]; exact h v) hτ
  rw [this, map_zero]

theorem thI_ext (y y' : TI I) (h : ∀ v, thI I v y = thI I v y') : y = y' :=
  sub_eq_zero.1 (thI_inj I _ fun v => by rw [map_sub, h v, sub_self])

theorem thI_surj (z : InfinitePlace I.F → ℂ) : ∃ y : TI I, ∀ v, thI I v y = z v := by
  obtain ⟨y0, h1, -⟩ := TT_surj I z 0
  exact ⟨kap I y0, fun v => by rw [thI_kap]; exact h1 v⟩

theorem thI_inclR (v : InfinitePlace I.F) (x : I.E) :
    thI I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) x) = I.φ v x := by
  show thI I v ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) ⊗ₜ[I.F] x) = _
  rw [thI_tmul, map_one, one_mul]

theorem thI_sigR (v : InfinitePlace I.F) (x : TI I) :
    thI I v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig x) =
      starRingEnd ℂ (thI I v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    have hs : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) I.cm.sig (a ⊗ₜ[I.F] y) =
        a ⊗ₜ[I.F] I.cm.sig y := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
    rw [hs, thI_tmul, thI_tmul, map_mul]
    congr 1
    · have hv : v.IsReal := I.cm.totReal.isReal v
      rw [evI_apply, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv, Complex.conj_ofReal]
    · exact I.cm.cmUnram.2.1 (I.φ v) y
  | add x y hx hy => simp only [map_add, hx, hy]

instance imtTI : IsModuleTopology (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I) := ⟨rfl⟩

instance topRingTI : IsTopologicalRing (TI I) :=
  IsModuleTopology.isTopologicalRing (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)

theorem continuous_evI (v : InfinitePlace I.F) : Continuous (evI I v) :=
  (InfinitePlace.Completion.isometry_extensionEmbedding v).continuous.comp (continuous_apply v)

theorem continuous_thI (v : InfinitePlace I.F) : Continuous (thI I v) := by
  apply IsModuleTopology.continuous_of_ringHom (R := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F)
  have : (thI I v).comp (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)) = evI I v := by
    ext a
    simp [Algebra.TensorProduct.algebraMap_apply, thI_tmul]
  rw [this]
  exact continuous_evI I v

theorem continuous_kap : Continuous (kap I) := by
  apply IsModuleTopology.continuous_of_ringHom (R := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F)
  have := IsModuleTopology.toContinuousSMul (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)
  have : (kap I).comp (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF I.F) (TT I)) =
      (algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)).comp
        (RingHom.fst (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (Formalism.MainNotions.S.Af I.F)) := by
    ext a
    show kap I (algebraMap _ _ a) = algebraMap _ (TI I) a.1
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Algebra.algebraMap_self, RingHom.id_apply, kap_tmul]
  rw [this]
  exact (continuous_algebraMap (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf I.F) (TI I)).comp continuous_fst

end Formalism.L2.SG.Pf.MeasInfW
