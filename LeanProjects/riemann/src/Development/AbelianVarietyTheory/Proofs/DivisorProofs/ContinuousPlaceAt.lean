import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.PlaceCoordsF

variable {F : Type} [Field F] [NumberField F]

def placeAt (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) : AF F := pairA F 0 (GlobalTheory.AdelicU.singleFin v x)

theorem placeAt_add (v : HeightOneSpectrum (𝓞 F)) (x y : Fv F v) :
    placeAt v (x + y) = placeAt v x + placeAt v y := by
  unfold placeAt pairA
  rw [map_add]
  exact Prod.ext (add_zero 0).symm rfl

theorem placeAt_injective (v : HeightOneSpectrum (𝓞 F)) : Function.Injective (placeAt v) := by
  intro x y h
  have h2 := congrArg (fun c : AF F => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) h
  simpa only [placeAt, pairA, GlobalTheory.AdelicU.evalV_singleFin_self] using h2

theorem continuous_placeAt (v : HeightOneSpectrum (𝓞 F)) : Continuous (placeAt v) := by
  unfold placeAt pairA
  exact continuous_const.prodMk (GlobalTheory.AdelicU.continuous_singleFin v)

theorem eq_placeAt_of_mul {v : HeightOneSpectrum (𝓞 F)} {α : Af F} (hα1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v α = 1)
    (hα0 : ∀ v', v' ≠ v → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v' α = 0) {c : AF F} (hc : pairA F 0 α * c = c) :
    c = placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v c.2) := by
  have h1 : c.1 = 0 := by
    have := congrArg Prod.fst hc
    rw [← this]
    exact zero_mul _
  have h2 : α * c.2 = c.2 := congrArg Prod.snd hc
  refine Prod.ext h1 ?_
  show c.2 = GlobalTheory.AdelicU.singleFin v _
  refine GlobalTheory.AdelicU.af_ext fun u => ?_
  by_cases hu : u = v
  · subst hu
    rw [GlobalTheory.AdelicU.evalV_singleFin_self]
  · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hu, ← h2, map_mul, hα0 u hu, zero_mul]

end GlobalTheory.PlaceCoordsF

namespace GlobalTheory.PlaceCoordsF

theorem coords_at_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (ε : AF F), IsPlaceIdemF F v ε → ∀ nS nT : ℕ,
      ∃ (N : ℕ) (Φ : (Fin N → v.adicCompletion F) →+ WOF F E nS nT), Continuous Φ ∧ Function.Injective Φ ∧
        ∀ y : WOF F E nS nT, (∀ i j, algebraMap (AF F) (AEF F E) ε * y i j = y i j) → y ∈ Set.range Φ := by
  intro F E _ _ _ _ _ v ε hε nS nT
  obtain ⟨α, rfl, hα1, hα0⟩ := hε
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AEF F E) := ⟨rfl⟩
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  let B : Module.Basis (Fin (Module.finrank F E)) (AF F) (AEF F E) :=
    Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let e := Fintype.equivFin (Fin nT × Fin nS × Fin (Module.finrank F E))
  let f : (Fin (Fintype.card (Fin nT × Fin nS × Fin (Module.finrank F E))) → v.adicCompletion F) → WOF F E nS nT :=
    fun t i j => B.equivFun.symm (fun l => placeAt v (t (e (i, j, l))))
  have hadd : ∀ s t, f (s + t) = f s + f t := by
    intro s t
    funext i j
    show B.equivFun.symm _ = B.equivFun.symm _ + B.equivFun.symm _
    rw [← map_add]
    congr 1
    funext l
    exact placeAt_add v _ _
  let Φ := AddMonoidHom.mk' f hadd
  refine ⟨_, Φ, ?_, ?_, ?_⟩
  · have hB : Continuous B.equivFun.symm := IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
    exact continuous_pi fun i => continuous_pi fun j =>
      hB.comp (continuous_pi fun l => (continuous_placeAt v).comp (continuous_apply _))
  · intro s t hst
    have key : ∀ i j l, s (e (i, j, l)) = t (e (i, j, l)) := by
      intro i j l
      have h1 : f s i j = f t i j := congrFun (congrFun hst i) j
      have h2 := congrFun (B.equivFun.symm.injective h1) l
      exact placeAt_injective v h2
    funext k
    have := key (e.symm k).1 (e.symm k).2.1 (e.symm k).2.2
    simpa only [Prod.mk.eta, Equiv.apply_symm_apply] using this
  · intro y hy
    have hc : ∀ i j l, B.equivFun (y i j) l =
        placeAt v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y i j) l).2) := by
      intro i j l
      refine eq_placeAt_of_mul hα1 hα0 ?_
      have h1 : pairA F 0 α • y i j = y i j := by rw [Algebra.smul_def]; exact hy i j
      have h2 := congrFun (congrArg B.equivFun h1) l
      rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
      exact h2
    refine ⟨fun k => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (B.equivFun (y (e.symm k).1 (e.symm k).2.1) (e.symm k).2.2).2, ?_⟩
    funext i j
    show B.equivFun.symm _ = y i j
    simp only [Equiv.symm_apply_apply]
    rw [← B.equivFun.symm_apply_apply (y i j)]
    congr 1
    funext l
    rw [B.equivFun.symm_apply_apply]
    exact (hc i j l).symm

end GlobalTheory.PlaceCoordsF
