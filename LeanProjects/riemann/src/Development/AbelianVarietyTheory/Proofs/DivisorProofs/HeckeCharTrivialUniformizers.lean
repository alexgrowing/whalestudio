import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DenseRangeUnits
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology

open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

noncomputable section

namespace GlobalTheory.HeckeUnifApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Inf

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def swapL : (InfiniteAdeleRing F ⊗[F] E) →ₗ[InfiniteAdeleRing F] (E ⊗[F] InfiniteAdeleRing F) where
  toFun := Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E
  map_add' := map_add _
  map_smul' c t := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

def swapR : (E ⊗[F] InfiniteAdeleRing F) →ₗ[InfiniteAdeleRing F] (InfiniteAdeleRing F ⊗[F] E) where
  toFun := Algebra.TensorProduct.comm F E (InfiniteAdeleRing F)
  map_add' := map_add _
  map_smul' c t := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1

theorem exists_infinite_equiv :
    ∃ j : (Ainf F ⊗[F] E) ≃+* InfiniteAdeleRing E, Continuous j ∧ Continuous j.symm ∧
      ∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x := by
  letI tB : TopologicalSpace (E ⊗[F] InfiniteAdeleRing F) := moduleTopology (InfiniteAdeleRing F) _
  haveI : IsModuleTopology (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F) := ⟨rfl⟩
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F)
  haveI := IsModuleTopology.toContinuousSMul (InfiniteAdeleRing F) (E ⊗[F] InfiniteAdeleRing F)
  haveI := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI := IsModuleTopology.toContinuousSMul (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  have hL : Continuous (swapL (F := F) (E := E)) := IsModuleTopology.continuous_of_linearMap _
  have hR : Continuous (swapR (F := F) (E := E)) := IsModuleTopology.continuous_of_linearMap _
  let h := GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingHomeomorph (K := F) (L := E)
  refine ⟨(Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E).toRingEquiv.trans
    (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv (K := F) (L := E)).toRingEquiv, ?_, ?_, ?_⟩
  · exact h.continuous.comp hL
  · exact hR.comp h.symm.continuous
  · intro x
    change GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv
      (Algebra.TensorProduct.comm F (InfiniteAdeleRing F) E ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x)) = _
    rw [Algebra.TensorProduct.comm_tmul, GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul', map_one,
      mul_one]

end Inf

open GlobalTheory.LFun in

theorem exists_tensor_adele_equiv :
    ∃ (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) (j : Ainf F ⊗[F] E ≃+* InfiniteAdeleRing E),
      Continuous Φ ∧ Continuous Φ.symm ∧ (∀ x : E, j ((1 : Ainf F) ⊗ₜ[F] x) = algebraMap E (InfiniteAdeleRing E) x) ∧
      ∀ z, Φ z = (j (infTens F E z), finAdEquiv F E (finTens F E z)) := by
  obtain ⟨j, hjc, hjc', hj⟩ := exists_infinite_equiv (F := F) (E := E)
  obtain ⟨s, hs, hsc, hsc'⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  refine ⟨s.trans (j.prodCongr (finAdEquiv F E)), j, (hjc.prodMap GlobalTheory.DefU.ClassFin.continuous_finAdEquiv).comp hsc,
    hsc'.comp (hjc'.prodMap continuous_finAdEquiv_symm), hj,
    fun z => Prod.ext (congrArg j (hs z).1) (congrArg (finAdEquiv F E) (hs z).2)⟩

open GlobalTheory.LFun in

theorem exists_hchar (χ : (AF F ⊗[F] E)ˣ →* Circle) (hχ : IsHecke F E χ) :
    ∃ (H : Formalism.L2.Host.HChar E) (u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ),
      (∀ y, H.1 y = Circle.toUnits (χ (u y))) ∧ Function.Surjective u ∧
      ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x := by
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv (F := F) (E := E)
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, u, fun y => rfl, fun g => ⟨Units.map Φ.toRingHom.toMonoidHom g, Units.ext (Φ.symm_apply_apply _)⟩,
    fun W x => ?_⟩
  change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
  rw [hloc]

theorem eq_one_of_unif_cofinite : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (χ : (AF F ⊗[F] E)ˣ →* Circle), GlobalTheory.LFun.IsHecke F E χ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ ϖ, Formalism.L2.Host.IsUnifAt w ϖ → χ (GlobalTheory.LFun.locIdele F w ϖ) = 1) → χ = 1 := by
  intro F E _ _ _ _ _ χ hχ hev
  obtain ⟨H, u, hH, hsurj, hloc⟩ := exists_hchar χ hχ
  have hfin : {w : HeightOneSpectrum (𝓞 E) | ¬ ∀ ϖ, Formalism.L2.Host.IsUnifAt w ϖ →
      χ (GlobalTheory.LFun.locIdele F w ϖ) = 1}.Finite := Filter.eventually_cofinite.1 hev
  have h1 : H.1 = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away H.1 H.2.1 H.2.2 hfin.toFinset fun v hv x => ?_
    have hv' : ∀ ϖ, Formalism.L2.Host.IsUnifAt v ϖ → χ (GlobalTheory.LFun.locIdele F v ϖ) = 1 := by
      simpa using hv
    refine GlobalTheory.FrobDense.eq_one_of_unif (H.1.comp (Neutral.B1.localIdele E v)) (fun y hy => ?_) x
    change H.loc v y = 1
    rw [hloc, GlobalTheory.LFun.locChar, MonoidHom.comp_apply, MonoidHom.comp_apply, hv' y hy, map_one]
  ext g
  obtain ⟨y, rfl⟩ := hsurj g
  have h2 : Circle.toUnits (χ (u y)) = 1 := (hH y).symm.trans (congrFun (congrArg DFunLike.coe h1) y)
  have h3 : ((χ (u y) : Circle) : ℂ) = 1 := by
    have := congrArg (fun z : ℂˣ => (z : ℂ)) h2
    simpa using this
  simpa using h3

end GlobalTheory.HeckeUnifApprox
