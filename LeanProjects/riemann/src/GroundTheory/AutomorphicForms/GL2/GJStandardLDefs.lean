import Mathlib
import GroundTheory.AutomorphicForms.GL2.GJGlobal
import GroundTheory.AutomorphicForms.GL2.GJStandardLUnramified
import GroundTheory.AutomorphicForms.GL2.GJLocalFEGamma
import GroundTheory.AutomorphicForms.GL2.GJFEInduced
import GroundTheory.AutomorphicForms.GL2.GJFELevi
import GroundTheory.AutomorphicForms.GL2.FiniteIdeleDecomp
import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
import GroundTheory.AutomorphicForms.GL2.GJFEInducedLevi
import GroundTheory.AutomorphicForms.RestrictedHaarProduct
import GroundTheory.GlobalFields.LocalFieldAtPlace

open MeasureTheory Filter Set Topology IsDedekindDomain NumberField NumberField.mixedEmbedding
open scoped NumberField.AdeleRing RestrictedProduct SchwartzMap Classical

namespace GroundTheory.Automorphic

noncomputable section

namespace GJStandardL

open GodementJacquet GLnLocal

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

instance measurableSpace_infiniteAdelicGL : MeasurableSpace (AdelicGLn.InfiniteAdelicGL K n) := _root_.borel _

instance borelSpace_infiniteAdelicGL : BorelSpace (AdelicGLn.InfiniteAdelicGL K n) := ⟨rfl⟩

variable (K n) in

def archComp : AdelicGLn.AdelicGL K n →* AdelicGLn.InfiniteAdelicGL K n :=
  (MonoidHom.fst _ _).comp (AdelicGLn.prodEquiv K n).toMonoidHom

variable (K n) in

def finComp : AdelicGLn.AdelicGL K n →* AdelicGLn.FiniteAdelicGL K n :=
  (MonoidHom.snd _ _).comp (AdelicGLn.prodEquiv K n).toMonoidHom

variable (n) in

def localComp (v : HeightOneSpectrum (𝓞 K)) :
    AdelicGLn.AdelicGL K n →* GL (Fin n) (v.adicCompletion K) where
  toFun g := AdelicGLn.finiteRestrictedEquiv K n (finComp K n g) v
  map_one' := by rw [map_one, map_one, RestrictedProduct.one_apply]
  map_mul' g h := by rw [map_mul, map_mul, RestrictedProduct.mul_apply]

def archMat (x : Matrix (Fin n) (Fin n) 𝔸[K]) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K) :=
  x.map Prod.fst

def localMat (v : HeightOneSpectrum (𝓞 K)) (x : Matrix (Fin n) (Fin n) 𝔸[K]) :
    Matrix (Fin n) (Fin n) (v.adicCompletion K) :=
  x.map fun a ↦ a.2 v

theorem coe_archComp (g : AdelicGLn.AdelicGL K n) :
    ((archComp K n g : AdelicGLn.InfiniteAdelicGL K n) : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) =
      archMat (g : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  ext i j
  exact AdelicGLn.prodEquiv_apply_fst K n g i j

theorem coe_localComp (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGLn.AdelicGL K n) :
    ((localComp n v g : GL (Fin n) (v.adicCompletion K)) : Matrix (Fin n) (Fin n) (v.adicCompletion K)) =
      localMat v (g : Matrix (Fin n) (Fin n) 𝔸[K]) := by
  ext i j
  rfl

theorem eventually_localComp_mem (g : AdelicGLn.AdelicGL K n) :
    ∀ᶠ v in cofinite, localComp n v g ∈ integralGL (v.adicCompletion K) n :=
  AdelicGLn.eventually_mem_integralGL K n g

def archSchwartz (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ))
    (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) : ℂ :=
  φ fun ij ↦ GroundTheory.Global.homeomorphMixedSpace K (x ij.1 ij.2)

def matrixTensor (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ))
    (Φ : ∀ v : HeightOneSpectrum (𝓞 K), Matrix (Fin n) (Fin n) (v.adicCompletion K) → ℂ)
    (x : Matrix (Fin n) (Fin n) 𝔸[K]) : ℂ :=
  archSchwartz φ (archMat x) * ∏ᶠ v, Φ v (localMat v x)

def archAbsDet (x : AdelicGLn.InfiniteAdelicGL K n) : ℝ :=
  ∏ w : InfinitePlace K, ‖((x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)).det) w‖ ^ w.mult

def archDetPow (x : AdelicGLn.InfiniteAdelicGL K n) (s : ℂ) : ℂ :=
  (archAbsDet x : ℂ) ^ s

def archIntegrand (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ))
    (f : AdelicGLn.InfiniteAdelicGL K n → ℂ) (s : ℂ) (x : AdelicGLn.InfiniteAdelicGL K n) : ℂ :=
  archSchwartz φ (x : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) * f x *
    archDetPow x (s + ((n : ℂ) - 1) / 2)

def archZeta (μ : Measure (AdelicGLn.InfiniteAdelicGL K n))
    (φ : 𝓢(Fin n × Fin n → mixedEmbedding.mixedSpace K, ℂ)) (f : AdelicGLn.InfiniteAdelicGL K n → ℂ)
    (s : ℂ) : ℂ :=
  ∫ x, archIntegrand φ f s x ∂μ

variable (n) in

def integralGLPositiveCompacts (v : HeightOneSpectrum (𝓞 K)) :
    TopologicalSpace.PositiveCompacts (GL (Fin n) (v.adicCompletion K)) where
  carrier := integralGL (v.adicCompletion K) n
  isCompact' := isCompact_integralGL _ n
  interior_nonempty' := by
    rw [(isOpen_integralGL _ n).interior_eq]
    exact ⟨1, (integralGL _ n).one_mem⟩

variable (n) in

def localHaar (v : HeightOneSpectrum (𝓞 K)) : Measure (GL (Fin n) (v.adicCompletion K)) :=
  Measure.haarMeasure (integralGLPositiveCompacts n v)

instance isHaarMeasure_localHaar (v : HeightOneSpectrum (𝓞 K)) : (localHaar n v).IsHaarMeasure := by
  unfold localHaar
  infer_instance

theorem localHaar_integralGL (v : HeightOneSpectrum (𝓞 K)) :
    localHaar n v (integralGL (v.adicCompletion K) n : Set (GL (Fin n) (v.adicCompletion K))) = 1 :=
  Measure.haarMeasure_self

def partialL (S : Finset (HeightOneSpectrum (𝓞 K))) {V : HeightOneSpectrum (𝓞 K) → Type*}
    [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (π : ∀ v, Representation ℂ (GL (Fin n) (v.adicCompletion K)) (V v)) (s : ℂ) : ℂ :=
  ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S}, LFunction (π v) s

end GJStandardL

end

end GroundTheory.Automorphic
