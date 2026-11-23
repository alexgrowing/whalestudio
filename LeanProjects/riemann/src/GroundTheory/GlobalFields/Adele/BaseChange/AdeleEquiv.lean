import Mathlib
import GroundTheory.GlobalFields.Adele.BaseChange.FiniteTensor
import GroundTheory.GlobalFields.SemilocalAlgebras.InfiniteAdeleTopology

namespace GroundTheory.Global

open IsDedekindDomain NumberField TensorProduct Module Topology
open scoped NumberField.AdeleRing

noncomputable section

namespace AdeleBaseChange

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

variable (K L) in

def adeleMap : 𝔸[K] →+* 𝔸[L] :=
  RingHom.prodMap (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := K) (L := L))
    (finiteAdeleMap K L)

theorem adeleMap_apply (x : 𝔸[K]) :
    adeleMap K L x =
      (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap x.1, finiteAdeleMap K L x.2) :=
  rfl

theorem continuous_adeleMap : Continuous (adeleMap K L) :=
  GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap.prodMap continuous_finiteAdeleMap

theorem adeleMap_algebraMap (k : K) :
    adeleMap K L (algebraMap K 𝔸[K] k) = algebraMap L 𝔸[L] (algebraMap K L k) :=
  Prod.ext (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap k)
    (finiteAdeleMap_algebraMap k)

variable (K L) in

def adeleTensorEquiv : L ⊗[K] 𝔸[K] ≃ₐ[L] 𝔸[L] :=
  (Algebra.TensorProduct.prodRight K L L (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)).trans
    (AlgEquiv.prodCongr GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv
      (finiteTensorEquiv K L))

theorem adeleTensorEquiv_tmul (l : L) (a : 𝔸[K]) :
    adeleTensorEquiv K L (l ⊗ₜ a) = algebraMap L 𝔸[L] l * adeleMap K L a :=
  Prod.ext (GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul' l a.1)
    (finiteTensorEquiv_tmul l a.2)

theorem adeleTensorEquiv_tmul_snd (l : L) (a : 𝔸[K]) (w : HeightOneSpectrum (𝓞 L)) :
    (adeleTensorEquiv K L (l ⊗ₜ a)).2 w =
      SemiLocal.tensorEquiv' L (below K w) (l ⊗ₜ a.2 (below K w)) ⟨w, liesOver_below w⟩ :=
  finiteTensorEquiv_tmul_apply l a.2 w

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι K L)

def coord (i : ι) (y : 𝔸[L]) : 𝔸[K] :=
  (GroundTheory.Global.InfinitePlace.adeleCoord b i y.1, finiteCoord b i y.2)

theorem continuous_coord (i : ι) : Continuous (coord b i) :=
  ((GroundTheory.Global.InfinitePlace.continuous_adeleCoord b i).comp continuous_fst).prodMk
    ((continuous_finiteCoord b i).comp continuous_snd)

def fstAddHom : 𝔸[L] →+ InfiniteAdeleRing L where
  toFun := Prod.fst
  map_zero' := rfl
  map_add' _ _ := rfl

def sndAddHom : 𝔸[L] →+ FiniteAdeleRing (𝓞 L) L where
  toFun := Prod.snd
  map_zero' := rfl
  map_add' _ _ := rfl

theorem adeleTensorEquiv_sum_coord (y : 𝔸[L]) :
    adeleTensorEquiv K L (∑ i, b i ⊗ₜ coord b i y) = y := by
  rw [map_sum]
  simp_rw [adeleTensorEquiv_tmul]
  refine Prod.ext ?_ ?_
  · change fstAddHom (∑ i, algebraMap L 𝔸[L] (b i) * adeleMap K L (coord b i y)) = y.1
    rw [map_sum]
    conv_rhs => rw [← GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_sum_adeleCoord b y.1]
    rw [map_sum]
    simp_rw [GroundTheory.Global.InfinitePlace.tensorInfiniteAdeleRingEquiv_tmul']
    rfl
  · change sndAddHom (∑ i, algebraMap L 𝔸[L] (b i) * adeleMap K L (coord b i y)) = y.2
    rw [map_sum]
    conv_rhs => rw [← finiteTensorMap_sum_finiteCoord b y.2]
    rw [map_sum]
    simp_rw [finiteTensorMap_tmul]
    rfl

theorem adeleTensorEquiv_symm_apply (y : 𝔸[L]) :
    (adeleTensorEquiv K L).symm y = ∑ i, b i ⊗ₜ coord b i y := by
  rw [AlgEquiv.symm_apply_eq]
  exact (adeleTensorEquiv_sum_coord b y).symm

end AdeleBaseChange

end

end GroundTheory.Global
