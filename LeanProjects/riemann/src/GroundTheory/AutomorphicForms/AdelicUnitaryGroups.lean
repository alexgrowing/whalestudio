import Mathlib
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Restricted
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.LatticeCompact
import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Anisotropic
import GroundTheory.GlobalFields.Adele.Discrete
import GroundTheory.GlobalFields.Adele.Topology

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct NumberField.AdeleRing

noncomputable section

variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)

section Congr

variable {R S : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]

def unitaryCongr (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm) :
    unitaryPoints K E H R ≃ₜ* unitaryPoints K E H S where
  toFun := unitaryMap K E H (e : R →ₐ[K] S)
  invFun := unitaryMap K E H (e.symm : S →ₐ[K] R)
  left_inv g := by
    let b := Module.finBasis K E
    apply unitaryCoords_injective H R b
    rw [unitaryCoords_unitaryMap, unitaryCoords_unitaryMap]
    funext p
    simp
  right_inv g := by
    let b := Module.finBasis K E
    apply unitaryCoords_injective H S b
    rw [unitaryCoords_unitaryMap, unitaryCoords_unitaryMap]
    funext p
    simp
  map_mul' := map_mul _
  continuous_toFun := continuous_unitaryMap _ he
  continuous_invFun := continuous_unitaryMap _ he'

theorem unitaryCongr_apply (e : R ≃ₐ[K] S) (he : Continuous e) (he' : Continuous e.symm)
    (g : unitaryPoints K E H R) :
    unitaryCongr H e he he' g = unitaryMap K E H (e : R →ₐ[K] S) g := rfl

end Congr

variable [NumberField K]

variable (K) in

def adeleRingEquivProd : 𝔸[K] ≃ₐ[K] InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K :=
  AlgEquiv.refl

variable (K) in

def infiniteAdeleRingEquivPi : InfiniteAdeleRing K ≃ₐ[K] ∀ w : InfinitePlace K, w.Completion :=
  AlgEquiv.refl

variable (K) in

def adeleInfiniteEval (w : InfinitePlace K) : 𝔸[K] →ₐ[K] w.Completion :=
  ((Pi.evalAlgHom K (fun w : InfinitePlace K => w.Completion) w).comp
    (infiniteAdeleRingEquivPi K).toAlgHom).comp
    ((AlgHom.fst K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable (K) in

def adeleFiniteEval (v : HeightOneSpectrum (𝓞 K)) : 𝔸[K] →ₐ[K] v.adicCompletion K :=
  (finiteAdeleEval K v).comp ((AlgHom.snd K _ _).comp (adeleRingEquivProd K).toAlgHom)

variable {κ : Type*} [Fintype κ] (b : Basis κ K E)

def adeleUnitaryEquiv (hH : IsUnit H.det) :
    unitaryPoints K E H 𝔸[K] ≃ₜ*
      (∀ w : InfinitePlace K, unitaryPoints K E H w.Completion) ×
        Πʳ v : HeightOneSpectrum (𝓞 K),
          [unitaryPoints K E H (v.adicCompletion K), localIntegral H b v] :=
  (unitaryCongr H (adeleRingEquivProd K) (by exact continuous_id) (by exact continuous_id)).trans
    ((unitaryProdEquiv K H _ _ hH).trans
      { toMulEquiv := MulEquiv.prodCongr
          ((unitaryCongr H (infiniteAdeleRingEquivPi K) (by exact continuous_id) (by exact continuous_id)).trans
            (unitaryPiEquiv K H (fun w : InfinitePlace K => w.Completion) hH)).toMulEquiv
          (finiteAdeleUnitaryEquiv H b hH).toMulEquiv
        continuous_toFun :=
          (((unitaryCongr H (infiniteAdeleRingEquivPi K) (by exact continuous_id) (by exact continuous_id)).trans
            (unitaryPiEquiv K H (fun w : InfinitePlace K => w.Completion) hH)).continuous.comp
              continuous_fst).prodMk
            ((finiteAdeleUnitaryEquiv H b hH).continuous.comp continuous_snd)
        continuous_invFun :=
          (((unitaryCongr H (infiniteAdeleRingEquivPi K) (by exact continuous_id) (by exact continuous_id)).trans
            (unitaryPiEquiv K H (fun w : InfinitePlace K => w.Completion) hH)).symm.continuous.comp
              continuous_fst).prodMk
            ((finiteAdeleUnitaryEquiv H b hH).symm.continuous.comp continuous_snd) })

theorem t2Space_unitaryPoints_adele (hH : IsUnit H.det) : T2Space (unitaryPoints K E H 𝔸[K]) :=
  t2Space_unitaryPoints H 𝔸[K] hH

theorem locallyCompactSpace_unitaryPoints_adele (hH : IsUnit H.det) :
    LocallyCompactSpace (unitaryPoints K E H 𝔸[K]) :=
  locallyCompactSpace_unitaryPoints H 𝔸[K] hH

variable (K) in

def unitaryDiagonal : unitaryPoints K E H K →* unitaryPoints K E H 𝔸[K] :=
  unitaryMap K E H (Algebra.ofId K 𝔸[K])

theorem discreteTopology_unitaryDiagonal_range :
    DiscreteTopology (unitaryDiagonal K H).range := by
  let b := Module.finBasis K E
  have := GroundTheory.Global.discreteTopology_principalSubgroup K
  have hmem : ∀ (x : (unitaryDiagonal K H).range) (p : ι × ι × Fin (finrank K E)),
      unitaryCoords H 𝔸[K] b x.1 p ∈ AdeleRing.principalSubgroup (𝓞 K) K := by
    rintro ⟨_, g, rfl⟩ p
    simp only [unitaryDiagonal, unitaryCoords_unitaryMap]
    exact ⟨unitaryCoords H K b g p, rfl⟩
  let c : (unitaryDiagonal K H).range → ι × ι × Fin (finrank K E) →
      AdeleRing.principalSubgroup (𝓞 K) K := fun x p => ⟨unitaryCoords H 𝔸[K] b x.1 p, hmem x p⟩
  refine DiscreteTopology.of_continuous_injective (f := c) ?_ ?_
  · exact continuous_pi fun p => Continuous.subtype_mk ((continuous_apply p).comp
      ((continuous_unitaryCoords H 𝔸[K] b).comp continuous_subtype_val)) _
  · intro x y hxy
    apply Subtype.ext
    apply unitaryCoords_injective H 𝔸[K] b
    funext p
    exact congrArg Subtype.val (congrFun hxy p)

section Hermitian

variable {V : Type*} [AddCommGroup V] [Module E V] (h : HermitianForm K E V) (v : Basis ι E V)

def adeleUnitaryEquivHermitian :
    unitaryPoints K E (gram h.toSesq v) 𝔸[K] ≃ₜ*
      (∀ w : InfinitePlace K, unitaryPoints K E (gram h.toSesq v) w.Completion) ×
        Πʳ w : HeightOneSpectrum (𝓞 K),
          [unitaryPoints K E (gram h.toSesq v) (w.adicCompletion K),
            localIntegral (gram h.toSesq v) b w] :=
  adeleUnitaryEquiv (gram h.toSesq v) b (isUnit_det_gram h v)

def hermitianDiagonal : h.unitaryGroup →* unitaryPoints K E (gram h.toSesq v) 𝔸[K] :=
  (unitaryDiagonal K (gram h.toSesq v)).comp
    (unitaryPointsRationalEquivHermitian K E h v).symm.toMonoidHom

end Hermitian

end

end GroundTheory.Automorphic
