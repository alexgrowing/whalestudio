import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutsSecOfIsLat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHomogeneousPolysTangentBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniqueIntegralLiftNormPInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitTorsAlgClosedFractionField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ScaleZeroComp

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.OmegaHT

theorem exists_primitiveRoot_of_isAlgClosed (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A]
    [IsAlgClosed (FractionRing A)] (n : ℕ) (hn : 0 < n) : ∃ ζ : A, IsPrimitiveRoot ζ n := by
  have hinj := IsFractionRing.injective A (FractionRing A)
  haveI : CharZero (FractionRing A) := charZero_of_injective_algebraMap hinj
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (FractionRing A) n
  have hi : IsIntegral A ζ := IsIntegral.of_pow hn (by rw [hζ.pow_eq_one]; exact isIntegral_one)
  obtain ⟨z, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  exact ⟨z, hζ.of_map_of_injective hinj⟩

theorem ringSt : RingSt := by
  intro E _ _ _ H X _ t hX p hp A _ _ _ _ _ x g e he
  obtain ⟨n, h, hh⟩ := GlobalTheory.HTMap.hodgeTate_map E H X t A x g e he p hp.out
    (exists_primitiveRoot_of_isAlgClosed A p hp.out.pos)
    (GlobalTheory.LineNorm.splitTors_of_isAlgClosed E H X t A x p hp.out.ne_zero)
  refine ⟨n + g, Fin.append h fun i k => if i = k then (p : A) else 0,
    ⟨fun i => Fin.append 0 fun k => if i = k then 1 else 0, fun i k => ?_⟩, fun C κ a v hv => ?_⟩
  · rw [Fin.sum_univ_add]
    simp
  · have key := GlobalTheory.HTLevel.mem_latHT_iff HTBound.htBound E H X t p C.S C.norm_p (spMap κ ≫ x)
      (GlobalTheory.LineNorm.WedgeMax.ext_intO hX _) g _ (GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t κ he) n
      (fun j i => κ (h j i)) (hh C.S κ).1 (hh C.S κ).2 a v
      (by simpa only [GlobalTheory.LineNorm.WedgeMax.spMap_comp, GlobalTheory.LineNorm.WedgeMax.spMap_dual_comp, Category.assoc] using hv)
    rw [GlobalTheory.LineNorm.WedgeMax.spMap_comp, Category.assoc, key, Fin.forall_fin_add]
    refine and_congr (by simp) (forall_congr' fun i => ?_)
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [hk.symm]) (by simp)]
    simp

end GlobalTheory.OmegaHT
