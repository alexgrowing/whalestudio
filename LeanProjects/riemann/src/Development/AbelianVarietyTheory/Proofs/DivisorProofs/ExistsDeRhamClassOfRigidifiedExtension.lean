import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocyclesOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneDiagSumEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagSumCoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsCharTorsVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupCocycleMemCobRangeOfDiagonalSumZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveDeRhamClassTorsionCharacterStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem pullTwo_mulBy_pow_self (p : ℕ) (R : Type) [CommRing R] (G : PDivGroup p R) (n : ℕ)
    (c : G.A n ⊗[R] G.A n) :
    pullbackTwo (mulBy R (G.A n) (p ^ n)) c =
      (Algebra.TensorProduct.lift (Bialgebra.counitAlgHom R (G.A n)) (Bialgebra.counitAlgHom R (G.A n))
        (fun _ _ ↦ Commute.all _ _) c) • (1 : G.A n ⊗[R] G.A n) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have ha := G.mulBy_pow_self n a
    have hb := G.mulBy_pow_self n b
    simp only [pullbackTwo, TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
    change mulBy R (G.A n) (p ^ n) a ⊗ₜ[R] mulBy R (G.A n) (p ^ n) b = _
    rw [ha, hb]
    simp [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_smul,
      TensorProduct.tmul_smul, mul_comm]
  | add x y hx hy => rw [map_add, hx, hy, map_add, add_smul]

theorem exists_isCan_rigToExt_eq : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ), (p : R) ^ N = 0 →
    ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → AllPrim (dp0 R) (𝟙 _) A →
    Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (x : G.RigExt),
    ∃ (c : primDR A) (x' : G.RigExt), IsCan t c x' ∧ G.rigToExt x' = G.rigToExt x := by
  intro p _ R _ N hN A _ hA hP hS G t x
  obtain ⟨⟨z, w⟩, rfl⟩ := Submodule.mkQ_surjective _ x
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow, hN]
  have hcob : cobOne R (G.A N) (diagSum R (G.A N) (p ^ N) (z.1 N)) = 0 := by
    rw [cobOne_diagSum_eq p R G N (p ^ N) hq _ (z.2 N).1, pullTwo_mulBy_pow_self, sub_self]
  obtain ⟨β, hβ, hβy⟩ := exists_isTorsChar p R A G t N _ hcob
  obtain ⟨c, d, hd⟩ := GlobalTheory.T.exists_primitive_deRham_class_torsion_character p R N hN A hA hP hS G t β hβ
  obtain ⟨z', w', hz', hw'⟩ := Dat.exists_cocycles_omega R A hA p G t c d
  refine ⟨c, G.rigMk (z', w'), ⟨d, z', w', hz', hw', rfl⟩, ?_⟩
  have h1 : diagSum R (G.A N) (p ^ N) (z'.1 N) = diagSum R (G.A N) (p ^ N) (z.1 N) := by
    rw [hz', Dat.diagSum_coc R A p G t c d N hN, hd _ _ (t.y_pow N)]
    have h2 := hβy (G.A N) (AlgHom.id R (G.A N))
    rwa [spOver_id, Category.id_comp] at h2
  have hdiag : diagSum R (G.A N) (p ^ N) ((z' - z).1 N) = 0 := by
    rw [Submodule.coe_sub, Pi.sub_apply, map_sub, h1, sub_self]
  have hmem := GlobalTheory.T.pDivGroup_cocycle_mem_cob_range_of_diagonalSum_zero p R N hN G (z' - z) hdiag
  show G.rigToExt (Submodule.Quotient.mk (z', w')) = G.rigToExt (Submodule.Quotient.mk (z, w))
  simp only [PDivGroup.rigToExt, Submodule.mapQ_apply, LinearMap.fst_apply]
  exact (Submodule.Quotient.eq _).2 hmem

end GlobalTheory.PtExt
