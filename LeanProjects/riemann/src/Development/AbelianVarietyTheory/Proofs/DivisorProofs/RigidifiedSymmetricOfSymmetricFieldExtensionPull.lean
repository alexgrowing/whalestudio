import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FracMapAlgebraMap
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RigidifiedSymmetricKernelTrivialDescendFieldExt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc

namespace GlobalTheory.Mum.GenDesc

theorem rigidified_and_sym_of_field_extension : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K') (A : Over (Sp K)) [GrpObj A] (A' : Over (Sp K')) [GrpObj A'] (φ : A'.left ⟶ A.left), IsAbelianScheme A → IsGrpPullback A' A (spMap i) φ → ∀ (L : LB A.left) (L' : LB A'.left), L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → Sym A' L' → Rigidified A L ∧ Sym A L := by
  intro K K' _ _ i A _ A' _ φ hA h L L' hL hL' hw hS
  refine ⟨?_, (GlobalTheory.PolDescent.rigidified_sym_kTriv_descend K K' i A A' φ L L' hA h hL hL' hw).2.1 hS⟩
  have : Subsingleton (𝟙_ (Over (Sp K))).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  exact GlobalTheory.PolDescent.exists_gen_of_unique (default : PrimeSpectrum K) (pull_isLB hL _)

end GlobalTheory.Mum.GenDesc
