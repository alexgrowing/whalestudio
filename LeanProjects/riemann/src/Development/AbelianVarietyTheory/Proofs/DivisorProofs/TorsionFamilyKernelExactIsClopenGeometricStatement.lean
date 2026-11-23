import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFamilyKernelExactIsClopenGeometric
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaAwayPowSelf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFamily_kernel_exact_isClopen_geometric : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (M h : ℕ), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∀ (Z : Over S) (e : (Fin h ⊕ Fin h → ℤ) → (Z ⟶ G)), (∀ a c, e (a + c) = e a * e c) → (∀ a, e a ^ M = 1) → GlobalTheory.HkClopen.Loc (S := Z.left) (fun k _ _ x => ∀ a, (Over.homMk x rfl : Over.mk (x ≫ Z.hom) ⟶ Z) ≫ e a = 1 ↔ ∃ c, a = M • c) := by
  first | (exact @GlobalTheory.kerClopen_geom) | (exact GlobalTheory.kerClopen_geom) | (intros; apply GlobalTheory.kerClopen_geom  <;> assumption)
