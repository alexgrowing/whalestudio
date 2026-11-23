import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPrechartTranslate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_prechart_translate : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field K] [IsAlgClosed K] [CharZero K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (N : ℕ), N ≠ 0 → ∀ (q : PrimeSpectrum R) (c : PreChart G N q), c.IsGrp → ∀ f : Tors G N K → K, (∀ s : Tors G N K, ∃ a : c.C, ∀ ψ : c.C →ₐ[R] K, ψ a = f (s * torsMap ψ c.j)) → ∀ (q' : PrimeSpectrum R) (c' : PreChart G N q') (s : Tors G N K) (P : Ideal c'.C) [P.IsPrime], algebraMap R c'.C c.r ∉ P → ∃ b : Localization.AtPrime P, ∀ ψ : Localization.AtPrime P →ₐ[R] K, ψ b = f (s * torsMap (ψ.comp (IsScalarTower.toAlgHom R c'.C (Localization.AtPrime P))) c'.j) := by
  first | exact @GlobalTheory.GroupBplus.Aff.MemLoc.exists_localElem | exact GlobalTheory.GroupBplus.Aff.MemLoc.exists_localElem | (intros; apply GlobalTheory.GroupBplus.Aff.MemLoc.exists_localElem <;> assumption)
