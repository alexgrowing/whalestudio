import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentTorsionKernelMultPPow
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpOverFstComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityFamily
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
open GlobalTheory.SqZeroPt
open scoped GlobalTheory.SqZeroPt
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.OpenOmega

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_torsion_kernel_mult_p_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] (GG : PDivGroup p R) (θ : TorsionMap G GG) (n : ℕ) (hs : PtSurj θ n), Module.Finite R (Wmod G) → Module.Projective R (Wmod G) → (∀ l : Wmod G →ₗ[R] R, ∃ (v : TM R R ⟶ G) (h : zeroSec R R ≫ v = η[G]), ∀ w, Phi v h w = l w) → SpecProp θ n hs → ∀ w : Wmod G, cnθ θ n hs w = 0 → w ∈ (Ideal.span {(p : R) ^ n} • ⊤ : Submodule R (Wmod G)) := by
  first | exact @GlobalTheory.OpenOmega.ker_cnθ_le | exact GlobalTheory.OpenOmega.ker_cnθ_le | (intros; apply GlobalTheory.OpenOmega.ker_cnθ_le <;> assumption)
