import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigOfOmegaInjectiveOfEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTwoPointFunctionMultiplesNaturalCharP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatPowEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSquare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffPointwiseCoboundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagSumCoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLiftMulByNatConvPowerComulEqSucc
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem mem_F1prim_of_rigToExt_eq_zero_of_pow_eq_zero : ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R] (N : ℕ),
    (p : R) ^ N = 0 → ∀ (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (x : G.RigExt), IsCan t c x → G.rigToExt x = 0 → c ∈ PrimitiveSubmodule A := by
  intro p _ R _ N hN A _ hA G t c x hx h0
  have : IsCommMonObj A := hA.comm
  obtain ⟨d, z, w, hz, -, rfl⟩ := hx
  have hq : ((p ^ N : ℕ) : R) = 0 := by rw [Nat.cast_pow]; exact hN

  have hmk : (Submodule.Quotient.mk z : G.VecExt) = 0 := h0
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1 hmk
  have hcob : d.coc N = cobOne R (G.A N) (B.1 N) := by
    rw [← hz N, ← hB]; rfl

  have hchiN : chi (p ^ N) d.g (G.A N) (t.y N) = 0 := by
    rw [← Dat.diagSum_coc R A p G t c d N hN, hcob]
    exact diagSum_cobOne_eq_zero p R G N hN (B.1 N)

  have hchi : ∀ (D : Type) [CommRing D] [Algebra R D] (y : Pt A D), y ^ (p ^ N) = 1 →
      chi (p ^ N) d.g D y = 0 := by
    intro D _ _ y hy
    obtain ⟨φ, rfl⟩ := t.surj N D y hy
    have h1 : t.y N ^ (p ^ N) = 1 := t.y_pow N
    have hn := chi_natural (p ^ N) R hq A (fv d.f) d.g d.add (G.A N) D φ (t.y N)
    rw [h1, hchiN, map_zero, sub_zero, sub_self] at hn
    exact hn
  have hcoc := (fv_isCoc_and_ev_eq R A d.f).1
  have hsym := isSymCoc_of_isAdd R A hA (fv d.f) d.g d.add
  have hpos : 0 < p ^ N := pow_pos (Fact.out : p.Prime).pos N
  obtain ⟨k, hk⟩ := Descent.exists_isCob (p ^ N) R hq A (fv d.f) d.g hcoc d.add hsym hchi
    (fun D _ _ y ↦ PtCover.exists_faithfullyFlat_pow_eq R A hA (p ^ N) hpos D y)
  have hF := (mem_hodgeFiltration_iff_pointwiseCoboundary R A d.f).2 ⟨k, hk⟩
  rw [d.cl] at hF
  exact hF

end GlobalTheory.PtExt
