import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfRingKrullDimConeIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
open NumberField MvPolynomial GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.CompHt
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.Adelic.LinSys

theorem finrank_quotient_piece_le_sections (k : Type) [Field k] (S : LinSys k) (hS : S.IsVariety)
    (m : ℕ) : Module.finrank k (quotPiece S.imageIdeal (m : ℤ)) ≤ lbH0 k (lbPow S.L m) := by
  classical
  let : Module k (lbPow S.L m).Sec := Module.compHom (lbPow S.L m).Sec (algebraMap k Γ(S.Y, ⊤))
  have : IsScalarTower k Γ(S.Y, ⊤) (lbPow S.L m).Sec :=
    ⟨fun a b s => by
      show (a • b) • s = algebraMap k Γ(S.Y, ⊤) a • (b • s)
      rw [Algebra.smul_def, mul_smul]⟩
  have hfin : Module.Finite k (coh (twist (structureModule S.Y) (lbPow S.L m)) 0) :=
    finite_coh_zero_twist_of_isProjOver (f := S.str) (fun _ => rfl) hS.proj (isLB_lbPow S.isLB m)
  have : Module.Finite k (lbPow S.L m).Sec :=
    Module.Finite.equiv ((cohZeroTwistEquiv (lbPow S.L m)).restrictScalars k)
  rw [lineBundleGlobalSectionsDim_eq_finrank]
  let V := homogeneousSubmodule (Fin S.N) k m

  let φ : V →ₗ[k] (lbPow S.L m).Sec :=
    { toFun := fun g => S.form g.2
      map_add' := fun g h => (ProjCoh.formSecAdd k S.b (m : ℤ)).map_add
        ⟨g.1, mem_polyGrading_natCast.2 g.2⟩ ⟨h.1, mem_polyGrading_natCast.2 h.2⟩
      map_smul' := fun c g => ProjCoh.formSec_smul k S.b c (mem_polyGrading_natCast.2 g.2) _ }

  let f : V →ₗ[k] MvPolynomial (Fin S.N) k ⧸ S.imageIdeal :=
    (Ideal.Quotient.mkₐ k S.imageIdeal).toLinearMap ∘ₗ V.subtype
  have hker : LinearMap.ker f = LinearMap.ker φ := by
    ext g
    simp only [LinearMap.mem_ker]
    change Ideal.Quotient.mk S.imageIdeal g.1 = 0 ↔ S.form g.2 = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact S.mem_imageIdeal_iff g.2
  have hrange : quotPiece S.imageIdeal (m : ℤ) = LinearMap.range f := by
    rw [quotPiece_natCast, LinearMap.range_comp, Submodule.range_subtype]
  rw [hrange, ← f.quotKerEquivRange.finrank_eq, (Submodule.quotEquivOfEq _ _ hker).finrank_eq,
    φ.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_le _

end GlobalTheory.Adelic.LinSys
