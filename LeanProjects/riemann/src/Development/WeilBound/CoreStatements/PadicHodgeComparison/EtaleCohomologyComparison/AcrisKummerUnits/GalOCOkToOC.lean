import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HarishChandraFormulaStatement
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (l) in

def clToC : PadicAlgCl l →+* ℂ_[l] := algebraMap _ _

theorem norm_clToC (x : PadicAlgCl l) : ‖clToC l x‖ = ‖x‖ := UniformSpace.Completion.norm_coe x

variable (l K) in

def okToOC : OK l K →+* OC l :=
  (((clToC l).comp K.val.toRingHom).comp (OK l K).subtype).codRestrict (normInteger ℂ_[l]) fun x =>
    mem_normInteger.2 ((norm_clToC _).trans_le (mem_normInteger.1 x.2))

theorem galOC_okToOC (σ : Gal(PadicAlgCl l/K)) (x : OK l K) : galOC σ (okToOC l K x) = okToOC l K x :=
  Subtype.ext (gal_smul_coe_of_mem σ x.1)

def PAlg.cToUg (A : PAlg l) : ℂ_[l] →+* A.Ug :=
  (Localization.awayLift ((algebraMap A.U A.Ug).comp A.oC) (l : OC l) (by
    rw [RingHom.comp_apply, map_natCast]
    exact IsLocalization.Away.algebraMap_isUnit (l : A.U))).comp
    ((IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).symm : ℂ_[l] →+* Localization.Away (l : OC l))

theorem PAlg.cToUg_coe (A : PAlg l) (x : OC l) : A.cToUg x = algebraMap A.U A.Ug (A.oC x) := by
  have e : (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).symm (x : ℂ_[l]) = algebraMap _ _ x :=
    (IsPerfectoidField.awayEquiv (K := ℂ_[l]) l).symm.commutes x
  rw [PAlg.cToUg, RingHom.comp_apply, RingHom.coe_coe, e]
  exact IsLocalization.lift_eq _ x

namespace Model

abbrev P (M : Model l K) : PAlg l ⥤ Type := PX M.p (okToOC l K)

abbrev MH (M : Model l K) (n j : ℕ) : Type 1 := CrystallineSemistableComparison.MH M.P n j

def galMH (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (n j : ℕ) : M.MH n j →ₛₗ[ACris.galCris σ] M.MH n j :=
  (galMor σ (pxTw M.p (okToOC l K) σ (galOC_okToOC σ)) n).pull j

def phiMH (M : Model l K) (n j : ℕ) : M.MH n j →ₛₗ[ACris.phi ℂ_[l] l] M.MH n j := (phiMor M.P n).pull j

def pullMH {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (n j : ℕ) : N.MH n j →ₗ[Acris l] M.MH n j :=
  (pullMor (pxMap (okToOC l K) u hu) n).pull j

end Model

end CrystallineSemistableComparison
