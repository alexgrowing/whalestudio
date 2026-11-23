import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AbsPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

structure Res (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) : Type 1 where
  k : Type
  [field : Field k]
  [char : CharP k l]
  [perf : PerfectRing k l]
  ρ : OK l K →+* k
  surj : Function.Surjective ρ
  s : k →+* Ob l
  hs : ∀ x : OK l K, ‖((PreTilt.untilt (s (ρ x)) - okToOC l K x : OC l) : ℂ_[l])‖ < 1

attribute [instance] Res.field Res.char Res.perf

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def Res.w (r : Res l K) : WittVector l r.k →+* Acris l := (algebraMap (Ainf l) (Acris l)).comp (WittVector.map r.s)

theorem isUnit_witt {k C : Type} [Field k] [CharP k l] [PerfectRing k l] [CommRing C] (g : WittVector l k →+* C) (h : IsUnit (l : C))
    (y : nonZeroDivisors (WittVector l k)) : IsUnit (g y) := by
  obtain ⟨m, b, e⟩ := WittVector.exists_eq_pow_p_mul' y.1 (nonZeroDivisors.coe_ne_zero y)
  rw [e, map_mul, map_pow, map_natCast]
  exact (h.pow m).mul (b.isUnit.map g)

def k₀Lift {k C : Type} [Field k] [CharP k l] [PerfectRing k l] [CommRing C] (g : WittVector l k →+* C) (h : IsUnit (l : C)) :
    Wc.K₀ l k →+* C := IsLocalization.lift (isUnit_witt g h)

def Res.iso (r : Res l K) : Iso l K (Wc.K₀ l r.k) where
  D M j := Wc.D l (B.schFn M.p) r.ρ j
  φ M j := Wc.phiD l (B.schFn M.p) r.ρ j
  pull u hu j := Wc.pullD l r.ρ (B.schMap u hu) j

def ResEx : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K],
  Nonempty (Res l K)

end CrystallineSemistableComparison
