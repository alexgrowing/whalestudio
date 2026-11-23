import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.HodgeSeqSheaf

variable {T : Scheme.{0}} (A : Over T) [GrpObj A]

def IsDRTriv (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)) : Prop :=
  ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V),
    letI := resAlg h
    ∀ (φ : (onAff A hV').left ⟶ (onAff A hV).left)
      (hφ : IsGrpPullback (onAff A hV') (onAff A hV) (spMap (algebraMap Γ(T, V) Γ(T, V'))) φ),
      φ ≫ pullback.fst A.hom hV.fromSpec = pullback.fst A.hom hV'.fromSpec →
      ∀ s : Γ(H, V), e V' hV' (GlobalTheory.Twist.resM H h s) = (GlobalTheory.Published.AbelianDeRham.bcMor hφ).pull (e V hV s)

theorem isDeRhamSheaf_iff (H : T.Modules) : IsDeRhamSheaf A H ↔ ∃ e, IsDRTriv A H e := Iff.rfl

end GlobalTheory.HodgeSeqSheaf
