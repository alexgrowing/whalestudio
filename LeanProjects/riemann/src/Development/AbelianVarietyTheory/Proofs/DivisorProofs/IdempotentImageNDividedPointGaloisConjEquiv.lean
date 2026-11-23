import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageBasePointRationalFractionFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointCharactersGaloisFixedOfRationalBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.GalFixQ

theorem eImage_equiv_conj : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (iw : W →+* R) {I : Type} [Fintype I] (s : I → R) (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ), IsCN R → 1 ≤ n → IsUnit (n : R) → ∀ ζ : R, IsPrimitiveRoot ζ n → ∀ (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)), DataFrom T iw s ε n Q e → TorsRat Q.B n → ∀ (D' : DegData R (maximalIdeal R)) (F : PFactor Q D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'] (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), IsSemiAbelian G' → U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (σ : AlgebraicClosure (FractionRing R) ≃ₐ[FractionRing R] AlgebraicClosure (FractionRing R)) (p₀ p p' : QkPt D'.toPre (AlgebraicClosure (FractionRing R)) n), p.y = F.e • p₀.y → GtPtAct F.o F.e p₀.g p.g → QkExt σ.toAlgHom.toRingHom p p' → QkPt.Equiv D'.toPre (AlgebraicClosure (FractionRing R)) p p' := by
  intro o W _ _ _ T R _ _ _ iw I _ s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F A' G' _ _ U' oA oG hSA hOL σ p₀ p p' hy hg hext
  have hB := D'.tau_bimult
  obtain ⟨b, hb⟩ := GlobalTheory.T.idempotent_image_base_point_rational_fractionField T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F p₀ p hy hg
  have hc := GlobalTheory.T.divisionPoint_characters_galoisFixed_of_rational_basePoint T R iw s ε n hCN hn hnu ζ hζ Q e hDF hTR D' F σ p₀ p hy hg ⟨b, hb⟩
  have hσ : σ.toAlgHom.toRingHom.comp (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) =
      algebraMap _ _ := σ.toAlgHom.comp_algebraMap
  have hpp : QkExt σ.toAlgHom.toRingHom p p := by
    refine ⟨rfl, ?_, hc⟩
    rw [hb, ← Category.assoc]
    congr 1
    rw [spMap, spMap, ← Spec.map_comp]
    congr 1
    ext x
    exact (RingHom.congr_fun hσ x).symm
  have e1 := (GlobalTheory.TorusExt.qkExt_iff hB _ hσ p p').1 hext
  have e2 := (GlobalTheory.TorusExt.qkExt_iff hB _ hσ p p).1 hpp
  rw [e1, ← e2]
  exact qk_equiv_refl hB p

end GlobalTheory.Mum.GalFixQ
