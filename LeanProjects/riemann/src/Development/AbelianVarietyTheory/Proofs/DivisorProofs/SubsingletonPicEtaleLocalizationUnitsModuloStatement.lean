import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonPicEtaleLocalizationUnitsModulo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_pic_etale_localization_unitsModulo : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], Subsingleton (CommRing.Pic (Localization (Algebra.algebraMapSubmonoid A' ((IsUnit.submonoid (B ⧸ Ideal.span {f})).comap (Ideal.Quotient.mk (Ideal.span {f})).toMonoidHom ⊔ Submonoid.powers f)))) := by
  first | (exact @GlobalTheory.PicLoc.subsingleton_pic_localization) | (exact GlobalTheory.PicLoc.subsingleton_pic_localization) | (intros; apply GlobalTheory.PicLoc.subsingleton_pic_localization <;> assumption)
