import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerLiftedCocycleImageEqPicardClass
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerLiftedCocycle_image_eq_picardClass : ∀ (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c) → HK.post ℤ _ qb 1 (CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))) = picClass L := by
  first | (exact @GlobalTheory.EtC.KumPic.PostVal.post_eq_picClass) | (exact GlobalTheory.EtC.KumPic.PostVal.post_eq_picClass) | (intros; apply GlobalTheory.EtC.KumPic.PostVal.post_eq_picClass  <;> assumption)
