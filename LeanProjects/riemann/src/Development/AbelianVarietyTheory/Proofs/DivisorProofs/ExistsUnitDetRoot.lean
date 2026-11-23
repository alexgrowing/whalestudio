import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOneAddSubOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormOneRootCongruentOddHostField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAtDetRootCongOneOddEqOne

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnitDetRoot

theorem infPart_sigR_one (D : D7) (x : AE D) (hx : infPart D x = 1) :
    infPart D (sigR (AF D.host.F) D.sp.cm.sig x) = 1 := by
  have h := GlobalTheory.DetRootCong.map_sigR (F := D.host.F) (E := D.host.E)
    (AlgHom.fst D.host.F (InfiniteAdeleRing D.host.F) (Af D.host.F)) D.sp.cm.sig x
  refine h.trans ?_
  exact (congrArg _ hx).trans (map_one _)

theorem exists_unit_detRoot : ∀ (D : D7) (V : HSp D) (N : ℕ), Odd N → ∀ k ∈ GfC V, (∀ z ∈ Formalism.L2.Pj.latHat V, ∃ y ∈ Formalism.L2.Pj.latHat V, (finHom V k).1.mulVec z - z = N • y) → ∃ x : (AE D)ˣ, FinUnit x ∧ IsDetRoot V k x ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y := by
  intro D V N hN k hk hu
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  rw [h1] at hu
  obtain ⟨w, hw, hwe⟩ := GlobalTheory.MarkDet.det_sub_one_of_cong D.host.F _ h3 h4 N hN.pos.ne' _ hu
  rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at hw
  have hn := GlobalTheory.RecDict.det_finHom_norm V k
  obtain ⟨y, y', hy, hy', hyy, hroot, p, hp, hpe⟩ := GlobalTheory.OddRoot.exists_root_odd D N hN _ w hw hwe hn
  obtain ⟨Y, hY1, hY2, hY3⟩ := GlobalTheory.DetRootCong.exists_idele D y y' hyy
  refine ⟨Y, ⟨hY1, hY2 ▸ hy, hY3 ▸ hy'⟩, ?_, p, hp, hY2 ▸ hpe⟩
  have hdet : (finHom V k).1.det = finPart D (matHom V k).1.det := ((finPart D).map_det _).symm
  have hdet' : (infHom V k).1.det = infPart D (matHom V k).1.det := ((infPart D).map_det _).symm
  have hk1 : infHom V k = 1 := hk
  rw [hk1, Units.val_one, Matrix.det_one] at hdet'
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  apply e.injective
  refine Prod.ext (((he _).1.trans ?_).trans (he _).1.symm) (((he _).2.trans ?_).trans (he _).2.symm)
  · change infPart D (Y : AE D) = infPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet', infPart_sigR_one D _ hY1, hY1, mul_one]
  · change finPart D (Y : AE D) = finPart D ((matHom V k).1.det * sigR (AF D.host.F) D.sp.cm.sig (Y : AE D))
    rw [RingHom.map_mul, ← hdet, GlobalTheory.DetRootCong.finPart_sigR, hY2]
    exact hroot

end GlobalTheory.UnitDetRoot
