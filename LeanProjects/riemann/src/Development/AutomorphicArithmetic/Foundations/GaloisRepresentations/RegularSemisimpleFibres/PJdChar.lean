import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacterHarishChandraProductCuspidalGLOfRegulStatement

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem detc_isChar {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t k : ℕ) :
    GlobalTheory.BI.IsChar ℂ ℂ (detc θ t k) := by
  let χ : GL (Fin t) F →* ℂ := (powMonoidHom k).comp (θ.comp
    ((algebraMap F (AlgebraicClosure F)).toMonoidHom.comp
      ((Units.coeHom F).comp Matrix.GeneralLinearGroup.det)))
  refine ⟨1, (algebraMap ℂ (Module.End ℂ (Fin 1 → ℂ))).toMonoidHom.comp χ, fun g => ?_⟩
  simp [Representation.character, χ, detc, Module.algebraMap_end_eq_smul_id, LinearMap.trace_id]

private theorem jd_isChar (hH : HcChar) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (L : List (ℕ × ℕ)) (hL : GlobalTheory.BI.IsChar ℂ ℂ (J θ L (deg L))) (D : List (ℕ × ℕ)) :
    GlobalTheory.BI.IsChar ℂ ℂ (JD θ D L (deg D + deg L)) := by
  induction D with
  | nil =>
    have e : deg ([] : List (ℕ × ℕ)) + deg L = deg L := by simp [GlobalTheory.Shin.deg]
    rw [e, JD_nil]
    exact hL
  | cons p D ih =>
    rw [JD_cons]
    refine hH F p.1 (deg D + deg L) _ ?_ _ _ (detc_isChar θ p.1 p.2) ih
    simp [GlobalTheory.Shin.deg, add_assoc]

theorem UpperTheory.Gal.InertialTypesAlt.jdChar :
    HcChar → JDChar := by
  intro hH F _ _ θ hθ
  refine ⟨detc_isChar θ, fun a hok hq => ?_⟩
  obtain ⟨-, -, hL⟩ := hok
  have hJ := GlobalTheory.T.isCharacter_harishChandraProductCuspidalGL_of_regular F θ hθ a.L (fun p hp => by rw [← hq]; exact hL p hp) _ rfl
  exact jd_isChar hH θ a.L hJ a.D
