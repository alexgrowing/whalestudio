import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendChainMapAlongQuasiIsoKInjectiveStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

def rcxSemi (φ : R →+* S) {K : Cx S} {J : Cx R} (m : (rcx φ).obj K ⟶ J) : SemiMap K J where
  app U s := ((m.f s).hom.app (op U)).hom.toAddMonoidHom
  nat g s a := (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom ((m.f s).hom.naturality g.op)) a).symm
  comm U s t a := by
    have h := congrArg (fun k => ((k.hom.app (op U)).hom a)) (m.comm s t)
    refine Eq.trans ?_ (h.trans ?_) <;> rfl

theorem rcxSemi_app (φ : R →+* S) {K : Cx S} {J : Cx R} (m : (rcx φ).obj K ⟶ J) (U : Scheme.{0}) (s : ℤ)
    (a : Sec (K.X s) U) : (rcxSemi φ m).app U s a = Sec.map (m.f s) (show Sec ((restr φ).obj (K.X s)) U from a) := rfl

end

theorem restrMap_exists : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S), ∃ ρ : SemiMap (res S F) (res R ((restr φ).obj F)),
    ∀ (U : Scheme.{0}) (a : Sec F U),
      ρ.app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
  intro R S _ _ φ F
  obtain ⟨hKI, -, hGE, -, hι, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R ((restr φ).obj F)
  obtain ⟨-, -, -, hq, hιS, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties S F
  have := rAug_quasiIso φ (resAug F)
  obtain ⟨m, hm⟩ := (GlobalTheory.T.extend_chainMap_along_quasiIso_kInjective R ((restr φ).obj F) ((rcx φ).obj (res S F)) (res R ((restr φ).obj F))
    (rAug φ (resAug F))).1 (resAug ((restr φ).obj F))
  refine ⟨rcxSemi φ m, fun U a => ?_⟩
  rw [rcxSemi_app]
  have h1 : Sec.map (resι S F) a = Sec.map ((resAug F).f 0) (Sec.map (sglι F) a) := by
    rw [← hιS]; rfl
  have h2 := rAug_f_zero φ (resAug F) U a
  have h3 : Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) =
      Sec.map (((rAug φ (resAug F)) ≫ m).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) := by
    rw [hm, ← hι]; rfl
  rw [h3, h1, ← h2]
  rfl

theorem restrMap_spec' : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (F : Shv S) (U : Scheme.{0}) (a : Sec F U), (restrMap φ F).app U 0 (Sec.map (resι S F) a) = Sec.map (resι R ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a) := by
  intro R S _ _ φ F U a
  exact pick_spec (restrMap_exists R S φ F) U a

end GlobalTheory.EtC
