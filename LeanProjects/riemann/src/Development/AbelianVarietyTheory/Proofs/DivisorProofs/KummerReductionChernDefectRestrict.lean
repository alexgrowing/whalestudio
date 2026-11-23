import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CorrFamAddTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientReductionFirstChernClassTateTwistAltI
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectEqOfPowEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPrimitiveRootAndRootsOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlueStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.RedChern

private theorem unitsMap_comp_appTop {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (u : (Γ(U, ⊤))ˣ) :
    Units.map (k ≫ g).appTop.hom.toMonoidHom u =
      Units.map k.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom u) := by
  ext
  simp [Scheme.Hom.comp_appTop]
  rfl

private theorem isUnit_natCast_appTop {V U : Scheme.{0}} (g : V ⟶ U) (Q : ℕ) (h : IsUnit (Q : Γ(U, ⊤))) :
    IsUnit (Q : Γ(V, ⊤)) := by
  simpa using h.map g.appTop.hom

theorem res_defectSec : ∀ (Q q : ℕ) [NeZero Q], q ∣ Q → ∀ (U : Scheme.{0}) (u : (Γ(U, ⊤))ˣ), IsUnit (Q : Γ(U, ⊤)) →
    ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ), v ^ Q = Units.map g.appTop.hom.toMonoidHom u →
      Sec.res g (GlobalTheory.EtC.RedChern.defectSec Q q U u) = GlobalTheory.EtC.RedChern.defect Q q V v := by
  intro Q q _ hqQ U u hQ

  let S : Sieve U :=
    { arrows := fun V g => ∃ v : (Γ(V, ⊤))ˣ, v ^ Q = Units.map g.appTop.hom.toMonoidHom u
      downward_closed := by
        rintro V W g ⟨v, hv⟩ k
        refine ⟨Units.map k.appTop.hom.toMonoidHom v, ?_⟩
        rw [← map_pow, hv, unitsMap_comp_appTop] }
  have hS : S ∈ Scheme.etaleTopology U := by
    obtain ⟨S₀, hS₀, hP⟩ := (GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).2.2.2 hQ u
    exact GrothendieckTopology.superset_covering _ (fun V g hg => hP V g hg) hS₀
  let s : ∀ (V : Scheme.{0}) (g : V ⟶ U), S.arrows g → Sec ((res _ (tw q 1)).X 0) V :=
    fun V g hg => defect Q q V hg.choose
  have hcompat : ∀ (V W : Scheme.{0}) (g : V ⟶ U) (k : W ⟶ V) (hg : S.arrows g),
      Sec.res k (s V g hg) = s W (k ≫ g) (S.downward_closed hg k) := by
    intro V W g k hg
    have hQV : IsUnit (Q : Γ(V, ⊤)) := isUnit_natCast_appTop g Q hQ
    have hQW : IsUnit (Q : Γ(W, ⊤)) := isUnit_natCast_appTop k Q hQV
    change Sec.res k (defect Q q V hg.choose) = defect Q q W (S.downward_closed hg k).choose
    rw [GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W V k hg.choose hQV]
    refine GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ W _ _ hQW ?_
    rw [(S.downward_closed hg k).choose_spec, ← map_pow, hg.choose_spec, unitsMap_comp_appTop]
  obtain ⟨a, ha⟩ := (GlobalTheory.T.etaleSheafSections_ext_and_glue _ _ U).2 S hS s hcompat
  have hex : ∃ a : Sec ((res _ (tw q 1)).X 0) U, ∀ (V : Scheme.{0}) (g : V ⟶ U) (v : (Γ(V, ⊤))ˣ),
      v ^ Q = Units.map g.appTop.hom.toMonoidHom u → Sec.res g a = defect Q q V v := by
    refine ⟨a, fun V g v hv => ?_⟩
    have hg : S.arrows g := ⟨v, hv⟩
    rw [ha V g hg]
    exact GlobalTheory.T.kummerReductionChernDefect_eq_of_pow_eq Q q hqQ V _ _ (isUnit_natCast_appTop g Q hQ) (hg.choose_spec.trans hv.symm)
  intro V g v hv
  exact pick_spec hex V g v hv

end GlobalTheory.EtC.RedChern
