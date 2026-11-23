import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ThetaSetupAlgebraMaps
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsFirstChernClassOfLineBundle

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

def limMod {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R} (act : ∀ j g, Sys.Hom (S j) (S j) (σ g)) :
    GMod R Γ where
  N j := (S j).lim
  act j g := (act j g).lim.toAddMonoidHom

def limAlg {R : Type} [CommRing R] {Γ : Type} (S : ℕ → Sys.{1} R) {σ : Γ → R →+* R} (act : ∀ j g, Sys.Hom (S j) (S j) (σ g))
    (one : ∀ n, (S 0).M n) (cup : ∀ n i j, (S i).M n → (S j).M n → (S (i + j)).M n) : GAlg R Γ where
  toGMod := limMod S act
  one x := ∀ n, (show (S 0).lim from x).1 n = one n
  cup {i j} x y z := ∀ n, (show (S (i + j)).lim from z).1 n = cup n i j ((show (S i).lim from x).1 n) ((show (S j).lim from y).1 n)

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

namespace Model

abbrev MS (M : Model l K) (j : ℕ) : Sys.{1} (Acris l) := MSys M.P j

def galS (M : Model l K) (j : ℕ) (σ : Gal(PadicAlgCl l/K)) : Sys.Hom (M.MS j) (M.MS j) (ACris.galCris σ) where
  f n := M.galMH σ n j
  comm n x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => (PAlg.pdOk_twId σ _).red_acr n.le_succ _))

def phiS (M : Model l K) (j : ℕ) : Sys.Hom (M.MS j) (M.MS j) (ACris.phi ℂ_[l] l) where
  f n := M.phiMH n j
  comm n x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => (PAlg.pdOk_frob _).red_acr n.le_succ _))

def pullS {M N : Model l K} (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (j : ℕ) : Sys.Hom (N.MS j) (M.MS j) (RingHom.id _) where
  f n := pullMH u hu n j
  comm n x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl

def MA (M : Model l K) : GAlg (Acris l) K.fixingSubgroup :=
  limAlg M.MS (σ := fun g => ACris.galCris (IntermediateField.fixingSubgroupEquiv K g))
    (fun j g => M.galS j (IntermediateField.fixingSubgroupEquiv K g)) (fun n => CH.oneH (AcrEl M.P n))
    (fun n _ _ x y => (CH.mulP (AcrEl M.P n)).cup rfl x y)

end Model

end CrystallineSemistableComparison
