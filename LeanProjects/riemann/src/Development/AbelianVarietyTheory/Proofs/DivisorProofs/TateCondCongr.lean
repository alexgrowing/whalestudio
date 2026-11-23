import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsCoprimeZpow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UPelLevel

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def TateCond (D : Datum F) (p N : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : OAct (𝓞 F) A) (PP : RigLB A)
    {k : Type} [Field k] (x : Sp k ⟶ S) (lv : D.La → (Over.mk x ⟶ A)) : Prop :=
  ∃ I : TateIsoP D p k (Over.mk x ⟶ A) (fun a g => g ≫ act.act a)
      (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c)), ∀ a, lv a = I.ev N a

def IsLevel (D : Datum F) (p N : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : OAct (𝓞 F) A) (PP : RigLB A)
    (T : Over S) (lv : D.La → (T ⟶ A)) : Prop :=
  (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ (∀ (c : 𝓞 F) a, lv (c • a) = lv a ≫ act.act c) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      TateCond D p N A act PP (x ≫ T.hom) fun a => (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a

theorem tateCond_congr (D : Datum F) (p N : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : OAct (𝓞 F) A)
    (PP : RigLB A) {k : Type} [Field k] {x x' : Sp k ⟶ S} (e : x = x') (lv : D.La → (Over.mk x ⟶ A))
    (lv' : D.La → (Over.mk x' ⟶ A))
    (h : ∀ a, (Over.homMk (𝟙 _) (by simp [e]) : Over.mk x' ⟶ Over.mk x) ≫ lv a = lv' a) :
    TateCond D p N A act PP x lv → TateCond D p N A act PP x' lv' := by
  subst e
  have h' : ∀ a, lv a = lv' a := fun a => by
    rw [← h a]
    have : (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) = 𝟙 _ := by ext; simp
    rw [this, Category.id_comp]
  rintro ⟨I, hI⟩
  exact ⟨I, fun a => (h' a).symm.trans (hI a)⟩

end GlobalTheory.UPelLevel
