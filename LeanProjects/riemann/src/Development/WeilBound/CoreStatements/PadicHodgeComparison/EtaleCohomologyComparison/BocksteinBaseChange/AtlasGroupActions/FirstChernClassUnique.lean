import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.BocksteinBaseChangeP
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AtlasGroupActions.ActSmul
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

namespace GlueL'

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (Amp : ∀ M : Model l K, E.LineData M.X → Prop)

theorem ch (hS : ∀ M : Model l K, M.Sm → ∃ D, Amp M D) (M : Model l K) (hM : M.Sm) : Nonempty ((dat Amp).Ch M) :=
  Exists.elim (hS M hM) fun D hD => ⟨(⟨D, hD⟩ : {D : E.LineData M.X // Amp M D})⟩

theorem refine (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) (a : (dat Amp).Ch M) (b : (dat Amp).Ch N) :
    ∃ a' : (dat Amp).Ch M, Nonempty ((dat Amp).Mo (𝟙 M.X) (Category.id_comp _) a' a) ∧ Nonempty ((dat Amp).Mo u hu a' b) :=
  ⟨a, Nonempty.intro (PUnit.unit : PUnit.{2}), Nonempty.intro (PUnit.unit : PUnit.{2})⟩

theorem act_smul {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (σ : K.fixingSubgroup) (c : (per l K).A)
    (y : ((dat Amp).A a).N j) : ((dat Amp).A a).act j σ (c • y) = (per l K).σA σ c • ((dat Amp).A a).act j σ y :=
  GlueLim.act_smul M.MS (fun j g => M.galS j (IntermediateField.fixingSubgroupEquiv K g)) j σ c y

theorem phi_smul {M : Model l K} (a : (dat Amp).Ch M) (j : ℕ) (c : (per l K).A) (y : ((dat Amp).A a).N j) :
    (dat Amp).phiA a j (c • y) = (per l K).φ c • (dat Amp).phiA a j y :=
  GlueLim.hom_smul (M.phiS j) c y

theorem one_uniq {M : Model l K} (a : (dat Amp).Ch M) (x y : ((dat Amp).A a).N 0) :
    ((dat Amp).A a).one x → ((dat Amp).A a).one y → x = y :=
  GlueLim.one_uniq M.MS _ _ _ x y

theorem cup_uniq {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (x : ((dat Amp).A a).N i) (y : ((dat Amp).A a).N j)
    (z z' : ((dat Amp).A a).N (i + j)) : ((dat Amp).A a).cup x y z → ((dat Amp).A a).cup x y z' → z = z' :=
  GlueLim.cup_uniq M.MS _ _ _ x y z z'

theorem bil (M : Model l K) (n i j : ℕ) : ∃ b : (M.MS i).M n →ₗ[Acris l] (M.MS j).M n →ₗ[Acris l] (M.MS (i + j)).M n,
    ∀ x y, b x y = (CH.mulP (AcrEl M.P n)).cup rfl x y :=
  P.cup_bilin (CH.mulP (AcrEl M.P n)) rfl

theorem cup_smul {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (c c' : (per l K).A) (x : ((dat Amp).A a).N i)
    (y : ((dat Amp).A a).N j) (z : ((dat Amp).A a).N (i + j)) :
    ((dat Amp).A a).cup x y z → ((dat Amp).A a).cup (c • x) (c' • y) ((c * c') • z) :=
  GlueLim.cup_smul M.MS _ _ (fun n _ _ x y => (CH.mulP (AcrEl M.P n)).cup rfl x y) (bil M) c c' x y z

theorem first_chern_class_unique (hR : E.RIn l) (hU : E.FirstChernUniqueEtale) (hEt : ∀ M D, Amp M D → Etale D.f) {M : Model l K} (a : (dat Amp).Ch M)
    (x y : ((dat Amp).A a).N 2) : (dat Amp).c1A a x → (dat Amp).c1A a y → x = y := fun hx hy =>
  Subtype.ext (hU l hR (OK l K) M.X M.p (okToOC l K) a.1 (hEt M a.1 a.2) _ _ hx hy)

theorem red_cup (hC : B.CompatH l) (M : Model l K) (k : Bool) (n i j : ℕ) (x : (M.HS k i).M (n + 1)) (y : (M.HS k j).M (n + 1)) :
    (M.HS k (i + j)).r n ((CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) k (n + 1))).cup rfl x y) =
      (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) k n)).cup rfl ((M.HS k i).r n x) ((M.HS k j).r n y) :=
  hC.cup (B.schFn M.p) (okToOC l K) k n.le_succ rfl x y

theorem cup_ex (hC : B.CompatH l) {M : Model l K} (a : (dat Amp).Ch M) {i j : ℕ} (x : ((dat Amp).H a).N i)
    (y : ((dat Amp).H a).N j) : ∃ z, ((dat Amp).H a).cup x y z :=
  GlueLim.cup_ex (M.HS false) _ _ (fun n _ _ x y => (CH.mulP (B.OcA (B.schFn M.p) (okToOC l K) false n)).cup rfl x y)
    (red_cup hC M false) x y

end GlueL'

theorem glueL : GlueL := fun _ _ _ Amp hC hR hU hEt hS =>
  { ch := GlueL'.ch Amp hS
    refine := fun M N u hu _ _ a b => GlueL'.refine Amp M N u hu a b
    act_smul := GlueL'.act_smul Amp
    phi_smul := GlueL'.phi_smul Amp
    one_uniq := GlueL'.one_uniq Amp
    cup_uniq := GlueL'.cup_uniq Amp
    cup_smul := GlueL'.cup_smul Amp
    first_chern_class_unique := GlueL'.first_chern_class_unique Amp hR hU hEt
    cup_ex := GlueL'.cup_ex Amp hC }

end CrystallineSemistableComparison
