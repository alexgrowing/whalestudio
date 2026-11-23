import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsSecOfLocal

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PtTie

section Move
open GlobalTheory.FieldBaseChange
variable {X' X X₁ X₂ Y Y₁ : Scheme.{0}} {L' : LB X'}

def isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) : LB.Iso (L'.pull (𝟙 X')) (L.pull m) :=
  ⟨fun p => res (fun _ hy => ⟨hy.1, mem_pull.1 hy.2⟩ :
    (L.pull m).U p.1 ⊓ (L'.pull (𝟙 X')).U p.2 ≤ (L.pull m).U p.1 ⊓ L'.U (p.2 PUnit.unit)) (w.s (p.1, p.2 PUnit.unit))⟩

theorem isoVal_isoFromPullId {L : LB X} {m : X' ⟶ X} (w : LB.Iso L' (L.pull m)) {Z : Scheme.{0}} (r : Z ⟶ X') (z : Z)
    (j : L.ι) (k : L'.ι) (hj : m (r z) ∈ L.U j) (hk : r z ∈ L'.U k) :
    isoVal (isoFromPullId w) r z j k = gv w r z (fun _ => j) k := by
  have hm : r z ∈ (L.pull m).U (fun _ => j) ⊓ (L'.pull (𝟙 X')).U (fun _ => k) := ⟨mem_pull.2 hj, mem_pull.2 hk⟩
  show gm r z _ (res _ (w.s (fun _ => j, k))) = _
  exact gm_res r z _ hm _

theorem isoFromPullId_isGen {L : LB X} {m : X' ⟶ X} {w : LB.Iso L' (L.pull m)} (hw : w.IsGen) :
    (isoFromPullId w).IsGen := by
  refine (isGen_iff _).2 fun Z r z j j' k k' hj hj' hk hk' => ?_
  have ik : r z ∈ L'.U (k PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk
  have ik' : r z ∈ L'.U (k' PUnit.unit) := (mem_pull (F := 𝟙 X') (x := r z)).1 hk'
  have a := isoVal_isoFromPullId w r z j (k PUnit.unit) hj ik
  have a' := isoVal_isoFromPullId w r z j' (k' PUnit.unit) hj' ik'
  have b := (isGen_iff w).1 hw Z r z j j' _ _ hj hj' ik ik'
  have c := (gm_pull_g L' (𝟙 X') r z k k' hk hk').trans
    (congrArg (fun f : Z ⟶ X' => gm f z _ (L'.g (k PUnit.unit) (k' PUnit.unit))) (Category.comp_id r))
  refine a.trans (b.trans ?_)
  exact congrArg₂ (fun s t => _ * s⁻¹ * t) c.symm a'.symm

end Move

section Comparison₂
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : letI := io.toAlgebra; FrPt Xo c T.Fr}
  {I : IntData Xo c T io y} {F : Type} [Field F] [Algebra T.Fr F] {xF : Sp F ⟶ Xo.X}

variable (I) (P : PELUnif (maximalIdeal T.V) I.G)

end Comparison₂

end GlobalTheory.PtTie
