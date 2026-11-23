import Mathlib
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.ExtLBAmb
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.MetricGlue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionCalculusOfFormMixedProjectionStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

namespace GlobalTheory.Published.Amb

variable {k : Type} [CommRing k] {X : Scheme.{0}}

private theorem comb_isometric_of_isometric {p : X ⟶ Sp k} {ι : Type} [Fintype ι] {L L' : ι → HermLB p}
    (hL : ∀ j, (L j).Isometric (L' j)) (n : ι → ℤ) : (comb L n).Isometric (comb L' n) := by
  unfold comb
  induction (Finset.univ : Finset ι).toList with
  | nil => exact HermLB.Isometric.refl _
  | cons i l ih =>
    simp only [List.foldr_cons]
    refine HermLB.Isometric.tens ?_ ih
    unfold zp
    exact HermLB.Isometric.tens (HermLB.Isometric.pow (hL i) _) (HermLB.Isometric.dual (HermLB.Isometric.pow (hL i) _))

theorem mixOn_congr [IsIntegral X] [IsLocallyNoetherian X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {ι : Type}
    [Fintype ι] {M M' : HermLB p} {L L' : ι → HermLB p} (hM : M.Isometric M') (hL : ∀ j, (L j).Isometric (L' j))
    (H : MixOn p D ι M L) : MixOn p D ι M' L' := by
  intro Φ hΦ n h hh r hr
  have hfam : ∀ o : Option ι, (o.elim M' L').Isometric (o.elim M L) := by
    intro o
    cases o with
    | none => exact HermLB.Isometric.symm hM
    | some j => exact HermLB.Isometric.symm (hL j)
  have hΦ' : IsArFun (fun o : Option ι => o.elim M L) D Φ :=
    ⟨fun n' => HermLB.Isometric.isSelfInter hX (comb_isometric_of_isometric hfam n') (hΦ.1 n'), hΦ.2⟩
  have hcomb : (comb L' n).Isometric (comb L n) := comb_isometric_of_isometric (fun j => HermLB.Isometric.symm (hL j)) n
  have hh' : (comb L n).IsArithHeight h := HermLB.Isometric.isArithHeight hX hcomb hh
  obtain ⟨r0, hr0, hdiv, hlog⟩ := HermLB.Isometric.exists_isRatSec (HermLB.Isometric.symm hM) hr
  obtain ⟨hint, heq⟩ := H Φ hΦ' n h hh' r0 hr0
  have hms : ∀ σ, MeasurableSet (offSupp p σ (M'.div hr)) := fun σ => (isOpen_offSupp _).measurableSet
  refine ⟨fun σ => ?_, ?_⟩
  · have hi := hint σ
    rw [HermLB.Isometric.chernIntegrableOn_eq (HermLB.Isometric.symm hcomb) σ D, hdiv] at hi
    exact hi.congr (hms σ) (hlog σ)
  · rw [heq, hdiv, sub_right_inj]
    simp only [HermLB.archInt]
    rw [hdiv]
    apply finsum_congr
    intro σ
    rw [HermLB.Isometric.chernInt_eq (HermLB.Isometric.symm hcomb) σ D]
    exact Weight.chernInt_congr (hms σ) (hlog σ)

theorem pull_congr {Y P : Scheme.{0}} {p : P ⟶ Sp k} {q : Y ⟶ Sp k} (M : HermLB p) {f g : Y ⟶ P} (e : f = g)
    (hf : f ≫ p = q) (hg : g ≫ p = q) : M.pull f hf = M.pull g hg := by
  subst e; rfl

theorem dim_closure_image {P : Scheme.{0}} (i : X ⟶ P) [IsClosedImmersion i] (x : X) :
    topologicalKrullDim (closure ({i x} : Set P)) = topologicalKrullDim (closure ({x} : Set X)) := by
  have hi : Topology.IsClosedEmbedding i := i.isClosedEmbedding
  have hE : Topology.IsEmbedding (fun z : closure ({x} : Set X) => i z.1) :=
    hi.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hset : closure ({i x} : Set P) = Set.range (fun z : closure ({x} : Set X) => i z.1) := by
    rw [← Set.image_singleton, hi.closure_image_eq]
    ext y
    simp
  rw [hset]
  exact (IsHomeomorph.topologicalKrullDim_eq _ hE.toHomeomorph.isHomeomorph).symm

end GlobalTheory.Published.Amb
