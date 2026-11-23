import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntegralPullMulDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithAmbientVerticalOrArithmeticVarietyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedArchRestrictedEqZeroOfNoComplexPointsStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.MixHt
open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull GlobalTheory.MultPull GlobalTheory.Points

variable {k : Type} [CommRing k]

theorem isEmpty_cxPts_of_map {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q)
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) :=

  isEmpty_iff.2 fun y => isEmpty_iff.1 (h σ) (PtsOver.map g hg (spMap σ) y)

theorem mixArch_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (hp : IsAmb p) (hq : IsAmb q) (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X) [IsIso g]
    (e : ℕ) (hX : topologicalKrullDim X = (e + 1 : ℕ)) (L : Fin e → HermLB p) (M : HermLB p)
    (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) :
    mixArch (fun a => (L a).pull g hg) (M.pull g hg)
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      mixArch L M hr := by
  have hY : topologicalKrullDim Y = (e + 1 : ℕ) :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso g)).isHomeomorph).trans hX
  have hg' : inv g ≫ q = p := by rw [← hg, IsIso.inv_hom_id_assoc]
  by_cases hp0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)
  · rw [(GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k X p hp0 e L M).1 r hr]
    exact (GlobalTheory.T.mixedArch_restricted_eq_zero_of_no_complexPoints k Y q (isEmpty_cxPts_of_map g hg hp0) e _ _).1 _ _
  by_cases hq0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)
  · exact absurd (isEmpty_cxPts_of_map (inv g) hg' hq0) hp0
  obtain ⟨e₁, he₁, hXa⟩ := (GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k X p hp (e + 1) hX).resolve_left fun ⟨_, _, _, h⟩ => hp0 h
  obtain ⟨e₂, he₂, hYa⟩ := (GlobalTheory.T.projArithAmbient_vertical_or_arithmeticVariety k Y q hq (e + 1) hY).resolve_left fun ⟨_, _, _, h⟩ => hq0 h
  obtain rfl : e₁ = e := by omega
  obtain rfl : e₂ = e₁ := by omega
  unfold mixArch
  congr 2
  funext n
  have h₁ : (comb (fun a => (L a).pull g hg) n).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      ((comb L n).pull g hg).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) := by
    simp only [HermLB.archInt, (isometric_comb_pull L n g hg).chernInt_eq]
  rw [h₁, GlobalTheory.T.archimedeanIntegral_pull_mul_degree k X Y p q e₂ hXa hYa g hg hη (by rw [Published.residueDegree_of_isClosedImmersion]; exact one_ne_zero),
    Published.residueDegree_of_isClosedImmersion, Nat.cast_one, one_mul]

theorem mult_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) ⤳ genericPoint X) [IsIso g]
    (M : HermLB p) {r : M.B.ι → X.functionFieldˣ} (hr : IsRatSec M.B r) (y : Y) :
    ((M.pull g hg).div (MultPull.isRatSec_pull_map g hη hr)).mult y = (M.div hr).mult (g y) := by
  change (divOfRatSec (LB.isLB_pull M.isLB g) (MultPull.isRatSec_pull_map g hη hr)).mult y =
    (divOfRatSec M.isLB hr).mult (g y)
  obtain ⟨c, hc⟩ := exists_chart (LB.isLB_pull M.isLB g) y
  have hc' : g y ∈ M.B.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
  rw [((presents_divOfRatSec _ _).isEqn c y hc).mult_eq,
    ((presents_divOfRatSec M.isLB hr).isEqn _ _ hc').mult_eq]
  exact ord_fnMap g hη y _

theorem transport : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), IsIso g → ∀ e : ℕ, topologicalKrullDim X = (e + 1 : ℕ) → ∀ (h : X → ℝ) (L : Fin e → HermLB p) (M : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), recVal (fun w => h (g w)) (fun a => (L a).pull g hg) (M.pull g hg) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = recVal h L M hr := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη _ e hX h L M r hr
  unfold recVal
  rw [mixArch_pull_iso p q hp hq g hg hη e hX L M r hr]
  congr 1
  refine (finsum_congr fun z => ?_).trans
    (finsum_comp_equiv (Scheme.homeoOfIso (asIso g)).toEquiv (f := fun x => ((M.div hr).mult x : ℝ) * h x))
  exact congrArg (fun n : ℤ => (n : ℝ) * h (g z)) (mult_pull_iso g hg _ M hr z)

end GlobalTheory.MixHt
