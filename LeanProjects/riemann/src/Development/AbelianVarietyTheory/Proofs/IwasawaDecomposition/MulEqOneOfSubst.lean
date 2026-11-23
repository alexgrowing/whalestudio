import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoefSetNonemptyOfNonneg
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LieImgIffIsLieCombStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueConstantTangentVectorsAlongArcStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans

set_option maxHeartbeats 800000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts
open GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.GradedPieces GlobalTheory.LieMet
open GlobalTheory.ArcQ (Wit LieImg ArcBasis)
open GlobalTheory.IndefiniteRowSideFullHecke.SectionsThroughEpsilonPoints (EpsPt IsLetters IsCombGt)

namespace GlobalTheory.LocM.FJ.FlagIndep

attribute [local instance] Over.cartesianMonoidalCategory

section Linear

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m : ℕ}

end Linear

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {X : Scheme.{0}} {t : SAB H X}
  {k : Type} [Field k] {y : Sp k ⟶ X} {m : ℕ}

theorem eig_of_comb {v : Fin m → (Sp (DualNumber k) ⟶ t.G.left)} (hv : ∀ i, IsTanAtG t y (v i)) {lam : 𝓞 E → k}
    (he : ∀ i a, v i ≫ (t.act.act a).left = spMap (epsMul (lam a)) ≫ v i) {cf : Fin m → k}
    {w : Sp (DualNumber k) ⟶ t.G.left} (hw : IsTanAtG t y w) (hc : IsCombAtG t y v cf w) (a : 𝓞 E) :
    w ≫ (t.act.act a).left = spMap (epsMul (lam a)) ≫ w := by
  have key : ∀ i, actR t.act a (tanOf (hv i)) = lam a • tanOf (hv i) := fun i => tan_ext (he i a)
  have e := (comb_iff hv cf hw).1 hc
  have : actR t.act a (tanOf hw) = lam a • tanOf hw := by
    rw [e, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, key, smul_comm]
  exact congrArg (fun z => (tv z).left) this

end Tangent

section Arcs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {F : DVF p}

def cst (F : DVF p) : F.O →+* LaurentSeries ↥F.K := F.toLaurent.comp PowerSeries.C

variable {b : Z.i.c.V W →+* F.O} {a : ArcIn Dw Z.i.l (Z.i.c.V W).subtype F.O b} {χ : Sp (PowerSeries F.O) ⟶ (Y Z.i).X}

def arcVec (Wt : Wit (Y Z.i) a χ) (w : epsR (PowerSeries F.O) ⟶ Wt.t.G) :
    Sp (DualNumber (LaurentSeries ↥F.K)) ⟶ (Y Z.i).t.G.left :=
  spMap (dualMap F.toLaurent) ≫ w.left ≫ Wt.m.φ

end Arcs

section Series

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  {Z : Mdl Y i₀} {F : DVF p}

theorem linInd_of_frame {X : Scheme.{0}} {t : SAB H X} {k : Type} [Field k] {y : Sp k ⟶ X} {l : Level H} {c : Coeff l}
    {f : c.F →+* k} {v : Vecs Dw t k} (h : IsFrame t f y v) (τ : E →+* ℂ) :
    LinearIndependent k fun i => tanOf (h.1 τ i).1 := by
  refine Fintype.linearIndependent_iffₛ.2 fun c c' e => ?_
  have hw := isTan_tv (∑ i, c i • tanOf (h.1 τ i).1)
  have hc : IsCombAtG t y (v τ) c (tv (∑ i, c i • tanOf (h.1 τ i).1)).left :=
    (comb_iff (fun i => (h.1 τ i).1) c hw).2 rfl
  have hc' : IsCombAtG t y (v τ) c' (tv (∑ i, c i • tanOf (h.1 τ i).1)).left :=
    (comb_iff (fun i => (h.1 τ i).1) c' hw).2 e
  exact fun i => congrFun ((h.2 τ _ hw (eig_of_comb (fun i => (h.1 τ i).1) (fun j a => (h.1 τ j).2 a) hw hc)).unique hc hc') i

variable (hty : ∀ σ, Z.ty σ = Finset.range (Dw.mult σ + 1)) {e : ∀ σ : E →+* ℂ, Fin (Dw.mult σ) → ℤ} {Mo : Z.X.Modules}
  (T : GrTriv Z e Mo) (f : Γ(Mo, Z.genO))

end Series

end GlobalTheory.LocM.FJ.FlagIndep
