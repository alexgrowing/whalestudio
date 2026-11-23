import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

namespace GlobalTheory.DetHT.BridgeBasis

theorem mem_latHT_iff_changeBasis : BridgeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F))
    (p : ℕ) [Fact p.Prime] [Algebra c.F ℂ_[p]] (yy : Sp ℂ_[p] ⟶ Xo.XF c) (yb : Sp 𝓞_ℂ_[p] ⟶ Z.X),
    letI := H.starRing; ∀ (Q : PtP E p) (π : Q.G.left ⟶ Z.t.G.left) (ψ : Q.A.A.left ⟶ Z.oF.t.G.left),
      PtAt Z yb yy Q π ψ → ∀ (n : ℕ) (xx : Fin n → LieG Q.Gt) (u u' : Fin n → (Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left))
      (g : Matrix (Fin n) (Fin n) ℂ_[p]), (∀ j, IsTanAtG Z.t (yy ≫ Z.j) (u j)) →
      (∀ j, LieTie Q (Q.gen ≫ π) (xx j) (u j)) → (∀ i, IsCombAtG Z.t (yy ≫ Z.j) u (g i) (u' i)) →
      ∀ (a : Fin n → ℂ_[p]) (w : Sp (DualNumber ℂ_[p]) ⟶ Z.t.G.left), IsCombAtG Z.t (yy ≫ Z.j) u' a w →
        (w ∈ GlobalTheory.ShFam.Pad.latHT Z.t p (yy ≫ Z.j) ↔ ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT) := by
  intro hB E _ _ _ H Dw l Xo c Z p _ _ yy yb
  letI := H.starRing
  intro Q π ψ hP n xx u u' g hu hx hg a w hw
  haveI : IsProper Z.s := projProper _ _ _ Z.proj
  haveI : IsNoetherianRing (𝓞 c.F) := Algebra.FiniteType.isNoetherianRing ℤ (𝓞 c.F)
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  haveI : Z.X.IsSeparated := ⟨by rw [← terminal.comp_from Z.s]; infer_instance⟩
  have hc : IsCombAtG Z.t (yy ≫ Z.j) u (g.transpose.mulVec a) w :=
    GlobalTheory.TangentLinear.isCombAtG_mulVec u hu u' g.transpose a w (fun i => by simpa [Matrix.transpose_apply] using hg i) hw
  rw [← hP.1] at hc
  have key := hB E H Z.X Z.t p Q yb π hP.2.1 n xx u hx (g.transpose.mulVec a) w hc
  rw [hP.1] at key
  rw [key]
  have hs : ∑ j, (g.transpose.mulVec a) j • Q.bLie (xx j) = ∑ i, a i • ∑ j, g i j • Q.bLie (xx j) := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [_root_.mul_comm]
  rw [hs]

end GlobalTheory.DetHT.BridgeBasis
