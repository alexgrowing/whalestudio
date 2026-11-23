import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSpanningHypotheses
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsUnitGramFrameBorelChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsHermCoordOfDatum

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Dict

theorem perFr_castFr_of_sameSp {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r}
    (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X' x v τ i = Formalism.L2.PjFree.perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X'
  cases X
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem exists_anFib_all_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ n : ℕ, Even n → ∃ s : c.F →+* ℂ, letI : Algebra c.F ℂ := s.toAlgebra; ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)), IsSympl X bas ∧ r = Dw.p + Dw.q ∧ (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧ (∀ j, rowType X (idx j) = relab c s (e j).1) ∧ ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r), FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀) := by
  intro E _ _ _ H Dw l Xo c h1 n hn
  obtain ⟨ξ, hξ, hξ0, hneg⟩ := GlobalTheory.SpanInhab.exists_imag_neg H
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ)
    (by rw [show cc (-ξ) = -cc ξ by simp [cc], hξ]) (neg_ne_zero.2 hξ0) _ rfl
  have hσ : Formalism.L2.PjFree.GoodEmb c c.F.val.toRingHom := rfl
  generalize c.F.val.toRingHom = σ at hσ
  obtain ⟨U, hU, -, ⟨k₀⟩, -, hG, -⟩ :=
    GlobalTheory.FrameUnif.exists_unf_hasPrinc E H Dw l Xo c σ _ ξ Gm φ h1 hσ hξ hneg hφ
  obtain ⟨W⟩ := nonempty_uw hU
  have huw := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ _ U hσ hU h1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k).1.trans (hG k₀).1.symm,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k).2.trans (hG k₀).2.symm,
      by rw [(huw k).1, (huw k₀).1, (hG k).2, (hG k₀).2]⟩
  have hdom : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) n := ⟨fun _ => antitone_const, hn⟩
  choose Dc hDe using fun k => GlobalTheory.Dict.exists_dic E H Dw l c σ _ W.g n (U.X k) (fun _ => 0) W.e hσ rfl
    (hU.2.1 k).1 (hU.2.1 k).2 (huw k).2.1 hdom
  have hper : ∀ k x v j, pv (U.X k) (Dc k).idx x v j =
      Formalism.L2.PjFree.perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2 := fun k x v j => by
    rw [(Dc k).per_eq, (hDe k).1]
  have hty : ∀ k j, rowType (U.X k) ((Dc k).idx j) = relab c σ (W.e j).1 := fun k j => by
    rw [(Dc k).ty_eq, (hDe k).1]
  refine ⟨σ, _, W.g, U.X k₀, (Dc k₀).bas, (Dc k₀).idx, W.e, (Dc k₀).hr, (Dc k₀).eL, (Dc k₀).sympl, rfl,
    fun ℓ => ?_, hty k₀, fun y => ?_⟩
  · rw [(Dc k₀).dir_eq, (hDe k₀).1]
  · let _ : Algebra c.F ℂ := σ.toAlgebra
    obtain ⟨k, x, t, hx, ht⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ _ U hσ hU).2 y
    obtain ⟨A, -⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ _ U hσ hU h1 W k (Dc k).bas (Dc k).idx (Dc k).sympl
      (hper k) (hty k) x hx
    obtain ⟨e1, -, e2, A', -⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c _ W.g (U.X k) (U.X k₀) (hsame k)
      (Dc k).bas (Dc k).idx (Dc k₀).bas (Dc k₀).idx W.e x.1 (U.X k).Λ (unC U k x) A 1 (Dc k).sympl (Dc k₀).sympl
      x.2 (huw k).2.1 (by simp [IsUn])
      (fun v => funext fun j => by rw [hper, hper, perFr_castFr_of_sameSp (hsame k)])
      (fun j => by rw [hty, hty])
    exact ⟨unC U k x, t, _, _, ht, e1, e2, ⟨A'⟩⟩

end GlobalTheory.Dict
