import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtEqOfPtOfFrameEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDomainCoordinatesHolomorphic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAndFderivMoebI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainArithmeticGroupLocallyInjectiveStatement
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped ComplexOrder Topology
open ReciprocityTheory.L2DbarEstimates (V)
open ReciprocityTheory.ChartRestriction.G.FD (Frame mat)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifSlice

open Matrix Formalism.DegreeFormula GlobalTheory.TrueCx ReciprocityTheory.ChartRestriction.G.FD

theorem locInj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ z₀ ∈ Formalism.DegreeFormula.DomI Tau j (r - j), ∃ O : Set (Tau → Matrix (Fin j) (Fin (r - j)) ℂ), IsOpen O ∧ z₀ ∈ O ∧ ∀ z ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ z' ∈ O ∩ Formalism.DegreeFormula.DomI Tau j (r - j), ∀ γ ∈ X.Γ, z' = Formalism.DegreeFormula.moebI (GlobalTheory.TrueCx.toUpq X hj κ γ) z → z = z' := GlobalTheory.T.boundedDomain_arithmeticGroup_locally_injective

theorem domPt_rel_of_pt_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r)
    (hU : Formalism.L2.PjFree.IsUnf U) (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    (k : U.Comp) {j : ℕ} (hj : j ≤ r) (hp : (U.X k).p0 = r - j) {Tau : Type} [Fintype Tau] (κ : Tau ≃ (U.X k).Ψ)
    (x x' : (U.X k).dom) (h : (U.un k x).x = (U.un k x').x) :
    ∃ γ ∈ (U.X k).Γ, domPt (U.X k) hj κ x'.1 = moebI (toUpq (U.X k) hj κ γ) (domPt (U.X k) hj κ x.1) := by
  obtain ⟨b, hb, hb0, hm, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor U hU hσ k x (U.un k x') h
  obtain ⟨γ, hγ, b', hb', e⟩ := (hU.2.2.2.1 k k ⟨_, hm⟩ x').1 ⟨t, ht⟩
  have e' : x'.1 = rmul (lact γ (rmul x.1 b)) b' := eq_of_heq (Sigma.mk.inj e).2
  refine ⟨γ, hγ, ?_⟩
  rw [e', domPt_rmul _ hj κ hb', domPt_lact _ hj κ hp γ hm,
    GlobalTheory.PointOfFrames.domPt_rmul_block _ hj κ _ b hb (by rw [← hp]; exact hb0)]

theorem flat_unflat {ι : Type} {p q : ℕ} (v : ι × Fin p × Fin q → ℂ) : flat (unflat v) = v := by
  funext ⟨i, a, b⟩; rfl

theorem unflat_flat {ι : Type} {p q : ℕ} (z : ι → Matrix (Fin p) (Fin q) ℂ) : unflat (flat z) = z := by
  funext i; ext a b; rfl

theorem continuous_unflat {ι : Type} {p q : ℕ} :
    Continuous (unflat : (ι × Fin p × Fin q → ℂ) → ι → Matrix (Fin p) (Fin q) ℂ) :=
  continuous_pi fun _ => continuous_matrix fun _ _ => continuous_apply _

theorem exists_slice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (n : ℕ), n = (U.X k).Ψ.card * (Dw.p * Dw.q) → ∃ (W : Set (V n)) (a : V n) (ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q)), IsOpen W ∧ a ∈ W ∧ (∀ w ∈ W, ψ w ∈ (U.X k).dom) ∧ (∀ τ i i', DifferentiableOn ℂ (fun w => mat (ψ w) τ i i') W) ∧ (∀ h : ψ a ∈ (U.X k).dom, (U.un k ⟨ψ a, h⟩).x = (U.un k x₀).x) ∧ ∀ w ∈ W, ∀ w' ∈ W, ∀ (h : ψ w ∈ (U.X k).dom) (h' : ψ w' ∈ (U.X k).dom), (U.un k ⟨ψ w, h⟩).x = (U.un k ⟨ψ w', h'⟩).x → w = w' := by
  intro E _ _ _ H Dw l Xo c σ U hσ hU k x₀ n hn
  classical
  have hj : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  have hcard : Fintype.card ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) = n := by
    rw [hn, Fintype.card_prod, Fintype.card_prod, Fintype.card_coe, Fintype.card_fin, Fintype.card_fin,
      Nat.add_sub_cancel_left]
  let f : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p)) ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let L : V n ≃L[ℂ] ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) :=
    (EuclideanSpace.equiv (Fin n) ℂ).trans (LinearEquiv.funCongrLeft ℂ ℂ f).toContinuousLinearEquiv
  set z₀ := domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 with hz₀
  have hz₀D : z₀ ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) := domPt_mem (U.X k) hj _ hp x₀.2
  obtain ⟨O, hO, hz₀O, hinj⟩ := locInj E (Dw.p + Dw.q) Dw.p (U.X k) hj (U.X k).Ψ (Equiv.refl _) hp z₀ hz₀D
  let ψ : V n → Frame (U.X k).Ψ (Dw.p + Dw.q) := fun w => SecFrame.frameAt (U.X k) hj (Equiv.refl _) (unflat (L w))
  have hdom : ∀ w, unflat (L w) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) → ψ w ∈ (U.X k).dom := fun w hw =>
    SecFrame.frameAt_mem (U.X k) hj _ hp hw
  have hpt : ∀ w, domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ w) = unflat (L w) := fun w => SecFrame.domPt_frameAt (U.X k) hj _ _
  refine ⟨{w | unflat (L w) ∈ O} ∩ L ⁻¹' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), L.symm (flat z₀), ψ,
    (hO.preimage (continuous_unflat.comp L.continuous)).inter
      (GlobalTheory.HodgeDomain.ActionDeriv.isOpen_domFlat.preimage L.continuous), ?_, fun w hw => hdom w hw.2,
    fun τ i i' => ((SecFrame.differentiable_frameAt (U.X k) hj (Equiv.refl _) τ i i').comp L.differentiable).differentiableOn,
    fun h => ?_, fun w hw w' hw' h h' e => ?_⟩
  · refine ⟨?_, ?_⟩
    · show unflat (L (L.symm (flat z₀))) ∈ O
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀O
    · show unflat (L (L.symm (flat z₀))) ∈ DomI (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p)
      rw [L.apply_symm_apply, unflat_flat]; exact hz₀D
  · have e0 : domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) (ψ (L.symm (flat z₀))) = domPt (U.X k) hj (Equiv.refl (U.X k).Ψ) x₀.1 := by
      rw [hpt, L.apply_symm_apply, unflat_flat]
    have h5 : ∀ τ, Formalism.MJ.moeb (frameCo (U.X k) hj (ψ (L.symm (flat z₀))) τ) 0 = Formalism.MJ.moeb (frameCo (U.X k) hj x₀.1 τ) 0 :=
      fun τ => congrFun e0 τ
    exact PointWell.pt_eq_of_block hU hσ k ⟨_, h⟩ x₀
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp h x₀.2 τ (h5 τ))
      (fun τ => PointWell.block_of_moeb_eq (U.X k) hj hp x₀.2 h τ (h5 τ).symm)
  · obtain ⟨γ, hγ, hγe⟩ := domPt_rel_of_pt_eq U hU hσ k hj hp (Equiv.refl (U.X k).Ψ) ⟨_, h⟩ ⟨_, h'⟩ e
    have hγe' : unflat (L w') = moebI (toUpq (U.X k) hj (Equiv.refl (U.X k).Ψ) γ) (unflat (L w)) := by
      rw [← hpt w', ← hpt w]; exact hγe
    have h1 := hinj _ ⟨hw.1, hw.2⟩ _ ⟨hw'.1, hw'.2⟩ γ hγ hγe'
    have h2 : L w = L w' := by rw [← flat_unflat (L w), h1, flat_unflat]
    exact L.injective h2

end GlobalTheory.UnifSlice
