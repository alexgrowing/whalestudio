import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointPoly
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMoebZero
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompMapAndFrDense
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.UnfInv

theorem one_mem_bor {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) :
    (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) ∈ ReciprocityTheory.ChartRestriction.G.FD.Bor Ψ r := by
  intro τ
  refine ⟨?_, fun a b hab => ?_⟩
  · change ¬ (1 : Matrix (Fin r) (Fin r) ℂ).det = 0
    simp
  · simp [Matrix.one_apply, (ne_of_lt hab).symm]

theorem rmul_one {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) (r : ℕ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) :
    ReciprocityTheory.ChartRestriction.G.FD.rmul x (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ)) = x := by
  funext τ
  show ReciprocityTheory.ChartRestriction.G.FD.mat x τ * ReciprocityTheory.ChartRestriction.G.FD.mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) τ = x τ
  rw [show ReciprocityTheory.ChartRestriction.G.FD.mat (fun _ => (1 : Matrix (Fin r) (Fin r) ℂ) : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) τ = 1 from rfl,
    Matrix.mul_one]
  rfl

theorem psi_moebI_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ ψ : ((U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ) → CxPts X.str (σ.comp e.toRingHom), (∀ x : (U.X k).dom, cxOf e σ hj (ψ (flat (domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) x.1))) = cxPt T.Z (U.un k x)) → ∀ γ ∈ gammaU (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ), ∀ v ∈ DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p), ψ (flat (moebI γ (unflat v))) = ψ v := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ γ hγ v hv
  obtain ⟨-, hk, -, h4, -⟩ := hU
  have hp0 : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by rw [(hk k).1]; omega
  haveI : IsOpenImmersion j := hL.1
  have hinj : Function.Injective (GlobalTheory.LieBase.cxOf (Z := T.Z) e σ hj) := by
    intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact (cancel_mono j).1 this
  obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.1 hγ
  obtain ⟨x, hx, hxv⟩ := FrameOnto.frame_onto E (Dw.p + Dw.q) Dw.p (U.X k) (Nat.le_add_right Dw.p Dw.q)
    (U.X k).Ψ (Equiv.refl _) hp0 (unflat v) hv
  have hx' : ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x ∈ (U.X k).dom := GlobalTheory.Reg.GenericFrameDensity.lact_mem_dom _ hγ₀ hx
  have hdom : domPt (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) (ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x) =
      moebI (toUpq (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) γ₀) (unflat v) := by
    rw [domPt_lact (U.X k) (Nat.le_add_right Dw.p Dw.q) (Equiv.refl (U.X k).Ψ) hp0 γ₀ hx]
    exact congrArg _ hxv
  have h1 := hψ ⟨x, hx⟩
  have h2 := hψ ⟨_, hx'⟩
  simp only at h1 h2
  rw [hxv] at h1
  rw [hdom] at h2
  apply hinj
  have h1' : GlobalTheory.LieBase.cxOf (Z := T.Z) e σ hj (ψ v) = cxPt T.Z (U.un k ⟨x, hx⟩) := h1
  rw [h2, h1']
  apply GlobalTheory.ShFam.cxPt_congr
  have hx'' : (⟨k, (⟨ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ x, hx'⟩ : (U.X k).dom).1⟩ : Σ k, ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ (Dw.p + Dw.q)) =
      ⟨k, ReciprocityTheory.ChartRestriction.G.FD.rmul (ReciprocityTheory.ChartRestriction.G.FD.lact γ₀ (⟨x, hx⟩ : (U.X k).dom).1)
        (fun _ => (1 : Matrix (Fin (Dw.p + Dw.q)) (Fin (Dw.p + Dw.q)) ℂ))⟩ := by
    rw [rmul_one]
  obtain ⟨t, ht⟩ := (h4 k k ⟨x, hx⟩ ⟨_, hx'⟩).2 ⟨γ₀, hγ₀, _, one_mem_bor _ _, hx''⟩
  exact ht.1

end GlobalTheory.UnfInv
