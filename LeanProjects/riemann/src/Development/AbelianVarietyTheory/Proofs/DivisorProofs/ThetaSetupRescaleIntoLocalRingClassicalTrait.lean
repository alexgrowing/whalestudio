import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemMovedToAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLiftRechart

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X.M.s → ∀ (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z), ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧ ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := by
  intro g n F W Z i X hg hn ho himm he8 hth hproj ε hε p _ z c
  set w : X.M.Z := (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw
  have hwr : X.π w ∈ Set.range i := by
    refine ⟨(spMap c.ι ≫ c.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)), ?_⟩
    have h := congrArg (fun f => f (IsLocalRing.closedPoint (PadicAlgCl p))) c.comm
    rw [hw]
    exact h.symm
  obtain ⟨U, c₀, hc, fg, frac, hth', hev, ρ', ε', u', hUa, hwU, hUi, hSame, hi₀, hdiag, hcomp⟩ :=
    GlobalTheory.T.exists_thetaSystem_moved_to_affineOpen g n F W Z i X hg hn ho himm he8 hth hproj ε hε w hwr
  have hle : X.M.ringOn (U : Set X.M.Z) ≤ X.M.O w := RatModel.ringOn_le_O hwU
  refine ⟨c₀, hc, X.M.ringOn (U : Set X.M.Z), fg, frac, hth', hev, ρ', ε', hSame, hi₀, hle, ?_⟩
  refine ⟨(X.M.valHom (gPt p ≫ c.y) w (RatModel.range_eq_singleton _ _)).comp
    (Subalgebra.inclusion hle).toRingHom, fun a => rfl, fun a => ?_⟩
  have hmem : algebraMap X.o₁ X.Ω₁ a ∈ X.M.O z := Subalgebra.algebraMap_mem _ a
  have h1 := c.norm_val_le ((X.M.stalkEquiv z).symm ⟨_, hmem⟩)
  simp only [CTrait.val] at h1
  rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply] at h1
  simpa using h1

end GlobalTheory.Poinc.GLiftRechart
