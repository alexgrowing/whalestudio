import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjUniversalTripleIdentification
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GalLabAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_universalTriple_identification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (a : D.X.S.Gam ≃+ D.X.S.Gam), D.GalLab σ a → ∀ (c₀ : D.X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra D.X.o₁ D.X.Ω₁) (fg : R'.FG) (frac : ∀ x : D.X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * D.X.S.th x ∈ R') (hev : ∀ x k, c₀ * D.X.S.ev x k ∈ R') (ρ' : (D.X.S.rechart c₀ hc R' fg frac hth hev).Real) (u' : Sp (ratHull R') ⟶ Xo.XF cf), USame D.X.ρ ρ' (fun x => x) (RingHom.id _) → spMap (ratHull R').val.toRingHom ≫ u' = D.X.uΩ → ∀ (G : Over (Sp (ratHull R'))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat R')) α → IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β → LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) → ∃ (wi : UWit D.X) (W₀ : Over (Sp D.X.Ω₁)) (_ : GrpObj W₀) (e : W₀.left ⟶ wi.G.left) (k₀ : W₀.left ⟶ G.left), IsGrpPullback W₀ wi.G (spMap (σ : D.X.Ω₁ →+* D.X.Ω₁)) e ∧ IsGrpPullback W₀ G (spMap (ratHull R').val.toRingHom) k₀ ∧ e ≫ wi.β = k₀ ≫ β ∧ ∀ x (w : Sp D.X.Ω₁ ⟶ wi.G.left), w ≫ wi.α = spMap D.X.S.R.val.toRingHom ≫ (D.X.ρ.pt x).left → ∃ w₀ : Sp D.X.Ω₁ ⟶ W₀.left, w₀ ≫ W₀.hom = 𝟙 _ ∧ w₀ ≫ e = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ w ∧ w₀ ≫ k₀ ≫ α = spMap R'.val.toRingHom ≫ (ρ'.pt (a x)).left := by
  first | exact @GlobalTheory.UPoinc.UGalTrans.exists_conj_uWit | exact GlobalTheory.UPoinc.UGalTrans.exists_conj_uWit | (intros; apply GlobalTheory.UPoinc.UGalTrans.exists_conj_uWit <;> assumption)
