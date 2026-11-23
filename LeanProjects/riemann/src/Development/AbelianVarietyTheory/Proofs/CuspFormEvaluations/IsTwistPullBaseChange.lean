import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistBaseChange

theorem eq_pullS_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (a : ℤ) {T T' : Over S}
    (h : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) s s') : s' = GlobalTheory.VVRank.pullS A a h s := by

  exact DVR.SecOps.sec_ext H

theorem isTwistPull_baseChange : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (L : LB A.left), L.IsLB → ∀ (T T' : Over S) (h : T' ⟶ T) (ψ : T ⊗ A ⟶ T ⊗ A) (m : T ⊗ A ⟶ A) (hm : ψ ≫ snd T A = m) (ψ' : T' ⊗ A ⟶ T' ⊗ A) (m' : T' ⊗ A ⟶ A) (hm' : ψ' ≫ snd T' A = m'), ψ' ≫ h ▷ A = h ▷ A ≫ ψ → ∀ (a b : ℤ) (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T' A).left, m'.left] ![a, -b])), α.IsGen → α'.IsGen → LB.Gen.Corr L _ _ _ _ α' (LB.pullGen L _ _ α (h ▷ A).left) → ∀ (s : LB.Sec (LPow A L b T)) (t : LB.Sec (LPow A L a T)) (s' : LB.Sec (LPow A L b T')) (t' : LB.Sec (LPow A L a T')), IsTwistPull A L ψ m hm a b α s t → IsPullSec A L b (h ▷ A) (whiskerRight_snd _ _) s s' → IsPullSec A L a (h ▷ A) (whiskerRight_snd _ _) t t' → IsTwistPull A L ψ' m' hm' a b α' s' t' := by
  intro S A _ L hL T T' h ψ m hm ψ' m' hm' hψ a b α α' hα hα' hcorr s t s' t' hst hs ht
  obtain rfl := eq_pullS_of_isPullSec A b h hs
  obtain rfl := eq_pullS_of_isPullSec A a h ht

  have e : ψ'.left ≫ (h ▷ A).left = (h ▷ A).left ≫ ψ.left := by
    rw [← Over.comp_left, hψ, Over.comp_left]
  refine GlobalTheory.VVRank.isTwistPull_of_sv A hL hα' (fun y J hJ => ?_)

  have hv : val α' (𝟙 _) y J = val α (𝟙 _ ≫ (h ▷ A).left) y J :=
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_corr hJ hcorr _).trans (ReciprocityTheory.ChartRestriction.G.Geo.Tor.val_pull hJ α _ _)
  rw [GlobalTheory.VVRank.sv_pullS A a h t _ y hJ, GlobalTheory.VVRank.sv_pullS A b h s _ y hJ,
    GlobalTheory.VVRank.sv_of_isTwistPull A hst _ y hJ, hv]
  simp only [Category.id_comp, e]

end GlobalTheory.TwistBaseChange
