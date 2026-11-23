import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLeOfClosedPoint
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.QCoh GlobalTheory.ChainPts GlobalTheory.ChainPts.PullHT
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

namespace GlobalTheory.ChainPts.PullHT

theorem repr_pulled_frame {X X' : Scheme.{0}} (g : X' ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {r : ℕ}
    {V W : X.Opens} {U T : X'.Opens} (hU : U ≤ g ⁻¹ᵁ V) (hT : T ≤ g ⁻¹ᵁ W) (hW : W ≤ V) (hTU : T ≤ U)
    {e : Fin r → Γ(F, V)} (he : GlobalTheory.VB.IsFrame e) (t : Γ(F, W)) (l : Fin r) :
    ((isFrame_pullS g hU he).basis hTU).repr (pullbackSections g F hT t) l =
      (g.appLE W T hT).hom ((he.basis hW).repr t l) := by
  have hb : ∀ k, pullbackSections g F hT (he.basis hW k) = (isFrame_pullS g hU he).basis hTU k := fun k => by
    rw [GlobalTheory.VB.IsFrame.basis_apply, GlobalTheory.VB.IsFrame.basis_apply]
    exact (pullbackSections_res g F hT hW _).trans (res_pullbackSections g F _ _ _).symm
  conv_lhs => rw [← (he.basis hW).sum_repr t]
  simp only [map_sum, pullbackSections_smul, hb]
  rw [← map_sum, Module.Basis.repr_sum_self]

theorem coef_pulled_frames {X X' : Scheme.{0}} (g : X' ⟶ X) {F : X.Modules} [F.IsQuasicoherent] {r : ℕ} (d : Bool)
    {V V' : X.Opens} {U U' : X'.Opens} (hU : U ≤ g ⁻¹ᵁ V) (hU' : U' ≤ g ⁻¹ᵁ V') {e : Fin r → Γ(F, V)}
    {s : Fin r → Γ(F, V')} (he : GlobalTheory.VB.IsFrame e) (hs : GlobalTheory.VB.IsFrame s) (l i : Fin r) :
    coef d (isFrame_pullS g hU he) (isFrame_pullS g hU' hs) l i =
      (g.appLE (V ⊓ V') (U ⊓ U') (inf_le_inf hU hU')).hom (coef d he hs l i) := by
  cases d
  · refine Eq.trans ?_ (repr_pulled_frame g hU (inf_le_inf hU hU') inf_le_left inf_le_left he _ l)
    exact congrArg (fun t => ((isFrame_pullS g hU he).basis inf_le_left).repr t l)
      ((res_pullbackSections g F _ _ _).trans (pullbackSections_res g F _ inf_le_right _).symm)
  · refine Eq.trans ?_ (repr_pulled_frame g hU' (inf_le_inf hU hU') inf_le_right inf_le_right hs _ i)
    exact congrArg (fun t => ((isFrame_pullS g hU' hs).basis inf_le_right).repr t i)
      ((res_pullbackSections g F _ _ _).trans (pullbackSections_res g F _ inf_le_left _).symm)

end GlobalTheory.ChainPts.PullHT
