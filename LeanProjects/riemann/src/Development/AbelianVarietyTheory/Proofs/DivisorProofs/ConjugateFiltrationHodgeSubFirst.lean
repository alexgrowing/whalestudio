import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.ConjSeq

theorem frobPull_incl_comp_linFrob_eq_zero : GlobalTheory.Published.ConjugateFiltration → GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ F : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV)) →
    ∀ Ψ : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj H ⟶ H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      e V hV ((Ψ).app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))) H
        (le_refl V) s)) =
      GlobalTheory.ConjSeq.frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V)
        (onAff A hV) (e V hV s)) →
    (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).map F.incl ≫ Ψ = 0 := by
  intro hC _ p _ T _ A _ g hA hg H e _ F hF Ψ hΨ
  let h0 := GlobalTheory.VB.natCast_eq_zero T p (ZMod p)
  let adj := Scheme.Modules.pullbackPushforwardAdjunction (GlobalTheory.VB.frob T p h0)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  have hz : adj.homEquiv F.toMod H 0 = 0 := by simp
  rw [hz]
  have key : ∀ (U : T.Opens) (hU : IsAffineOpen U) (t : Γ(H, U)), t ∈ F.sec U →
      (adj.homEquiv _ _ Ψ).app U t = 0 := by
    intro U hU t ht
    have h1 : (adj.homEquiv _ _ Ψ).app U t =
        Ψ.app U (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p h0) H (le_refl U) t) := by
      rw [Adjunction.homEquiv_unit]
      exact congrArg (Ψ.app U) (GlobalTheory.QCoh.res_self _ (le_refl U) _).symm
    rw [h1]
    apply (e U hU).injective
    rw [hΨ U hU t]
    refine Eq.trans ?_ (LinearEquiv.map_zero (e U hU)).symm
    exact (hC p Γ(T, U) (GlobalTheory.SS.FrobField.cast_zero h0 U) (onAff A hU) g
      (VB.isAbelianScheme_onAff A hA hU) (VB.smooth_onAff A hg hU) _
      (frobMor p Γ(T, U) (GlobalTheory.SS.FrobField.cast_zero h0 U) (onAff A hU) _)).1 _ ((hF U hU t).1 ht)
  have key2 : ∀ (W : T.Opens) (t : Γ(H, W)), t ∈ F.sec W → (adj.homEquiv _ _ Ψ).app W t = 0 := by
    intro W t ht
    refine GlobalTheory.QCoh.section_eq_of_cover _ (fun U : {U : T.Opens // IsAffineOpen U ∧ U ≤ W} ↦ U.1)
      (fun U ↦ U.2.2) ?_ _ _ fun U ↦ ?_
    · intro x hx
      obtain ⟨U, hU, hxU, hle⟩ := GlobalTheory.QCoh.exists_affine_mem_le x hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨U, hU, hle⟩, hxU⟩
    · rw [map_zero, ← GlobalTheory.QCoh.hom_app_res]
      exact key _ U.2.1 _ (F.res_mem U.2.2 ht)
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  exact (key2 W _ (F.incl_app_mem s)).trans rfl

end GlobalTheory.ConjSeq
