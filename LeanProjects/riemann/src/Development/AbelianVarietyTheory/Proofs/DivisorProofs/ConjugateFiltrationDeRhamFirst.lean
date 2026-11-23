import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFrameOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.IsQuasicoherentEigenQuot
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.ConjSeq

theorem frobLin_comp_cokernel_π_eq_zero : ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ C : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ C.sec V ↔ e V hV s ∈ GlobalTheory.ConjSeq.conjDR p Γ(T, V)
        (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V) (onAff A hV)) →
    ∀ Ψ : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj H ⟶ H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      e V hV ((Ψ).app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))) H
        (le_refl V) s)) =
      GlobalTheory.ConjSeq.frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V)
        (onAff A hV) (e V hV s)) →
    Ψ ≫ cokernel.π C.incl = 0 := by
  intro p _ T _ A _ g _ _ H e _ C hC Ψ hΨ
  set f := GlobalTheory.VB.frob T p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) with hf
  have key : ∀ (U : T.Opens) (s : Γ(H, U)),
      Ψ.app U (GlobalTheory.QCoh.pullbackSections f H (le_refl U) s) ∈ C.sec U := by
    intro U s
    refine C.mem_of_local fun x hx => ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    have hWU' : W ≤ U := hWU
    refine ⟨W, hWU', hxW, ?_⟩
    have h1 : GlobalTheory.Twist.resM H hWU' (Ψ.app U (GlobalTheory.QCoh.pullbackSections f H (le_refl U) s)) =
        Ψ.app W (GlobalTheory.QCoh.pullbackSections f H (le_refl W) (GlobalTheory.Twist.resM H hWU' s)) := by
      rw [← GlobalTheory.Twist.app_resM]
      congr 1
      exact (GlobalTheory.QCoh.res_pullbackSections f H (le_refl U) hWU' s).trans
        (GlobalTheory.QCoh.pullbackSections_res f H (le_refl W) hWU' s).symm
    rw [h1, hC W hW, hΨ W hW]
    exact Submodule.subset_span ⟨_, rfl⟩

  have hu : ∀ (U : T.Opens) (s : Γ(H, U)),
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app U s =
        GlobalTheory.QCoh.pullbackSections f H (le_refl U) s := by
    intro U s
    exact (GlobalTheory.Twist.resM_self _ _).symm
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  ext s
  simp only [Adjunction.homEquiv_unit, Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.Hom.zero_app, Limits.comp_zero]
  show (cokernel.π C.incl).app U (Ψ.app U (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app H).app U s)) = 0
  rw [hu]
  exact C.cokernel_π_app_eq_zero_iff.2 (key U s)

end GlobalTheory.ConjSeq
