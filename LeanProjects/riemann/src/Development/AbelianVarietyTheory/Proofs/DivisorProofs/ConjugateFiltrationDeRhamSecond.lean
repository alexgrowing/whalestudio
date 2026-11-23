import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

namespace GlobalTheory.ConjIso

theorem epi_frobPull_conj : ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ C : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ C.sec V ↔ e V hV s ∈ GlobalTheory.ConjSeq.conjDR p Γ(T, V)
        (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V) (onAff A hV)) →
    ∀ Ψ : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj H ⟶ C.toMod, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      e V hV ((Ψ ≫ C.incl).app V (GlobalTheory.QCoh.pullbackSections (GlobalTheory.VB.frob T p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))) H
        (le_refl V) s)) =
      GlobalTheory.ConjSeq.frobDR p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V)
        (onAff A hV) (e V hV s)) →
    Epi Ψ := by
  intro p _ T _ A _ g _ _ H e _ C hC Ψ hΨ
  refine GlobalTheory.QCoh.epi_of_locally_app_surjective Ψ fun W x hx => ?_
  obtain ⟨V, hV, hxV, hle⟩ := GlobalTheory.QCoh.exists_affine_mem_le x hx
  refine ⟨V, hxV, hle, fun c => ?_⟩
  let M : Submodule Γ(T, V) _ :=
    (LinearMap.range (GlobalTheory.QCoh.homAppLinear (Ψ ≫ C.incl) V)).map (e V hV).toLinearMap
  have hspan : GlobalTheory.ConjSeq.conjDR p Γ(T, V)
      (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V) (onAff A hV) ≤ M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, rfl⟩
    refine ⟨(Ψ ≫ C.incl).app V (GlobalTheory.QCoh.pullbackSections
      (GlobalTheory.VB.frob T p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))) H (le_refl V) ((e V hV).symm y)),
      ⟨_, rfl⟩, ?_⟩
    have := hΨ V hV ((e V hV).symm y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this
  have hc : e V hV (C.incl.app V c) ∈ M :=
    hspan ((hC V hV _).1 (C.incl_app_mem c))
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := hc
  refine ⟨t, C.incl_app_injective V ?_⟩
  have := (e V hV).injective ht
  simpa using this

end GlobalTheory.ConjIso
