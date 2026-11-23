import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPullbackDeRhamMapExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateFiltrationHodgeSubFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateFiltrationDeRhamFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateFiltrationDeRhamSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateFiltrationHodgeSubSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationSubDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfEpiVectorBundleSameRankStatement

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjSeq

theorem conj_iso_frobPull_quot : GlobalTheory.Published.ConjugateFiltration → GlobalTheory.CovTop.Hypotheses2 → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}} [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A]
    (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ F : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV)) →
    ∀ C : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ C.sec V ↔ e V hV s ∈ GlobalTheory.ConjSeq.conjDR p Γ(T, V)
        (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V) (onAff A hV)) →
    Nonempty (C.toMod ≅ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj (cokernel F.incl)) := by
  intro hP h2 p _ T _ A _ g hA hg H e he F hF C hC
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.T.frobenius_pullback_de_rham_map_exists h2 p A g hA hg H e he
  have hzC : Ψ ≫ cokernel.π C.incl = 0 := GlobalTheory.T.conjugate_filtration_de_rham_first p A g hA hg H e he C hC Ψ hΨ
  let Ψc : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj H ⟶ C.toMod := Abelian.monoLift C.incl Ψ hzC
  have hΨc : Ψc ≫ C.incl = Ψ := Abelian.monoLift_comp _ _ _
  have hepi : Epi Ψc := GlobalTheory.T.conjugate_filtration_de_rham_second p A g hA hg H e he C hC Ψc (by rw [hΨc]; exact hΨ)
  have hzF : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).map F.incl ≫ Ψ = 0 := GlobalTheory.T.conjugate_filtration_hodge_sub_first hP h2 p A g hA hg H e he F hF Ψ hΨ
  have hzF' : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).map F.incl ≫ Ψc = 0 := by
    rw [← cancel_mono C.incl, Category.assoc, hΨc, hzF, zero_comp]
  let π : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj (cokernel F.incl) ⟶ C.toMod :=
    (PreservesCokernel.iso (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))) F.incl).hom ≫ cokernel.desc _ Ψc hzF'
  have hfac : (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).map (cokernel.π F.incl) ≫ π = Ψc := by
    simp only [π, ← Category.assoc, PreservesCokernel.π_iso_hom, cokernel.π_desc]
  have : Epi π := epi_of_epi_fac hfac
  have : IsIso π := GlobalTheory.T.isIso_of_epi_vector_bundle_same_rank π g ((GlobalTheory.T.hodge_filtration_sub_de_rham h2 p A g hA hg H e he F hF).frobPull p _)
    (GlobalTheory.T.conjugate_filtration_hodge_sub_second hP h2 p A g hA hg H e he C hC)
  exact ⟨(asIso π).symm⟩

end GlobalTheory.ConjSeq
