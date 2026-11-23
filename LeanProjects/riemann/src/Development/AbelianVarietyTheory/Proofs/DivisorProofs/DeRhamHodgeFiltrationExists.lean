import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubOfAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamFiltrationIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamHodgeSubbundleExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamSubbundleAffineSectionCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplOfIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectPairingDualSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarizationDeRhamPairingStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory

namespace GlobalTheory.ConjSeq

theorem hodge_quot_iso (hDual : GlobalTheory.Published.DualAbelianScheme) (hCube : GlobalTheory.Published.CubeTheorem)
    (hP2 : GlobalTheory.CovTop.Hypotheses2) (hPD : GlobalTheory.Published.PoincareDeRhamDuality) {T : Scheme.{0}} (A : Over T)
    [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom)
    (hpol : ∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV))
    (he : IsDRIso A H e) (F : GlobalTheory.VB.Sub H)
    (hF : ∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV)) :
    Nonempty (cokernel F.incl ≅ GlobalTheory.VB.dual (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A)) := by
  have hAD := hP2.p5
  have hH : GlobalTheory.VB.IsVB H (2 * g) := GlobalTheory.DeRhamSheaf.VB.isVB_of_isDeRhamSheaf hAD T A g hA hg H ⟨e, he⟩
  obtain ⟨iF⟩ := GlobalTheory.T.de_rham_filtration_iso hP2 A g hA hg H e he F hF
  have : SmoothOfRelativeDimension g A.hom := hg
  have hFv : GlobalTheory.VB.IsVB F.toMod g := (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.isVB_hodge A hA g).of_iso iF.symm
  obtain ⟨b, hb, hperf, hrel⟩ := GlobalTheory.T.principal_polarization_de_rham_pairing hDual hCube hP2 hPD A g hA hg hpol H e he
  have hAV : ∀ (V : T.Opens) (hV : IsAffineOpen V), IsAbelianScheme (onAff A hV) := fun V hV =>
    GlobalTheory.DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
  have hgV : ∀ (V : T.Opens) (hV : IsAffineOpen V), SmoothOfRelativeDimension g (onAff A hV).hom :=
    fun V hV => GlobalTheory.DeRhamSheaf.VB.smooth_onAff A hg hV
  have isoF : ∀ (V : T.Opens) (hV : IsAffineOpen V) (x y : Γ(F.toMod, V)),
      b V hV (F.incl.app V x) (F.incl.app V y) = 0 := by
    intro V hV x y
    obtain ⟨-, hcomp, -, -, hrk⟩ := hAD.2.1 Γ(T, V) (onAff A hV) g (hAV V hV) (hgV V hV)
    obtain ⟨hfin, hproj, hrank⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hAD.1 (hAV V hV) (hgV V hV)
    obtain ⟨P, hP, φ, hφ, hr⟩ := hrel V hV
    refine GlobalTheory.T.perfect_pairing_dual_symplectic Γ(T, V) Γ(H, V) (primDR (onAff A hV)) (e V hV) g hfin hproj hrank (b V hV)
      (hperf V hV) φ hr (PrimitiveSubmodule (onAff A hV)) hcomp hrk ?_ _ _ ((hF V hV _).1 (F.incl_app_mem x))
      ((hF V hV _).1 (F.incl_app_mem y))
    intro x' y' hx hy
    exact (hPD Γ(T, V) (onAff A hV) (onAff A hV) g (hAV V hV) (hAV V hV) (hgV V hV) (hgV V hV) P hP φ
      hφ).2 x' (show x' ∈ (PrimitiveSubmodule _).dualAnnihilator from (Submodule.mem_dualAnnihilator _).2 hx) y'
      (show y' ∈ (PrimitiveSubmodule _).dualAnnihilator from (Submodule.mem_dualAnnihilator _).2 hy)
  let β := GlobalTheory.AffinePairingGlue.toDual b hb
  haveI : IsIso β := GlobalTheory.AffinePairingGlue.isIso_toDual b hb hH hperf
  have wF := GlobalTheory.AffinePairingGlue.comp_toDual_comp_dualMap b hb F.incl isoF
  have sF := GlobalTheory.VB.lagrangian_shortExact T g F.toMod H hFv hH F.incl β inferInstance
    (fun V hV => GlobalTheory.ConjQuot.compl_of_iff F (e V hV) _ (hF V hV)
      (hAD.2.1 Γ(T, V) (onAff A hV) g (hAV V hV) (hgV V hV)).2.1) wF
  let kF : cokernel F.incl ≅ GlobalTheory.VB.dual F.toMod :=
    (colimit.isColimit _).coconePointUniqueUpToIso sF.gIsCokernel
  exact ⟨kF ≪≫ GlobalTheory.VB.dualIso iF.symm⟩

theorem conjugate_sequence : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.ConjugateFiltration →
    GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.PoincareDeRhamDuality → ∀ (p : ℕ) [Fact p.Prime] (T : Scheme.{0})
    [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) →
    ∀ H : T.Modules, GlobalTheory.DeRhamSheaf.IsDeRhamSheaf A H →
      ∃ S : ShortComplex T.Modules, S.ShortExact ∧ Nonempty (S.X₂ ≅ H) ∧
        Nonempty (S.X₁ ≅ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj
          (GlobalTheory.VB.dual (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A))) ∧
        Nonempty (S.X₃ ≅ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj
          (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.hodge A)) := by
  intro hDual hCube hC h2 hD p _ T _ A _ g hA hg hpol H hH
  obtain ⟨e, he⟩ := (isDeRhamSheaf_iff A H).1 hH
  obtain ⟨F, hF⟩ := GlobalTheory.HodgeSubsheaf.exists_hodgeSub h2 A g hA hg H e he
  obtain ⟨C, hCs⟩ := GlobalTheory.T.de_rham_hodge_subbundle_exists h2 p A g hA hg H e he
  obtain ⟨i₁⟩ := GlobalTheory.T.de_rham_subbundle_affine_section_criterion hC h2 p A g hA hg H e he F hF C hCs
  obtain ⟨i₃⟩ := GlobalTheory.ConjQuot.main hDual hCube hC h2 hD p A g hA hg hpol H e he F hF C hCs
  obtain ⟨j₂⟩ := GlobalTheory.T.de_rham_filtration_iso h2 A g hA hg H e he F hF
  obtain ⟨j₃⟩ := hodge_quot_iso hDual hCube h2 hD A g hA hg hpol H e he F hF
  haveI := C.mono_incl
  refine ⟨ShortComplex.mk C.incl (cokernel.π C.incl) (cokernel.condition _), ?_, ⟨Iso.refl _⟩,
    ⟨i₁ ≪≫ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).mapIso j₃⟩,
    ⟨i₃ ≪≫ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).mapIso j₂⟩⟩
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }

end GlobalTheory.ConjSeq
