import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIffAlt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ConjugateFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamSubbundleAffineSectionCriterionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamFiltrationIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoDualOfAffinePairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOfBijectiveLiftSemi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectPairingDualSymplecticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalPolarizationDeRhamPairingStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf

attribute [local instance] Over.cartesianMonoidalCategory
open MonoidalCategory

namespace GlobalTheory.ConjQuot

theorem compl_of_iff {T : Scheme.{0}} {H : T.Modules} (S : GlobalTheory.VB.Sub H) {V : T.Opens} {N : Type 1}
    [AddCommGroup N] [Module Γ(T, V) N] (e : Γ(H, V) ≃ₗ[Γ(T, V)] N) (W : Submodule Γ(T, V) N)
    (hS : ∀ s : Γ(H, V), s ∈ S.sec V ↔ e s ∈ W) (hW : ∃ W' : Submodule Γ(T, V) N, IsCompl W W') :
    Function.Injective (GlobalTheory.QCoh.appLinear S.incl V) ∧
      ∃ N' : Submodule Γ(T, V) Γ(H, V), IsCompl (LinearMap.range (GlobalTheory.QCoh.appLinear S.incl V)) N' := by
  refine ⟨S.incl_app_injective V, ?_⟩
  obtain ⟨W', hW'⟩ := hW
  have hr : LinearMap.range (GlobalTheory.QCoh.appLinear S.incl V) = W.comap e.toLinearMap := by
    ext s
    simp only [LinearMap.mem_range, Submodule.mem_comap]
    exact S.mem_sec_iff.symm.trans (hS s)
  refine ⟨W'.comap e.toLinearMap, ?_⟩
  rw [hr]
  have := (OrderIso.isCompl_iff (f := (Submodule.orderIsoMapComap e.symm))).1 hW'
  simpa [Submodule.map_equiv_eq_comap_symm] using this

theorem main : GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.CubeTheorem → GlobalTheory.Published.ConjugateFiltration →
    GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.Published.PoincareDeRhamDuality → ∀ (p : ℕ) [Fact p.Prime] {T : Scheme.{0}}
    [Algebra (ZMod p) Γ(T, ⊤)] (A : Over T) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → (∃ c, GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.IsPrincipalPol A c) → ∀ (H : T.Modules)
    (e : ∀ (V : T.Opens) (hV : IsAffineOpen V), Γ(H, V) ≃ₗ[Γ(T, V)] primDR (onAff A hV)), IsDRIso A H e →
    ∀ F : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ F.sec V ↔ e V hV s ∈ PrimitiveSubmodule (onAff A hV)) →
    ∀ C : GlobalTheory.VB.Sub H, (∀ (V : T.Opens) (hV : IsAffineOpen V) (s : Γ(H, V)),
      s ∈ C.sec V ↔ e V hV s ∈ GlobalTheory.ConjSeq.conjDR p Γ(T, V)
        (GlobalTheory.SS.FrobField.cast_zero (GlobalTheory.VB.natCast_eq_zero T p (ZMod p)) V) (onAff A hV)) →
    Nonempty (cokernel C.incl ≅ (GlobalTheory.VB.frobPull p (GlobalTheory.VB.natCast_eq_zero T p (ZMod p))).obj F.toMod) := by
  intro hDual hCube hConj hP2 hPD p _ T _ A _ g hA hg hpol H e he F hF C hC
  have hAD := hP2.p5
  have hH : GlobalTheory.VB.IsVB H (2 * g) := GlobalTheory.DeRhamSheaf.VB.isVB_of_isDeRhamSheaf hAD T A g hA hg H ⟨e, he⟩
  obtain ⟨iF⟩ := GlobalTheory.T.de_rham_filtration_iso hP2 A g hA hg H e he F hF
  have : SmoothOfRelativeDimension g A.hom := hg
  have hFv : GlobalTheory.VB.IsVB F.toMod g := (GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase.isVB_hodge A hA g).of_iso iF.symm
  obtain ⟨b, hb, hperf, hrel⟩ := GlobalTheory.T.principal_polarization_de_rham_pairing hDual hCube hP2 hPD A g hA hg hpol H e he

  have hloc : ∀ (V : T.Opens) (hV : IsAffineOpen V) (S : Submodule Γ(T, V) (primDR (onAff A hV))),
      (∃ S', IsCompl S S') → (∀ P : PrimeSpectrum Γ(T, V), Module.rankAtStalk S P = g) →
      (∀ (P : LB ((onAff A hV) ⊗ (onAff A hV)).left), GlobalTheory.AbDual.IsDual (onAff A hV) (onAff A hV) P →
        ∀ φ : HdR (onAff A hV) →ₗ[Γ(T, V)] HdR (onAff A hV) →ₗ[Γ(T, V)] Γ(T, V),
          GlobalTheory.AbDual.IsCorrForm (GlobalTheory.Cris.dp0 Γ(T, V)) (𝟙 _) (onAff A hV) (onAff A hV) P φ →
          ∀ x y : HdR (onAff A hV), (∀ c ∈ S, x c = 0) → (∀ c ∈ S, y c = 0) → φ x y = 0) →
      ∀ u v : Γ(H, V), e V hV u ∈ S → e V hV v ∈ S → b V hV u v = 0 := by
    intro V hV S hS hrk hiso u v hu hv
    have hA' := GlobalTheory.DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
    have hg' := GlobalTheory.DeRhamSheaf.VB.smooth_onAff A hg hV
    obtain ⟨hfin, hproj, hrank⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hAD.1 hA' hg'
    obtain ⟨P, hP, φ, hφ, hr⟩ := hrel V hV
    exact GlobalTheory.T.perfect_pairing_dual_symplectic Γ(T, V) Γ(H, V) (primDR (onAff A hV)) (e V hV) g hfin hproj hrank (b V hV) (hperf V hV) φ hr
      S hS hrk (hiso P hP φ hφ) u v hu hv

  have hAV : ∀ (V : T.Opens) (hV : IsAffineOpen V), IsAbelianScheme (onAff A hV) := fun V hV =>
    GlobalTheory.DeRhamSheaf.VB.isAbelianScheme_onAff A hA hV
  have hgV : ∀ (V : T.Opens) (hV : IsAffineOpen V), SmoothOfRelativeDimension g (onAff A hV).hom :=
    fun V hV => GlobalTheory.DeRhamSheaf.VB.smooth_onAff A hg hV
  have hp : (p : Γ(T, ⊤)) = 0 := GlobalTheory.VB.natCast_eq_zero T p (ZMod p)

  have hCV := fun (V : T.Opens) (hV : IsAffineOpen V) =>
    hConj p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero hp V) (onAff A hV) g (hAV V hV) (hgV V hV)
      (GlobalTheory.ConjSeq.cast_left p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero hp V) (onAff A hV))
      (GlobalTheory.ConjSeq.frobMor p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero hp V) (onAff A hV)
        (GlobalTheory.ConjSeq.cast_left p Γ(T, V) (GlobalTheory.SS.FrobField.cast_zero hp V) (onAff A hV)))
  have isoF : ∀ (V : T.Opens) (hV : IsAffineOpen V) (x y : Γ(F.toMod, V)),
      b V hV (F.incl.app V x) (F.incl.app V y) = 0 := by
    intro V hV x y
    obtain ⟨-, hcomp, -, -, hrk⟩ := hAD.2.1 Γ(T, V) (onAff A hV) g (hAV V hV) (hgV V hV)
    refine hloc V hV (PrimitiveSubmodule (onAff A hV)) hcomp hrk ?_ _ _ ((hF V hV _).1 (F.incl_app_mem x))
      ((hF V hV _).1 (F.incl_app_mem y))
    intro P hP φ hφ x' y' hx hy
    exact (hPD Γ(T, V) (onAff A hV) (onAff A hV) g (hAV V hV) (hAV V hV) (hgV V hV) (hgV V hV) P hP φ
      hφ).2 x' (show x' ∈ (PrimitiveSubmodule _).dualAnnihilator from (Submodule.mem_dualAnnihilator _).2 hx) y'
      (show y' ∈ (PrimitiveSubmodule _).dualAnnihilator from (Submodule.mem_dualAnnihilator _).2 hy)
  have isoC : ∀ (V : T.Opens) (hV : IsAffineOpen V) (x y : Γ(C.toMod, V)),
      b V hV (C.incl.app V x) (C.incl.app V y) = 0 := by
    intro V hV x y
    obtain ⟨-, hcomp, hrk, hd⟩ := hCV V hV
    refine hloc V hV _ hcomp hrk ?_ _ _ ((hC V hV _).1 (C.incl_app_mem x))
      ((hC V hV _).1 (C.incl_app_mem y))
    intro P hP φ hφ x' y' hx hy
    exact hd (onAff A hV) (hAV V hV) (hgV V hV) _ _ P hP φ hφ x' y'
      (fun c => hx _ (Submodule.subset_span ⟨c, rfl⟩)) (fun c => hy _ (Submodule.subset_span ⟨c, rfl⟩))
  let β := GlobalTheory.AffinePairingGlue.toDual b hb
  haveI : IsIso β := GlobalTheory.AffinePairingGlue.isIso_toDual b hb hH hperf
  have wF := GlobalTheory.AffinePairingGlue.comp_toDual_comp_dualMap b hb F.incl isoF
  have wC := GlobalTheory.AffinePairingGlue.comp_toDual_comp_dualMap b hb C.incl isoC
  have sF := GlobalTheory.VB.lagrangian_shortExact T g F.toMod H hFv hH F.incl β inferInstance
    (fun V hV => compl_of_iff F (e V hV) _ (hF V hV)
      (hAD.2.1 Γ(T, V) (onAff A hV) g (hAV V hV) (hgV V hV)).2.1) wF
  let kF : cokernel F.incl ≅ GlobalTheory.VB.dual F.toMod :=
    (colimit.isColimit _).coconePointUniqueUpToIso sF.gIsCokernel
  obtain ⟨jC⟩ := GlobalTheory.T.de_rham_subbundle_affine_section_criterion hConj hP2 p A g hA hg H e he F hF C hC
  have hq : GlobalTheory.VB.IsVB (cokernel F.incl) g := hFv.dual.of_iso kF.symm
  have hCv : GlobalTheory.VB.IsVB C.toMod g := (hq.frobPull p hp).of_iso jC.symm
  have sC := GlobalTheory.VB.lagrangian_shortExact T g C.toMod H hCv hH C.incl β inferInstance
    (fun V hV => compl_of_iff C (e V hV) _ (hC V hV) (hCV V hV).2.1) wC
  let kC : cokernel C.incl ≅ GlobalTheory.VB.dual C.toMod :=
    (colimit.isColimit _).coconePointUniqueUpToIso sC.gIsCokernel
  haveI := GlobalTheory.DualPull.isIso_theta (GlobalTheory.VB.frob T p hp) hq
  haveI := hFv.isIso_toBidual_of_local_frames
  exact ⟨kC ≪≫ GlobalTheory.VB.dualIso jC.symm ≪≫ (asIso (GlobalTheory.DualPull.theta (GlobalTheory.VB.frob T p hp) _)).symm ≪≫
    (GlobalTheory.VB.frobPull p hp).mapIso (GlobalTheory.VB.dualIso kF.symm) ≪≫
    (GlobalTheory.VB.frobPull p hp).mapIso (asIso (GlobalTheory.VB.cartierDualToBidual F.toMod)).symm⟩

end GlobalTheory.ConjQuot
