import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TcoMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAffCoverSpec
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ToPtIdPtBijective
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSmoothFiniteCoverOfFormsNoCommonZeroStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedQuotientOfArtinianOfMaximalLeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexPointKerEvalEqMaximalStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsArtinianRingFibQuotStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFormsTransversalAtComplexPointsStatement

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechDR GlobalTheory.PD KaehlerDifferential

namespace GlobalTheory.PD.FibRed

theorem quotEquiv_of_germ {X : Scheme.{0}} [IsIntegral X] [Algebra ℂ X.functionField] {F : Type} [Field F] [Algebra ℂ F]
    [Algebra F X.functionField] [IsScalarTower ℂ F X.functionField] {d : ℕ} (x : Fin (d + 1) → F) (U : X.Opens)
    (hg : genericPoint X ∈ U) (t : Fin d → Γ(X, U))
    (hring : ∀ y, y ∈ rB ℂ X.functionField x {0} ↔ ∃ f : Γ(X, U), (X.presheaf.germ U (genericPoint X) hg).hom f = y)
    (ht : ∀ j, (X.presheaf.germ U (genericPoint X) hg).hom (t j) = algebraMap F X.functionField (x j.succ / x 0)) :
    Nonempty ((Γ(X, U) ⧸ Ideal.span (Set.range t)) ≃+*
      (rB ℂ X.functionField x {0} ⧸ Ideal.span (Set.range fun j : Fin d =>
        (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) := by
  set g := (X.presheaf.germ U (genericPoint X) hg).hom
  have hinj : Function.Injective g := germ_injective_of_isIntegral X _ hg
  let g' : Γ(X, U) →+* rB ℂ X.functionField x {0} :=
    g.codRestrict (rB ℂ X.functionField x {0}).toSubring fun f => (hring _).2 ⟨f, rfl⟩
  have hbij : Function.Bijective g' := by
    refine ⟨fun a b h => hinj (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨f, hf⟩ := (hring y).1 y.2
    exact ⟨f, Subtype.ext hf⟩
  let e := RingEquiv.ofBijective g' hbij
  refine ⟨Ideal.quotientEquiv _ _ e ?_⟩
  rw [Ideal.map_span, ← Set.range_comp]
  congr 2
  funext j
  exact Subtype.ext (ht j).symm

theorem exists_finCover_fibre_reduced : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ) (d : ℕ) [SmoothOfRelativeDimension d p] [inst : Algebra ℂ X.functionField], inst = ffAlg p → IsProjOver p → ∀ S : Finset (CxPts p (RingHom.id ℂ)), ∃ (F : IntermediateField ℂ X.functionField) (x : Fin (d + 1) → F) (U : Fin (d + 1) → X.Opens), IsFinCover ℂ X.functionField x ∧ IsAffCover p U (rB ℂ X.functionField x) ∧ IsReduced ((rB ℂ X.functionField x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ X.functionField x j⟩ : rB ℂ X.functionField x {0})))) ∧ ∀ y ∈ S, y ∈ CxPts.ptsIn p (RingHom.id ℂ) (U 0) ∧ ∀ j : Fin d, ∀ (hg : genericPoint X ∈ U 0) (f : Sec p (U 0)), (X.presheaf.germ (U 0) (genericPoint X) hg).hom f = algebraMap F X.functionField (x j.succ / x 0) → CxPts.ev p (RingHom.id ℂ) (U 0) f y = 0 := by
  intro X _ p d _ inst hinst hproj S
  obtain ⟨N, ι, hι, hιp⟩ := hproj
  obtain ⟨n, f, hf, hn, hcov, hgen, hS, htr⟩ := GlobalTheory.T.exists_forms_transversal_at_complexPoints X p d N ι hι hιp S
  obtain ⟨F, x, hFC, hAC, hx⟩ := GlobalTheory.T.exists_finiteCover_affineCover_of_forms_no_commonZero X p d hinst N ι hι hιp n f hf hn hcov hgen
  set U0 := GlobalTheory.EtProj.fOpen ι (f 0) with hU0
  set t : Fin d → Γ(X, U0) := fun j => GlobalTheory.EtProj.fRatio ι (f j.succ) (f 0) (hf j.succ) (hf 0) with ht_def
  have hx0 : x 0 = 1 := by
    apply (algebraMap F X.functionField).injective
    rw [hx 0, GlobalTheory.EtProj.fRatio_self, map_one, map_one]
  have ht : ∀ j, (X.presheaf.germ U0 (genericPoint X) (hgen 0)).hom (t j) =
      algebraMap F X.functionField (x j.succ / x 0) := by
    intro j
    rw [hx0, div_one, hx j.succ]
  have hring : ∀ y, y ∈ rB ℂ X.functionField x {0} ↔
      ∃ g : Γ(X, U0), (X.presheaf.germ U0 (genericPoint X) (hgen 0)).hom g = y := by
    intro y
    have hle : ({0} : Finset (Fin (d + 1))).inf (fun i => GlobalTheory.EtProj.fOpen ι (f i)) = U0 := by simp [hU0]
    rw [hAC.ring {0} (Finset.singleton_nonempty 0) y]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨X.presheaf.map (homOfLE hle.ge).op g, ?_⟩
      exact X.presheaf.germ_res_apply (homOfLE hle.ge) _ _ g
    · rintro ⟨g, rfl⟩
      refine ⟨X.presheaf.map (homOfLE hle.le).op g, ?_⟩
      exact X.presheaf.germ_res_apply (homOfLE hle.le) _ _ g
  obtain ⟨E⟩ := quotEquiv_of_germ x U0 (hgen 0) t hring ht
  have hU0aff : IsAffineOpen U0 := by
    simpa [hU0] using hAC.affine {0} (Finset.singleton_nonempty 0)
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  haveI hart : IsArtinianRing (Γ(X, U0) ⧸ Ideal.span (Set.range t)) := by
    haveI := GlobalTheory.T.isArtinianRing_rB_quot_span_tco_of_isFinCover ℂ X.functionField F d x hFC
    exact RingEquiv.isArtinianRing E.symm
  have hred : IsReduced (Γ(X, U0) ⧸ Ideal.span (Set.range t)) := by
    refine GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' _ _ hart fun m hm hIm => ?_
    obtain ⟨y, hy, rfl⟩ := GlobalTheory.T.exists_complexPoint_ker_eval_eq_maximal X p U0 hU0aff m hm
    refine htr y hy fun j => ?_
    exact hIm (Ideal.subset_span ⟨j, rfl⟩)
  refine ⟨F, x, fun i => GlobalTheory.EtProj.fOpen ι (f i), hFC, hAC, ?_, fun y hyS => ⟨(hS y hyS).1, ?_⟩⟩
  · haveI := hred
    exact isReduced_of_injective E.symm E.symm.injective
  · intro j hg g hgj
    have : g = t j := by
      apply germ_injective_of_isIntegral X _ hg
      exact hgj.trans (ht j).symm
    rw [this]
    exact (hS y hyS).2 j

end GlobalTheory.PD.FibRed
