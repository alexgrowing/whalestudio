import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfRingHom
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AbPartActIsAdj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GenericLieMultiplicitiesUniformisedGroup
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumOfTorusCoords
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumBaseChangeMaps
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsSemiAbelianOfProperGenericTorusExtensionSpecialFiber
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPatOfPolAV
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
open CategoryTheory AlgebraicGeometry Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.BdDim GlobalTheory.SiegelTor GlobalTheory.ZM GlobalTheory.CM GlobalTheory.Models
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.BdDim

theorem isAbPart_of_gtCoord {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : Out.DegPre R) (e : ℕ)
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (g : Out.GtCoord I D e G) {k : Type} [Field k] (r : R →+* k)
    (hr : ∀ a ∈ I ^ (e + 1), r a = 0) : IsAbPart G (spMap r) D.P.A (spMap r) := by
  obtain ⟨E, -, d, π, hπ, -⟩ := GlobalTheory.ZH.UFib.exists_gtDatum_of_gtCoord R I D e G g
  let r' : R ⧸ I ^ (e + 1) →+* k := Ideal.Quotient.lift _ r hr
  have hf : spMap r' ≫ Out.thick R I e = spMap r := by
    rw [← Spec.map_comp]
    rfl
  obtain ⟨E', -, d', π', hπ', -⟩ := GlobalTheory.exists_gtDatum_baseChange_maps _ _ (spMap r') E _ d
  have := E'.free
  have := E'.finite
  have := d'.q_affine
  let X : TorusExtension ((Over.pullback (spMap r')).obj (Out.thickObj R I e G)) :=
    { X := E'.X, B := E'.B, isAbelian := E'.isAbelian, q := d'.q, q_hom := d'.q_hom, q_flat := d'.q_flat,
      q_surjective := d'.q_surjective, q_quasiCompact := inferInstance, i := d'.i, i_hom := d'.i_hom,
      isKernel := d'.isKernel }
  exact ⟨_, _, _, X, _,
    ((isGrpPullback_pullback _ (spMap r')).comp (isGrpPullback_pullback G (Out.thick R I e))).congr hf rfl,
    (hπ'.comp hπ).congr hf rfl⟩

theorem exists_pat_abPart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T : Formalism.L2.Pj.CDVR) (t : SAB H (Sp T.V)) (P : PELUnif (maximalIdeal T.V) t), ∃ Q : PAT H (Sp T.V), (∀ (F : Type) [Field F] [IsAlgClosed F] (f : T.V →+* F), Function.Injective f → ∀ (τ : 𝓞 E →+* F) (N : ℕ), LieMult t.act (spMap f) τ N → ∃ n, LieMult Q.t.act (spMap f) τ n ∧ n + Module.finrank (𝓞 E) P.D.toPre.X = N) ∧ ∀ (k : Type) [Field k] (r : T.V →+* k), IsLocalHom r → IsAbPart t.G (spMap r) Q.t.G (spMap r) := by
  intro E _ _ _ H T t P
  obtain ⟨Q, e, -, he, -⟩ := GlobalTheory.LamF.exists_pat_of_polAV GlobalTheory.abelianSchemeLaws_all.1 E H T.V P.D.toPre.P
    (GlobalTheory.LocM.abPartAct P) (fun a => by
      have h := GlobalTheory.LocM.abPartAct_isAdj E H T.V _ t P a
      rw [← GlobalTheory.LocM.bar_eq_star H] at h
      simpa only [LamEq, Category.comp_id] using h)
  have := he.isMonHom
  have hp := isGrpPullback_of_iso e
  refine ⟨Q, fun F _ _ f hf τ N hN => ?_, fun k _ r hr => ?_⟩
  · obtain ⟨n, hn, hN'⟩ := GlobalTheory.LieUnif.lieMult_unif E H T t P F f hf τ N hN
    refine ⟨n, (GlobalTheory.lieMult_iff_of_isGrpPullback hp Q.t.act (GlobalTheory.LocM.abPartAct P)
      (fun a => congrArg (·.left) (he.comm a)) (spMap f) τ n).2 ?_, hN'⟩
    rw [Category.comp_id]
    exact hn
  · have h := isAbPart_of_gtCoord (maximalIdeal T.V) P.D.toPre 0 t.G (P.U.toUnifPre.gt 0) r (fun a ha => by
      rw [zero_add, pow_one] at ha
      by_contra h0
      exact ha (hr.map_nonunit a (IsUnit.mk0 _ h0)))
    refine h.trans ⟨_, _, _, _, ((isGrpPullback_pullback Q.t.G (spMap r)).comp hp).congr (Category.comp_id _) rfl,
      isGrpPullback_pullback Q.t.G (spMap r)⟩

end GlobalTheory.BdDim

end
