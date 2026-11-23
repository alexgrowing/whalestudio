import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreChangeOfPolarizedField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFamilyConjInvariant
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniformisationOfComplexConjugateKeyDatum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHorizontalLieDeterminantSectionOfConj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentFlagVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeSmoothConj
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AbLeConj

open GlobalTheory.ArchMetricCompare GlobalTheory.ConjUnif

theorem abLe_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (z z' : Sp ℂ ⟶ X), z' = spMap (starRingEnd ℂ) ≫ z → ∀ (g : TanM z t.G →ₗ[ℂ] TanM z t.G →ₗ⋆[ℂ] ℂ) (g' : TanM z' t.G →ₗ[ℂ] TanM z' t.G →ₗ⋆[ℂ] ℂ), (∀ (v : TanM z t.G) (v' : TanM z' t.G), (tv v').left = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ (tv v).left → g' v' v' = starRingEnd ℂ (g v v)) → ∀ C : ℝ, AbLe g C → AbLe g' C := by
  intro E _ _ _ H X t z z' hz g g' hg C hAb φ' m' hφ' n hn u' Hm' χ' hA' v' w' W h1 h2
  have hzz : spMap (starRingEnd ℂ) ≫ z' = z := by
    rw [hz, ← Category.assoc, GlobalTheory.ShFam.HodgeConj.spMap_conj_conj', Category.id_comp]
  obtain ⟨A'', _, ψc, hc⟩ : ∃ (A'' : Over (Sp ℂ)) (_ : GrpObj A'') (ψc : A''.left ⟶ φ'.P.A.left),
      IsGrpPullback A'' φ'.P.A cj ψc :=
    ⟨_, _, _, isGrpPullback_pullback φ'.P.A cj⟩
  let Q : Out.PolAV (Sp ℂ) := pullPol φ'.P hc
  have hQ : IsPolFibre (starRingEnd ℂ) φ'.P Q ψc := ⟨rfl, hc, ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso _, ReciprocityTheory.ChartRestriction.G.Geo.Tor.idIso_isGen (pull_isLB φ'.P.isLB ψc)⟩⟩
  obtain ⟨φ, m, χ, ψ', hPQ, hψ, hF, hpb, hχ, hq, -⟩ := GlobalTheory.BdFib.exists_fibAt_baseChange E H X t ℂ ℂ (starRingEnd ℂ) z' φ' m' hφ' Q ψc hQ
  rw [hzz] at hF

  let v : TanM z t.G := bcTan (starRingEnd ℂ) hzz v'
  have hv : (tv v).left = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ (tv v').left := left_bcTan _ hzz v'
  have hvv : (tv v').left = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ (tv v).left := by
    rw [hv, ← Category.assoc, GlobalTheory.ShFam.HodgeConj.spMap_dual_conj_conj', Category.id_comp]

  have sq : (spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ w'.left) ≫ φ'.G.hom = (epsR ℂ).hom ≫ spMap (starRingEnd ℂ) := by
    rw [Category.assoc, Over.w]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  let w : epsR ℂ ⟶ φ.G := Over.homMk (hpb.1.lift _ _ sq) (hpb.1.lift_snd _ _ _)
  have hw : w.left ≫ χ = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ w'.left := hpb.1.lift_fst _ _ _
  have h1' : w.left ≫ m.F = (tv v).left := by
    rw [← hχ, ← Category.assoc, hw, Category.assoc, h1, hv]
  have ht' : IsTangent w' := GlobalTheory.ConjFlat.isTangent_of_fibre hφ'.1 (by rw [h1]; exact (isTan_tv v').2)
  have htq : IsTangent (w' ≫ φ'.q) := GlobalTheory.CM.DiffCoord.isTangent_comp_hom φ'.q ht'
  obtain ⟨G, sm, L, cub, P, rig, rg, cubB, q, qf, qs, qa, Xt, i, ih, ik, pl⟩ := φ
  subst hPQ
  have hq' : q.left ≫ ψc = χ ≫ φ'.q.left := (eq_of_heq hψ) ▸ hq
  have e : (w ≫ q).left ≫ ψc = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ (w' ≫ φ'.q).left := by
    have e1 : (w ≫ q).left ≫ ψc = w.left ≫ (q.left ≫ ψc) := Category.assoc _ _ _
    rw [e1, hq']
    have e2 : w.left ≫ (χ ≫ φ'.q.left) = (w.left ≫ χ) ≫ φ'.q.left := (Category.assoc _ _ _).symm
    rw [e2, hw]
    exact Category.assoc _ _ _
  have h2' : (conjPull hc u').IsDiff (star W) (w ≫ q) := cj_isDiff hc (pullId u') htq e h2
  have hA := conjPull_isAH hc u' hA'
  have key := hAb _ m hF n hn (conjPull hc u') (Hm'.map star) _ hA v w (star W) h1' h2'
  have hgv := hg v v' hvv
  have hH : (hermForm (Hm'.map star) (star W) (star W)).re = (hermForm Hm' W W).re := by
    unfold hermForm
    rw [← star_form, star_star]
    simp
  rw [hH] at key
  rw [hgv]
  simpa using key

end GlobalTheory.AbLeConj
