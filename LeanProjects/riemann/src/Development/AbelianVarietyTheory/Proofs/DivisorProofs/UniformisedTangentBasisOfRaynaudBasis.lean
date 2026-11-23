import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TanRay

open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv_mem mkT tv_mkT tanM_ext tv_add tv_smul)

theorem tanBasis_of_isPointOf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∃ b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G), ∀ a, b a = v' a := by
  intro E _ _ _ H R _ _ _ _ _ _ t P
  letI := H.starRing
  intro Y n vH v' hv
  have hc : IsAdicComplete ((maximalIdeal R).map (algebraMap R (DualNumber R))) (DualNumber R) := by
    have : Module.Finite R (DualNumber R) := inferInstanceAs (Module.Finite R (R × R))
    exact GlobalTheory.isAdicComplete_map_of_finite (maximalIdeal R) (DualNumber R)
  have : Nontrivial (DualNumber R) := (TrivSqZeroExt.inl_injective (R := R) (M := R)).nontrivial
  have : IsLocalRing (DualNumber R) := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst
  have hT : GlobalTheory.AdicColimit.IsAdicColimit (maximalIdeal R) (overAt (𝟙 (Sp R)) (DualNumber R)) := by
    refine GlobalTheory.AdicColimit.IsAdicColimit.of_iso (Over.isoMk (Iso.refl _) ?_)
      (GlobalTheory.AdicColimit.isAdicColimit_spec_of_isLocalRing R (maximalIdeal R) (DualNumber R)
        (algebraMap R (DualNumber R)) hc)
    simp
  have hΦ := Y.rep
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusModel.exists_mulEquiv P.U.toUnifPre GlobalTheory.allSixLaws.1.globalFns hΦ
  have nat : ∀ (k : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ overAt (𝟙 (Sp R)) (DualNumber R))
      (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H), J _ hT (k ≫ w) = k ≫ J _ hT w := fun k w =>
    (hJ _ hT _ _).2 (((hJ _ hT w _).1 rfl).pull k (hΦ.1 _ _ k _))
  have hs : ∀ (a : R) (w : overAt (𝟙 (Sp R)) (DualNumber R) ⟶ Y.H),
      J _ hT (smT (𝟙 (Sp R)) a w) = smT (𝟙 (Sp R)) a (J _ hT w) := fun a w => nat _ w
  have mem : ∀ v : TanM (𝟙 (Sp R)) Y.H, smT (𝟙 (Sp R)) 0 (J _ hT (tv v)) = 1 := fun v => by
    rw [← hs, tv_mem, map_one]
  let L : TanM (𝟙 (Sp R)) Y.H →ₗ[R] TanM (𝟙 (Sp R)) t.G :=
    { toFun := fun v => mkT (J _ hT (tv v)) (mem v)
      map_add' := fun u v => tanM_ext (by
        simp only [tv_mkT, tv_add, map_mul])
      map_smul' := fun a v => tanM_ext (by
        simp only [tv_mkT, tv_smul, RingHom.id_apply, hs]) }
  have hL : Function.Bijective L := by
    refine ⟨fun u v h => tanM_ext ((J _ hT).injective ?_), fun w => ?_⟩
    · have := congrArg tv h
      simpa [L, tv_mkT] using this
    · have h0 : smT (𝟙 (Sp R)) 0 ((J _ hT).symm (tv w)) = 1 := by
        apply (J _ hT).injective
        rw [hs, MulEquiv.apply_symm_apply, tv_mem, map_one]
      refine ⟨mkT _ h0, tanM_ext ?_⟩
      show J _ hT ((J _ hT).symm (tv w)) = tv w
      exact MulEquiv.apply_symm_apply _ _
  refine ⟨vH.map (LinearEquiv.ofBijective L hL), fun a => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofBijective_apply]
  refine tanM_ext ?_
  exact (hJ _ hT _ _).2 (hv a)

end GlobalTheory.TanRay
