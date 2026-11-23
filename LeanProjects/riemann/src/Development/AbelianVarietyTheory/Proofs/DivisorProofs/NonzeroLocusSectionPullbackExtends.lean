import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfIntersectionLowerHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ModelSecExt

open GlobalTheory.PrimSec GlobalTheory.AbLaw

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

theorem genericPoint_mem_range (M : TrueGeo.Model Y) :
    haveI := M.ar.isIntegral; genericPoint M.X ∈ Set.range M.j := by
  haveI := M.ar.isIntegral
  have := M.ar.finite
  have := M.ar.isDomain
  haveI := HtSelfInter.charZero_residueField_genericPoint M.ar.charZero
  have h0 := Mean4O.asIdeal_eq_bot M.p (genericPoint M.X)
  have hr : genericPoint M.X ∈ Set.range (Limits.pullback.fst M.p (spMap (algebraMap (𝓞 F) F))) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨IsLocalRing.closedPoint F, PrimeSpectrum.ext ?_⟩
    show Ideal.comap (algebraMap (𝓞 F) F) (IsLocalRing.maximalIdeal F) = _
    rw [IsLocalRing.maximalIdeal_eq_bot, h0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)
  obtain ⟨z, hz⟩ := hr
  refine ⟨M.pb.isoPullback.inv z, ?_⟩
  rw [← hz, ← M.pb.isoPullback_inv_fst, Scheme.Hom.comp_apply]

theorem app_injective (M : TrueGeo.Model Y) (W : M.X.Opens) : Function.Injective (M.j.app W).hom := by
  haveI := M.ar.isIntegral
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra hne
  obtain ⟨y, hy⟩ := genericPoint_mem_range M
  have hb : M.X.basicOpen a ≠ ⊥ := fun h => hne ((basicOpen_eq_bot_iff a).1 h)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb
  have hη : genericPoint M.X ∈ M.X.basicOpen a := ((genericPoint_spec M.X).mem_open_set_iff (M.X.basicOpen a).isOpen).2 ⟨x, trivial, hx⟩
  have : y ∈ M.j ⁻¹ᵁ M.X.basicOpen a := by rw [Scheme.Hom.mem_preimage, hy]; exact hη
  rw [Scheme.preimage_basicOpen] at this
  change y ∈ Y.X.basicOpen ((M.j.app W).hom a) at this
  rw [ha, Scheme.basicOpen_zero] at this
  exact this

theorem exists_extension (M : TrueGeo.Model Y) {U : M.X.Opens} (t : Γ(Y.X, M.j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (V : M.X.Opens) (hV : V ≤ U) (b : Γ(M.X, V)), x ∈ V ∧
      (M.j.app V).hom b = rs Y.X (pre_le M.j hV) t) :
    ∃ b : Γ(M.X, U), (M.j.app U).hom b = t := by
  choose V hV b hx hb using h
  have hc : U ≤ ⨆ x : U, V x.1 x.2 := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := M.X.sheaf.existsUnique_gluing' (fun x : U => V x.1 x.2) U
    (fun x => homOfLE (hV x.1 x.2)) hc (fun x => b x.1 x.2) (fun x y => by
      apply app_injective M
      refine (app_rs M.j inf_le_left _).trans (Eq.trans ?_ (app_rs M.j inf_le_right _).symm)
      rw [hb, hb]
      exact (rs_rs _ _ _).trans (rs_rs _ _ _).symm)
  refine ⟨s, Y.X.sheaf.eq_of_locally_eq' (fun x : U => M.j ⁻¹ᵁ V x.1 x.2) (M.j ⁻¹ᵁ U)
    (fun x => homOfLE fun _ hy => hV x.1 x.2 hy) ?_ _ _ fun x => ?_⟩
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨M.j y, hy⟩, hx _ hy⟩
  · exact (app_rs M.j (hV x.1 x.2) s).symm.trans ((congrArg _ (hs x)).trans (hb x.1 x.2))

end GlobalTheory.ModelSecExt

open GlobalTheory.PrimSec GlobalTheory.AbLaw GlobalTheory.ModelSecExt in

theorem GlobalTheory.ModelSecExt.main : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (M : TrueGeo.Model Y) (B : LB M.X),
    B.IsLB → ∀ t : (B.pull M.j).Sec, ∃ s : B.Sec, ∀ y : Y.X,
      M.j y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus s ↔ y ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus t := by
  intro F _ _ Y M B hB t
  haveI := M.ar.isIntegral
  haveI := M.ar.isNoetherian
  have hx : ∀ x : M.X, ∃ (i : B.ι) (W : M.X.Opens), IsAffineOpen W ∧ x ∈ W ∧ W ≤ B.U i := by
    intro x
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ i, B.U i from hB.cover ▸ trivial)
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ :=
      M.X.isBasis_affineOpens.exists_subset_of_mem_open hi (B.U i).isOpen
    exact ⟨i, W, hW, hxW, hWU⟩
  choose ci Wx hWa hxW hWle using hx
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover (fun x => (Wx x : Set M.X)) (fun x => (Wx x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxW x⟩)
  choose π b hπ hb using fun x => exists_numerator M.pb (hWa x) (loc t (ci x) (hWle x))
  classical
  let c : 𝓞 F := ∏ x ∈ S, π x
  have hc : algebraMap (𝓞 F) F c ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ _)]
    exact Finset.prod_ne_zero_iff.2 fun x _ => hπ x
  have hb' : ∀ x ∈ S, ∃ b' : Γ(M.X, Wx x), (M.j.app (Wx x)).hom b' =
      cst Y.str (M.j ⁻¹ᵁ Wx x) (algebraMap (𝓞 F) F c) * loc t (ci x) (hWle x) := by
    intro x hxS
    refine ⟨cst M.p (Wx x) (∏ y ∈ S.erase x, π y) * b x, ?_⟩
    rw [map_mul, app_cst M.pb.w, hb, ← mul_assoc, ← map_mul, ← map_mul, Finset.prod_erase_mul _ _ hxS]
  choose! b' hb' using hb'
  have key : ∀ i, ∃ s : Γ(M.X, B.U i), (M.j.app (B.U i)).hom s =
      cst Y.str (M.j ⁻¹ᵁ B.U i) (algebraMap (𝓞 F) F c) * loc t i le_rfl := by
    intro i
    refine exists_extension M _ fun x hx => ?_
    obtain ⟨z, hzS, hxz⟩ := Set.mem_iUnion₂.1 (hS (Set.mem_univ x))
    have hV : B.U i ⊓ Wx z ≤ B.U i := inf_le_left
    have hk : B.U i ⊓ Wx z ≤ B.U (ci z) := inf_le_right.trans (hWle z)
    refine ⟨B.U i ⊓ Wx z, hV, rs M.X (le_inf hV hk) (B.g i (ci z)).val * rs M.X inf_le_right (b' z), ⟨hx, hxz⟩, ?_⟩
    rw [map_mul, app_rs M.j (inf_le_right : B.U i ⊓ Wx z ≤ Wx z) (b' z), hb' z hzS, map_mul, rs_cst, rs_loc t (ci z) (hWle z) (inf_le_right : B.U i ⊓ Wx z ≤ Wx z), map_mul, rs_cst,
      rs_loc t i le_rfl hV,
      loc_trans t i (ci z) (le_rfl.trans hV) hk]
    ring
  choose s hs using key
  have hunit : ∀ W : Y.X.Opens, IsUnit (cst Y.str W (algebraMap (𝓞 F) F c)) := fun W =>
    (IsUnit.mk0 _ hc).map _
  refine ⟨⟨s, fun i k => ?_⟩, fun y => ?_⟩
  · apply app_injective M
    change (M.j.app _).hom (rs M.X inf_le_left (s i)) = (M.j.app _).hom (_ * rs M.X inf_le_right (s k))
    rw [map_mul, app_rs, app_rs, hs, hs, map_mul, map_mul, rs_cst, rs_cst,
      rs_loc t _ _ inf_le_left, rs_loc t _ _ inf_le_right, loc_trans t i k _ inf_le_right, rs_self]
    ring
  · have hmem : ∀ i, y ∈ M.j ⁻¹ᵁ B.U i →
        (M.j y ∈ M.X.basicOpen (s i) ↔ y ∈ Y.X.basicOpen (t.f (fun _ => i))) := by
      intro i hy
      change y ∈ M.j ⁻¹ᵁ M.X.basicOpen (s i) ↔ _
      rw [Scheme.preimage_basicOpen]
      change y ∈ Y.X.basicOpen ((M.j.app (B.U i)).hom (s i)) ↔ _
      rw [hs, Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (hunit _)]
      exact ⟨fun h => (mem_basicOpen_rs _ _ hy).1 h.2, fun h => ⟨hy, (mem_basicOpen_rs _ _ hy).2 h⟩⟩
    constructor
    · intro h
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ M.j ⁻¹ᵁ B.U i := M.X.basicOpen_le (s i) hi
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, (hmem i hy).1 hi⟩
    · intro h
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 h
      have hy : y ∈ M.j ⁻¹ᵁ B.U (k PUnit.unit) := Set.mem_iInter.1 (Y.X.basicOpen_le (t.f k) hk) PUnit.unit
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨k PUnit.unit, (hmem (k PUnit.unit) hy).2 hk⟩
