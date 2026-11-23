import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibreStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ValGenExtend

def genSec {X : Scheme.{0}} {L : LB X} (t : LB.Gen L) (ht : t.IsGen) : LB.Sec L :=
  ⟨fun i => (t.s i).val, fun i j => by
    have h := congrArg Units.val (ht i j)
    exact h⟩

theorem isGen_inv_of_eq {X : Scheme.{0}} {N : LB X} (t : LB.Gen N) (ht : t.IsGen)
    (g : ∀ a b, Γ(X, N.U a ⊓ N.U b)ˣ) (hg : ∀ a b, g a b = (N.g a b)⁻¹) :
    LB.Gen.IsGen (L := ⟨N.ι, N.U, g⟩) ⟨fun i => (t.s i)⁻¹⟩ := by
  intro a b
  have h : res (inf_le_left : N.U a ⊓ N.U b ≤ _) (t.s a)⁻¹ =
      g a b * res (inf_le_right : N.U a ⊓ N.U b ≤ _) (t.s b)⁻¹ := by
    rw [map_inv, map_inv, ht a b, _root_.mul_inv, hg]
  exact h

theorem exists_isGen_inv {X Y : Scheme.{0}} {I : Type} {U : I → X.Opens}
    (g g' : ∀ a b, Γ(X, U a ⊓ U b)ˣ) (hg : ∀ a b, g' a b = (g a b)⁻¹) (j : Y ⟶ X)
    (t : LB.Gen ((⟨I, U, g⟩ : LB X).pull j)) (ht : t.IsGen) :
    ∃ t' : LB.Gen ((⟨I, U, g'⟩ : LB X).pull j), t'.IsGen ∧ ∀ i : I,
      rs Y (le_pull ⟨I, U, g⟩ j (W := U i) (i := i) le_rfl) (t.s fun _ => i).val *
        rs Y (le_pull ⟨I, U, g'⟩ j (W := U i) (i := i) le_rfl) (t'.s fun _ => i).val = 1 := by
  refine ⟨⟨fun i => (t.s i)⁻¹⟩,
    isGen_inv_of_eq t ht ((⟨I, U, g'⟩ : LB X).pull j).g fun a b => ?_, fun i => ?_⟩
  · dsimp only [LB.pull, LB.LinComb]
    simp only [hg, map_inv, zpow_one, Finset.prod_inv_distrib]
    try rfl
  · exact (map_mul _ _ _).symm.trans ((congrArg _ (Units.mul_inv _)).trans (map_one _))

theorem mem_basicOpen_of_mem {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) {x : X}
    (hx : x ∈ Out.nonzeroLocus s) {i : L.ι} (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have h := congrArg X.basicOpen (s.compat i k)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (L.g i k).isUnit] at h
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at h
  have hm : x ∈ L.U i ⊓ L.U k := ⟨hi, X.basicOpen_le _ hk⟩
  exact (h.ge (⟨hm, hm, hk⟩ : x ∈ _ ⊓ (_ ⊓ X.basicOpen (s.f k)))).2

theorem app_cst {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {X Y : Scheme.{0}}
    {f : X ⟶ Sp O} {j : Y ⟶ X} {g : Y ⟶ Sp K} (h : j ≫ f = g ≫ spMap φ) (U : X.Opens) (a : O) :
    (j.app U).hom (GlobalTheory.AbLaw.cst f U a) = GlobalTheory.AbLaw.cst g (j ⁻¹ᵁ U) (φ a) := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ f.appTop ≫ j.appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appTop := by
    rw [← Scheme.Hom.comp_appTop, h, Scheme.Hom.comp_appTop, Scheme.ΓSpecIso_inv_naturality_assoc]
  have h2 := congrArg (fun u => u.hom a) h1
  have h3 := congrArg (fun u => u.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)))
    (j.naturality (homOfLE (le_top : U ≤ ⊤)).op)
  exact h3.trans (congrArg (rs Y le_top) h2)

theorem isUnit_of_mem_basicOpen {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}}
    (f : X ⟶ Sp O) {U : X.Opens} {a : O} {x : X} (hx : x ∈ X.basicOpen (GlobalTheory.AbLaw.cst f U a))
    (hf : f x = IsLocalRing.closedPoint O) : IsUnit a := by
  have h : X.basicOpen (GlobalTheory.AbLaw.cst f U a) =
      U ⊓ X.basicOpen (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom a)) :=
    Scheme.basicOpen_res _ _ _
  have h1 : x ∈ X.basicOpen (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)) := (h.le hx).2
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine] at h1
  have h2 : a ∉ (f x).asIdeal := h1
  rw [hf] at h2
  exact not_not.1 h2

theorem triv_of_triv_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → Triv (M.pull j) → Triv M := by
  intro O K _ _ _ _ _ _ _ _ X XK f j fK hp hsm hqc hgi M hM ⟨t, ht⟩
  have : IsDominant (spMap (algebraMap O K)) :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective O K)).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap O K))
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isPullback hp.flip
  have : QuasiCompact j := MorphismProperty.of_isPullback (P := @QuasiCompact) hp.flip inferInstance
  have : IsIntegral XK := GeometricallyIntegral.geometrically_isIntegral _ _ _ hp
  obtain ⟨z⟩ : Nonempty XK := inferInstance
  obtain ⟨i₀, hi₀⟩ := exists_chart hM (j z)
  have : Nonempty ((M.pull j).U fun _ => i₀) := ⟨⟨z, le_pull M j le_rfl hi₀⟩⟩
  obtain ⟨t', ht', htt⟩ := exists_isGen_inv M.g (GlobalTheory.AbLaw.pw M (-1)).g
    (fun a b => zpow_neg_one _) j t ht
  have hne : (t'.s fun _ => i₀).val ≠ 0 := fun h => by
    have h1 := htt i₀
    have : Nonempty (j ⁻¹ᵁ M.U i₀) := ⟨⟨z, hi₀⟩⟩
    rw [h, map_zero, mul_zero] at h1
    exact zero_ne_one h1
  obtain ⟨c, s, hc, hs, x, hx, hfx⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K X XK f j fK hp hsm hqc hgi M hM
    (genSec t ht) ⟨fun _ => i₀, (t.s fun _ => i₀).ne_zero⟩
  obtain ⟨c', s', hc', hs', x', hx', hfx'⟩ := GlobalTheory.T.exists_sec_nonzero_on_special_fibre_extending_smul O K X XK f j fK hp hsm hqc hgi _
    (isLB_pw hM (-1)) (genSec t' ht') ⟨fun _ => i₀, hne⟩
  have hprod : ∀ i : M.ι, (j.app (M.U i)).hom (s.f i * (show Γ(X, M.U i) from s'.f i)) =
      GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) (c * c') := fun i => by
    have h' : (j.app (M.U i)).hom (s'.f i) = GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) c' *
      rs XK (le_pull (GlobalTheory.AbLaw.pw M (-1)) j (W := M.U i) (i := i) le_rfl)
        (t'.s fun _ => i).val := hs' i
    have h : (j.app (M.U i)).hom (s.f i) = GlobalTheory.AbLaw.cst fK (j ⁻¹ᵁ M.U i) c *
      rs XK (le_pull M j le_rfl) (t.s fun _ => i).val := hs i
    rw [map_mul, h, h', _root_.mul_mul_mul_comm, ← map_mul]
    exact (congrArg _ (htt i)).trans (_root_.mul_one _)
  have key : ∀ i, IsUnit (s.f i) := by
    rcases ValuationRing.isInteger_or_isInteger O (c * c') with ⟨a, ha⟩ | ⟨a, ha⟩
    · have e : ∀ i : M.ι, s.f i * (show Γ(X, M.U i) from s'.f i) = GlobalTheory.AbLaw.cst f (M.U i) a :=
        fun i => j.app_injective _ ((hprod i).trans (ha ▸ (app_cst _ hp.w _ a).symm))
      obtain ⟨y, hy, hy₁, hy₂⟩ := (f.isIrreducible_preimage f.isOpenMap
        (isIrreducible_singleton (x := IsLocalRing.closedPoint O))).isPreirreducible _ _
        (Out.nonzeroLocus s).isOpen (Out.nonzeroLocus s').isOpen ⟨x, hfx, hx⟩ ⟨x', hfx', hx'⟩
      obtain ⟨k, hk⟩ := exists_chart hM y
      have hu : IsUnit a := by
        refine isUnit_of_mem_basicOpen f (U := M.U k) (x := y) ?_ hy
        rw [← e k, Scheme.basicOpen_mul]
        exact ⟨mem_basicOpen_of_mem s hy₁ hk, mem_basicOpen_of_mem s' hy₂ (i := k) hk⟩
      exact fun i => isUnit_of_mul_isUnit_left ((e i).symm ▸ hu.map _)
    · intro i
      have e : s.f i * ((show Γ(X, M.U i) from s'.f i) * GlobalTheory.AbLaw.cst f (M.U i) a) = 1 := by
        refine j.app_injective _ ?_
        change (j.app (M.U i)).hom _ = (j.app (M.U i)).hom _
        rw [← _root_.mul_assoc, map_mul, hprod, app_cst _ hp.w, ← map_mul, ha,
          mul_inv_cancel₀ (mul_ne_zero hc hc'), map_one, map_one]
      exact IsUnit.of_mul_eq_one _ e
  exact ⟨⟨fun i => (key i).unit⟩, fun a b => Units.ext (s.compat a b)⟩

end GlobalTheory.ValGenExtend
