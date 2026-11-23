import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingExistsAssociatedOfSumEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.PrimSec

section General
variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}}

theorem isPushout_app {g : R →+* R'} {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    {U : X.Opens} (hU : IsAffineOpen U) :
    IsPushout (CommRingCat.ofHom (AbLaw.cst f U)) (CommRingCat.ofHom g) (π.app U)
      (CommRingCat.ofHom (AbLaw.cst f' (π ⁻¹ᵁ U))) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of R')) (Iso.refl _) ?_ ?_ ?_ ?_
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl

theorem pre_le (π : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) : π ⁻¹ᵁ V ≤ π ⁻¹ᵁ U := fun _ hy => h hy

theorem app_rs (π : X' ⟶ X) {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) :
    (π.app V).hom (rs X h a) = rs X' (pre_le π h) ((π.app U).hom a) :=
  congrArg (fun φ => φ.hom a) (π.naturality (homOfLE h).op)

theorem app_cst {g : R →+* R'} {f : X ⟶ Spec (CommRingCat.of R)} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of R')} (H : π ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g))
    (U : X.Opens) (r : R) : (π.app U).hom (AbLaw.cst f U r) = AbLaw.cst f' (π ⁻¹ᵁ U) (g r) := by
  have e₁ := congrArg (fun φ => φ.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) H
  have e₂ := congrArg (fun φ => φ.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e₁ e₂
  refine (app_rs π le_top _).trans ?_
  change rs X' le_top (π.appTop.hom _) = rs X' le_top (f'.appTop.hom _)
  rw [e₂, ← e₁]
  rfl

theorem mem_basicOpen_rs {U V : X.Opens} (h : V ≤ U) (a : Γ(X, U)) {x : X} (hx : x ∈ V) :
    x ∈ X.basicOpen (rs X h a) ↔ x ∈ X.basicOpen a := by
  have := X.basicOpen_res a (homOfLE h).op
  refine (congrArg (x ∈ ·) this).to_iff.trans ?_
  exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩

theorem mem_basicOpen_cst (f : X ⟶ Spec (CommRingCat.of R)) (W : X.Opens) (r : R) {x : X} (hx : x ∈ W) :
    x ∈ X.basicOpen (AbLaw.cst f W r) ↔ r ∉ (f x).asIdeal := by
  refine (mem_basicOpen_rs le_top _ hx).trans ?_
  have e₁ := f.preimage_basicOpen_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have e₂ := basicOpen_eq_of_affine (R := CommRingCat.of R) r
  refine (congrArg (x ∈ ·) e₁).to_iff.symm.trans ?_
  exact (congrArg (f x ∈ ·) e₂).to_iff

theorem mem_basicOpen_iff {U : X.Opens} (hU : IsAffineOpen U) (x : U) (s : Γ(X, U)) :
    x.1 ∈ X.basicOpen s ↔ s ∉ (hU.primeIdealOf x).asIdeal := by
  have h : (hU.primeIdealOf x : Spec Γ(X, U)) ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen s ↔
      x.1 ∈ X.basicOpen s := by
    conv_rhs => rw [← hU.fromSpec_primeIdealOf x]
    rfl
  rw [← h, hU.fromSpec_preimage_basicOpen]
  rfl

theorem cst_eq (f : X ⟶ Spec (CommRingCat.of R)) (U : X.Opens) :
    AbLaw.cst f U = (f.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  ext x; simp [AbLaw.cst, Scheme.Hom.appLE]; rfl

theorem cst_smooth (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] {U : X.Opens} (hU : IsAffineOpen U) :
    (AbLaw.cst f U).Smooth := by
  rw [cst_eq]
  exact RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv
    (f.smooth_appLE (isAffineOpen_top _) hU le_top)

theorem exists_etale_chart (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] {U : X.Opens} {x : X} (hx : x ∈ U) :
    ∃ V : X.Opens, IsAffineOpen V ∧ x ∈ V ∧ V ≤ U ∧ ∃ (n : ℕ) (φ : MvPolynomial (Fin n) R →+* Γ(X, V)),
      φ.comp MvPolynomial.C = AbLaw.cst f V ∧ φ.Etale := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hW : IsAffineOpen W := hW
  letI := (AbLaw.cst f W).toAlgebra
  haveI : Algebra.Smooth R Γ(X, W) := cst_smooth f hW
  obtain ⟨g, hg, hs⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth R (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  have hxg : x ∈ X.basicOpen g := by
    exact (mem_basicOpen_iff hW ⟨x, hxW⟩ g).2 hg
  haveI := hW.isLocalization_basicOpen g
  letI := (AbLaw.cst f (X.basicOpen g)).toAlgebra
  haveI : IsScalarTower R Γ(X, W) Γ(X, X.basicOpen g) :=
    .of_algebraMap_eq fun r => (rs_cst f (X.basicOpen_le g) r).symm
  have h2 : Algebra.IsStandardSmooth R Γ(X, X.basicOpen g) :=
    .of_algEquiv ((IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)).restrictScalars R)
  obtain ⟨n, φ, h3, h4⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial (f := AbLaw.cst f (X.basicOpen g)) h2
  exact ⟨_, hW.basicOpen g, hxg, (X.basicOpen_le g).trans hWU, n, φ, h3, h4⟩

theorem isPrime_map [IsLocalRing R] (f : X ⟶ Spec (CommRingCat.of R)) [GeometricallyIntegral f] {V : X.Opens}
    (hV : IsAffineOpen V) {x : X} (hx : x ∈ V) (hfx : f x = IsLocalRing.closedPoint R) :
    ((IsLocalRing.maximalIdeal R).map (AbLaw.cst f V)).IsPrime := by
  let g := IsLocalRing.residue R
  let t := Spec.map (CommRingCat.ofHom g)
  have H := IsPullback.of_hasPullback f t
  haveI : IsIntegral (pullback f t) :=
    GeometricallyIntegral.geometrically_isIntegral t _ _ H
  have po := isPushout_app H hV
  have hne : Nonempty (pullback.fst f t ⁻¹ᵁ V) := by
    have : x ∈ Set.range (pullback.fst f t) := by
      rw [Scheme.Pullback.range_fst]
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      rw [hfx]
      exact IsLocalRing.comap_closedPoint g
    obtain ⟨y, rfl⟩ := this
    exact ⟨⟨y, hx⟩⟩
  have hk : RingHom.ker ((pullback.fst f t).app V).hom = (IsLocalRing.maximalIdeal R).map (AbLaw.cst f V) := by
    apply le_antisymm
    · intro b hb
      let I := (IsLocalRing.maximalIdeal R).map (AbLaw.cst f V)
      let q : IsLocalRing.ResidueField R →+* Γ(X, V) ⧸ I :=
        Ideal.quotientMap I (AbLaw.cst f V) Ideal.le_comap_map
      have e := congrArg (fun φ => φ.hom b) (po.inl_desc (CommRingCat.ofHom (Ideal.Quotient.mk I))
        (CommRingCat.ofHom q) (by ext a; rfl))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
      rw [RingHom.mem_ker.1 hb, map_zero] at e
      exact Ideal.Quotient.eq_zero_iff_mem.1 e.symm
    · refine Ideal.map_le_iff_le_comap.2 fun a ha => ?_
      change ((pullback.fst f t).app V).hom (AbLaw.cst f V a) = 0
      rw [app_cst H.w, show g a = 0 from (IsLocalRing.residue_eq_zero_iff a).2 ha, map_zero]
  rw [← hk]
  exact RingHom.ker_isPrime _

end General

section Generic
variable {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X} {fK : XK ⟶ Sp K}
  (H : IsPullback j fK f (spMap (algebraMap O K)))
include H

theorem isLocalization_app {U : X.Opens} (hU : IsAffineOpen U) :
    letI := (j.app U).hom.toAlgebra
    IsLocalization ((nonZeroDivisors O).map (AbLaw.cst f U)) Γ(XK, j ⁻¹ᵁ U) := by
  have po := isPushout_app H hU
  let := (j.app U).hom.toAlgebra
  let : Algebra O Γ(X, U) := (AbLaw.cst f U).toAlgebra
  let : Algebra K Γ(XK, j ⁻¹ᵁ U) := (AbLaw.cst fK (j ⁻¹ᵁ U)).toAlgebra
  let : Algebra O Γ(XK, j ⁻¹ᵁ U) := ((j.app U).hom.comp (AbLaw.cst f U)).toAlgebra
  have : IsScalarTower O Γ(X, U) Γ(XK, j ⁻¹ᵁ U) := .of_algebraMap_eq' rfl
  have : IsScalarTower O K Γ(XK, j ⁻¹ᵁ U) := .of_algebraMap_eq' congr($(po.w).hom)
  exact (Algebra.isLocalization_iff_isPushout (nonZeroDivisors O) K).mpr (CommRingCat.isPushout_iff_isPushout.mp po)

theorem exists_numerator {U : X.Opens} (hU : IsAffineOpen U) (t : Γ(XK, j ⁻¹ᵁ U)) :
    ∃ (π : O) (b : Γ(X, U)), π ≠ 0 ∧ (j.app U).hom b = AbLaw.cst fK (j ⁻¹ᵁ U) (algebraMap O K π) * t := by
  letI := (j.app U).hom.toAlgebra
  haveI := isLocalization_app H hU
  obtain ⟨⟨b, _, π, hπ, rfl⟩, h⟩ := IsLocalization.surj ((nonZeroDivisors O).map (AbLaw.cst f U)) t
  refine ⟨π, b, nonZeroDivisors.ne_zero hπ, ?_⟩
  rw [← app_cst H.w, mul_comm]
  exact h.symm

theorem app_injective_of_affine [Smooth f] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective (j.app U).hom := by
  letI := (j.app U).hom.toAlgebra
  haveI := isLocalization_app H hU
  letI := (AbLaw.cst f U).toAlgebra
  haveI : Module.Flat O Γ(X, U) := (cst_smooth f hU).flat
  refine IsLocalization.injective (M := (nonZeroDivisors O).map (AbLaw.cst f U)) Γ(XK, j ⁻¹ᵁ U) ?_
  rintro _ ⟨π, hπ, rfl⟩
  have := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(X, U)) hπ
  refine mem_nonZeroDivisors_iff_left.2 fun b hb => this ?_
  simp only [Algebra.smul_def, mul_zero]
  exact hb

theorem app_injective [Smooth f] (U : X.Opens) : Function.Injective (j.app U).hom := by
  intro a b h
  refine X.sheaf.eq_of_locally_eq' (fun V : {V : X.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ a b fun V => ?_
  · intro x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, hWU⟩, hxW⟩
  · apply app_injective_of_affine H V.1.2
    exact (app_rs j V.2 a).trans ((congrArg _ h).trans (app_rs j V.2 b).symm)

theorem exists_extension [Smooth f] {U : X.Opens} (t : Γ(XK, j ⁻¹ᵁ U))
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U) (b : Γ(X, V)), x ∈ V ∧
      (j.app V).hom b = rs XK (pre_le j hV) t) :
    ∃ b : Γ(X, U), (j.app U).hom b = t := by
  choose V hV b hx hb using h
  have hc : U ≤ ⨆ x : U, V x.1 x.2 := fun x hxU =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx x hxU⟩
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun x : U => V x.1 x.2) U
    (fun x => homOfLE (hV x.1 x.2)) hc (fun x => b x.1 x.2) (fun x y => by
      apply app_injective H
      refine (app_rs j inf_le_left _).trans (Eq.trans ?_ (app_rs j inf_le_right _).symm)
      rw [hb, hb]
      exact (rs_rs _ _ _).trans (rs_rs _ _ _).symm)
  refine ⟨s, XK.sheaf.eq_of_locally_eq' (fun x : U => j ⁻¹ᵁ V x.1 x.2) (j ⁻¹ᵁ U)
    (fun x => homOfLE fun _ hy => hV x.1 x.2 hy) ?_ _ _ fun x => ?_⟩
  · intro y hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨j y, hy⟩, hx _ hy⟩
  · exact (app_rs j (hV x.1 x.2) s).symm.trans ((congrArg _ (hs x)).trans (hb x.1 x.2))

end Generic

section Sections
variable {X XK : Scheme.{0}} {j : XK ⟶ X} {M : LB X}

def loc (σ : LB.Sec (M.pull j)) (i : M.ι) {V : X.Opens} (hV : V ≤ M.U i) : Γ(XK, j ⁻¹ᵁ V) :=
  rs XK (le_pull M j hV) (σ.f (fun _ => i))

theorem rs_loc (σ : LB.Sec (M.pull j)) (i : M.ι) {V W : X.Opens} (hV : V ≤ M.U i) (h : W ≤ V) :
    rs XK (pre_le j h) (loc σ i hV) = loc σ i (h.trans hV) := rs_rs _ _ _

theorem loc_trans (σ : LB.Sec (M.pull j)) (i k : M.ι) {V : X.Opens} (hi : V ≤ M.U i) (hk : V ≤ M.U k) :
    loc σ i hi = (j.app V).hom (rs X (le_inf hi hk) (M.g i k).val) * loc σ k hk := by
  have h := congrArg (rs XK (le_inf (le_pull M j hi) (le_pull M j hk))) (σ.compat (fun _ => i) (fun _ => k))
  rw [map_mul] at h
  refine (rs_rs _ _ _).symm.trans (h.trans ?_)
  refine congrArg₂ (· * ·) ?_ (rs_rs _ _ _)
  rw [app_rs]
  have e : (M.pull j).g (fun _ => i) (fun _ => k) = res (fun _ hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit,
      Set.mem_iInter.1 hy.2 PUnit.unit⟩ : (M.pull j).U (fun _ => i) ⊓ (M.pull j).U (fun _ => k) ≤
        j ⁻¹ᵁ (M.U i ⊓ M.U k)) (pullU j _ (M.g i k)) := by
    change ∏ _ : PUnit, _ ^ (1 : ℤ) = _
    rw [Fintype.prod_unique]
    exact zpow_one _
  rw [e]
  exact rs_rs _ _ _

theorem rs_injective {Z : Scheme.{0}} [IsIntegral Z] {U V : Z.Opens} (h : V ≤ U) (hV : Nonempty V) :
    Function.Injective (rs Z h) := map_injective_of_isIntegral Z (homOfLE h)

theorem nonempty_of_ne_zero {Z : Scheme.{0}} {U : Z.Opens} {a : Γ(Z, U)} (ha : a ≠ 0) : Nonempty U := by
  by_contra h
  have : U = ⊥ := by
    rw [eq_bot_iff]
    exact fun x hx => (h ⟨⟨x, hx⟩⟩).elim
  subst this
  exact ha (Subsingleton.elim _ _)

theorem loc_ne_zero [IsIntegral XK] (σ : LB.Sec (M.pull j)) (hσ : ∃ i, σ.f i ≠ 0) (i : M.ι) {V : X.Opens}
    (hV : V ≤ M.U i) (hne : Nonempty (j ⁻¹ᵁ V)) : loc σ i hV ≠ 0 := by
  obtain ⟨k, hk⟩ := hσ
  intro h
  have h1 : σ.f (fun _ => i) = 0 := rs_injective (le_pull M j hV) hne (h.trans (map_zero _).symm)
  have h2 := σ.compat k (fun _ => i)
  rw [h1, map_zero, mul_zero] at h2
  obtain ⟨⟨y, hy⟩⟩ := hne
  obtain ⟨⟨z, hz⟩⟩ := nonempty_of_ne_zero hk
  obtain ⟨w, hw⟩ := nonempty_preirreducible_inter ((M.pull j).U k).isOpen ((M.pull j).U (fun _ => i)).isOpen
    ⟨z, hz⟩ ⟨y, le_pull M j hV hy⟩
  exact hk (rs_injective inf_le_left ⟨⟨w, hw⟩⟩ (h2.trans (map_zero _).symm))

end Sections

section Main
variable {O K : Type} [CommRing O] [IsDomain O] [ValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  {X XK : Scheme.{0}} {f : X ⟶ Sp O} {j : XK ⟶ X} {fK : XK ⟶ Sp K}
  (H : IsPullback j fK f (spMap (algebraMap O K))) {M : LB X} (σ : LB.Sec (M.pull j))
include H

theorem exists_of_ne [Ring.DimensionLEOne O] (c : K) (i : M.ι) {x : X} (hx : x ∈ M.U i)
    (hfx : f x ≠ IsLocalRing.closedPoint O) :
    ∃ (V : X.Opens) (hV : V ≤ M.U i) (b : Γ(X, V)), x ∈ V ∧
      (j.app V).hom b = AbLaw.cst fK (j ⁻¹ᵁ V) c * loc σ i hV := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx (M.U i).isOpen
  have hWU : W ≤ M.U i := hWU
  obtain ⟨π, b, hπ, hb⟩ := exists_numerator H hW (AbLaw.cst fK (j ⁻¹ᵁ W) c * loc σ i hWU)
  have h0 : (f x).asIdeal = ⊥ := by
    by_contra h
    exact hfx (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal ((f x).isPrime.isMaximal h)))
  have hxπ : x ∈ X.basicOpen (AbLaw.cst f W π) := (mem_basicOpen_cst f W π hxW).2 (by rw [h0]; exact hπ)
  have hle := X.basicOpen_le (AbLaw.cst f W π)
  obtain ⟨u, hu⟩ : IsUnit (AbLaw.cst f (X.basicOpen (AbLaw.cst f W π)) π) := by
    rw [← rs_cst f hle]
    exact X.toRingedSpace.isUnit_res_basicOpen _
  refine ⟨_, hle.trans hWU, u⁻¹.val * rs X hle b, hxπ, ?_⟩
  rw [map_mul, app_rs, hb, map_mul, map_mul, rs_cst, rs_cst, rs_loc σ _ _ hle, ← app_cst H.w, ← hu, ← _root_.mul_assoc, ← map_mul,
    Units.inv_mul, map_one, _root_.one_mul]

theorem exists_of_eq [Ring.DimensionLEOne O] [IsAlgClosed K] [Smooth f] [GeometricallyIntegral f]
    (hσ : ∃ i, σ.f i ≠ 0) (i : M.ι) {x : X} (hx : x ∈ M.U i)
    (hfx : f x = IsLocalRing.closedPoint O) :
    ∃ (V : X.Opens) (hV : V ≤ M.U i) (c : K) (b : Γ(X, V)), x ∈ V ∧ c ≠ 0 ∧
      (j.app V).hom b = AbLaw.cst fK (j ⁻¹ᵁ V) c * loc σ i hV ∧
      ∃ y ∈ X.basicOpen b, f y = IsLocalRing.closedPoint O := by
  haveI : IsIntegral XK := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  obtain ⟨V, hV, hxV, hVU, n, φ, hφ, hφ'⟩ := exists_etale_chart f hx
  have hp := isPrime_map f hV hxV hfx
  have hinj := app_injective H V
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hne : Nonempty (j ⁻¹ᵁ V) :=
    nonempty_of_ne_zero (a := 1) fun h => one_ne_zero (hinj ((map_one _).trans (h.trans (map_zero _).symm)))
  haveI : IsDomain Γ(X, V) := hinj.isDomain _
  obtain ⟨π, b, hπ, hb⟩ := exists_numerator H hV (loc σ i hVU)
  have hπ' : algebraMap O K π ≠ 0 := fun h => hπ (IsFractionRing.injective O K (h.trans (map_zero _).symm))
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact mul_ne_zero ((map_ne_zero _).2 hπ') (loc_ne_zero σ hσ i hVU hne) hb.symm
  letI := (AbLaw.cst f V).toAlgebra
  letI := φ.toAlgebra
  haveI : IsScalarTower O (MvPolynomial (Fin n) O) Γ(X, V) := .of_algebraMap_eq' hφ.symm
  haveI : Algebra.Etale (MvPolynomial (Fin n) O) Γ(X, V) := hφ'
  obtain ⟨ρ, b', e, hb'⟩ := GlobalTheory.etale_mvPolynomial_exists_content O K n Γ(X, V) hp b hb0
  have hρ : algebraMap O K ρ ≠ 0 := fun h => hb0 (by
    rw [e, IsFractionRing.injective O K (h.trans (map_zero _).symm), map_zero, zero_mul])
  refine ⟨V, hVU, (algebraMap O K ρ)⁻¹ * algebraMap O K π, b', hxV, mul_ne_zero (inv_ne_zero hρ) hπ', ?_, ?_⟩
  · rw [map_mul, _root_.mul_assoc, ← hb, e, map_mul]
    change _ = _ * ((j.app V).hom (AbLaw.cst f V ρ) * _)
    rw [app_cst H.w, ← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hρ, map_one, _root_.one_mul]
  · obtain ⟨y, hy⟩ := hV.isoSpec.hom.surjective
      (⟨(IsLocalRing.maximalIdeal O).map (AbLaw.cst f V), hp⟩ : PrimeSpectrum Γ(X, V))
    have hy' : (hV.primeIdealOf y).asIdeal = (IsLocalRing.maximalIdeal O).map (AbLaw.cst f V) :=
      congrArg PrimeSpectrum.asIdeal hy
    refine ⟨y.1, (mem_basicOpen_iff hV y b').2 (hy' ▸ hb'), ?_⟩
    refine PrimeSpectrum.ext (((IsLocalRing.maximalIdeal.isMaximal O).eq_of_le (f y.1).isPrime.ne_top
      fun a ha => ?_).symm)
    by_contra h
    exact (mem_basicOpen_iff hV y _).1 ((mem_basicOpen_cst f V a y.2).2 h) (hy' ▸ Ideal.mem_map_of_mem _ ha)

theorem exists_eq_mul [Smooth f] [GeometricallyIntegral f] {i k : M.ι} {V W : X.Opens} (hV : V ≤ M.U i)
    (hW : W ≤ M.U k) {c d : K} (hd : d ≠ 0) {a : Γ(X, V)} {b : Γ(X, W)}
    (ha : (j.app V).hom a = AbLaw.cst fK (j ⁻¹ᵁ V) c * loc σ i hV)
    (hb : (j.app W).hom b = AbLaw.cst fK (j ⁻¹ᵁ W) d * loc σ k hW)
    (hx : ∃ x ∈ V, f x = IsLocalRing.closedPoint O)
    (hy : ∃ y ∈ X.basicOpen b, f y = IsLocalRing.closedPoint O) :
    ∃ r : O, c = algebraMap O K r * d := by
  rcases ValuationRing.isInteger_or_isInteger O (c / d) with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, by rw [hr, div_mul_cancel₀ _ hd]⟩
  by_cases hc : c = 0
  · exact ⟨0, by rw [hc, map_zero, zero_mul]⟩
  have hr' : d = algebraMap O K r * c := by rw [hr, inv_div, div_mul_cancel₀ _ hc]
  have hirr' : ∀ p : Sp O, IsIrreducible (f ⁻¹' {p}) := fun p => by
    rw [← f.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.fiberι _).continuous.continuousOn
  have hirr := hirr' (IsLocalRing.closedPoint O)
  obtain ⟨x, hx, hfx⟩ := hx
  obtain ⟨y, hy, hfy⟩ := hy
  obtain ⟨z, hfz, hzV, hzb⟩ := hirr.isPreirreducible _ _ V.isOpen (X.basicOpen b).isOpen ⟨x, hfx, hx⟩ ⟨y, hfy, hy⟩
  have hz : z ∈ V ⊓ W := ⟨hzV, X.basicOpen_le b hzb⟩
  have e : rs X (inf_le_right : V ⊓ W ≤ W) b = AbLaw.cst f (V ⊓ W) r *
      (rs X (le_inf (inf_le_right.trans hW) (inf_le_left.trans hV)) (M.g k i).val *
        rs X (inf_le_left : V ⊓ W ≤ V) a) := by
    apply app_injective H
    rw [app_rs, hb, map_mul, rs_cst, rs_loc σ _ _ inf_le_right, map_mul, map_mul,
      app_cst H.w, app_rs j inf_le_left, ha, map_mul,
      rs_cst, rs_loc σ _ _ inf_le_left, loc_trans σ k i _ (inf_le_left.trans hV), hr', map_mul]
    ring
  have h1 := (mem_basicOpen_rs (inf_le_right : V ⊓ W ≤ W) b hz).2 hzb
  rw [e, Scheme.basicOpen_mul] at h1
  have h2 := (mem_basicOpen_cst f _ r hz).1 h1.1
  rw [show f z = IsLocalRing.closedPoint O from hfz] at h2
  obtain ⟨u, rfl⟩ : IsUnit r := by
    by_contra h
    exact h2 h
  exact ⟨u⁻¹.val, by rw [hr', ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]⟩

end Main

end GlobalTheory.PrimSec

open GlobalTheory.PrimSec in

theorem GlobalTheory.exists_smul_sec_nonzero_on_special_fibre : ∀ (O K : Type) [CommRing O] [IsDomain O] [ValuationRing O] [Ring.DimensionLEOne O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (X XK : Scheme.{0}) (f : X ⟶ Sp O) (j : XK ⟶ X) (fK : XK ⟶ Sp K), IsPullback j fK f (spMap (algebraMap O K)) → Smooth f → QuasiCompact f → GeometricallyIntegral f → ∀ M : LB X, M.IsLB → ∀ σ : LB.Sec (M.pull j), (∃ i, σ.f i ≠ 0) → ∃ (c : K) (s : LB.Sec M), c ≠ 0 ∧ (∀ i, (j.app (M.U i)).hom (s.f i) = cst fK (j ⁻¹ᵁ M.U i) c * rs XK (le_pull M j le_rfl) (σ.f (fun _ => i))) ∧ ∃ x ∈ Out.nonzeroLocus s, f x = IsLocalRing.closedPoint O := by
  intro O K _ _ _ _ _ _ _ _ X XK f j fK H hs _ hg M hM σ hσ
  obtain ⟨x₀, hx₀⟩ := f.surjective (IsLocalRing.closedPoint O)
  obtain ⟨i₀, hi₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x₀ ∈ ⨆ i, M.U i from hM.cover ▸ trivial)
  obtain ⟨V₀, hV₀, c, b₀, hxV₀, hc, hb₀, y, hy, hfy⟩ := exists_of_eq H σ hσ i₀ hi₀ hx₀
  have key : ∀ i, ∃ s : Γ(X, M.U i), (j.app (M.U i)).hom s = AbLaw.cst fK (j ⁻¹ᵁ M.U i) c * loc σ i le_rfl := by
    intro i
    refine exists_extension H _ fun x hx => ?_
    by_cases hfx : f x = IsLocalRing.closedPoint O
    · obtain ⟨V, hV, d, b, hxV, hd, hb, hy'⟩ := exists_of_eq H σ hσ i hx hfx
      obtain ⟨r, hr⟩ := exists_eq_mul H σ hV₀ hV hd hb₀ hb ⟨x₀, hxV₀, hx₀⟩ hy'
      refine ⟨V, hV, AbLaw.cst f V r * b, hxV, ?_⟩
      rw [map_mul, map_mul, app_cst H.w, hb, rs_cst, rs_loc σ _ _ hV, hr, map_mul, _root_.mul_assoc]
    · obtain ⟨V, hV, b, hxV, hb⟩ := exists_of_ne H σ c i hx hfx
      refine ⟨V, hV, b, hxV, ?_⟩
      rw [hb, map_mul, rs_cst, rs_loc σ _ _ hV]
  choose s hs' using key
  refine ⟨c, ⟨s, fun i k => ?_⟩, hc, hs', y, ?_, hfy⟩
  · apply app_injective H
    change (j.app _).hom (rs X inf_le_left (s i)) = (j.app _).hom (_ * rs X inf_le_right (s k))
    rw [map_mul, app_rs, app_rs, hs', hs', map_mul, map_mul, rs_cst, rs_cst,
      rs_loc σ _ _ inf_le_left, rs_loc σ _ _ inf_le_right,
      loc_trans σ i k _ inf_le_right, rs_self]
    ring
  · refine TopologicalSpace.Opens.mem_iSup.2 ⟨i₀, ?_⟩
    have e : rs X hV₀ (s i₀) = b₀ := by
      apply app_injective H
      rw [app_rs, hs', hb₀, map_mul, rs_cst, rs_loc σ _ _ hV₀]
    rw [← e] at hy
    exact (mem_basicOpen_rs hV₀ _ (X.basicOpen_le _ hy)).1 hy
