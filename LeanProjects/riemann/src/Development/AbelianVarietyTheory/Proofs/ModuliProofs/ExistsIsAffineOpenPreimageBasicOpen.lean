import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsDenomOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open TopologicalSpace

namespace GlobalTheory.AmpleSpread

open GlobalTheory.SecSpread GlobalTheory.LBGerm

variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}

theorem exists_const_mul_eq_zero (H : IsPullback φ π p (spMap (algebraMap R K))) {U : X.Opens}
    (hU : IsAffineOpen U) (a : Γ(X, U)) (h : ∀ z, φ z ∈ U → gs φ z U a = 0) :
    ∃ d : R, d ≠ 0 ∧ ∀ y ∈ U, cst p y d * gs (𝟙 X) y U a = 0 := by
  have e : (φ.app U).hom a = 0 := fn_ext fun z hz => by
    have hz' : φ z ∈ U := hz
    refine (gs_pull (𝟙 X') φ z U hz' _).trans ?_
    rw [Category.id_comp, h z hz', gs_zero (𝟙 X') z _ hz]
  let _ := (φ.app U).hom.toAlgebra
  have hl := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := .of R) (L := .of K) (nonZeroDivisors R) H hU
  obtain ⟨⟨_, d, hd, rfl⟩, hm⟩ := (@IsLocalization.map_eq_zero_iff _ _ _ _ _ _ hl a).1 e
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun y hy => ?_⟩
  have e' := congrArg (gs (𝟙 X) y U) (show constFn p U d * a = 0 from hm)
  rwa [gs_mul _ y _ hy, gs_constFn p U _ y hy, Category.id_comp, gs_zero _ y _ hy] at e'

theorem exists_sec_preimage_nonzeroLocus_eq (H : IsPullback φ π p (spMap (algebraMap R K))) [CompactSpace X]
    [X.IsSeparated] {L : LB X} (hL : L.IsLB) (s : (L.pull φ).Sec) :
    ∃ θ : L.Sec, φ ⁻¹ᵁ Out.nonzeroLocus θ = Out.nonzeroLocus s := by
  classical
  obtain ⟨α, _, V, c, hV, hle, hc⟩ := exists_finite_affine_refinement hL
  have loc : ∀ x : α, ∃ (d : R) (_ : d ≠ 0) (a : Γ(X, V x)), ∀ z, φ z ∈ V x → gs φ z (V x) a =
      cst (φ ≫ p) z d * gs (𝟙 X') z ((L.pull φ).U (fun _ => c x)) (s.f (fun _ => c x)) := by
    intro x
    have hle' : φ ⁻¹ᵁ V x ≤ (L.pull φ).U (fun _ => c x) := fun z hz => mem_pull.2 (hle x hz)
    obtain ⟨d, hd, a, ha⟩ := exists_denom_of_isAffineOpen H (hV x) (resG X' hle' (s.f (fun _ => c x)))
    refine ⟨d, hd, a, fun z hz => ?_⟩
    have e := congrArg (gs (𝟙 X') z _) ha
    have hz' : (𝟙 X' : X' ⟶ X') z ∈ φ ⁻¹ᵁ V x := hz
    rw [gs_mul _ z _ hz', gs_res _ z hle' hz', gs_pull (𝟙 X') φ z _ hz, gs_pull (𝟙 X') φ z _ hz,
      Category.id_comp, gs_constFn p _ φ z hz] at e
    exact e.symm
  choose d hd a ha using loc
  obtain ⟨b, hb⟩ : ∃ b : ∀ x, Γ(X, V x), ∀ x z, φ z ∈ V x → gs φ z (V x) (b x) =
      cst (φ ≫ p) z (∏ x, d x) * gs (𝟙 X') z ((L.pull φ).U (fun _ => c x)) (s.f (fun _ => c x)) :=
    ⟨fun x => constFn p _ (∏ w ∈ Finset.univ.erase x, d w) * a x, fun x z hz => by
      rw [gs_mul φ z _ hz, gs_constFn p _ φ z hz, ha x z hz, ← Finset.mul_prod_erase _ d (Finset.mem_univ x), cst_mul]
      ring⟩
  have kill : ∀ q : α × α, ∃ e : R, e ≠ 0 ∧ ∀ y ∈ V q.1 ⊓ V q.2, cst p y e * (gs (𝟙 X) y _ (b q.1) -
      (gm (𝟙 X) y (L.U (c q.1) ⊓ L.U (c q.2)) (L.g (c q.1) (c q.2))).val * gs (𝟙 X) y _ (b q.2)) = 0 := by
    rintro ⟨x, w⟩
    have l : V x ⊓ V w ≤ L.U (c x) ⊓ L.U (c w) := inf_le_inf (hle x) (hle w)
    have hx : ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (y : Z), r y ∈ V x ⊓ V w → gs r y (V x ⊓ V w) (resG X inf_le_left (b x) -
        resG X l (L.g (c x) (c w)).val * resG X inf_le_right (b w)) =
        gs r y _ (b x) - (gm r y (L.U (c x) ⊓ L.U (c w)) (L.g (c x) (c w))).val * gs r y _ (b w) := fun r y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_unit r y _ (l hy)]
    obtain ⟨e, he, h⟩ := exists_const_mul_eq_zero H ((hV x).inf (hV w)) _ fun z hz => (hx φ z hz).trans (by
      rw [hb x z hz.1, hb w z hz.2, pull_sec_trans s z (l hz).1 (l hz).2]
      ring)
    exact ⟨e, he, fun y hy => (congrArg _ (hx (𝟙 X) y hy)).symm.trans (h y hy)⟩
  choose e he hk using kill
  obtain ⟨θ, hθ⟩ := exists_sec_of_refinement hL V c hle hc (fun x => constFn p _ (∏ q, e q) * b x)
    fun y x w hx hw => by
      have h := hk (x, w) y ⟨hx, hw⟩
      rw [gs_mul _ y _ hx, gs_mul _ y _ hw, gs_constFn p _ _ y hx, gs_constFn p _ _ y hw, Category.id_comp,
        ← Finset.mul_prod_erase _ e (Finset.mem_univ (x, w)), cst_mul]
      linear_combination cst p y (∏ q ∈ Finset.univ.erase (x, w), e q) * h
  refine ⟨θ, Opens.ext (Set.ext fun z => ?_)⟩
  obtain ⟨x, hx⟩ := hc (φ z)
  have h₁ := congrArg (φ.stalkMap z).hom (hθ (φ z) (c x) x (hle x hx) hx)
  rw [map_mul, ← gs_stalkMap φ z _ (hle x hx), ← gs_stalkMap φ z _ hx, gs_mul φ z _ hx, gs_constFn p _ φ z hx,
    hb x z hx] at h₁
  refine (mem_nonzeroLocus_iff_pull θ φ z (hle x hx)).trans (Iff.trans ?_
    (mem_nonzeroLocus_iff_isUnit s (k := fun _ => c x) (mem_pull.2 (hle x hx))).symm)
  rw [h₁, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff]
  exact ⟨fun h => h.2.2.2, fun h => ⟨(Units.isUnit _).map _,
    isUnit_cst H.w z (Finset.prod_ne_zero_iff.2 fun q _ => he q),
    isUnit_cst H.w z (Finset.prod_ne_zero_iff.2 fun q _ => hd q), h⟩⟩

theorem exists_basicOpen_le {V : (Sp R).Opens} (hV : genericPoint (Sp R) ∈ V) :
    ∃ f : R, f ≠ 0 ∧ PrimeSpectrum.basicOpen f ≤ V := by
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  refine ⟨f, ?_, hle⟩
  rintro rfl
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hf (Ideal.zero_mem _)

omit [IsDomain R] in

theorem isAffineOpen_inf_preimage_basicOpen (p : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) (f : R) :
    IsAffineOpen (U ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  have := hU.basicOpen (constFn p U f)
  have e := Scheme.basicOpen_appLE p U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)
  rw [basicOpen_eq_of_affine] at e
  exact e ▸ this

set_option backward.isDefEq.respectTransparency false in

theorem exists_isAffineOpen_preimage_basicOpen (H : IsPullback φ π p (spMap (algebraMap R K))) [QuasiCompact p]
    [QuasiSeparated p] [IsAffine X'] : ∃ f : R, f ≠ 0 ∧ IsAffineOpen (p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  have H' : IsPullback φ (π ≫ e.hom) p ((Sp R).fromSpecStalk (genericPoint (Sp R))) := by
    have h₀ : IsPullback (spMap (algebraMap R K)) e.hom (𝟙 _) ((Sp R).fromSpecStalk (genericPoint (Sp R))) :=
      IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans he.symm⟩
    have := H.paste_vert h₀
    rwa [Category.comp_id] at this
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit H'
  have (V : StalkLimit.AffNhd (genericPoint (Sp R))) : CompactSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have (V : StalkLimit.AffNhd (genericPoint (Sp R))) : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have : IsAffine (StalkLimit.cone H').pt := ‹IsAffine X'›
  obtain ⟨V, hV⟩ := Scheme.exists_isAffine_of_isLimit _ _ hc
  have : IsAffine (pullback p V.1.ι) := hV
  have h₁ : IsAffineOpen (p ⁻¹ᵁ V.1) := IsAffine.of_isIso (pullbackRestrictIsoRestrict p V.1).inv
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le V.2.1
  refine ⟨f, hf, ?_⟩
  have h₂ := isAffineOpen_inf_preimage_basicOpen p h₁ f
  rwa [inf_eq_right.2 (p.preimage_mono hle)] at h₂

theorem exists_preimage_basicOpen_le (H : IsPullback φ π p (spMap (algebraMap R K))) [UniversallyClosed p]
    {U : X.Opens} (hU : φ ⁻¹ᵁ U = ⊤) : ∃ f : R, f ≠ 0 ∧ p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ U := by
  have hc : IsClosed (p '' (U : Set X)ᶜ) := p.isClosedMap _ U.isOpen.isClosed_compl
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le (V := ⟨_, hc.isOpen_compl⟩) (by
    rintro ⟨x, hx, e⟩
    obtain ⟨y, hy⟩ : genericPoint (Sp R) ∈ Set.range (spMap (algebraMap R K)) :=
      (IsGenericPointHom.fractionField R K).range_eq.ge rfl
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x y (e.trans hy.symm)
    exact hx (hU.ge (Set.mem_univ z)))
  exact ⟨f, hf, fun x hx => by_contra fun h => hle hx ⟨x, h, rfl⟩⟩

theorem exists_cover (H : IsPullback φ π p (spMap (algebraMap R K))) [IsProper p] {L : LB X} (hL : L.IsLB)
    (h : IsAmpleLB (L.pull φ)) :
    ∃ f : R, f ≠ 0 ∧ ∃ n, 1 ≤ n ∧ ∃ (N : ℕ) (θ : Fin (N + 1) → (lbPow L n).Sec),
      p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ ⨆ i, Out.nonzeroLocus (θ i) ∧
      ∀ i, IsAffineOpen (Out.nonzeroLocus (θ i) ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  obtain ⟨n, hn, N, s, hs, ha⟩ := h.exists_cover
  have hP := isLB_lbPow hL n
  choose t ht using fun i => exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hP φ) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL φ n).symm (s i)
  choose θ hθ using fun i => exists_sec_preimage_nonzeroLocus_eq H hP (t i)
  obtain ⟨f₀, hf₀, h₀⟩ := exists_preimage_basicOpen_le H (U := ⨆ i, Out.nonzeroLocus (θ i)) (by
    rw [Scheme.Hom.preimage_iSup, ← hs]
    exact iSup_congr fun i => (hθ i).trans (ht i))
  have aff : ∀ i, ∃ g : R, g ≠ 0 ∧ IsAffineOpen (Out.nonzeroLocus (θ i) ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen g) := fun i => by
    have := isAffineHom_nonzeroLocus_ι hP (θ i)
    have : IsAffine (φ ⁻¹ᵁ Out.nonzeroLocus (θ i)) := by
      rw [hθ, ht]; exact ha i
    obtain ⟨g, hg, h₁⟩ := exists_isAffineOpen_preimage_basicOpen
      ((isPullback_morphismRestrict φ (Out.nonzeroLocus (θ i))).paste_vert H)
    refine ⟨g, hg, ?_⟩
    have h₂ : IsAffineOpen ((Out.nonzeroLocus (θ i)).ι ''ᵁ (Out.nonzeroLocus (θ i)).ι ⁻¹ᵁ
        p ⁻¹ᵁ PrimeSpectrum.basicOpen g) := h₁.image_of_isOpenImmersion (Out.nonzeroLocus (θ i)).ι
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h₂
  choose g hg hga using aff
  refine ⟨f₀ * ∏ i, g i, mul_ne_zero hf₀ (Finset.prod_ne_zero_iff.2 fun i _ => hg i), n, hn, N, θ,
    (p.preimage_mono (PrimeSpectrum.basicOpen_mul_le_left _ _)).trans h₀, fun i => ?_⟩
  have h₁ := isAffineOpen_inf_preimage_basicOpen p (hga i) (f₀ * ∏ i, g i)
  have hle : PrimeSpectrum.basicOpen (f₀ * ∏ i, g i) ≤ PrimeSpectrum.basicOpen (g i) := by
    rw [← Finset.mul_prod_erase _ g (Finset.mem_univ i), mul_left_comm]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  rwa [inf_assoc, inf_eq_right.2 (p.preimage_mono hle)] at h₁

theorem relAmple_spread : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp R)) (M : LB A.left), IsProper A.hom → M.IsLB → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap R K)))) (M.pull (pullback.fst A.hom (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap φ))) (M.pull (pullback.fst A.hom (spMap φ))) := by
  intro R K _ _ _ _ _ _ A M _ hM h
  obtain ⟨f, hf, n, hn, N, θ, hc, ha⟩ := exists_cover (IsPullback.of_hasPullback A.hom (spMap (algebraMap R K))) hM
    (isAmpleLB_of_relAmple_of_isAffine _ (LB.isLB_pull hM _) h)
  refine ⟨f, hf, fun R' _ φ hu => ?_⟩
  let ψ := pullback.fst A.hom (spMap φ)
  have : IsProper (Over.mk (pullback.snd A.hom (spMap φ))).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback A.hom (spMap φ)).flip inferInstance
  have hD : ∀ z, ψ z ∈ A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f := fun z => by
    have e : A.hom (ψ z) = spMap φ (pullback.snd A.hom (spMap φ) z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    show A.hom (ψ z) ∈ PrimeSpectrum.basicOpen f
    rw [e]
    exact fun hm => (pullback.snd A.hom (spMap φ) z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  refine (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2
    (isAmpleLB_of_cover (LB.isLB_pull hM _) hn (fun i => secPowPull (θ i) ψ) (top_le_iff.1 fun z _ => ?_) fun i => ?_)
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc (hD z))
    exact Opens.mem_iSup.2 ⟨i, (nonzeroLocus_secPowPull (θ i) ψ).ge hi⟩
  · have e : ψ ⁻¹ᵁ (Out.nonzeroLocus (θ i) ⊓ A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f) =
        Out.nonzeroLocus (secPowPull (θ i) ψ) :=
      (le_antisymm (fun z hz => hz.1) fun z hz => ⟨hz, hD z⟩).trans (nonzeroLocus_secPowPull (θ i) ψ).symm
    exact e ▸ (ha i).preimage ψ

end GlobalTheory.AmpleSpread
