import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenPreimageBasicOpen

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open TopologicalSpace

namespace GlobalTheory.AmpleSpreadAt

open GlobalTheory.SecSpread GlobalTheory.LBGerm

variable {R : Type} [CommRing R] {q : PrimeSpectrum R}
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp (Localization.AtPrime q.asIdeal)}

theorem exists_denom (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) {U : X.Opens}
    (hU : IsAffineOpen U) (t : Γ(X', φ ⁻¹ᵁ U)) :
    ∃ d ∈ q.asIdeal.primeCompl, ∃ a : Γ(X, U), (φ.app U).hom (constFn p U d) * t = (φ.app U).hom a := by
  let _ := (φ.app U).hom.toAlgebra
  have hl := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := .of R) (L := .of (Localization.AtPrime q.asIdeal))
    q.asIdeal.primeCompl H hU
  obtain ⟨⟨a, ⟨_, d, hd, rfl⟩⟩, e⟩ := @IsLocalization.surj _ _ _ _ _ _ hl t
  exact ⟨d, hd, a, (mul_comm _ _).trans e⟩

theorem exists_const_mul_eq_zero (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal))))
    {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) (h : ∀ z, φ z ∈ U → gs φ z U a = 0) :
    ∃ d ∈ q.asIdeal.primeCompl, ∀ y ∈ U, cst p y d * gs (𝟙 X) y U a = 0 := by
  have e : (φ.app U).hom a = 0 := fn_ext fun z hz => by
    have hz' : φ z ∈ U := hz
    refine (gs_pull (𝟙 X') φ z U hz' _).trans ?_
    rw [Category.id_comp, h z hz', gs_zero (𝟙 X') z _ hz]
  let _ := (φ.app U).hom.toAlgebra
  have hl := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := .of R) (L := .of (Localization.AtPrime q.asIdeal))
    q.asIdeal.primeCompl H hU
  obtain ⟨⟨_, d, hd, rfl⟩, hm⟩ := (@IsLocalization.map_eq_zero_iff _ _ _ _ _ _ hl a).1 e
  refine ⟨d, hd, fun y hy => ?_⟩
  have e' := congrArg (gs (𝟙 X) y U) (show constFn p U d * a = 0 from hm)
  rwa [gs_mul _ y _ hy, gs_constFn p U _ y hy, Category.id_comp, gs_zero _ y _ hy] at e'

theorem isUnit_cst (hw : φ ≫ p = π ≫ spMap (algebraMap R (Localization.AtPrime q.asIdeal))) (z : X') {d : R}
    (hd : d ∈ q.asIdeal.primeCompl) : IsUnit (cst (φ ≫ p) z d) := by
  have hu : IsUnit (algebraMap R (Localization.AtPrime q.asIdeal) d) :=
    IsLocalization.map_units (Localization.AtPrime q.asIdeal) (⟨d, hd⟩ : q.asIdeal.primeCompl)
  rw [hw, cst, ← gs_pull π _ z ⊤ trivial]
  have e := congrArg (gs π z ⊤) (spMap_appTop (algebraMap R (Localization.AtPrime q.asIdeal)) d)
  refine (congrArg IsUnit e).mpr ?_
  rw [gs_eq π z ⊤ trivial]
  exact ((hu.map _).map _).map _

theorem exists_sec_preimage_nonzeroLocus_eq
    (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) [CompactSpace X]
    [X.IsSeparated] {L : LB X} (hL : L.IsLB) (s : (L.pull φ).Sec) :
    ∃ θ : L.Sec, φ ⁻¹ᵁ Out.nonzeroLocus θ = Out.nonzeroLocus s := by
  classical
  obtain ⟨α, _, V, c, hV, hle, hc⟩ := exists_finite_affine_refinement hL
  have loc : ∀ x : α, ∃ (d : R) (_ : d ∈ q.asIdeal.primeCompl) (a : Γ(X, V x)), ∀ z, φ z ∈ V x → gs φ z (V x) a =
      cst (φ ≫ p) z d * gs (𝟙 X') z ((L.pull φ).U (fun _ => c x)) (s.f (fun _ => c x)) := by
    intro x
    have hle' : φ ⁻¹ᵁ V x ≤ (L.pull φ).U (fun _ => c x) := fun z hz => mem_pull.2 (hle x hz)
    obtain ⟨d, hd, a, ha⟩ := exists_denom H (hV x) (resG X' hle' (s.f (fun _ => c x)))
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
  have kill : ∀ xw : α × α, ∃ e : R, e ∈ q.asIdeal.primeCompl ∧ ∀ y ∈ V xw.1 ⊓ V xw.2, cst p y e * (gs (𝟙 X) y _ (b xw.1) -
      (gm (𝟙 X) y (L.U (c xw.1) ⊓ L.U (c xw.2)) (L.g (c xw.1) (c xw.2))).val * gs (𝟙 X) y _ (b xw.2)) = 0 := by
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
  obtain ⟨θ, hθ⟩ := exists_sec_of_refinement hL V c hle hc (fun x => constFn p _ (∏ xw, e xw) * b x)
    fun y x w hx hw => by
      have h := hk (x, w) y ⟨hx, hw⟩
      rw [gs_mul _ y _ hx, gs_mul _ y _ hw, gs_constFn p _ _ y hx, gs_constFn p _ _ y hw, Category.id_comp,
        ← Finset.mul_prod_erase _ e (Finset.mem_univ (x, w)), cst_mul]
      linear_combination cst p y (∏ xw ∈ Finset.univ.erase (x, w), e xw) * h
  refine ⟨θ, Opens.ext (Set.ext fun z => ?_)⟩
  obtain ⟨x, hx⟩ := hc (φ z)
  have h₁ := congrArg (φ.stalkMap z).hom (hθ (φ z) (c x) x (hle x hx) hx)
  rw [map_mul, ← gs_stalkMap φ z _ (hle x hx), ← gs_stalkMap φ z _ hx, gs_mul φ z _ hx, gs_constFn p _ φ z hx,
    hb x z hx] at h₁
  refine (mem_nonzeroLocus_iff_pull θ φ z (hle x hx)).trans (Iff.trans ?_
    (mem_nonzeroLocus_iff_isUnit s (k := fun _ => c x) (mem_pull.2 (hle x hx))).symm)
  rw [h₁, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff]
  exact ⟨fun h => h.2.2.2, fun h => ⟨(Units.isUnit _).map _,
    isUnit_cst H.w z (Submonoid.prod_mem _ fun xw _ => he xw),
    isUnit_cst H.w z (Submonoid.prod_mem _ fun x _ => hd x), h⟩⟩

theorem exists_basicOpen_le' {x : Sp R} {V : (Sp R).Opens} (hV : x ∈ V) :
    ∃ f : R, x ∈ (PrimeSpectrum.basicOpen f : (Sp R).Opens) ∧ (PrimeSpectrum.basicOpen f : (Sp R).Opens) ≤ V := by
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  exact ⟨f, hf, hle⟩

theorem exists_basicOpen_le {V : (Sp R).Opens} (hV : (q : Sp R) ∈ V) :
    ∃ f : R, f ∉ q.asIdeal ∧ PrimeSpectrum.basicOpen f ≤ V := by
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le' hV
  exact ⟨f, hf, hle⟩

set_option backward.isDefEq.respectTransparency false in

theorem spMap_eq_fromSpecStalk (q : PrimeSpectrum R) :
    Spec.map (Spec.stalkIso (CommRingCat.of R) (q : Sp R)).hom ≫ (Sp R).fromSpecStalk (q : Sp R) =
      spMap (algebraMap R (Localization.AtPrime q.asIdeal)) := by
  have e : (Sp R).fromSpecStalk (q : Sp R) = Spec.map (Spec.stalkIso (CommRingCat.of R) (q : Sp R)).inv ≫
      spMap (algebraMap R (Localization.AtPrime q.asIdeal)) := by
    refine (Spec.fromSpecStalk_eq (CommRingCat.of R) (q : Sp R)).trans ?_
    rw [spMap, ← Spec.map_comp]
    exact congrArg Spec.map (Spec.algebraMap_stalkIso_inv (R := CommRingCat.of R) (x := q)).symm
  refine (congrArg (Spec.map (Spec.stalkIso (CommRingCat.of R) (q : Sp R)).hom ≫ ·) e).trans ?_
  rw [← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in

theorem exists_isAffineOpen_preimage_basicOpen_of_stalk {x : Sp R} {p' : X' ⟶ Spec ((Sp R).presheaf.stalk x)}
    (H' : IsPullback φ p' p ((Sp R).fromSpecStalk x)) [QuasiCompact p] [QuasiSeparated p] [IsAffine X'] :
    ∃ f : R, x ∈ (PrimeSpectrum.basicOpen f : (Sp R).Opens) ∧ IsAffineOpen (p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit H'
  have (V : StalkLimit.AffNhd x) : CompactSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have (V : StalkLimit.AffNhd x) : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have : IsAffine (StalkLimit.cone H').pt := ‹IsAffine X'›
  obtain ⟨V, hV⟩ := Scheme.exists_isAffine_of_isLimit _ _ hc
  have : IsAffine (pullback p V.1.ι) := hV
  have h₁ : IsAffineOpen (p ⁻¹ᵁ V.1) := IsAffine.of_isIso (pullbackRestrictIsoRestrict p V.1).inv
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le' V.2.1
  refine ⟨f, hf, ?_⟩
  have h₂ := GlobalTheory.AmpleSpread.isAffineOpen_inf_preimage_basicOpen p h₁ f
  rwa [inf_eq_right.2 (p.preimage_mono hle)] at h₂

theorem exists_isAffineOpen_preimage_basicOpen
    (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) [QuasiCompact p]
    [QuasiSeparated p] [IsAffine X'] : ∃ f : R, f ∉ q.asIdeal ∧ IsAffineOpen (p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  have h₀ : IsPullback (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))
      (Spec.map (Spec.stalkIso (CommRingCat.of R) (q : Sp R)).hom) (𝟙 _) ((Sp R).fromSpecStalk (q : Sp R)) :=
    IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans (spMap_eq_fromSpecStalk q).symm⟩
  have H' := H.paste_vert h₀
  rw [Category.comp_id] at H'
  obtain ⟨f, hf, h⟩ := exists_isAffineOpen_preimage_basicOpen_of_stalk H'
  exact ⟨f, hf, h⟩

theorem exists_preimage_basicOpen_le
    (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) [UniversallyClosed p]
    {U : X.Opens} (hU : φ ⁻¹ᵁ U = ⊤) : ∃ f : R, f ∉ q.asIdeal ∧ p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ U := by
  have hc : IsClosed (p '' (U : Set X)ᶜ) := p.isClosedMap _ U.isOpen.isClosed_compl
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le (q := q) (V := ⟨_, hc.isOpen_compl⟩) (by
    rintro ⟨x, hx, e⟩
    have hy : spMap (algebraMap R (Localization.AtPrime q.asIdeal))
        (IsLocalRing.closedPoint (Localization.AtPrime q.asIdeal)) = q :=
      PrimeSpectrum.ext (Localization.AtPrime.under_maximalIdeal (I := q.asIdeal))
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x _ (e.trans hy.symm)
    exact hx (hU.ge (Set.mem_univ z)))
  exact ⟨f, hf, fun x hx => by_contra fun h => hle hx ⟨x, h, rfl⟩⟩

theorem exists_cover (H : IsPullback φ π p (spMap (algebraMap R (Localization.AtPrime q.asIdeal)))) [IsProper p]
    {L : LB X} (hL : L.IsLB) (h : IsAmpleLB (L.pull φ)) :
    ∃ f : R, f ∉ q.asIdeal ∧ ∃ n, 1 ≤ n ∧ ∃ (N : ℕ) (θ : Fin (N + 1) → (lbPow L n).Sec),
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
  have aff : ∀ i, ∃ g : R, g ∉ q.asIdeal ∧
      IsAffineOpen (Out.nonzeroLocus (θ i) ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen g) := fun i => by
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
  have hm : f₀ * ∏ i, g i ∈ q.asIdeal.primeCompl :=
    q.asIdeal.primeCompl.mul_mem hf₀ (Submonoid.prod_mem _ fun i _ => hg i)
  refine ⟨f₀ * ∏ i, g i, hm, n, hn, N, θ,
    (p.preimage_mono (PrimeSpectrum.basicOpen_mul_le_left _ _)).trans h₀, fun i => ?_⟩
  have h₁ := GlobalTheory.AmpleSpread.isAffineOpen_inf_preimage_basicOpen p (hga i) (f₀ * ∏ i, g i)
  have hle : PrimeSpectrum.basicOpen (f₀ * ∏ i, g i) ≤ PrimeSpectrum.basicOpen (g i) := by
    rw [← Finset.mul_prod_erase _ g (Finset.mem_univ i), mul_left_comm]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  rwa [inf_assoc, inf_eq_right.2 (p.preimage_mono hle)] at h₁

end GlobalTheory.AmpleSpreadAt

namespace GlobalTheory.AmpleSpreadAt

theorem relAmple_spread_at : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (q : PrimeSpectrum R) (A : Over (Sp R)) (M : LB A.left), IsProper A.hom → M.IsLB → ∀ (B : Over (Sp (Localization.AtPrime q.asIdeal))) (φ : B.left ⟶ A.left) (N : LB B.left), IsPullback φ B.hom A.hom (spMap (algebraMap R (Localization.AtPrime q.asIdeal))) → N.IsLB → LBIso N (M.pull φ) → Out.RelAmple B N → ∃ (U : (Sp R).Opens) (_ : q ∈ U), Out.RelAmple (Over.mk (A.hom ∣_ U)) (M.pull (A.hom ⁻¹ᵁ U).ι) := by
  intro R _ _ q A M _ hM B φ N H hN hNM h
  have h₁ : IsAmpleLB (M.pull φ) :=
    (isAmpleLB_of_relAmple_of_isAffine B hN h).of_lbIso (LB.isLB_pull hM φ) hNM.symm
  obtain ⟨f, hf, n, hn, N', θ, hc, ha⟩ := exists_cover H hM h₁
  let U : (Sp R).Opens := PrimeSpectrum.basicOpen f
  refine ⟨U, hf, ?_⟩
  have hb : (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f) = U :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) f
  have hU : IsAffineOpen U :=
    by have := (isAffineOpen_top (Sp R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f); rwa [hb] at this
  have : IsAffine U.toScheme := hU
  have : IsProper (Over.mk (A.hom ∣_ U)).hom :=
    inferInstanceAs (IsProper (A.hom ∣_ _))
  let ψ := (A.hom ⁻¹ᵁ U).ι
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (isPullback_morphismRestrict A.hom U) inferInstance
  refine (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2
    (isAmpleLB_of_cover (LB.isLB_pull hM _) hn (fun i => secPowPull (θ i) ψ) (top_le_iff.1 fun z _ => ?_) fun i => ?_)
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc z.2)
    exact Opens.mem_iSup.2 ⟨i, (nonzeroLocus_secPowPull (θ i) ψ).ge hi⟩
  · have e : ψ ⁻¹ᵁ (Out.nonzeroLocus (θ i) ⊓ A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f) =
        Out.nonzeroLocus (secPowPull (θ i) ψ) :=
      (le_antisymm (fun z hz => hz.1) fun z hz => ⟨hz, z.2⟩).trans (nonzeroLocus_secPowPull (θ i) ψ).symm
    exact e ▸ (ha i).preimage ψ

end GlobalTheory.AmpleSpreadAt
