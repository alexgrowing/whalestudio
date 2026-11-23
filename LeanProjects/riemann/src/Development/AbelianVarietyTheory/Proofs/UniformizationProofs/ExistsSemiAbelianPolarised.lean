import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TopLePtHomPreimageSmoothOpenIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPointEquivSmoothLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LiftMulHomPullbackFst
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyTorusExtensionSplitTorus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemCoordOpenTwoIffNotMemRangeZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullbackSectionNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecGeneratesSpecialFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MultiplicativeReduction

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.WeierstrassCurve

theorem exists_sec_of_iso {X X' : Scheme.{0}} {L : LB X} {N : LB X'} (hL : L.IsLB) (hN : N.IsLB) (F : X' ⟶ X)
    (H : LBIso (L.pull F) N) (θ : H0 L 1) :
    ∃ s : N.Sec, ∀ y : X', y ∈ nonzeroLocus s ↔ F y ∈ nonzeroLocus θ := by
  have hP := linComb_isLB L hL (K := Fin 1) (fun _ => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))
  have mem : ∀ (i : L.ι) (y : X), y ∈ L.U i → y ∈ LB.wchart L (fun _ : Fin 1 => 𝟙 X) (fun _ => i) :=
    fun i y hy => Set.mem_iInter.2 fun _ => hy
  let a : ChartPull L (LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ))) (𝟙 X) :=
    { idx := fun i _ => i
      le := fun i y hy => mem i y hy
      g := fun y i j hi hj => Eq.symm ((gm_linComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => ((1 : ℕ) : ℤ)) (𝟙 X) y _ _
        (mem i y hi) (mem j y hj)).trans (by rw [Fintype.prod_unique, Nat.cast_one, zpow_one, Category.id_comp])) }
  have h₁ := LBIso.chartPull a (chartPullId _) ⟨_, idIso_isGen hP⟩
  have h₂ := LBIso.chartPull (Geo.Tor.chartPullPull _ F F rfl) (Geo.Tor.chartPullPull _ F F rfl) h₁
  obtain ⟨w, hw⟩ := LBIso.trans hN (pull_isLB hL F) (pull_isLB hP F) H.symm h₂
  obtain ⟨s', hs'⟩ := sec_pull_down ((isGen_iff w).1 hw) hP hN θ
  refine ⟨s', fun y => ?_⟩
  refine (mem_nonzeroLocus _ y).trans
    (Iff.trans ⟨fun ⟨k, hk, u⟩ => ?_, fun ⟨j, hj, u⟩ => ?_⟩ (mem_nonzeroLocus _ (F y)).symm)
  · obtain ⟨j, hj⟩ := exists_chart hP (F y)
    have e := hs' _ (𝟙 _) y j k hj hk
    rw [Category.id_comp, gs_stalkMap F y _ hj] at e
    exact ⟨j, hj, (isUnit_map_iff (F.stalkMap y).hom _).1 ((congrArg IsUnit e).mpr ((Units.isUnit _).mul u))⟩
  · obtain ⟨k, hk⟩ := exists_chart hN y
    have e := hs' _ (𝟙 _) y j k hj hk
    rw [Category.id_comp] at e
    exact ⟨k, hk, isUnit_of_mul_isUnit_right ((congrArg IsUnit ((gs_stalkMap F y _ hj _).symm.trans e)).mp (u.map _))⟩

theorem exists_iso_schemeOver {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (W : WeierstrassCurve R)
    [(W.map f).IsElliptic] (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : R →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P) :
    ∃ φ : (Over.pullback (Spec.map (CommRingCat.ofHom f))).obj (Over.mk (U.ι ≫ toSpec W)) ≅ schemeOver (W.map f),
      φ.hom.left ≫ mapHom W f rfl = pullback.fst _ _ ≫ U.ι := by
  have hr : Set.range (mapHom W f rfl) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    let t := (scheme (W.map f)).fromSpecResidueField y
    obtain ⟨ρ, hρ⟩ := Spec.map_surjective (t ≫ toSpec (W.map f))
    obtain ⟨P, h, e⟩ := exists_eq_ptHom (W.map f) (A := (scheme (W.map f)).residueField y) ρ.hom t hρ.symm
    have : ((W.map f).map ρ.hom).IsElliptic := inferInstance
    have h₁ := (hU _ (ρ.hom.comp f) P (h.comp_of_map_eq rfl)).2 h.nonsingular
    rw [← ptHom_mapHom W f rfl ρ.hom P h, ← e] at h₁
    have h₂ := h₁ (Set.mem_univ (IsLocalRing.closedPoint _))
    change mapHom W f rfl (t _) ∈ U at h₂
    exact (congrArg (fun q => mapHom W f rfl q ∈ U) (Scheme.fromSpecResidueField_apply y _)).mp h₂
  have hm := IsOpenImmersion.lift_fac U.ι (mapHom W f rfl) hr
  have hp : IsPullback (IsOpenImmersion.lift U.ι (mapHom W f rfl) hr) (toSpec (W.map f)) (U.ι ≫ toSpec W)
      (Spec.map (CommRingCat.ofHom f)) := by
    have h₀ : IsPullback (IsOpenImmersion.lift U.ι (mapHom W f rfl) hr) (𝟙 _) U.ι (mapHom W f rfl) :=
      IsPullback.of_vert_isIso_mono ⟨hm.trans (Category.id_comp _).symm⟩
    simpa using h₀.paste_vert (isPullback_mapHom W f rfl)
  refine ⟨Over.isoMk hp.isoPullback.symm hp.isoPullback_inv_snd, ?_⟩
  change hp.isoPullback.inv ≫ _ = _
  exact ((congrArg (· ≫ U.ι) hp.isoPullback_inv_fst).symm.trans
    ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hm))).symm

theorem isUnimodularSol_twoPt {R A : Type} [CommRing R] [CommRing A] (a : R) (ρ : R →+* A) :
    IsUnimodularSol ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve R).map ρ) ![0, 0, 1] :=
  isUnimodularSol_some (by simp [WeierstrassCurve.Affine.equation_iff, WeierstrassCurve.map])

theorem nonsingular_twoPt {R k : Type} [CommRing R] [Field k] (a : R) (ρ : R →+* k) :
    ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve R).map ρ).toProjective.Nonsingular ![0, 0, 1] ↔ ρ a ≠ 0 := by
  rw [WeierstrassCurve.Projective.nonsingular_iff, WeierstrassCurve.Projective.equation_iff]
  simp [WeierstrassCurve.map]

theorem add_twoPt {R k : Type} [CommRing R] [Field k] (a : R) (ρ : R →+* k) :
    ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve R).map ρ).toProjective.add ![0, 0, 1] ![0, 0, 1] 0 = 0 ∧
      ((⟨1, 0, 0, a, 0⟩ : WeierstrassCurve R).map ρ).toProjective.add ![0, 0, 1] ![0, 0, 1] 2 = 0 := by
  rw [WeierstrassCurve.Projective.add_self]
  constructor
  · simp [WeierstrassCurve.Projective.dblXYZ, WeierstrassCurve.Projective.dblX, WeierstrassCurve.map]
  · simp [WeierstrassCurve.Projective.dblXYZ, WeierstrassCurve.Projective.dblZ, WeierstrassCurve.Projective.negY,
      WeierstrassCurve.map]

theorem isElliptic_generic : ((⟨1, 0, 0, PowerSeries.X, 0⟩ : WeierstrassCurve (PowerSeries ℚ)).map
    (algebraMap _ (FractionRing (PowerSeries ℚ)))).IsElliptic := by
  refine ⟨?_⟩
  rw [WeierstrassCurve.map_Δ, isUnit_iff_ne_zero, map_ne_zero_iff _ (IsFractionRing.injective _ _)]
  have : (⟨1, 0, 0, PowerSeries.X, 0⟩ : WeierstrassCurve (PowerSeries ℚ)).Δ =
      PowerSeries.X ^ 2 * (1 - 64 * PowerSeries.X) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  rw [this]
  refine mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) fun h => ?_
  simpa using congrArg PowerSeries.constantCoeff h

theorem isClosed_twoPt {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {a : V}
    (ha : a ∈ IsLocalRing.maximalIdeal V) (W : WeierstrassCurve V) (hW : W = ⟨1, 0, 0, a, 0⟩) (U : (scheme W).Opens)
    (hU : ∀ (k : Type) [Field k] (ρ : V →+* k) (P : Fin 3 → k) (h : IsUnimodularSol (W.map ρ) P),
      ⊤ ≤ ptHom W ρ P h ⁻¹ᵁ U ↔ (W.map ρ).toProjective.Nonsingular P)
    (x : Spec (.of (FractionRing V)) ⟶ U.toScheme) (h : IsUnimodularSol (W.map (algebraMap V _)) ![0, 0, 1])
    (hx : x ≫ U.ι = ptHom W (algebraMap V _) ![0, 0, 1] h) : IsClosed (Set.range x) := by
  subst hW
  let σ := ptHom _ (RingHom.id V) ![0, 0, 1] (isUnimodularSol_twoPt a _)
  have hσ : ∀ (k : Type) [CommRing k] (ρ : V →+* k),
      Spec.map (CommRingCat.ofHom ρ) ≫ σ = ptHom _ ρ ![0, 0, 1] (isUnimodularSol_twoPt a _) := fun k _ ρ =>
    (SpecMap_ptHom _ _ _ _ ρ).trans (ptHom_congr _ _ _ _ (RingHom.comp_id ρ) (by ext i; fin_cases i <;> simp) _)
  have hs : σ ≫ toSpec _ = 𝟙 _ := (ptHom_toSpec ..).trans (Spec.map_id _)
  have : IsClosedImmersion (σ ≫ toSpec _) := by rw [hs]; infer_instance
  have : IsClosedImmersion σ := IsClosedImmersion.of_comp σ (toSpec _)
  have hx' : x ≫ U.ι = jK V ≫ σ := hx.trans (hσ _ _).symm
  have e : Set.range x = U.ι ⁻¹' Set.range σ := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      exact ⟨jK V z, (congrArg (fun q => q z) hx').symm⟩
    · rintro y ⟨p, hp⟩
      by_cases h0 : p.asIdeal = ⊥
      · have hj : jK V (IsLocalRing.closedPoint _) = p := by
          refine PrimeSpectrum.ext ?_
          rw [h0]
          change Ideal.comap (algebraMap V (FractionRing V)) (IsLocalRing.maximalIdeal _) = ⊥
          rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, ← RingHom.injective_iff_ker_eq_bot]
          exact IsFractionRing.injective _ _
        refine ⟨IsLocalRing.closedPoint _, U.ι.isOpenEmbedding.injective ?_⟩
        rw [← hp, ← hj]
        exact congrArg (fun q => q (IsLocalRing.closedPoint _)) hx'
      · exfalso
        have hm : p.asIdeal = IsLocalRing.maximalIdeal V :=
          IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime h0 p.isPrime)
        refine (nonsingular_twoPt a (IsLocalRing.residue V)).1 ((hU _ _ _ (isUnimodularSol_twoPt a _)).1 ?_)
          ((IsLocalRing.residue_eq_zero_iff a).2 ha)
        rw [← hσ]
        intro z _
        have hz : Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) z = p := by
          refine PrimeSpectrum.ext ?_
          rw [hm]
          change Ideal.comap (IsLocalRing.residue V) z.asIdeal = _
          have := z.isPrime
          rw [Ideal.eq_bot_of_prime z.asIdeal, ← RingHom.ker_eq_comap_bot, IsLocalRing.ker_residue]
        change σ (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) z) ∈ U
        rw [hz, hp]
        exact y.2
  rw [e]
  exact σ.isClosedEmbedding.isClosed_range.preimage U.ι.continuous

open GlobalTheory.PolTranslate in

theorem transl_mem_range_iff {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : 𝟙_ (Over S) ⟶ G} (hx : x * x = 1)
    (z : G.left) : (transl x).left z ∈ Set.range (η[G]).left ↔ z ∈ Set.range x.left := by
  have h₁ : (1 : 𝟙_ (Over S) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
  have e₁ : η[G] ≫ transl x = x := by
    rw [comp_transl, ← h₁, _root_.one_mul]; simp
  have e₂ : x ≫ transl x = η[G] := by
    rw [comp_transl, ← h₁, ← hx]; simp
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, ?_⟩
    have e := congrArg (fun q => q.left z) (transl_transl hx)
    exact (congrArg (fun q => q.left p) e₁).symm.trans ((congrArg (transl x).left hp).trans e)
  · rintro ⟨p, rfl⟩
    exact ⟨p, (congrArg (fun q => q.left p) e₂).symm⟩

theorem one_pullback_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) (G : Over S) [GrpObj G] :
    (η[(Over.pullback φ).obj G]).left ≫ pullback.fst G.hom φ = φ ≫ (η[G]).left := by
  rw [Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

open GlobalTheory.PolTranslate in

theorem exists_pol_twoTorsion (hL : Laws) {K : Type} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G] (φ : G ≅ schemeOver W)
    (hφ : (η[G]).left ≫ φ.hom.left = zero W) (x : 𝟙_ _ ⟶ G) (hx : x * x = 1) :
    ∃ (A : PolAV (Spec (CommRingCat.of K))) (e : G ≅ A.A) (θ : H0 A.L 1), IsMonHom e.hom ∧ A.g = 1 ∧
      ∀ z : G.left, e.hom.left z ∈ nonzeroLocus θ ↔ z ∉ Set.range x.left := by
  obtain ⟨A₀, e, θ, he, hg, hθ⟩ := exists_polAV_section_origin K W
  let e₀ : G ≅ A₀.A := φ ≪≫ e.symm
  have h₀ : e₀.hom ≫ e.hom = φ.hom := by simp [e₀]
  have hw : G.hom = e₀.hom.left ≫ A₀.A.hom := (Over.w e₀.hom).symm
  have : IsIso e₀.hom.left := ((Over.forget _).mapIso e₀).isIso_hom
  have : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  have hG : IsAbelianScheme G := by
    have := A₀.isAb.smooth
    have := A₀.isAb.proper
    have := A₀.isAb.geomConnected
    refine ⟨inferInstance, ?_, ?_, ?_⟩
    · rw [hw]; infer_instance
    · rw [hw]; infer_instance
    · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
        (IsPullback.of_horiz_isIso ⟨(Over.w e₀.hom).trans (Category.comp_id _).symm⟩) this
  have hη : η[G] ≫ e₀.hom = η[A₀.A] := by
    rw [← cancel_mono e.hom, Category.assoc, h₀]
    exact Over.OverMorphism.ext (hφ.trans he.symm)
  have := hL.rigidity _ G A₀.A hG A₀.isAb e₀.hom hη
  obtain ⟨A, e', θ', _, hg', hθ'⟩ := exists_translate K A₀ (x ≫ e₀.hom)
    (by rw [← MonObj.mul_comp, hx, MonObj.one_comp]) θ
  refine ⟨A, e₀ ≪≫ e'.symm, θ', inferInstanceAs (IsMonHom (e₀.hom ≫ e'.inv)), hg'.trans hg, fun z => ?_⟩
  have k : (e₀ ≪≫ e'.symm).hom ≫ (e'.hom * (toUnit _ ≫ x ≫ e₀.hom)) = transl x ≫ e₀.hom := by
    rw [MonObj.comp_mul, transl, MonObj.mul_comp]
    simp
  rw [hθ', ← transl_mem_range_iff hx]
  refine Iff.trans (iff_of_eq (congrArg (fun q => q.left z ∈ nonzeroLocus θ) k)) ?_
  refine (hθ _).trans (not_congr ?_)
  rw [← he]
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p, e₀.hom.left.isOpenEmbedding.injective ?_⟩
    exact (congrArg (fun q => q.left p) hη).trans (e.hom.left.isOpenEmbedding.injective hp)
  · rintro ⟨p, hp⟩
    exact ⟨p, congrArg e.hom.left ((congrArg (fun q => q.left p) hη).symm.trans (congrArg e₀.hom.left hp))⟩

theorem exists_semiAbelian_polarised : Laws → ∃ (G : Over (Spec (CommRingCat.of (PowerSeries ℚ)))) (_ : GrpObj G) (_ : IsCommMonObj G) (A : PolAV (Spec (CommRingCat.of (FractionRing (PowerSeries ℚ))))) (eA : (Over.pullback (jK (PowerSeries ℚ))).obj G ≅ A.A) (i : splitTorus (Spec (CommRingCat.of (IsLocalRing.ResidueField (PowerSeries ℚ)))) ℤ ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (IsLocalRing.residue (PowerSeries ℚ))))).obj G), IsSemiAbelian G ∧ IsMonHom eA.hom ∧ IsMonHom i.hom ∧ A.g = 1 ∧ ∃ (LG : RigLB G) (_c : CubicalStr G LG) (s : LB.Gen (LB.LinComb LG.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen ∧ LB.Gen.Corr LG.L _ _ _ _ (LB.pullGen LG.L _ _ s (eSec G)) (LB.oneGen LG.L) ∧ (∃ w : LB.Iso (A.L.pull eA.hom.left) (LG.L.pull (pullback.fst G.hom (jK (PowerSeries ℚ)))), w.IsGen) ∧ ∃ θ : H0 LG.L 1, ∀ x : G.left, G.hom x = IsLocalRing.closedPoint (PowerSeries ℚ) → x ∈ nonzeroLocus θ := by
  intro hL
  obtain ⟨W, hW⟩ : ∃ W : WeierstrassCurve (PowerSeries ℚ), W = ⟨1, 0, 0, PowerSeries.X, 0⟩ := ⟨_, rfl⟩
  obtain ⟨U, hU, hsm, hqc, hgi⟩ := exists_smoothLocus _ W
  have hs : Smooth (U.ι ≫ toSpec W) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨_, _, hη, hmul⟩ := GlobalTheory.exists_grpObj_smoothLocus _ W U hU hs hgi
  obtain ⟨hG, i, hi⟩ := isSemiAbelian_and_specialFibre W hW U hU hs hgi hqc hmul
  let f := algebraMap (PowerSeries ℚ) (FractionRing (PowerSeries ℚ))
  have : (W.map f).IsElliptic := hW ▸ isElliptic_generic
  obtain ⟨φ, hφ⟩ := exists_iso_schemeOver f W U hU
  let G := Over.mk (U.ι ≫ toSpec W)
  let j := pullback.fst G.hom (jK (PowerSeries ℚ))
  have hη' : (η[(Over.pullback (jK (PowerSeries ℚ))).obj G]).left ≫ j ≫ U.ι = jK _ ≫ zero W := by
    rw [← hη, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ U.ι) (one_pullback_fst _ G)
  have hP : IsUnimodularSol (W.map f) ![0, 0, 1] := hW ▸ isUnimodularSol_twoPt _ _
  have hX : f PowerSeries.X ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 PowerSeries.X_ne_zero
  have hPU := (hU _ f _ hP).2 (hW ▸ (nonsingular_twoPt _ f).2 hX)
  have hr : Set.range (ptHom W f _ hP) ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hPU (Set.mem_univ y)
  have ha := IsOpenImmersion.lift_fac U.ι (ptHom W f _ hP) hr
  have ha' : IsOpenImmersion.lift U.ι (ptHom W f _ hP) hr ≫ U.ι ≫ toSpec W = jK _ := by
    rw [← Category.assoc, ha, ptHom_toSpec]
  let a : Over.mk (jK (PowerSeries ℚ)) ⟶ G := Over.homMk _ ha'
  let x : 𝟙_ _ ⟶ (Over.pullback (jK (PowerSeries ℚ))).obj G :=
    Over.homMk (pullback.lift a.left (𝟙 _) (ha'.trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)
  have hxa : x.left ≫ j = a.left := pullback.lift_fst _ _ _
  have hx : x * x = 1 := by
    have h₁ : (1 : 𝟙_ _ ⟶ (Over.pullback (jK (PowerSeries ℚ))).obj G) = η[_] := by rw [Hom.one_def]; simp
    rw [h₁]
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have h₂ := SmoothLocusBaseChange.lift_mul_pullback_fst (jK (PowerSeries ℚ)) G x x (𝟙 _) a a
      (hxa.symm.trans (Category.id_comp _).symm) (hxa.symm.trans (Category.id_comp _).symm)
    obtain ⟨h, h₃⟩ := hmul _ f a a _ _ hP hP ha ha
    refine (cancel_mono U.ι).1 ?_
    refine Eq.trans ?_ (hη'.symm.trans (Category.assoc _ _ _).symm)
    refine (congrArg (· ≫ U.ι) (h₂.trans (Category.id_comp _))).symm.trans (h₃.trans ?_)
    rw [SpecMap_zero, ptHom_eq_ptHom_iff_minors]
    obtain ⟨h₄, h₅⟩ := add_twoPt PowerSeries.X f
    rw [← hW] at h₄ h₅
    intro m l
    fin_cases m <;> fin_cases l <;> simp [h₄, h₅]
  have hz : (η[(Over.pullback (jK (PowerSeries ℚ))).obj G]).left ≫ φ.hom.left = zero (W.map f) := by
    apply (isPullback_mapHom W f rfl).hom_ext
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hφ).trans (hη'.trans (zero_mapHom W f rfl).symm))
    · exact (Over.w (η[(Over.pullback (jK (PowerSeries ℚ))).obj G] ≫ φ.hom)).trans (zero_toSpec _).symm
  obtain ⟨A, eA, θ, heA, hg, hθ⟩ := exists_pol_twoTorsion hL (W.map f) _ φ hz x hx
  obtain ⟨LG, c, s, hs₁, hs₂, w, hw⟩ := PolExtension.exists_cubical_symmetric_extension hL _ G hG A eA heA
  refine ⟨G, inferInstance, inferInstance, A, eA, i, hG, heA, hi, hg, LG, c, s, hs₁, hs₂, ⟨w, hw⟩, ?_⟩
  obtain ⟨t, ht⟩ := exists_sec_of_iso A.isLB (pull_isLB LG.isLB j) eA.hom.left ⟨w, hw⟩ θ
  have ht' : ∀ z, z ∈ nonzeroLocus t ↔ z ∉ Set.range x.left := fun z => (ht z).trans (hθ z)
  refine exists_sec_generates_specialFibre _ G hG LG.L LG.isLB t
    ⟨(η[(Over.pullback (jK (PowerSeries ℚ))).obj G]).left (IsLocalRing.closedPoint _), (ht' _).2 ?_⟩ ?_
  · rintro ⟨p, hp⟩
    have h₁ : ptHom W f _ hP p ∈ coordOpen W 2 := (ptHom_preimage_coordOpen W f _ hP 2).ge
      (PrimeSpectrum.basicOpen_one.ge (Set.mem_univ p))
    have h₂ : ptHom W f _ hP p = zero W (jK _ (IsLocalRing.closedPoint _)) :=
      (congrArg (fun q => q p) ((congrArg (· ≫ U.ι) hxa).trans ha)).symm.trans
        ((congrArg (j ≫ U.ι) hp).trans (congrArg (fun q => q (IsLocalRing.closedPoint _)) hη'))
    rw [h₂] at h₁
    exact (zero_preimage_coordOpen_two W).le h₁
  · have e : j '' {z | z ∉ nonzeroLocus t} = Set.range a.left := by
      rw [← hxa]
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        obtain ⟨p, rfl⟩ := not_not.1 (mt (ht' z).2 hz)
        exact ⟨p, rfl⟩
      · rintro ⟨p, rfl⟩
        exact ⟨x.left p, fun h => (ht' _).1 h ⟨p, rfl⟩, rfl⟩
    refine e ▸ isClosed_twoPt (a := PowerSeries.X) ?_ W hW U hU a.left hP ha
    rw [PowerSeries.maximalIdeal_eq_span_X]
    exact Ideal.subset_span rfl

end GlobalTheory.MultiplicativeReduction
