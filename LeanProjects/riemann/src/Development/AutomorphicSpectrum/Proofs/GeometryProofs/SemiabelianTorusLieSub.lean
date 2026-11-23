import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EigLat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCocharLie
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinear
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFunctorialMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtends
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianHomLieExtendsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusEmbeddingLieInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCocharacterLieModelStatement
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueHomExtensionSemiAbelian
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (torusFst ringHom_ext_ZU)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TsOk

theorem lifts_cochar {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] (f : S' ⟶ S) {R R' : Type} [CommRing R]
    [CommRing R'] (d : R →+* R') (x : Sp R ⟶ S) (x' : Sp R' ⟶ S') (hx : x' ≫ f = spMap d ≫ x)
    (MT : LieModel (splitTorus S X) x (X →+ R)) (hMT : IsCocharLie MT)
    (MT' : LieModel (splitTorus S' X) x' (X →+ R')) (hMT' : IsCocharLie MT') (δ : X →+ R) :
    MT.Lifts d ((GlobalTheory.Diag.baseChangeIso f X).inv.left ≫ pullback.fst (splitTorus S X).hom f) δ
      (MT'.pt (d.toAddMonoidHom.comp δ)) := by
  unfold LieModel.Lifts
  apply (GlobalTheory.Diag.isPullback_torusFst S X).hom_ext
  · have e1 : ((GlobalTheory.Diag.baseChangeIso f X).inv.left ≫ pullback.fst (splitTorus S X).hom f) ≫ torusFst S X =
        torusFst S' X := by
      rw [Category.assoc, ← GlobalTheory.Diag.baseChangeIso_hom_torusFst, ← Category.assoc, ← Over.comp_left,
        Iso.inv_hom_id, Over.id_left, Category.id_comp]
    rw [Category.assoc, e1, Category.assoc]
    have hp := Spec.map_preimage ((MT'.pt (d.toAddMonoidHom.comp δ)).left ≫
      pullback.fst (splitTorusAff ZU X).hom (toZ S'))
    have hq := Spec.map_preimage ((MT.pt δ).left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ S))
    have h1 := hMT' (d.toAddMonoidHom.comp δ)
    have h2 := hMT δ
    unfold charVal at h1 h2
    show _ ≫ pullback.fst _ _ = _ ≫ _ ≫ pullback.fst _ _
    refine hp.symm.trans (Eq.trans ?_ (congrArg (fun z => spMap (dualMap d) ≫ z) hq))
    rw [spMap, ← Spec.map_comp]
    congr 1
    refine CommRingCat.hom_ext (ringHom_ext_ZU fun χ => ?_)
    rw [h1 χ]
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [h2 χ]
    ext <;> simp
  · rw [Category.assoc, (GlobalTheory.Diag.isGrpPullback X f).1.w, Category.assoc, ← Category.assoc _ _ f, Over.w]
    have := LieTangent.spec_dual_alg d
    simp only [Over.mk_hom, Category.assoc]
    rw [hx, Over.w]
    simp only [Over.mk_hom]
    rw [← Category.assoc, ← Category.assoc (spMap (dualMap d))]
    exact congrArg (· ≫ x) this.symm

theorem dvd_of_forall_maximal {O : Type} [CommRing O] (a b : O)
    (H : ∀ P : Ideal O, P.IsMaximal → ∃ s n : O, s ∉ P ∧ a * n = s * b) : a ∣ b := by
  let I : Ideal O :=
    { carrier := {s | a ∣ s * b}
      add_mem' := fun {x y} hx hy => by
        show a ∣ (x + y) * b
        rw [add_mul]
        exact dvd_add hx hy
      zero_mem' := by
        show a ∣ 0 * b
        simp
      smul_mem' := fun c x hx => by
        show a ∣ (c • x) * b
        rw [smul_eq_mul, _root_.mul_assoc]
        exact Dvd.dvd.mul_left hx c }
  by_cases hI : I = ⊤
  · have h1 : (1 : O) ∈ I := hI ▸ Submodule.mem_top
    have h2 : a ∣ 1 * b := h1
    rwa [_root_.one_mul] at h2
  · obtain ⟨P, hP, hIP⟩ := I.exists_le_maximal hI
    obtain ⟨s, n, hs, e⟩ := H P hP
    exact absurd (hIP (show s ∈ I from ⟨n, e.symm⟩)) hs

theorem exists_local_quot {O T K : Type} [CommRing O] [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [Field K] [Algebra T K] [IsFractionRing T K] (a : O →+* T) (G : Over (Sp O)) [GrpObj G]
    (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left) (hG : IsSemiAbelian G)
    (h : IsGrpPullback GK G (spMap ((algebraMap T K).comp a)) φ)
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i : splitTorus (Sp K) X ⟶ GK) [IsMonHom i] [Mono i]
    (MT : LieModel (splitTorus (Sp K) X) (𝟙 _) (X →+ K)) (hMT : IsCocharLie MT)
    {E : Type} [AddCommGroup E] [Module O E] (M : LieModel G (𝟙 _) E)
    (e : E) (δ : X →+ O)
    (he : M.Lifts ((algebraMap T K).comp a) φ e
      (MT.pt (((algebraMap T K).comp a).toAddMonoidHom.comp δ) ≫ i))
    (a₀ : O) (ha₀ : a a₀ ≠ 0) (y : E) (hy : a₀ • y = e) :
    ∃ δT : X →+ T, ∀ χ, a a₀ * δT χ = a (δ χ) := by
  have := hG.comm
  have := hG.separated
  let y₀ : Sp T ⟶ Sp O := spMap a
  let g : Sp K ⟶ Sp T := spMap (algebraMap T K)
  have hgy : g ≫ y₀ = spMap ((algebraMap T K).comp a) := by
    simp only [g, y₀, spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let H := (Over.pullback y₀).obj G
  have hH : IsGrpPullback H G y₀ (pullback.fst G.hom y₀) := isGrpPullback_pullback G y₀
  have hHs : IsSemiAbelian H := IsSemiAbelian.pullback y₀ G hG
  have := hHs.comm
  have := hHs.smooth
  have := hHs.separated
  have hA := ((isGrpPullback_pullback H g).comp hH).congr hgy rfl
  obtain ⟨α, hαm, hα⟩ := grpPullback_iso h hA
  let TT := splitTorus (Sp T) X
  have hTb := GlobalTheory.Diag.isGrpPullback X g
  let β := GlobalTheory.Diag.baseChangeIso g X
  obtain ⟨F, ⟨hFm, hF⟩, -⟩ := GlobalTheory.existsUnique_hom_extension_semiAbelian T K TT H
    (GlobalTheory.Diag.isSemiAbelian _ X) hHs (β.hom ≫ i ≫ α.hom) inferInstance
  let φT : (splitTorus (Sp K) X).left ⟶ TT.left := β.inv.left ≫ pullback.fst TT.hom g
  let φH : GK.left ⟶ H.left := α.hom.left ≫ pullback.fst H.hom g
  have hφH : φH ≫ pullback.fst G.hom y₀ = φ := by
    simpa only [φH, Category.assoc] using hα
  have hGH : IsGrpPullback GK H g φH :=
    ((isGrpPullback_of_iso α).comp (isGrpPullback_pullback H g)).congr (Category.id_comp _) rfl
  have hC : φT ≫ F.left = i.left ≫ φH := by
    have hpull : ((Over.pullback g).map F).left ≫ pullback.fst H.hom g = pullback.fst TT.hom g ≫ F.left :=
      pullback.lift_fst _ _ _
    have hl : ((Over.pullback g).map F).left = β.hom.left ≫ i.left ≫ α.hom.left := by
      rw [hF]; rfl
    have hb : β.inv.left ≫ β.hom.left = 𝟙 _ := by
      rw [← Over.comp_left, β.inv_hom_id, Over.id_left]
    simp only [φT, φH, Category.assoc]
    rw [← hpull, hl]
    simp only [Category.assoc]
    rw [reassoc_of% hb]
  have hgen : ∀ (A : Type) [CommRing A] (g' : K →+* A)
      (t : Over.mk (spMap g' ≫ spMap (algebraMap T K) ≫ 𝟙 (Sp T)) ⟶ TT), t ≫ F = 1 → t = 1 := by
    intro A _ g' t ht
    let W : Over (Sp K) := Over.mk (spMap g')
    have hg : W.hom ≫ g = spMap g' ≫ spMap (algebraMap T K) ≫ 𝟙 (Sp T) := by
      simp [W, g]
    let P₁ := LiePull.pts hTb hg
    let P₂ := LiePull.pts hGH hg
    have h₀ : P₁ (P₁.symm t) = t := P₁.apply_symm_apply t
    have h₁ : P₂ (P₁.symm t ≫ i) = t ≫ F := by
      apply Over.OverMorphism.ext
      have e₁ : (P₁.symm t).left ≫ φT = t.left := congrArg (fun z => z.left) h₀
      show ((P₁.symm t).left ≫ i.left) ≫ φH = t.left ≫ F.left
      rw [Category.assoc, ← hC, ← Category.assoc, e₁]
    have h₂ : P₁.symm t ≫ i = 1 := P₂.injective (by rw [h₁, ht, map_one])
    have h₃ : P₁.symm t = 1 := (cancel_mono i).1 (by rw [h₂, MonObj.one_comp])
    rw [← h₀, h₃, map_one]
  obtain ⟨ET, t1, t2, ⟨L⟩⟩ := lieModel_exists (Sp O) G T (spMap a ≫ 𝟙 _)
  have gen : ∀ (z : Sp T ⟶ Sp O), spMap a ≫ 𝟙 (Sp O) = z →
      ∃ N' : LieModel G z ET, ∀ x, (N'.pt x).left = (L.pt x).left := by
    rintro z rfl
    exact ⟨L, fun _ => rfl⟩
  obtain ⟨L', hL'⟩ := gen (𝟙 (Sp T) ≫ y₀) (by simp [y₀])
  obtain ⟨MH, hMH⟩ := (LiePull.lieModel_pullback _ _ G H y₀ _ hH T (𝟙 _) ET).1 L'
  obtain ⟨jT, hjT, -⟩ := LieBaseChange.existsUnique_semilinear_lifts (Sp O) G O T a (𝟙 _) E ET M L
  obtain ⟨MTT, hMTT⟩ := GlobalTheory.T.exists_cocharacter_lie_model (Sp T) X T (𝟙 _)
  obtain ⟨A, hAd, -⟩ := lieModel_exists_unique_diff (Sp T) TT H T (𝟙 _) (X →+ T) ET MTT MH F
  obtain ⟨hinj, hsat⟩ := GlobalTheory.T.torus_embedding_lie_injective T K (Sp T) (𝟙 _) H X F hgen MTT hMTT ET MH A hAd
  let δa : X →+ T := a.toAddMonoidHom.comp δ
  let v := MT.pt (((algebraMap T K).comp a).toAddMonoidHom.comp δ)
  have e₁ : v.left ≫ φT = spMap (dualMap (algebraMap T K)) ≫ (MTT.pt δa).left :=
    lifts_cochar g (algebraMap T K) (𝟙 _) (𝟙 _) (by simp [g]) MTT hMTT MT hMT δa
  have hright : spMap (dualMap (algebraMap T K)) ≫ (MTT.pt δa ≫ F).left ≫ pullback.fst G.hom y₀ =
      (v ≫ i).left ≫ φ := by
    rw [Over.comp_left, Category.assoc, ← Category.assoc (spMap _), ← e₁, Over.comp_left]
    simp only [Category.assoc]
    rw [reassoc_of% hC, hφH]
  have hleft : spMap (dualMap (algebraMap T K)) ≫ (MH.pt (jT e)).left ≫ pullback.fst G.hom y₀ =
      (v ≫ i).left ≫ φ := by
    rw [hMH, hL', LieHomOk.lifts_id _ _ _ _ (hjT e), ← Category.assoc,
      ← LieHomOk.spMap_dualMap_comp]
    exact he.symm
  have hw : ∀ q : epsAt (𝟙 (Sp T)) ⟶ H,
      (q.left ≫ pullback.fst G.hom y₀) ≫ G.hom = (epsAt (𝟙 (Sp T))).hom ≫ y₀ := fun q => by
    rw [Category.assoc, hH.1.w, ← Category.assoc, Over.w]
  have key : jT e = A δa := by
    apply MH.inj
    rw [hAd]
    apply Over.OverMorphism.ext
    apply hH.1.hom_ext
    · exact LieHomOk.ext_of_spMap_injective (dualMap (algebraMap T K))
        (LieTangent.dualMap_injective (IsFractionRing.injective T K)) G.hom _ _
        ((hw _).trans (hw _).symm) (hleft.trans hright.symm)
    · exact (Over.w _).trans (Over.w _).symm
  have hz : a a₀ • jT y = A δa := by
    rw [← key, ← hy, map_smulₛₗ]
  obtain ⟨δT, hδT⟩ := hsat (a a₀) (jT y) ha₀ (hz ▸ ⟨δa, rfl⟩)
  refine ⟨δT, fun χ => ?_⟩
  have e₃ : a a₀ • δT = δa := hinj (by rw [map_smul, hδT, hz])
  exact DFunLike.congr_fun e₃ χ

theorem exists_quot_at {O K : Type} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
    (hO : ¬ IsField O) (G : Over (Sp O)) [GrpObj G] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left)
    (hG : IsSemiAbelian G) (h : IsGrpPullback GK G (spMap (algebraMap O K)) φ)
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i : splitTorus (Sp K) X ⟶ GK) [IsMonHom i] [Mono i]
    (MT : LieModel (splitTorus (Sp K) X) (𝟙 _) (X →+ K)) (hMT : IsCocharLie MT)
    {E : Type} [AddCommGroup E] [Module O E] (M : LieModel G (𝟙 _) E) (e : E) (δ : X →+ O)
    (he : M.Lifts (algebraMap O K) φ e (MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ i))
    (a : O) (ha : a ≠ 0) (y : E) (hy : a • y = e) (P : Ideal O) (hPm : P.IsMaximal) (χ : X) :
    ∃ s n : O, s ∉ P ∧ a * n = s * δ χ := by
  have hP : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hPm hO
  have hle : P.primeCompl ≤ nonZeroDivisors O := P.primeCompl_le_nonZeroDivisors
  let c : Localization.AtPrime P →+* K := IsLocalization.lift (M := P.primeCompl) (g := algebraMap O K)
    fun s => IsUnit.mk0 _ fun h0 => nonZeroDivisors.ne_zero (hle s.2)
      (IsFractionRing.injective O K (h0.trans (map_zero _).symm))
  have hc : c.comp (algebraMap O (Localization.AtPrime P)) = algebraMap O K := IsLocalization.lift_comp _
  letI : Algebra (Localization.AtPrime P) K := c.toAlgebra
  have hcK : (algebraMap (Localization.AtPrime P) K).comp (algebraMap O (Localization.AtPrime P)) =
      algebraMap O K := hc
  haveI : IsScalarTower O (Localization.AtPrime P) K := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : IsFractionRing (Localization.AtPrime P) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ K
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O hP _
  have hinj : Function.Injective (algebraMap O (Localization.AtPrime P)) :=
    IsLocalization.injective _ hle
  have h' : IsGrpPullback GK G (spMap ((algebraMap (Localization.AtPrime P) K).comp
      (algebraMap O (Localization.AtPrime P)))) φ := by rw [hcK]; exact h
  have he' : M.Lifts ((algebraMap (Localization.AtPrime P) K).comp (algebraMap O (Localization.AtPrime P))) φ e
      (MT.pt (((algebraMap (Localization.AtPrime P) K).comp
        (algebraMap O (Localization.AtPrime P))).toAddMonoidHom.comp δ) ≫ i) := by rw [hcK]; exact he
  obtain ⟨δT, hδT⟩ := exists_local_quot (algebraMap O (Localization.AtPrime P)) G GK φ hG h' X i MT hMT M e δ he'
    a (fun h0 => ha (hinj (h0.trans (map_zero _).symm))) y hy
  obtain ⟨⟨n, s⟩, hs⟩ := IsLocalization.surj P.primeCompl (δT χ)
  refine ⟨s, n, s.2, hinj ?_⟩
  rw [map_mul, map_mul, ← hs, ← _root_.mul_assoc, hδT χ, mul_comm]

theorem saturated : ∀ (O K : Type) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (G : Over (Sp O)) [GrpObj G] (GK : Over (Sp K)) [GrpObj GK] (φ : GK.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback GK G (spMap (algebraMap O K)) φ → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp K) X ⟶ GK) [IsMonHom i] [Mono i] (MT : LieModel (splitTorus (Sp K) X) (𝟙 _) (X →+ K)), IsCocharLie MT → ∀ (E : Type) [AddCommGroup E] [Module O E] (M : LieModel G (𝟙 _) E), ∃ io : (X →+ O) →ₗ[O] E, (∀ δ, M.Lifts (algebraMap O K) φ (io δ) (MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ i)) ∧ Function.Injective io ∧ ∀ (a : O) (y : E), a ≠ 0 → a • y ∈ LinearMap.range io → y ∈ LinearMap.range io := by
  intro O K _ _ _ _ _ G _ GK _ φ hG h X _ _ _ i _ _ MT hMT E _ _ M
  have := hG.comm
  have := hG.separated
  obtain ⟨MTO, hMTO⟩ := GlobalTheory.T.exists_cocharacter_lie_model (Sp O) X O (𝟙 _)
  have hT := GlobalTheory.Diag.isGrpPullback X (spMap (algebraMap O K))
  obtain ⟨io, hio⟩ := GlobalTheory.T.semiabelian_hom_lie_extends O K (splitTorus (Sp O) X) G (splitTorus (Sp K) X) GK _ φ
    (GlobalTheory.Diag.isSemiAbelian _ X) hG hT h i (X →+ O) E MTO M
  have hL : ∀ δ, M.Lifts (algebraMap O K) φ (io δ)
      (MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ i) := fun δ =>
    hio δ _ (lifts_cochar (spMap (algebraMap O K)) (algebraMap O K) (𝟙 _) (𝟙 _) (by simp) MTO hMTO MT hMT δ)
  have hcinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hinj : Function.Injective io := by
    intro δ δ' e
    have e₁ : MT.pt ((algebraMap O K).toAddMonoidHom.comp δ) ≫ i =
        MT.pt ((algebraMap O K).toAddMonoidHom.comp δ') ≫ i := by
      apply Over.OverMorphism.ext
      apply h.1.hom_ext
      · have l₁ := hL δ
        have l₂ := hL δ'
        unfold LieModel.Lifts at l₁ l₂
        rw [l₁, l₂, e]
      · exact (Over.w _).trans (Over.w _).symm
    have e₂ := MT.inj ((cancel_mono i).1 e₁)
    ext χ
    exact hcinj (DFunLike.congr_fun e₂ χ)
  obtain ⟨EK, i1, i2, MK, N, j, -, hj⟩ := LieHomOk.exists_generic_model (algebraMap O K) G GK φ h M
  have hjj : ∀ a, spMap (dualMap (algebraMap O K)) ≫ (M.pt a).left = (N.pt (j a)).left :=
    fun a => (LieHomOk.lifts_id _ _ _ _ (hj a)).symm
  have hjinj : Function.Injective j := fun a b hab => M.inj (Over.OverMorphism.ext
    (LieHomOk.ext_of_spMap_injective (dualMap (algebraMap O K)) (LieTangent.dualMap_injective hcinj) G.hom _ _
      ((Over.w (M.pt a)).trans (Over.w (M.pt b)).symm) (by rw [hjj, hjj, hab])))
  have htf : ∀ (a : O) (z : E), a ≠ 0 → a • z = 0 → z = 0 := by
    intro a z ha hz
    have h₁ := congrArg j hz
    rw [map_smulₛₗ, map_zero] at h₁
    have h₂ : algebraMap O K a ≠ 0 := fun h0 => ha (hcinj (h0.trans (map_zero _).symm))
    exact hjinj ((smul_eq_zero.1 h₁).resolve_left h₂ |>.trans (map_zero j).symm)
  refine ⟨io, hL, hinj, fun a y ha hy => ?_⟩
  obtain ⟨δ, hδ⟩ := hy
  by_cases hO : IsField O
  · obtain ⟨b, hb⟩ := hO.mul_inv_cancel ha
    exact ⟨b • δ, by rw [map_smul, hδ, smul_smul, mul_comm, hb, one_smul]⟩
  · have hdiv : ∀ χ, ∃ r : O, δ χ = a * r := fun χ => dvd_of_forall_maximal a (δ χ) fun P hP =>
      exists_quot_at hO G GK φ hG h X i MT hMT M (io δ) δ (hL δ) a ha y hδ.symm P hP χ
    choose r hr using hdiv
    let δ' : X →+ O := AddMonoidHom.mk' r fun p q =>
      mul_left_cancel₀ ha (by rw [_root_.mul_add, ← hr, ← hr, ← hr, map_add])
    have e₁ : a • δ' = δ := by
      ext χ
      exact (hr χ).symm
    refine ⟨δ', sub_eq_zero.1 (htf a _ ha ?_)⟩
    rw [smul_sub, ← map_smul, e₁, hδ, sub_self]

end GlobalTheory.CompanionTheory.Ar.TsOk
