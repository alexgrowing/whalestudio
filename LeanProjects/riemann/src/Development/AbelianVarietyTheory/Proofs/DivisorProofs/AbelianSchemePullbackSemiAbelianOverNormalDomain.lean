import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem link_of_normal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), (U₀ : Set M.Z).Nonempty → ∀ (O : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [IsIntegrallyClosed O] [Algebra O Ω] [IsFractionRing O Ω] (x : Sp O ⟶ M.Z) (u : S.R →+* O), spMap (algebraMap O Ω) ≫ x = M.pt → (algebraMap O Ω).comp u = S.R.val.toRingHom → ∃ gm : ((Over.pullback (spMap u)).obj ρ.P.A).left ⟶ FinalForm.G.left, Link FinalForm x (spMap u) ((Over.pullback (spMap u)).obj ρ.P.A) (pullback.fst ρ.P.A.hom (spMap u)) gm := by
  intro o Ω _ _ _ _ S ρ M U₀ EE FinalForm hU O _ _ _ _ _ _ x u hx hu

  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact M.top_le_preimage_pt hU (x := w) trivial
  let x₀ : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt hr
  have hx₀ : x₀ ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hxu : x₀ ≫ FinalForm.u₀ = spMap S.R.val.toRingHom := FinalForm.u₀_gen x₀ hx₀
  let j : Sp Ω ⟶ Sp O := spMap (algebraMap O Ω)
  have hju : j ≫ spMap u = spMap S.R.val.toRingHom := (spMap_comp u (algebraMap O Ω)).symm.trans (congrArg spMap hu)

  let Q := (Over.pullback FinalForm.u₀).obj ρ.P.A
  let A₀ := (Over.pullback M.pt).obj FinalForm.G
  let ν : pullback FinalForm.G.hom M.pt ⟶ pullback ρ.P.A.hom FinalForm.u₀ :=
    FinalForm.cart.1.lift (pullback.fst FinalForm.G.hom M.pt) (pullback.snd FinalForm.G.hom M.pt ≫ x₀)
             (by rw [pullback.condition, Category.assoc, hx₀])
  have hν₁ : ν ≫ FinalForm.φ = pullback.fst FinalForm.G.hom M.pt := FinalForm.cart.1.lift_fst _ _ _
  have hν₂ : ν ≫ Q.hom = pullback.snd FinalForm.G.hom M.pt ≫ x₀ := FinalForm.cart.1.lift_snd _ _ _
  have gη : IsGrpPullback A₀ FinalForm.G (x₀ ≫ U₀.ι) (ν ≫ FinalForm.φ) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx₀.symm hν₁.symm
  have gν : IsGrpPullback A₀ Q x₀ ν := FinalForm.cart.cancel gη hν₂
  have gψ : IsGrpPullback A₀ ρ.P.A (j ≫ spMap u) (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) :=
    (gν.comp (isGrpPullback_pullback ρ.P.A FinalForm.u₀)).congr (by rw [hju, hxu]) rfl

  let A := (Over.pullback (spMap u)).obj ρ.P.A
  have hA := isGrpPullback_pullback ρ.P.A (spMap u)
  have wA : (ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀) ≫ ρ.P.A.hom = (A₀.hom ≫ j) ≫ spMap u := by
    rw [gψ.1.w, Category.assoc]
  let φ₂ : A₀.left ⟶ A.left := hA.1.lift _ _ wA
  have eφ₂ : φ₂ ≫ pullback.fst ρ.P.A.hom (spMap u) = ν ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ := hA.1.lift_fst _ _ _
  have sφ₂ : φ₂ ≫ A.hom = A₀.hom ≫ j := hA.1.lift_snd _ _ _
  have hφ₂ : IsGrpPullback A₀ A j φ₂ := hA.cancel (gψ.congr rfl eφ₂.symm) sφ₂

  let GO := (Over.pullback x).obj FinalForm.G
  have hGO := isGrpPullback_pullback FinalForm.G x
  have gη' : IsGrpPullback A₀ FinalForm.G (j ≫ x) (pullback.fst FinalForm.G.hom M.pt) :=
    (isGrpPullback_pullback FinalForm.G M.pt).congr hx.symm rfl
  have wG : pullback.fst FinalForm.G.hom M.pt ≫ FinalForm.G.hom = (A₀.hom ≫ j) ≫ x := by rw [gη'.1.w, Category.assoc]
  let φ₁ : A₀.left ⟶ GO.left := hGO.1.lift _ _ wG
  have eφ₁ : φ₁ ≫ pullback.fst FinalForm.G.hom x = pullback.fst FinalForm.G.hom M.pt := hGO.1.lift_fst _ _ _
  have hφ₁ : IsGrpPullback A₀ GO j φ₁ := hGO.cancel (gη'.congr rfl eφ₁.symm) (hGO.1.lift_snd _ _ _)
  have sA : IsSemiAbelian A := IsSemiAbelian.pullback _ _ (GlobalTheory.isSemiAbelian_of_isAbelianScheme _ ρ.P.isAb)
  have sG : IsSemiAbelian GO := IsSemiAbelian.pullback _ _ FinalForm.semi
  obtain ⟨E, ⟨hE, hEφ⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O) (GlobalTheory.IsGenericPointHom.fractionField O Ω) sA sG hφ₂ hφ₁
  haveI := hE
  let gm : A.left ⟶ FinalForm.G.left := E.hom.left ≫ pullback.fst FinalForm.G.hom x
  have hgm : IsGrpPullback A FinalForm.G x gm := ((isGrpPullback_of_iso E).comp hGO).congr (Category.id_comp _) rfl
  have key : φ₂ ≫ gm = ν ≫ FinalForm.φ := by
    show φ₂ ≫ E.hom.left ≫ pullback.fst FinalForm.G.hom x = _
    rw [← Category.assoc, hEφ, eφ₁, hν₁]
  have hgmw : gm ≫ FinalForm.G.hom = A.hom ≫ x := hgm.1.w
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ sA
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian _ FinalForm.semi
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing O Ω
  haveI : IsSchemeTheoreticallyDominant φ₂ := .of_isPullback hφ₂.1.flip
  refine ⟨gm, hgm, ?_, ?_⟩
  · intro f Fm hf T' p p' h₁ h₂
    let fO := (Over.pullback (spMap u)).map f
    let fQ := (Over.pullback FinalForm.u₀).map f
    have hfO₁ : fO.left ≫ pullback.fst ρ.P.A.hom (spMap u) = pullback.fst ρ.P.A.hom (spMap u) ≫ f.left :=
      pullback.lift_fst _ _ _
    have hfQ₁ : fQ.left ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = pullback.fst ρ.P.A.hom FinalForm.u₀ ≫ f.left :=
      pullback.lift_fst _ _ _
    have hfO₂ : fO.left ≫ A.hom = A.hom := Over.w fO
    have hp' : p' = p ≫ fO.left := by
      apply pullback.hom_ext
      · rw [h₂, Category.assoc, hfO₁]
      · show p' ≫ A.hom = (p ≫ fO.left) ≫ A.hom
        rw [Category.assoc, hfO₂, h₁]
    have wk : (ν ≫ fQ.left) ≫ Q.hom = A₀.hom ≫ x₀ := by
      rw [Category.assoc, Over.w fQ, gν.1.w]
    let k : A₀.left ⟶ A₀.left := gν.1.lift _ _ wk
    have hk₁ : k ≫ ν = ν ≫ fQ.left := gν.1.lift_fst _ _ _
    have hk₂ : k ≫ A₀.hom = A₀.hom := gν.1.lift_snd _ _ _
    have hφk : φ₂ ≫ fO.left = k ≫ φ₂ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, hfO₁, eφ₂, reassoc_of% eφ₂, reassoc_of% hk₁, hfQ₁]
      · show (φ₂ ≫ fO.left) ≫ A.hom = (k ≫ φ₂) ≫ A.hom
        rw [Category.assoc, hfO₂, Category.assoc, sφ₂, ← Category.assoc, hk₂]
    have main : fO.left ≫ gm = gm ≫ Fm.left := by
      refine GlobalTheory.ExtUnique.hom_ext_of_dominant FinalForm.G.hom ?_ φ₂ ?_
      · rw [Category.assoc, hgmw, ← Category.assoc, hfO₂, Category.assoc, Over.w Fm, hgmw]
      · calc φ₂ ≫ fO.left ≫ gm = k ≫ φ₂ ≫ gm := by rw [← Category.assoc, hφk, Category.assoc]
          _ = (k ≫ ν) ≫ FinalForm.φ := by rw [key, Category.assoc]
          _ = ν ≫ FinalForm.φ ≫ Fm.left := by rw [hk₁, Category.assoc, hf]
          _ = φ₂ ≫ gm ≫ Fm.left := by rw [← Category.assoc, ← key, Category.assoc]
    rw [hp', Category.assoc, main]
  · intro a Wo h hs T' p x' h₁ h₂
    have hpa : (ρ.pt a).left ≫ ρ.P.A.hom = 𝟙 _ := by simpa [baseOver] using Over.w (ρ.pt a)
    let σ : Sp O ⟶ A.left := pullback.lift (spMap u ≫ (ρ.pt a).left) (𝟙 (Sp O))
      (by rw [Category.assoc, hpa]; simp)
    have hσ₁ : σ ≫ pullback.fst ρ.P.A.hom (spMap u) = spMap u ≫ (ρ.pt a).left := pullback.lift_fst _ _ _
    have hσ₂ : σ ≫ A.hom = 𝟙 _ := pullback.lift_snd _ _ _
    have hp : p = (p ≫ A.hom) ≫ σ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hσ₁, h₂, Category.assoc]
      · show p ≫ A.hom = ((p ≫ A.hom) ≫ σ) ≫ A.hom
        rw [Category.assoc, hσ₂, Category.comp_id]
    let O' := x ⁻¹ᵁ Wo
    have hpb := isPullback_morphismRestrict x Wo
    let q : T' ⟶ O'.toScheme := hpb.lift x' (p ≫ A.hom) (by rw [h₁, Category.assoc])
    have hq₁ : q ≫ (x ∣_ Wo) = x' := hpb.lift_fst _ _ _
    have hq₂ : q ≫ O'.ι = p ≫ A.hom := hpb.lift_snd _ _ _
    have hmain : O'.ι ≫ σ ≫ gm = (x ∣_ Wo) ≫ h := by
      by_cases hO : (O' : Set (Sp O)).Nonempty
      · have hr' : Set.range j ⊆ Set.range O'.ι := by
          rw [Scheme.Opens.range_ι, (GlobalTheory.IsGenericPointHom.fractionField O Ω).range_eq, Set.singleton_subset_iff]
          exact ((genericPoint_spec (Sp O)).mem_open_set_iff O'.isOpen).2 (by simpa using hO)
        let jO : Sp Ω ⟶ O'.toScheme := IsOpenImmersion.lift O'.ι j hr'
        have hjO : jO ≫ O'.ι = j := IsOpenImmersion.lift_fac _ _ _
        haveI : IsDominant (jO ≫ O'.ι) := by rw [hjO]; infer_instance
        haveI : IsDominant jO := IsDominant.of_comp_of_isOpenImmersion jO O'.ι
        refine ext_of_isDominant_of_isSeparated FinalForm.G.hom ?_ jO ?_
        · simp only [Category.assoc]
          rw [hgmw, ← Category.assoc σ, hσ₂, Category.id_comp, hs.1, morphismRestrict_ι]
        · let x'' : Sp Ω ⟶ pullback ρ.P.A.hom FinalForm.u₀ := pullback.lift (spMap S.R.val.toRingHom ≫ (ρ.pt a).left) x₀
            (by rw [Category.assoc, hpa, hxu]; simp)
          have hx''₁ : x'' ≫ pullback.fst ρ.P.A.hom FinalForm.u₀ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left :=
            pullback.lift_fst _ _ _
          have hx''₂ : x'' ≫ pullback.snd ρ.P.A.hom FinalForm.u₀ = x₀ := pullback.lift_snd _ _ _
          have hsec := hs.2 (jO ≫ (x ∣_ Wo)) x''
            (by rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hjO, hx])
            (by rw [FinalForm.cart.1.w, ← Category.assoc]; erw [hx''₂]; exact hx₀) hx''₁
          let e : Sp Ω ⟶ A₀.left := hφ₂.1.lift (j ≫ σ) (𝟙 _) (by rw [Category.assoc, hσ₂, Category.comp_id, Category.id_comp])
          have he₁ : e ≫ φ₂ = j ≫ σ := hφ₂.1.lift_fst _ _ _
          have he₂ : e ≫ A₀.hom = 𝟙 _ := hφ₂.1.lift_snd _ _ _
          have heν : e ≫ ν = x'' := by
            apply pullback.hom_ext
            · rw [hx''₁, Category.assoc, ← eφ₂, ← Category.assoc, he₁, Category.assoc, hσ₁, ← Category.assoc, hju]
            · rw [hx''₂, Category.assoc]
              erw [hν₂]
              rw [← Category.assoc]
              erw [he₂]
              rw [Category.id_comp]
          calc jO ≫ O'.ι ≫ σ ≫ gm = (e ≫ φ₂) ≫ gm := by rw [← Category.assoc, hjO, he₁, Category.assoc]
            _ = (e ≫ ν) ≫ FinalForm.φ := by rw [Category.assoc, key, Category.assoc]
            _ = jO ≫ (x ∣_ Wo) ≫ h := by rw [heν, ← Category.assoc, hsec]
      · haveI : IsEmpty O'.toScheme := ⟨fun y => hO ⟨y.1, y.2⟩⟩
        exact isInitialOfIsEmpty.hom_ext _ _
    rw [hp, ← hq₂, ← hq₁, Category.assoc, Category.assoc, hmain, Category.assoc]

end GlobalTheory.Poinc.Sep.Spz
