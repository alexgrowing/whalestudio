import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenImmersionQuasiFiniteLocusOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective

section ProOpen

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory.HomExtProOpen

open GlobalTheory GlobalTheory.HomExt GlobalTheory.HomExtNormal

theorem existsUnique_hom_extension_of_dvr
    (H : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f))
    (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) (hX : Geo.Tor.IsNormalScheme X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (G G' : Over X) [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') (hf : IsMonHom f) :
    ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback j).map F = f := by
  have := hG.smooth
  have := hG'.smooth
  have := hG.quasiCompact
  have := hG'.quasiCompact
  have := hG'.separated
  have : GlobalTheory.IsNormalScheme X := (GlobalTheory.isNormalScheme_iff X).mpr hX
  have : GlobalTheory.IsNormalScheme G.left := (GlobalTheory.isNormalScheme_iff _).mpr
    (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hX)
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  let u : pullback G.hom j ⟶ G.left := pullback.fst G.hom j
  let φ : pullback G.hom j ⟶ G'.left := f.left ≫ pullback.fst G'.hom j
  have hw : f.left ≫ pullback.snd G'.hom j = pullback.snd G.hom j := Over.w f
  have huφ : u ≫ G.hom = φ ≫ G'.hom := by
    rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hw]
  have : IsDominant u := isDominant_pullback_fst_of_isOpenMap j G.hom G.hom.isOpenMap
  have : IsPreimmersion u := inferInstanceAs (IsPreimmersion (pullback.fst G.hom j))
  have : Flat u := inferInstanceAs (Flat (pullback.fst G.hom j))
  have : QuasiCompact u := inferInstanceAs (QuasiCompact (pullback.fst G.hom j))
  have hus := isIso_stalkMap_of_flat_of_surjectiveOnStalks u
  have : GlobalTheory.IsNormalScheme (pullback G.hom j) := GlobalTheory.IsNormalScheme.of_isIso_stalkMap u
  let Γ := graphClosure G.hom G'.hom u φ huφ
  let p : Γ ⟶ G.left := graphClosure.fst G.hom G'.hom u φ huφ
  let q : Γ ⟶ G'.left := graphClosure.snd G.hom G'.hom u φ huφ
  let i : pullback G.hom j ⟶ Γ := graphClosure.incl G.hom G'.hom u φ huφ
  have hip : i ≫ p = u := graphClosure.incl_fst ..
  have hiq : i ≫ q = φ := graphClosure.incl_snd ..
  have hpq : p ≫ G.hom = q ≫ G'.hom := graphClosure.condition ..
  have hpb := graphClosure.isPullback_incl G.hom G'.hom u φ huφ
  have : IsPreimmersion i := MorphismProperty.of_isPullback hpb ‹IsPreimmersion u›
  have : Flat i := MorphismProperty.of_isPullback hpb ‹Flat u›
  have : QuasiCompact i := graphClosure.quasiCompact_incl ..
  have : IsSchemeTheoreticallyDominant i := graphClosure.schemeDominant_incl ..
  have : IsDominant i := inferInstance
  have : IsReduced Γ := graphClosure.isReduced ..
  have : LocallyOfFiniteType p := graphClosure.locallyOfFiniteType_fst ..
  have : QuasiCompact p := graphClosure.quasiCompact_fst ..
  have : IsSeparated p := graphClosure.isSeparated_fst ..
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : IsLocallyNoetherian Γ := LocallyOfFiniteType.isLocallyNoetherian p
  have : Surjective p := by
    refine ⟨fun σ ↦ ?_⟩
    rcases mem_range_or_exists_dvr u σ with ⟨w, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩
    · exact ⟨i w, by rw [← Scheme.Hom.comp_apply, hip]⟩
    obtain ⟨F, s, -, -, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ a c hc
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom (a ≫ G.hom) = pullback.snd G.hom (a ≫ G.hom) := Over.w F
    obtain ⟨l, ⟨hl, -⟩, -⟩ := graphClosure.existsUnique_lift G.hom G'.hom u φ huφ a
      (s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom))
      (by rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hF, reassoc_of% hs₂])
      (spMap (algebraMap T (FractionRing T))) c hc.symm hs
    exact ⟨l (IsLocalRing.closedPoint T), by rw [← hl]; rfl⟩
  let Γ' : Over X := Over.mk (p ≫ G.hom)
  let p' : Γ' ⟶ G := Over.homMk p rfl
  let q' : Γ' ⟶ G' := Over.homMk q hpq.symm
  have : LocallyOfFiniteType p'.left := ‹LocallyOfFiniteType p›
  have key : ∀ (k : Type) [Field k] (x : Sp k ⟶ Γ'.left) (n : ℕ),
      x ≫ (p' ^ n).left = x ≫ (1 : Γ' ⟶ G).left → x ≫ (q' ^ n).left = x ≫ (1 : Γ' ⟶ G').left := by
    intro k _ x n hx
    rcases mem_range_or_exists_dvr i (x default) with hw | ⟨T, _, _, _, a, c, hc, ha⟩
    · obtain ⟨c, rfl⟩ := exists_lift_of_range_subset i x (by
        rintro _ ⟨t, rfl⟩
        rwa [Subsingleton.elim t default])
      exact comp_pow_eq_one_of_pullback_hom j f p' q' _ c
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hip.symm)
        (by rw [Category.assoc]; exact congrArg (c ≫ ·) hiq.symm) n hx
    obtain ⟨F, s, _, hs₁, hs₂, hs⟩ := exists_hom_along_dvr H j hG hG' f T _ (a ≫ p) c
      (by rw [← reassoc_of% hc, hip])
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    have hF : F.left ≫ pullback.snd G'.hom ((a ≫ p) ≫ G.hom) =
      pullback.snd G.hom ((a ≫ p) ≫ G.hom) := Over.w F
    have hb : s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom) = a ≫ q := by
      have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk ((a ≫ p) ≫ G.hom)) (X := G')
        (spMap (algebraMap T (FractionRing T)))
        (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) (by
          change (s ≫ F.left ≫ pullback.fst G'.hom ((a ≫ p) ≫ G.hom)) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hF,
            reassoc_of% hs₂]))
        (b := Over.homMk (a ≫ q) (by
          change (a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc, Category.assoc, hpq]))
        (hs.trans (by
          change _ = spMap (algebraMap T (FractionRing T)) ≫ a ≫ q
          rw [← reassoc_of% hc, hiq]))
      exact congrArg CommaMorphism.left this
    let r : Sp (IsLocalRing.ResidueField T) ⟶ Sp T := spMap (IsLocalRing.residue T)
    have hr : x default ∈ Set.range (r ≫ a) := by
      refine ⟨IsLocalRing.closedPoint _, ?_⟩
      exact (Scheme.Hom.comp_apply r a _).trans
        ((congrArg a (IsLocalRing.comap_closedPoint (IsLocalRing.residue T))).trans ha)
    rw [field_point_comp_eq_iff _ _ x _ ⟨default, rfl⟩,
      ← field_point_comp_eq_iff (Z := Γ'.left) _ _ (r ≫ a) _ hr] at hx ⊢
    exact comp_pow_eq_one_of_pullback_hom _ F p' q' (r ≫ a) (r ≫ s)
      (by rw [Category.assoc, hs₁, Category.assoc]; rfl)
      (by rw [Category.assoc, hb, Category.assoc]; rfl) n hx
  have : IsPreimmersion (i ≫ p) := by rwa [hip]
  have : Flat (i ≫ p) := by rwa [hip]
  have : IsDominant (i ≫ p) := by rwa [hip]
  have : QuasiCompact (i ≫ p) := by rwa [hip]
  have hQ : IsOpenImmersion (p.quasiFiniteLocus.ι ≫ p) := isOpenImmersion_quasiFiniteLocus i p
  have hgraph : ∀ w : Γ, ∃ (T : Scheme.{0}) (τ : T ⟶ X)
      (F : (Over.pullback τ).obj G ⟶ (Over.pullback τ).obj G') (l : pullback G.hom τ ⟶ Γ)
      (x : ↥(pullback G.hom τ)), IsMonHom F ∧ l ≫ p = pullback.fst G.hom τ ∧
        l ≫ q = F.left ≫ pullback.fst G'.hom τ ∧ l x = w := by
    intro w
    rcases mem_range_or_exists_dvr i w with ⟨c, rfl⟩ | ⟨T, _, _, _, a, c, hc, rfl⟩
    · exact ⟨U, j, f, i, c, hf, hip, hiq, rfl⟩
    have := schemeTheoreticallyDominant_fractionField T (FractionRing T)
    set iK := spMap (algebraMap T (FractionRing T)) with hiK
    let t : Sp T ⟶ X := (a ≫ p) ≫ G.hom
    let y : Sp (FractionRing T) ⟶ U := c ≫ pullback.snd G.hom j
    have h0 : c ≫ u = iK ≫ a ≫ p := by rw [← hip, reassoc_of% hc]
    have hy : y ≫ j = iK ≫ t := by
      change (c ≫ pullback.snd G.hom j) ≫ j = iK ≫ (a ≫ p) ≫ G.hom
      rw [Category.assoc, ← pullback.condition]
      simpa [u] using congrArg (· ≫ G.hom) h0
    obtain ⟨F, hF, hFf⟩ := exists_hom_along_trait H j hG hG' f T (FractionRing T) t y hy
    have hFw : F.left ≫ pullback.snd G'.hom t = pullback.snd G.hom t := Over.w F
    let d : pullback (pullback.snd G.hom t) iK ⟶ pullback G.hom t := pullback.fst _ _
    have : IsDominant d := isDominant_pullback_fst_of_isOpenMap iK (pullback.snd G.hom t)
      (pullback.snd G.hom t).isOpenMap
    have : GlobalTheory.IsNormalScheme (pullback G.hom t) := (GlobalTheory.isNormalScheme_iff _).mpr
      (forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth (pullback.snd G.hom t)
        ((GlobalTheory.isNormalScheme_iff _).mp inferInstance))
    have : IsSchemeTheoreticallyDominant d := IsSchemeTheoreticallyDominant.of_isDominant d
    let v : pullback (pullback.snd G.hom t) iK ⟶ pullback G.hom (iK ≫ t) :=
      pullback.lift (d ≫ pullback.fst G.hom t) (pullback.snd _ iK) (by
        change (pullback.fst _ _ ≫ pullback.fst G.hom t) ≫ G.hom = _
        rw [Category.assoc, pullback.condition, reassoc_of% (pullback.condition (f := pullback.snd G.hom t) (g := iK))])
    have hv₁ : v ≫ pullback.fst G.hom (iK ≫ t) = d ≫ pullback.fst G.hom t :=
      pullback.lift_fst _ _ _
    have hv₂ : v ≫ pullback.snd G.hom (iK ≫ t) = pullback.snd _ iK := pullback.lift_snd _ _ _
    have hv : v ≫ pullMap iK t _ rfl G = d := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, hv₁]
      · rw [Category.assoc, pullMap_snd, reassoc_of% hv₂]
        exact pullback.condition.symm
    let ρ := pullMap y j _ hy G
    have hρ₁ : ρ ≫ pullback.fst G.hom j = pullback.fst G.hom (iK ≫ t) := pullMap_fst ..
    have hρ₂ : ρ ≫ pullback.snd G.hom j = pullback.snd G.hom (iK ≫ t) ≫ y := pullMap_snd ..
    have hw₁ : d ≫ pullback.fst G.hom t = (v ≫ ρ) ≫ u := by
      change _ = (v ≫ ρ) ≫ pullback.fst G.hom j
      rw [Category.assoc, hρ₁, hv₁]
    have hw₂ : d ≫ F.left ≫ pullback.fst G'.hom t = (v ≫ ρ) ≫ φ := by
      rw [← hv, Category.assoc, Category.assoc, hFf]
    have hcond : pullback.fst G.hom t ≫ G.hom = (F.left ≫ pullback.fst G'.hom t) ≫ G'.hom := by
      rw [Category.assoc, pullback.condition, pullback.condition, reassoc_of% hFw]
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := graphClosure.existsUnique_lift G.hom G'.hom u φ huφ
      (pullback.fst G.hom t) (F.left ≫ pullback.fst G'.hom t) hcond d (v ≫ ρ) hw₁ hw₂
    let s : Sp T ⟶ pullback G.hom t := pullback.lift (a ≫ p) (𝟙 _) (by simp [t])
    have hs₁ : s ≫ pullback.fst G.hom t = a ≫ p := pullback.lift_fst _ _ _
    have hs₂ : s ≫ pullback.snd G.hom t = 𝟙 _ := pullback.lift_snd _ _ _
    have hq : s ≫ F.left ≫ pullback.fst G'.hom t = a ≫ q := by
      let v' : Sp (FractionRing T) ⟶ pullback G.hom (iK ≫ t) :=
        pullback.lift (iK ≫ a ≫ p) (𝟙 _) (by simp [t])
      have hv'₁ : v' ≫ pullback.fst G.hom (iK ≫ t) = iK ≫ a ≫ p := pullback.lift_fst _ _ _
      have hv'₂ : v' ≫ pullback.snd G.hom (iK ≫ t) = 𝟙 _ := pullback.lift_snd _ _ _
      have h₁ : v' ≫ pullMap iK t _ rfl G = iK ≫ s := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullMap_fst, hv'₁, Category.assoc, hs₁]
        · rw [Category.assoc, pullMap_snd, reassoc_of% hv'₂, Category.assoc, hs₂, Category.comp_id]
      have h₂ : v' ≫ ρ = c := by
        apply pullback.hom_ext
        · rw [Category.assoc, hρ₁, hv'₁]
          exact h0.symm
        · rw [Category.assoc, hρ₂, reassoc_of% hv'₂]
      have h₃ : iK ≫ s ≫ F.left ≫ pullback.fst G'.hom t = iK ≫ a ≫ q := by
        rw [← reassoc_of% h₁, hFf, reassoc_of% h₂, ← reassoc_of% hc, hiq]
      have := over_ext_of_schemeTheoreticallyDominant (Y := Over.mk t) (X := G') iK
        (a := Over.homMk (s ≫ F.left ≫ pullback.fst G'.hom t) (by
          change (s ≫ F.left ≫ pullback.fst G'.hom t) ≫ G'.hom = t
          rw [Category.assoc s, Category.assoc F.left, pullback.condition, reassoc_of% hFw,
            reassoc_of% hs₂]))
        (b := Over.homMk (a ≫ q) (by
          change (a ≫ q) ≫ G'.hom = (a ≫ p) ≫ G.hom
          rw [Category.assoc, Category.assoc, hpq]))
        h₃
      exact congrArg CommaMorphism.left this
    have hsl : s ≫ l = a := by
      refine graphClosure.hom_ext G.hom G'.hom u φ huφ ?_ ?_
      · change (s ≫ l) ≫ p = a ≫ p
        rw [Category.assoc, hl₁, hs₁]
      · change (s ≫ l) ≫ q = a ≫ q
        rw [Category.assoc, hl₂, hq]
    exact ⟨Sp T, t, F, l, s (IsLocalRing.closedPoint T), hF, hl₁, hl₂,
      (Scheme.Hom.comp_apply s l _).symm.trans (by rw [hsl])⟩
  have hinj : ∀ w₁ w₂ : Γ, p w₁ = p w₂ → w₁ = w₂ := by
    intro w₁ w₂ hw₁₂
    obtain ⟨T₁, τ₁, F₁, l₁, x₁, m₁, a₁, b₁, rfl⟩ := hgraph w₁
    obtain ⟨T₂, τ₂, F₂, l₂, x₂, m₂, a₂, b₂, rfl⟩ := hgraph w₂
    have hx : pullback.fst G.hom τ₁ x₁ = pullback.fst G.hom τ₂ x₂ := by
      rw [← a₁, ← a₂, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact hw₁₂
    obtain ⟨Ω, _, _, e₁, e₂, he, ⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := exists_common_point _ _ x₁ x₂ hx
    let τ : Sp Ω ⟶ X := e₁ ≫ pullback.fst G.hom τ₁ ≫ G.hom
    have h₁ : (e₁ ≫ pullback.snd G.hom τ₁) ≫ τ₁ = τ := by
      rw [Category.assoc, ← pullback.condition]
    have h₂ : (e₂ ≫ pullback.snd G.hom τ₂) ≫ τ₂ = τ := by
      rw [Category.assoc, ← pullback.condition, ← reassoc_of% he]
    obtain ⟨F₁', m₁', c₁⟩ := exists_pull_hom _ τ₁ τ h₁ F₁
    obtain ⟨F₂', m₂', c₂⟩ := exists_pull_hom _ τ₂ τ h₂ F₂
    let g₁ := pullMap _ τ₁ τ h₁ G ≫ l₁
    let g₂ := pullMap _ τ₂ τ h₂ G ≫ l₂
    have hg₁p : g₁ ≫ p = pullback.fst G.hom τ := by
      change (pullMap _ τ₁ τ h₁ G ≫ l₁) ≫ p = _
      rw [Category.assoc, a₁, pullMap_fst]
    have hg₂p : g₂ ≫ p = pullback.fst G.hom τ := by
      change (pullMap _ τ₂ τ h₂ G ≫ l₂) ≫ p = _
      rw [Category.assoc, a₂, pullMap_fst]
    have hg₁q : g₁ ≫ q = F₁'.left ≫ pullback.fst G'.hom τ := by
      rw [c₁, Category.assoc, b₁]
    have hg₂q : g₂ ≫ q = F₂'.left ≫ pullback.fst G'.hom τ := by
      rw [c₂, Category.assoc, b₂]
    have hF : F₁' = F₂' := by
      refine hom_eq_of_torsion (IsSemiAbelian.pullback τ G hG) (IsSemiAbelian.pullback τ G' hG')
        F₁' F₂' fun y n hn hy ↦ ?_
      let e := TorsionLift.ptsEquiv τ G (𝟙_ (Over (Sp Ω))) τ (Category.id_comp _)
      have hx : (e y) ^ n = 1 := by rw [← map_pow, hy, map_one]
      have hxl : (e y).left = y.left ≫ pullback.fst G.hom τ := TorsionLift.ptsEquiv_left ..
      have hqf : ∀ z : Sp Ω ⟶ Γ, z ≫ p = (e y).left →
          Set.range z ⊆ Set.range p.quasiFiniteLocus.ι := by
        rintro z hz _ ⟨s, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact quasiFiniteAt_of_torsion hG' p' q'
          (fun a b ↦ graphClosure.hom_ext G.hom G'.hom u φ huφ) key τ (e y) hn hx (z s)
          ⟨s, by rw [← hz]; exact (Scheme.Hom.comp_apply _ _ _).symm⟩
      let z₁ : Sp Ω ⟶ Γ := y.left ≫ g₁
      let z₂ : Sp Ω ⟶ Γ := y.left ≫ g₂
      have hz₁ : z₁ ≫ p = (e y).left := by
        change (y.left ≫ g₁) ≫ p = _
        rw [Category.assoc, hg₁p, hxl]
      have hz₂ : z₂ ≫ p = (e y).left := by
        change (y.left ≫ g₂) ≫ p = _
        rw [Category.assoc, hg₂p, hxl]
      let z₁' := IsOpenImmersion.lift p.quasiFiniteLocus.ι z₁ (hqf z₁ hz₁)
      let z₂' := IsOpenImmersion.lift p.quasiFiniteLocus.ι z₂ (hqf z₂ hz₂)
      have hz₁' : z₁' ≫ p.quasiFiniteLocus.ι = z₁ := IsOpenImmersion.lift_fac _ _ _
      have hz₂' : z₂' ≫ p.quasiFiniteLocus.ι = z₂ := IsOpenImmersion.lift_fac _ _ _
      have hz' : z₁' = z₂' := by
        rw [← cancel_mono (p.quasiFiniteLocus.ι ≫ p), reassoc_of% hz₁', reassoc_of% hz₂', hz₁, hz₂]
      have hz : z₁ = z₂ := by rw [← hz₁', ← hz₂', hz']
      apply Over.OverMorphism.ext
      change y.left ≫ F₁'.left = y.left ≫ F₂'.left
      have hw₁ : F₁'.left ≫ pullback.snd G'.hom τ = pullback.snd G.hom τ := Over.w F₁'
      have hw₂ : F₂'.left ≫ pullback.snd G'.hom τ = pullback.snd G.hom τ := Over.w F₂'
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, ← hg₁q, ← hg₂q]
        exact congrArg (· ≫ q) (by simpa [z₁, z₂] using hz)
      · rw [Category.assoc, Category.assoc, hw₁, hw₂]
    have hg : g₁ = g₂ := by
      refine graphClosure.hom_ext G.hom G'.hom u φ huφ ?_ ?_
      · exact hg₁p.trans hg₂p.symm
      · refine hg₁q.trans (hF ▸ hg₂q.symm)
    let b : Sp Ω ⟶ pullback G.hom τ := pullback.lift (e₁ ≫ pullback.fst G.hom τ₁) (𝟙 _) (by simp [τ])
    have hbf : b ≫ pullback.fst G.hom τ = e₁ ≫ pullback.fst G.hom τ₁ := pullback.lift_fst _ _ _
    have hbs : b ≫ pullback.snd G.hom τ = 𝟙 _ := pullback.lift_snd _ _ _
    have hb₁ : b ≫ pullMap _ τ₁ τ h₁ G = e₁ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, hbf]
      · rw [Category.assoc, pullMap_snd, reassoc_of% hbs]
    have hb₂ : b ≫ pullMap _ τ₂ τ h₂ G = e₂ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullMap_fst, hbf, he]
      · rw [Category.assoc, pullMap_snd, reassoc_of% hbs]
    have hl : e₁ ≫ l₁ = e₂ ≫ l₂ := by
      rw [← hb₁, ← hb₂, Category.assoc, Category.assoc]
      exact congrArg (b ≫ ·) hg
    rw [Subsingleton.elim s₂ s₁]
    simp only [← Scheme.Hom.comp_apply]
    rw [hl]
  have : LocallyQuasiFinite p := locallyQuasiFinite_iff_finite_preimage_singleton.mpr fun σ ↦
    Set.Subsingleton.finite fun a ha b hb ↦ hinj a b (ha.trans hb.symm)
  have : IsIso p := isIso_of_densePart i p
  obtain ⟨ψ, hψ, huψ⟩ := graphClosure.exists_extension_of_isIso_fst G.hom G'.hom u φ huφ
  let F : G ⟶ G' := Over.homMk ψ hψ.symm
  have hF : (Over.pullback j).map F = f := by
    ext1
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans huψ
    · exact (Over.w _).trans hw.symm
  refine ⟨F, ⟨?_, hF⟩, fun F' hF' ↦ pullback_map_injective_of_flat j (hF'.2.trans hF.symm)⟩
  have : IsMonHom ((Over.pullback j).map F) := hF ▸ hf
  exact isMonHom_of_pullback_of_flat j F

end GlobalTheory.HomExtProOpen

end ProOpen

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory
open scoped CategoryTheory.Obj

theorem GlobalTheory.exists_oAct_extend_dedekindModel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [Field K] (ω : R →+* K) (U Y : Scheme.{0}) (sY : Y ⟶ Sp R) (jQ : U ⟶ pullback sY (spMap ω)) (G' : Over Y) [GrpObj G'] [IsCommMonObj G'] (t₀ : SAB H U) (φ : t₀.G.left ⟶ G'.left), IsDedFrac ω → Geo.Tor.IsNormalScheme Y → IsProjOver sY → Flat sY → IsOpenImmersion jQ → Dense (Set.range jQ) → IsSemiAbelian G' → IsGrpPullback t₀.G G' (jQ ≫ pullback.fst _ _) φ → ∃ act : OAct (𝓞 E) G', ∀ a, (t₀.act.act a).left ≫ φ = φ ≫ (act.act a).left := by
  intro E _ _ _ H R K _ _ ω U Y sY jQ G' _ _ t₀ φ hω hY hP hF hjQ hD hG' hφ
  obtain ⟨⟨_, _⟩, _, hfr⟩ := hω
  letI := ω.toAlgebra
  obtain ⟨hN, -, -, hpre, hfl, hdom, hqc⟩ :=
    GlobalTheory.genericPart_dense_proOpen R K Y U sY jQ hF hP hjQ hD
  set j : U ⟶ Y := jQ ≫ pullback.fst sY (spMap ω) with hj
  have := hG'.smooth
  have := hG'.separated
  have : GlobalTheory.IsNormalScheme Y := (GlobalTheory.isNormalScheme_iff Y).mpr hY
  have : IsSchemeTheoreticallyDominant j := IsSchemeTheoreticallyDominant.of_isDominant j
  have key : ∀ x, ∃ F : G' ⟶ G', (t₀.act.act x).left ≫ φ = φ ≫ F.left := by
    intro x
    obtain ⟨e, he, he'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G' j)
    have := t₀.act.hom x
    obtain ⟨F, ⟨-, hF⟩, -⟩ := GlobalTheory.HomExtProOpen.existsUnique_hom_extension_of_dvr
      GlobalTheory.homExtension_semiAbelian_dvr Y U j hY G' G' hG' hG' (e.inv ≫ t₀.act.act x ≫ e.hom) inferInstance
    refine ⟨F, ?_⟩
    have h1 : ((Over.pullback j).map F).left ≫ pullback.fst G'.hom j = pullback.fst G'.hom j ≫ F.left :=
      GlobalTheory.ExtUnique.pullback_map_left_fst j F
    rw [hF] at h1
    have h2 : e.hom ≫ e.inv ≫ t₀.act.act x ≫ e.hom = t₀.act.act x ≫ e.hom := e.hom_inv_id_assoc _
    rw [← he', Category.assoc, ← h1, ← Over.comp_left_assoc (f := e.hom), h2, Over.comp_left_assoc]
  obtain ⟨a, ha, -⟩ := GlobalTheory.ExtUnique.existsUnique_oAct_of_isGrpPullback hφ t₀.act key
  exact ⟨a, ha⟩
