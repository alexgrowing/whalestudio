import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenExtendNormal

open GlobalTheory.DvrModel

theorem coheight_apply_le_one {H S : Scheme.{0}} (p : H ⟶ S) (hp : GeneralizingMap p) (x : H)
    (hx : Order.coheight x ≤ 1) : Order.coheight (p x) ≤ 1 := by
  have hx' := (Order.coheight_le_coe_iff (n := 1)).1 hx
  refine (Order.coheight_le_coe_iff (n := 1)).2 fun y hy ↦ ?_
  obtain ⟨x', h₁, rfl⟩ := hp (show y ⤳ p x from hy.le)
  have hlt : x < x' := ⟨h₁, fun h ↦ hy.not_ge (Specializes.map h p.continuous)⟩
  have hm : IsMax x' := by simpa using hx' x' hlt
  have : IsMax (p x') := fun w hw ↦ by
    obtain ⟨x'', h₂, rfl⟩ := hp (show w ⤳ p x' from hw)
    exact Specializes.map (hm (show x' ≤ x'' from h₂)) p.continuous
  simpa using this

theorem mem_range_of_preimmersion {H Y Z : Scheme.{0}} [IsIntegral H] (g : Y ⟶ H)
    [IsPreimmersion g] (k : Z ⟶ Y) (z : Z) (hz : g (k z) = genericPoint H) (y : Y)
    (A : H.Opens) [Nonempty A] (τ : Γ(H, A)) (O : Y.Opens) (hy : y ∈ O) (c : Γ(Y, O))
    (h : gs k z O c = gs (k ≫ g) z A τ) :
    H.germToFunctionField A τ ∈ (algebraMap (H.presheaf.stalk (g y)) H.functionField).range := by
  obtain ⟨u, hu⟩ := g.stalkMap_surjective y (Y.presheaf.germ O y hy c)
  obtain ⟨B, hB, σ, rfl⟩ := H.presheaf.germ_exist u
  rw [Scheme.Hom.germ_stalkMap_apply] at hu
  obtain ⟨O', hO', i₁, i₂, hO⟩ := Y.presheaf.germ_eq y _ _ _ _ hu
  have hsp : k z ⤳ y := by
    rw [← g.isEmbedding.isInducing.specializes_iff, hz]
    exact (genericPoint_spec H).specializes trivial
  have hkz : k z ∈ O' := hsp.mem_open O'.isOpen hO'
  have : Nonempty B := ⟨⟨_, hB⟩⟩
  have hA : (k ≫ g) z ∈ A := by
    rw [Scheme.Hom.comp_apply, hz]; exact genericPoint_mem_opens A
  have hB' : (k ≫ g) z ∈ B := by
    rw [Scheme.Hom.comp_apply, hz]; exact genericPoint_mem_opens B
  have h₁ : gs (k ≫ g) z B σ = gs (k ≫ g) z A τ := by
    rw [← h, ← gs_pull k g z B hB', ← gs_res k z i₁.le hkz, ← gs_res k z i₂.le hkz]
    exact congrArg _ hO
  rw [gs_eq _ _ _ hA, gs_eq _ _ _ hB', ← Scheme.Hom.germ_stalkMap_apply,
    ← Scheme.Hom.germ_stalkMap_apply] at h₁
  have key : ∀ (w : H) (hw : w = genericPoint H) {R : Type} [CommRing R] [Nontrivial R]
      (f : H.presheaf.stalk w →+* R) (hwA : w ∈ A) (hwB : w ∈ B),
      f (H.presheaf.germ B w hwB σ) = f (H.presheaf.germ A w hwA τ) →
      H.germToFunctionField B σ = H.germToFunctionField A τ := by
    rintro _ rfl R _ _ f _ _ hf
    exact RingHom.injective (R := H.functionField) f hf
  rw [← key _ hz ((k ≫ g).stalkMap z).hom hA hB' h₁]
  exact germToFunctionField_mem_range_stalk B σ hB

theorem exists_gen_germ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] {H X : Scheme.{0}}
    (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H) (hs : Smooth p)
    (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _)
    (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K))
    (heK : eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e) {L : LB X} (hL : L.IsLB)
    {I : Type} [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ)
    (ψ : I → (pullback p (etaK V K) ⟶ X)) (hψ : ψ = fun i ↦ pullback.fst p (etaK V K) ≫ φ i)
    (χ : I → (Spec (CommRingCat.of V) ⟶ X)) (hχ : χ = fun i ↦ e ≫ φ i)
    (t : LB.Gen (LB.LinComb L ψ ε)) (ρ : LB.Gen (LB.LinComb L χ ε)) (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K))) :
    ∃ c : LB.Gen (LB.LinComb L φ ε), ∀ z a, pullback.fst p (etaK V K) z ∈ LB.wchart L φ a →
      gm (pullback.fst p (etaK V K)) z (LB.wchart L φ a) (c.s a) =
        gm (𝟙 _) z (LB.wchart L ψ a) (t.s a) := by
  subst hψ hχ
  obtain ⟨c, ⟨-, rfl⟩, -⟩ := GlobalTheory.GenExtend.existsUnique_gen_extend V K H X p e hs hg he eK heK L hL
    I φ ε t ρ ht hρ hc
  refine ⟨c, fun z a hz ↦ ?_⟩
  have hm : (𝟙 _ : pullback p (etaK V K) ⟶ _) z ∈
      LB.wchart L (fun i ↦ pullback.fst p (etaK V K) ≫ φ i) a := (wchart_comp L _ φ a).ge hz
  exact ((gm_res _ z _ hm _).trans ((gm_pull _ _ z _ hz _).trans (by rw [Category.id_comp]; rfl))).symm

theorem mem_range_of_notMem {S U H HU X : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S]
    [GlobalTheory.IsNormalScheme S] [Nonempty U] [IsIntegral H] {j : U ⟶ S} [IsOpenImmersion j] {p : H ⟶ S}
    {e : S ⟶ H} {jH : HU ⟶ H} {pU : HU ⟶ U} {eU : U ⟶ HU} [Smooth p] [GeometricallyIntegral p]
    (he : e ≫ p = 𝟙 _) (hP : IsPullback jH pU p j) (heU : eU ≫ jH = j ≫ e) {L : LB X}
    (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (H ⟶ X)} {ε : I → ℤ}
    {t : LB.Gen (LB.LinComb L (fun i ↦ jH ≫ φ i) ε)}
    {ρ : LB.Gen (LB.LinComb L (fun i ↦ e ≫ φ i) ε)} (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j))
    (x : H) (hx : Order.coheight x = 1) (hxU : p x ∉ Set.range j) (a : I → L.ι)
    (hxa : x ∈ LB.wchart L φ a) (A : H.Opens) [Nonempty A] (τ : Γ(H, A)ˣ)
    (hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z), jH (r z) ∈ A →
      gm (r ≫ jH) z A τ = gm r z (LB.wchart L (fun i ↦ jH ≫ φ i) a) (t.s a)) :
    H.germToFunctionField A τ.val ∈ (algebraMap (H.presheaf.stalk x) H.functionField).range ∧
    H.germToFunctionField A (τ⁻¹).val ∈ (algebraMap (H.presheaf.stalk x) H.functionField).range := by
  have hη : genericPoint S ∈ Set.range j := by
    have : Nonempty j.opensRange := ⟨⟨j (Nonempty.some inferInstance), _, rfl⟩⟩
    exact genericPoint_mem_opens j.opensRange
  have h1 : Order.coheight (p x) = 1 := by
    refine le_antisymm (coheight_apply_le_one p (Flat.generalizingMap p) x hx.le) ?_
    rw [Order.one_le_iff_ne_zero, Order.coheight_ne_zero]
    intro hm
    have h₁ : genericPoint S ⤳ p x := (genericPoint_spec S).specializes trivial
    exact hxU (Specializes.mem_open (hm (show p x ≤ genericPoint S from h₁))
      j.isOpenEmbedding.isOpen_range hη)
  have := GlobalTheory.IsNormalScheme.isDiscreteValuationRing_stalk h1
  let V : Type := S.presheaf.stalk (p x)
  let K : Type := S.functionField
  let v : Spec (CommRingCat.of V) ⟶ S := S.fromSpecStalk (p x)
  have hv : IsPreimmersion v := inferInstanceAs (IsPreimmersion (S.fromSpecStalk (p x)))
  have hev : etaK V K ≫ v = S.fromSpecStalk (genericPoint S) :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk ((genericPoint_spec S).specializes trivial)
  have hpt : ∀ z, (etaK V K ≫ v) z = genericPoint S := fun z ↦ by
    rw [hev, Subsingleton.elim z (IsLocalRing.closedPoint K)]
    exact Scheme.fromSpecStalk_closedPoint
  let w : Spec (CommRingCat.of K) ⟶ U := IsOpenImmersion.lift j (etaK V K ≫ v) (by
    rintro _ ⟨z, rfl⟩
    rw [hpt]
    exact hη)
  have hw : w ≫ j = etaK V K ≫ v := IsOpenImmersion.lift_fac _ _ _
  let g := pullback.fst p v
  let pV := pullback.snd p v
  have hg : IsPreimmersion g := MorphismProperty.pullback_fst _ _ hv
  let eV : Spec (CommRingCat.of V) ⟶ pullback p v := pullback.lift (v ≫ e) (𝟙 _) (by simp [he])
  have heV : eV ≫ pV = 𝟙 _ := pullback.lift_snd _ _ _
  have heV' : eV ≫ g = v ≫ e := pullback.lift_fst _ _ _
  let k := pullback.fst pV (etaK V K)
  let pK := pullback.snd pV (etaK V K)
  have hP' : IsPullback (k ≫ g) pK p (etaK V K ≫ v) :=
    (IsPullback.of_hasPullback pV (etaK V K)).paste_horiz (IsPullback.of_hasPullback p v)
  let eK : Spec (CommRingCat.of K) ⟶ pullback pV (etaK V K) :=
    pullback.lift (etaK V K ≫ eV) (𝟙 _) (by simp [heV])
  have heK : eK ≫ k = etaK V K ≫ eV := pullback.lift_fst _ _ _
  have heK' : eK ≫ pK = 𝟙 _ := pullback.lift_snd _ _ _
  let q : pullback pV (etaK V K) ⟶ HU := hP.lift (k ≫ g) (pK ≫ w)
    (by rw [hP'.w, Category.assoc, hw])
  have hq : q ≫ jH = k ≫ g := hP.lift_fst _ _ _
  have hjH : Mono jH := MorphismProperty.of_isPullback (P := .monomorphisms _) hP.flip
    (inferInstanceAs (Mono j))
  have heq : eK ≫ q = w ≫ eU := by
    rw [← cancel_mono jH, Category.assoc, hq, ← Category.assoc, heK, Category.assoc, heV',
      Category.assoc, heU, ← Category.assoc w, hw, Category.assoc]
  obtain ⟨c, hc'⟩ := exists_gen_germ V K pV eV inferInstance inferInstance heV eK heK hL
    (fun i ↦ g ≫ φ i) ε (fun i ↦ q ≫ jH ≫ φ i)
    (funext fun i ↦ by rw [← Category.assoc, hq, Category.assoc])
    (fun i ↦ v ≫ e ≫ φ i) (funext fun i ↦ by rw [← Category.assoc, ← heV', Category.assoc])
    (LB.pullGen L _ _ t q) (LB.pullGen L _ _ ρ v) (DVR.pullGen_isGen _ _ _ _ ht _)
    (DVR.pullGen_isGen _ _ _ _ hρ _) (corr_of_val hL fun y J hJ ↦ by
      have := val_corr hJ hc w
      rw [val_pull hJ, val_pull hJ] at this
      rw [val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
        heq, ← hw, this])
  have hpη : p (genericPoint H) = genericPoint S := by
    have : Surjective p := ⟨fun s ↦ ⟨e s, by rw [← Scheme.Hom.comp_apply, he]; rfl⟩⟩
    have h := (genericPoint_spec H).image p.continuous
    rw [Set.image_univ, p.surjective.range_eq, closure_univ] at h
    exact h.eq (genericPoint_spec S)
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback hP' (genericPoint H)
    (IsLocalRing.closedPoint K) (hpη.trans (hpt _).symm)
  obtain ⟨y, hyx, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback p v) x
    (IsLocalRing.closedPoint V) (Scheme.fromSpecStalk_closedPoint).symm
  have : Nonempty (LB.wchart L φ a) := ⟨⟨_, hxa⟩⟩
  have hzA : (k ≫ g) z ∈ A := hz ▸ genericPoint_mem_opens A
  have hza : (k ≫ g) z ∈ LB.wchart L φ a := hz ▸ genericPoint_mem_opens _
  have hkz : k z ∈ LB.wchart L (fun i ↦ g ≫ φ i) a := (wchart_comp L g φ a).ge hza
  have hqz : q z ∈ LB.wchart L (fun i ↦ jH ≫ φ i) a :=
    (wchart_comp L jH φ a).ge (show (q ≫ jH) z ∈ LB.wchart L φ a from hq ▸ hza)
  have hy : y ∈ LB.wchart L (fun i ↦ g ≫ φ i) a :=
    (wchart_comp L g φ a).ge (show g y ∈ LB.wchart L φ a from
      (congrArg (· ∈ LB.wchart L φ a) hyx).mpr hxa)
  have hm : (𝟙 _ : pullback pV (etaK V K) ⟶ _) z ∈
      LB.wchart L (fun i ↦ q ≫ jH ≫ φ i) a := (wchart_comp L q (fun i ↦ jH ≫ φ i) a).ge hqz
  have hgm : gm k z (LB.wchart L (fun i ↦ g ≫ φ i) a) (c.s a) = gm (k ≫ g) z A τ := by
    rw [← hq, hτ _ q z (show (q ≫ jH) z ∈ A from hq ▸ hzA)]
    exact (hc' z a hkz).trans ((gm_res _ z _ hm _).trans ((gm_pull _ _ z _ hqz _).trans
      (by rw [Category.id_comp]; rfl)))
  rw [← hyx]
  constructor
  · refine mem_range_of_preimmersion g k z hz y A _ _ hy (LB.ts c a).val ?_
    rw [gs_unit _ _ _ hkz, gs_unit _ _ _ hzA]
    exact congrArg Units.val hgm
  · refine mem_range_of_preimmersion g k z hz y A _ _ hy (LB.ts c a)⁻¹.val ?_
    rw [gs_unit _ _ _ hkz, gs_unit _ _ _ hzA, map_inv, map_inv]
    exact congrArg (fun u ↦ Units.val u⁻¹) hgm

theorem unit_ext_of_isOpenImmersion {H Y : Scheme.{0}} [IsIntegral H] (j : Y ⟶ H)
    [IsOpenImmersion j] [Nonempty Y] {O : H.Opens} {u v : Γ(H, O)ˣ}
    (h : ∀ y, j y ∈ O → gm j y O u = gm j y O v) : u = v := by
  have : pullU j O u = pullU j O v := unit_ext fun y hy ↦ by
    rw [gm_pull (𝟙 Y) j y O hy, gm_pull (𝟙 Y) j y O hy, Category.id_comp, h y hy]
  refine Units.ext (GlobalTheory.PrimeSection.appLE_injective j (U := O) rfl ?_)
  rw [← Scheme.Hom.app_eq_appLE]
  exact congrArg Units.val this

theorem existsUnique_gen_extend :
    ∀ (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S], Geo.Tor.IsNormalScheme S → ∀ (U H HU X : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H) (pU : HU ⟶ U) (eU : U ⟶ HU), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → IsPullback jH pU p j → eU ≫ jH = j ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => jH ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c jH = t := by
  intro S _ _ hS U H HU X _ j _ p e jH pU eU hsm hgi he hP heU L hL I _ φ ε t ρ ht hρ hc
  have := GlobalTheory.IsNormalScheme.of_pred hS
  have : IsIntegral H := GeometricallyIntegral.isIntegral_of_isLocallyNoetherian p
  have : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian p
  have : GlobalTheory.IsNormalScheme H := GlobalTheory.IsNormalScheme.of_pred
    (GlobalTheory.forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth p hS)
  have : IsOpenImmersion jH :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hP.flip inferInstance
  have : Nonempty HU := ⟨eU (Nonempty.some inferInstance)⟩
  have hW (a) (y : HU) : y ∈ LB.wchart L (fun i ↦ jH ≫ φ i) a ↔ jH y ∈ LB.wchart L φ a := by
    rw [wchart_comp]; rfl
  have hex (a : I → L.ι) : ∃ s : Γ(H, LB.wchart L φ a)ˣ, ∀ y, jH y ∈ LB.wchart L φ a →
      gm jH y _ s = gm (𝟙 HU) y (LB.wchart L (fun i ↦ jH ≫ φ i) a) (t.s a) := by
    by_cases hne : ∃ y, jH y ∈ LB.wchart L φ a
    swap
    · exact ⟨1, fun y hy ↦ (hne ⟨y, hy⟩).elim⟩
    obtain ⟨y₀, hy₀⟩ := hne
    let A : H.Opens := jH ''ᵁ LB.wchart L (fun i ↦ jH ≫ φ i) a
    have hA : A ≤ LB.wchart L φ a := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hW a y).1 hy
    have : Nonempty A := ⟨⟨_, y₀, (hW a y₀).2 hy₀, rfl⟩⟩
    have : Nonempty (LB.wchart L φ a) := ⟨⟨_, hy₀⟩⟩
    let τ : Γ(H, A)ˣ := Units.map (jH.appIso _).inv.hom.toMonoidHom (LB.ts t a)
    have hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z), jH (r z) ∈ A →
        gm (r ≫ jH) z A τ = gm r z (LB.wchart L (fun i ↦ jH ≫ φ i) a) (t.s a) := by
      intro Z r z hz
      rw [← gm_pull r jH z A hz, ← gm_res r z (jH.preimage_image_eq _).le hz]
      exact congrArg _ (Units.ext (congrArg (fun f ↦ f.hom (LB.ts t a).val)
        (jH.appIso_inv_app (LB.wchart L (fun i ↦ jH ≫ φ i) a))))
    have hmem : ∀ x ∈ LB.wchart L φ a, Order.coheight x = 1 →
        H.germToFunctionField A τ.val ∈ (algebraMap (H.presheaf.stalk x) H.functionField).range ∧
        H.germToFunctionField A (τ⁻¹).val ∈
          (algebraMap (H.presheaf.stalk x) H.functionField).range := fun x hx h1 ↦ by
      by_cases hxU : p x ∈ Set.range j
      · obtain ⟨u, hu⟩ := hxU
        obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hP x u hu.symm
        have : jH y ∈ A := ⟨y, (hW a y).2 hx, rfl⟩
        exact ⟨germToFunctionField_mem_range_stalk A _ this,
          germToFunctionField_mem_range_stalk A _ this⟩
      · exact mem_range_of_notMem he hP heU hL ht hρ hc x h1 hxU a hx A τ hτ
    obtain ⟨s₁, h₁⟩ := exists_germToFunctionField_eq_of_coheight_eq_one _ _
      fun x hx h1 ↦ (hmem x hx h1).1
    obtain ⟨s₂, h₂⟩ := exists_germToFunctionField_eq_of_coheight_eq_one _ _
      fun x hx h1 ↦ (hmem x hx h1).2
    have h₁₂ : s₁ * s₂ = 1 := H.germToFunctionField_injective _ (by
      rw [map_mul, h₁, h₂, ← map_mul, Units.mul_inv, map_one, map_one])
    let s : Γ(H, LB.wchart L φ a)ˣ := ⟨s₁, s₂, h₁₂, (mul_comm _ _).trans h₁₂⟩
    have hs : res hA s = τ := Units.ext (H.germToFunctionField_injective A
      ((germToFunctionField_res hA s₁).trans h₁))
    refine ⟨s, fun y hy ↦ ?_⟩
    have hyA : jH y ∈ A := ⟨y, (hW a y).2 hy, rfl⟩
    rw [← gm_res jH y hA hyA, hs, ← hτ _ (𝟙 HU) y hyA, Category.id_comp]
  choose s hs using hex
  have hpull (c : LB.Gen (LB.LinComb L φ ε)) (a) (y) (hy : jH y ∈ LB.wchart L φ a) :
      gm (𝟙 HU) y (LB.wchart L (fun i ↦ jH ≫ φ i) a) ((LB.pullGen L _ _ c jH).s a) =
        gm jH y (LB.wchart L φ a) (c.s a) :=
    (gm_res _ y _ ((hW a y).2 hy) _).trans ((gm_pull _ _ y _ hy _).trans
      (by rw [Category.id_comp]; rfl))
  refine ⟨⟨s⟩, ⟨fun a b ↦ unit_ext_of_isOpenImmersion jH fun y hy ↦ ?_, ?_⟩, ?_⟩
  · have := gen_trans ht (𝟙 HU) y ((hW a y).2 hy.1) ((hW b y).2 hy.2)
    rw [← hs a y hy.1, ← hs b y hy.2] at this
    refine (gm_res jH y _ hy _).trans (this.trans (Eq.symm ((map_mul _ _ _).trans ?_)))
    refine congrArg₂ (· * ·) ((gm_linComb L φ ε jH y a b hy.1 hy.2).trans ?_) (gm_res jH y _ hy _)
    simp only [trF, Category.id_comp]
  · refine congrArg LB.Gen.mk (funext fun a ↦ unit_ext fun y hy ↦ ?_)
    exact (hpull ⟨s⟩ a y ((hW a y).1 hy)).trans (hs a y ((hW a y).1 hy))
  · rintro ⟨c⟩ ⟨-, rfl⟩
    refine congrArg LB.Gen.mk (funext fun a ↦ unit_ext_of_isOpenImmersion jH fun y hy ↦ ?_)
    exact (hpull ⟨c⟩ a y hy).symm.trans (hs a y hy).symm

end GlobalTheory.GenExtendNormal
