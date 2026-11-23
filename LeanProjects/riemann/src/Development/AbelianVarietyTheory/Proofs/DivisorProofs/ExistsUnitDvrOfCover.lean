import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleIsoNormalisedAlongSectionRetract

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace Opposite GlobalTheory.GenericExtend GlobalTheory.PicGlue

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.DenseGlue

theorem exists_unit_dvr_of_cover {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] {X P Q H Z : Scheme.{0}}
    {f : H ⟶ Spec (.of V)} [Smooth f] [GeometricallyIntegral f] {k : Z ⟶ H} {fK : Z ⟶ Spec (.of K)}
    (hK : IsPullback k fK f (Spec.map (CommRingCat.ofHom (algebraMap V K))))
    {N : LB P} {J : Q ⟶ P} {φ : H ⟶ P} (hN : ∀ x : H, ∃ a, φ x ∈ N.U a) {ψ : Z ⟶ Q} (hψ : ψ ≫ J = k ≫ φ)
    (hW : ∀ A : P.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ J ⁻¹ᵁ A)
    {e : X ⟶ P} {l : Spec (.of V) ⟶ X} {eV : Spec (.of V) ⟶ H} (heV : eV ≫ φ = l ≫ e)
    (heV' : eV ≫ f = 𝟙 _) {eK : Spec (.of K) ⟶ Z}
    (heK : eK ≫ k = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ eV)
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N J τ) {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ z a, e (l (Spec.map (CommRingCat.ofHom (algebraMap V K)) z)) ∈ N.U a →
      gm (eK ≫ ψ) z (J ⁻¹ᵁ N.U a) (τ a) =
        gm (Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ l) z (e ⁻¹ᵁ N.U a) (ρ a)) (a : N.ι) :
    ∃ s : Γ(H, φ ⁻¹ᵁ N.U a)ˣ, res le_rfl (pullU k _ s) = res (hW _) (pullU ψ _ (τ a)) := by
  have hs := IsPullback.of_hasPullback f
    (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral_of_geometricallyIntegral hs
  set n := Spec.map (CommRingCat.ofHom (algebraMap V K)) with hn
  obtain ⟨a₀, h₀⟩ : ∃ a, e (l (IsLocalRing.closedPoint V)) ∈ N.U a := by
    have := hN (eV (IsLocalRing.closedPoint V))
    rwa [← Scheme.Hom.comp_apply, heV, Scheme.Hom.comp_apply] at this
  have hA : l ⁻¹ᵁ e ⁻¹ᵁ N.U a₀ ≤ eV ⁻¹ᵁ φ ⁻¹ᵁ N.U a₀ := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, heV]
  have hA' : n ⁻¹ᵁ l ⁻¹ᵁ e ⁻¹ᵁ N.U a₀ ≤ eK ⁻¹ᵁ k ⁻¹ᵁ φ ⁻¹ᵁ N.U a₀ := by
    rw [← Scheme.Hom.comp_preimage eK, heK]
    exact n.preimage_mono hA
  have hu : res le_rfl (pullU n _ (pullU l _ (ρ a₀))) =
      res hA' (pullU eK _ (res (hW _) (pullU ψ _ (τ a₀)))) := by
    refine unit_ext fun z hz ↦ ?_
    rw [gm_res_pullU (𝟙 _) n z le_rfl hz, gm_res_pullU (𝟙 _) eK z hA' hz, Category.id_comp,
      Category.id_comp, gm_pull n l z _ hz, gm_res_pullU eK ψ z (hW _) (hA' hz), hρ z a₀ hz]
  obtain ⟨s, ⟨hsu, -, hsr⟩, -⟩ := DvrModel.existsUnique_isUnit_appLE_eq hK hs
    (U := fun a ↦ φ ⁻¹ᵁ N.U a) (g := fun a b ↦ (pullU φ _ (N.g a b)).val)
    (W := fun a ↦ k ⁻¹ᵁ φ ⁻¹ᵁ N.U a) (fun _ ↦ rfl) hN
    (fun a b ↦ Units.isUnit _) (r := fun a ↦ (res (hW _) (pullU ψ _ (τ a))).val)
    (fun a b ↦ congrArg Units.val (hτ.res_pullU hψ hW a b))
    (fun a ↦ Units.isUnit _) heV' heK (a₀ := a₀) (A := l ⁻¹ᵁ e ⁻¹ᵁ N.U a₀) h₀ hA rfl hA'
    (pullU l _ (ρ a₀)).isUnit (congrArg Units.val hu)
  exact ⟨(hsu a).unit, Units.ext (hsr a)⟩

theorem extAt_of_cover {X U P : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {N : LB P}
    {eU : U ⟶ pullback p j} (w : eU ≫ pullback.fst p j = j ≫ e)
    (hπ : eU ≫ pullback.snd p j = 𝟙 U)
    {τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N _ τ)
    {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a))
    (y : P) (hN : ∀ x, p x ⤳ p y → ∃ a, x ∈ N.U a) (hx : Order.coheight (p y) = 1) (a : N.ι) (ha : y ∈ N.U a) :
    ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
      ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := by
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst p j)
  have := IsNormalScheme.of_isIso_stalkMap (pullback.fst p j)
  have := IsNormalScheme.isDiscreteValuationRing_stalk hx
  let V : Type := X.presheaf.stalk (p y)
  let K : Type := FractionRing V
  let l : Spec (.of V) ⟶ X := X.fromSpecStalk (p y)
  have : IsPreimmersion l := inferInstanceAs (IsPreimmersion (X.fromSpecStalk (p y)))
  have hl : Set.range l = {ξ | ξ ⤳ p y} := Scheme.range_fromSpecStalk
  let n : Spec (.of K) ⟶ Spec (.of V) := Spec.map (CommRingCat.ofHom (algebraMap V K))
  obtain ⟨κ, hκ⟩ := exists_lift j (n ≫ l) (by
    rintro _ ⟨o, rfl⟩
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    obtain ⟨v, rfl⟩ : ξ ∈ Set.range l := hl ▸ hξy
    have hv : n o ⤳ v := (PrimeSpectrum.le_iff_specializes (n o) v).1 (by
      intro c hc
      have hc' : algebraMap V K c ∈ o.asIdeal := hc
      rw [Ideal.eq_bot_of_prime o.asIdeal, Ideal.mem_bot,
        map_eq_zero_iff _ (IsFractionRing.injective V K)] at hc'
      rw [hc']
      exact Ideal.zero_mem _)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range (hv.map l.continuous) hξ)
  let φ := pullback.fst p l
  let f := pullback.snd p l
  let k := pullback.fst f n
  let fK := pullback.snd f n
  have hK : IsPullback k fK f n := .of_hasPullback f n
  have := DvrModel.isIntegral_of_geometricallyIntegral hK
  have := DvrModel.isIntegral hK
  have := DvrModel.isOpenImmersion_generic hK
  let ψ : pullback f n ⟶ pullback p j := pullback.lift (k ≫ φ) (fK ≫ κ) (by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hK.w, Category.assoc, Category.assoc,
      hκ])
  have hψ : ψ ≫ pullback.fst p j = k ≫ φ := pullback.lift_fst _ _ _
  have hψ' : ψ ≫ pullback.snd p j = fK ≫ κ := pullback.lift_snd _ _ _
  let eV : Spec (.of V) ⟶ pullback p l := pullback.lift (l ≫ e) (𝟙 _) (by simp [he])
  have heV : eV ≫ φ = l ≫ e := pullback.lift_fst _ _ _
  have heV' : eV ≫ f = 𝟙 _ := pullback.lift_snd _ _ _
  let eK : Spec (.of K) ⟶ pullback f n := pullback.lift (n ≫ eV) (𝟙 _) (by simp [heV'])
  have heK : eK ≫ k = n ≫ eV := pullback.lift_fst _ _ _
  have heK' : eK ≫ fK = 𝟙 _ := pullback.lift_snd _ _ _
  have hek : eK ≫ ψ = κ ≫ eU := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hψ, reassoc_of% heK, heV, Category.assoc, w, reassoc_of% hκ]
    · rw [Category.assoc, hψ', reassoc_of% heK', Category.assoc, hπ, Category.comp_id]
  have hW : ∀ A : P.Opens, k ⁻¹ᵁ φ ⁻¹ᵁ A ≤ ψ ⁻¹ᵁ pullback.fst p j ⁻¹ᵁ A := fun A ↦ by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hψ]
  obtain ⟨s, hu⟩ := exists_unit_dvr_of_cover hK (fun x ↦ hN _ (by
    have : φ x ∈ Set.range φ := ⟨x, rfl⟩
    rwa [Scheme.Pullback.range_fst, Set.mem_preimage, hl] at this)) hψ hW heV heV' heK hτ (ρ := ρ) (fun z a hz ↦ by
    rw [hek, hρ, hκ]
    rw [← Scheme.Hom.comp_apply κ, hκ]
    exact hz) a
  obtain ⟨h, hh⟩ : y ∈ Set.range φ := by
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, hl]
    exact specializes_rfl
  obtain ⟨z, hz⟩ : genericPoint (pullback p l :) ∈ k.opensRange :=
    have : Nonempty k.opensRange := ⟨⟨k (Nonempty.some inferInstance), _, rfl⟩⟩
    genericPoint_mem_opens _
  have hg : ∀ y, y ⤳ φ h → φ (k z) ⤳ y := fun y hy ↦ by
    obtain ⟨h', rfl⟩ : y ∈ Set.range φ := by
      rw [Scheme.Pullback.range_fst, Set.mem_preimage, hl]
      exact (hh ▸ hy).map p.continuous
    rw [hz]
    exact (genericPoint_specializes h').map φ.continuous
  have ha' : φ h ∈ N.U a := by rw [hh]; exact ha
  have hza : z ∈ k ⁻¹ᵁ φ ⁻¹ᵁ N.U a := (hg _ specializes_rfl).mem_open (N.U a).isOpen ha'
  suffices H : ExtAt (pullback.fst p j) (N.U a) (τ a).val (φ h) ∧
      ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val (φ h) by rwa [hh] at H
  exact ⟨extAt_of_generic _ φ k ψ hψ _ _ _ le_rfl (hW _) (appLE_inv_eq _ hu).1 z hza h ha' hg,
    extAt_of_generic _ φ k ψ hψ _ _ _ le_rfl (hW _) (appLE_inv_eq _ hu).2 z hza h ha' hg⟩

theorem exists_unit_ext {X U P : Scheme.{0}} [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (j : U ⟶ X) [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j]
    (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P} (he : e ≫ p = 𝟙 X) {N : LB P}
    {V : X.Opens} (hle : ∀ a, N.U a ≤ p ⁻¹ᵁ V) (hcov : ∀ x ∈ p ⁻¹ᵁ V, ∃ a, x ∈ N.U a)
    {eU : U ⟶ pullback p j} (w : eU ≫ pullback.fst p j = j ≫ e)
    (hπ : eU ≫ pullback.snd p j = 𝟙 U)
    {τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ} (hτ : Compat N _ τ)
    {ρ : ∀ a, Γ(X, e ⁻¹ᵁ N.U a)ˣ}
    (hρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ U) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a)) (a : N.ι) :
    ∃ σ : Γ(P, N.U a)ˣ, pullU (pullback.fst p j) _ σ = τ a := by
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have key : ∀ y ∈ N.U a, Order.coheight y ≤ 1 → y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := fun y ha h1 hy ↦ by
    refine extAt_of_cover j p he w hπ hτ hρ y
      (fun x hx ↦ hcov x (hx.mem_open V.isOpen (hle a ha)))
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  obtain ⟨s, hs⟩ := exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key y ha h1 hy).1
  obtain ⟨s', hs'⟩ := exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key y ha h1 hy).2
  have hm : s * s' = 1 := hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  exact ⟨⟨s, s', hm, (mul_comm _ _).trans hm⟩, Units.ext hs⟩

theorem gm_eq_of_pull {Q P : Scheme.{0}} (J : Q ⟶ P) [IsOpenImmersion J] (q : Q) {O O' : P.Opens}
    (h : J q ∈ O) (h' : J q ∈ O') {s : Γ(P, O)ˣ} {t : Γ(P, O')ˣ} (hst : gm J q O s = gm J q O' t) :
    gm (𝟙 P) (J q) O s = gm (𝟙 P) (J q) O' t := by
  rw [germ_pull_eq_stalkMap J q O h, germ_pull_eq_stalkMap J q O' h'] at hst
  exact Units.map_injective (f := (J.stalkMap q).hom.toMonoidHom)
    (ConcreteCategory.bijective_of_isIso (J.stalkMap q)).1 hst

theorem unit_eq_of_dense {X P : Scheme.{0}} [IsLocallyNoetherian X] [IsReduced X] (U : X.Opens)
    [IsDominant U.ι] (p : P ⟶ X) [Flat p] {O : P.Opens} {s t : Γ(P, O)ˣ}
    (h : ∀ x ∈ O, x ∈ p ⁻¹ᵁ U → gm (𝟙 P) x O s = gm (𝟙 P) x O t) : s = t := by
  have := IsSchemeTheoreticallyDominant.of_isDominant U.ι
  have hJ := (pullback.fst p U.ι).app_injective
  refine Units.map_injective (f := ((pullback.fst p U.ι).app O).hom.toMonoidHom) (hJ _) ?_
  change pullU _ _ _ = pullU _ _ _
  refine unit_ext fun q hq ↦ ?_
  have hq' : pullback.fst p U.ι q ∈ Set.range (pullback.fst p U.ι) := ⟨q, rfl⟩
  rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι] at hq'
  rw [gm_pull _ _ q _ hq, gm_pull _ _ q _ hq, Category.id_comp, germ_pull_eq_stalkMap _ q O hq,
    germ_pull_eq_stalkMap _ q O hq, h _ hq hq']

theorem gm_mul_of_dense {X P : Scheme.{0}} [IsLocallyNoetherian X] [IsReduced X] (U : X.Opens)
    [IsDominant U.ι] (p : P ⟶ X) [Flat p] {O₁ O₂ O₃ O₄ : P.Opens} (s₁ : Γ(P, O₁)ˣ) (s₂ : Γ(P, O₂)ˣ)
    (s₃ : Γ(P, O₃)ˣ) (s₄ : Γ(P, O₄)ˣ)
    (h : ∀ x ∈ p ⁻¹ᵁ U, x ∈ O₁ → x ∈ O₂ → x ∈ O₃ → x ∈ O₄ →
      gm (𝟙 P) x _ s₁ * gm (𝟙 P) x _ s₂ = gm (𝟙 P) x _ s₃ * gm (𝟙 P) x _ s₄)
    (x : P) (h₁ : x ∈ O₁) (h₂ : x ∈ O₂) (h₃ : x ∈ O₃) (h₄ : x ∈ O₄) :
    gm (𝟙 P) x _ s₁ * gm (𝟙 P) x _ s₂ = gm (𝟙 P) x _ s₃ * gm (𝟙 P) x _ s₄ := by
  let O := (O₁ ⊓ O₂) ⊓ (O₃ ⊓ O₄)
  have l₁ : O ≤ O₁ := inf_le_left.trans inf_le_left
  have l₂ : O ≤ O₂ := inf_le_left.trans inf_le_right
  have l₃ : O ≤ O₃ := inf_le_right.trans inf_le_left
  have l₄ : O ≤ O₄ := inf_le_right.trans inf_le_right
  have key : res l₁ s₁ * res l₂ s₂ = res l₃ s₃ * res l₄ s₄ := unit_eq_of_dense U p fun z hz hU ↦ by
    rw [map_mul, map_mul, gm_res _ z l₁ hz, gm_res _ z l₂ hz, gm_res _ z l₃ hz, gm_res _ z l₄ hz]
    exact h z hU (l₁ hz) (l₂ hz) (l₃ hz) (l₄ hz)
  have hx : x ∈ O := ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  have := congrArg (gm (𝟙 P) x O) key
  rwa [map_mul, map_mul, gm_res _ x l₁ hx, gm_res _ x l₂ hx, gm_res _ x l₃ hx, gm_res _ x l₄ hx] at this

theorem exists_cmp_ext {X P : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (U : X.Opens)
    [IsDominant U.ι] (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P} (he : e ≫ p = 𝟙 X)
    {V₁ V₂ : X.Opens} {L M : LB P} (hL : IsOn (p ⁻¹ᵁ V₁) L) (hM : IsOn (p ⁻¹ᵁ V₂) M)
    (u : Cmp (p ⁻¹ᵁ U) L M) (hu : IsoOn (p ⁻¹ᵁ U) L M u) (r : RigD e L) (r' : RigD e M)
    (hn : PicGlue.Norm e (p ⁻¹ᵁ U) L M u r r') (W : P.Opens) :
    ∃ w : Cmp W L M, ∀ x ∈ p ⁻¹ᵁ U, ∀ a b, x ∈ W → x ∈ L.U a → x ∈ M.U b →
      gm (𝟙 P) x _ (w a b) = gm (𝟙 P) x _ (u a b) := by
  let J := pullback.fst p U.ι
  have hJ : Set.range J = (p ⁻¹ᵁ U : P.Opens) := by
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]; rfl
  have hJU : ∀ q, J q ∈ p ⁻¹ᵁ U := fun q ↦ by
    rw [← SetLike.mem_coe, ← hJ]; exact ⟨q, rfl⟩
  let eU : U.toScheme ⟶ pullback p U.ι := pullback.lift (U.ι ≫ e) (𝟙 _) (by simp [he])
  have w : eU ≫ J = U.ι ≫ e := pullback.lift_fst _ _ _
  have hπ : eU ≫ pullback.snd p U.ι = 𝟙 _ := pullback.lift_snd _ _ _
  have hle : ∀ c : L.ι × M.ι, J ⁻¹ᵁ (LB.div L M).U c ≤ J ⁻¹ᵁ (p ⁻¹ᵁ U ⊓ (L.U c.1 ⊓ M.U c.2)) :=
    fun c q hq ↦ ⟨hJU q, hq⟩
  let τ : ∀ c, Γ(pullback p U.ι, J ⁻¹ᵁ (LB.div L M).U c)ˣ := fun c ↦ res (hle c) (pullU J _ (u c.1 c.2))
  have hτ : Compat (LB.div L M) J τ := fun Z s z c d hc hd ↦ by
    have hc' : (s ≫ J) z ∈ L.U c.1 ⊓ M.U c.2 := hc
    have hd' : (s ≫ J) z ∈ L.U d.1 ⊓ M.U d.2 := hd
    have hU : (s ≫ J) z ∈ p ⁻¹ᵁ U := hJU _
    rw [gm_res_pullU s J z (hle c) hc, gm_res_pullU s J z (hle d) hd]
    refine Eq.trans ?_ (congrArg (· * _) (gm_div M L (s ≫ J) z c d ⟨hc', hd'⟩)).symm
    have k := congrArg (Units.map ((s ≫ J).stalkMap z).hom.toMonoidHom)
      (hu _ hU c.1 d.1 c.2 d.2 hc'.1 hd'.1 hc'.2 hd'.2)
    rw [map_mul, map_mul, ← germ_pull_eq_stalkMap _ z (p ⁻¹ᵁ U ⊓ (L.U c.1 ⊓ M.U c.2)) ⟨hU, hc'⟩,
      ← germ_pull_eq_stalkMap _ z (M.U c.2 ⊓ M.U d.2) ⟨hc'.2, hd'.2⟩,
      ← germ_pull_eq_stalkMap _ z (L.U c.1 ⊓ L.U d.1) ⟨hc'.1, hd'.1⟩,
      ← germ_pull_eq_stalkMap _ z (p ⁻¹ᵁ U ⊓ (L.U d.1 ⊓ M.U d.2)) ⟨hU, hd'⟩] at k
    rw [mul_right_comm, ← k, mul_inv_cancel_right]
  have l₁ : ∀ c : L.ι × M.ι, e ⁻¹ᵁ (LB.div L M).U c ≤ e ⁻¹ᵁ L.U c.1 := fun c y hy ↦ hy.1
  have l₂ : ∀ c : L.ι × M.ι, e ⁻¹ᵁ (LB.div L M).U c ≤ e ⁻¹ᵁ M.U c.2 := fun c y hy ↦ hy.2
  let ρ : ∀ c, Γ(X, e ⁻¹ᵁ (LB.div L M).U c)ˣ := fun c ↦ res (l₁ c) (r c.1) * (res (l₂ c) (r' c.2))⁻¹
  have H := exists_unit_ext U.ι p he (N := LB.div L M) (V := V₁ ⊓ V₂)
    (fun c x hx ↦ ⟨hL.le _ hx.1, hM.le _ hx.2⟩) (fun x hx ↦ by
      obtain ⟨a, ha⟩ := hL.cov x hx.1
      obtain ⟨b, hb⟩ := hM.cov x hx.2
      exact ⟨(a, b), ha, hb⟩) w hπ hτ (ρ := ρ) fun Z κ z c hc ↦ by
      have hc' : (κ ≫ U.ι) z ∈ e ⁻¹ᵁ (LB.div L M).U c := hc
      have hw : J ((κ ≫ eU) z) = e ((κ ≫ U.ι) z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Category.assoc, w, Category.assoc]
      have hU : e ((κ ≫ U.ι) z) ∈ p ⁻¹ᵁ U := hw ▸ hJU _
      have hm : e ((κ ≫ U.ι) z) ∈ p ⁻¹ᵁ U ⊓ (L.U c.1 ⊓ M.U c.2) := ⟨hU, hc'⟩
      rw [gm_res_pullU (κ ≫ eU) J z (hle c) (show J ((κ ≫ eU) z) ∈ (LB.div L M).U c by rw [hw]; exact hc'), Category.assoc, w, ← Category.assoc,
        ← gm_pull (κ ≫ U.ι) e z _ hm, map_mul, map_inv, gm_res _ z (l₁ c) hc', gm_res _ z (l₂ c) hc',
        germ_pull_eq_stalkMap _ z _ hm, germ_pull_eq_stalkMap _ z _ (l₁ c hc'),
        germ_pull_eq_stalkMap _ z _ (l₂ c hc'), ← hn _ c.1 c.2 hU hc'.1 hc'.2, map_mul, mul_inv_cancel_right,
        gm_pull (𝟙 X) e ((κ ≫ U.ι) z) _ hm, Category.id_comp]
  choose σ hσ using H
  refine ⟨fun a b ↦ res inf_le_right (σ (a, b)), fun x hx a b hW ha hb ↦ ?_⟩
  obtain ⟨q, rfl⟩ : x ∈ Set.range J := by rw [hJ]; exact hx
  refine (gm_res (𝟙 P) (J q) (inf_le_right : W ⊓ (L.U a ⊓ M.U b) ≤ L.U a ⊓ M.U b) ⟨hW, ha, hb⟩ (σ (a, b))).trans ?_
  refine gm_eq_of_pull J q (O := L.U a ⊓ M.U b) (O' := p ⁻¹ᵁ U ⊓ (L.U a ⊓ M.U b)) ⟨ha, hb⟩ ⟨hx, ha, hb⟩ ?_
  have h₁ := gm_pull (𝟙 _) J q (L.U a ⊓ M.U b) ⟨ha, hb⟩ (σ (a, b))
  have h₂ := gm_res_pullU (𝟙 _) J q (hle (a, b)) ⟨ha, hb⟩ (u a b)
  rw [Category.id_comp] at h₁ h₂
  exact h₁.symm.trans ((congrArg (gm (𝟙 _) q _) (hσ (a, b))).trans h₂)

theorem exists_cmp_comp {P : Scheme.{0}} {D W₁ W₂ : P.Opens} {L M L₀ : LB P} (h₀ : IsOn D L₀)
    (v : Cmp W₁ L L₀) (v' : Cmp W₂ M L₀) (hv : IsoOn W₁ L L₀ v) (hv' : IsoOn W₂ M L₀ v')
    (h₁ : ∀ a, ∀ x ∈ D, x ∈ L.U a → x ∈ W₁) (h₂ : ∀ b, ∀ x ∈ D, x ∈ M.U b → x ∈ W₂)
    (s₁ : ∀ a, ∀ x ∈ L.U a, gm (𝟙 P) x _ (L.g a a) = 1) (s₂ : ∀ a, ∀ x ∈ M.U a, gm (𝟙 P) x _ (M.g a a) = 1) :
    ∃ u : Cmp D L M, ∀ x ∈ D, ∀ a b d, x ∈ L.U a → x ∈ M.U b → x ∈ L₀.U d →
      gm (𝟙 P) x _ (u a b) * gm (𝟙 P) x _ (v' b d) = gm (𝟙 P) x _ (v a d) := by
  have H : ∀ a b, ∃ u : Γ(P, D ⊓ (L.U a ⊓ M.U b))ˣ, ∀ x ∈ D, ∀ d, x ∈ L.U a → x ∈ M.U b → x ∈ L₀.U d →
      gm (𝟙 P) x _ u * gm (𝟙 P) x _ (v' b d) = gm (𝟙 P) x _ (v a d) := fun a b ↦ by
    let O : L₀.ι → P.Opens := fun d ↦ (D ⊓ (L.U a ⊓ M.U b)) ⊓ L₀.U d
    have l₁ : ∀ d, O d ≤ W₁ ⊓ (L.U a ⊓ L₀.U d) := fun d x hx ↦ ⟨h₁ a x hx.1.1 hx.1.2.1, hx.1.2.1, hx.2⟩
    have l₂ : ∀ d, O d ≤ W₂ ⊓ (M.U b ⊓ L₀.U d) := fun d x hx ↦ ⟨h₂ b x hx.1.1 hx.1.2.2, hx.1.2.2, hx.2⟩
    let t : ∀ d, Γ(P, O d)ˣ := fun d ↦ res (l₁ d) (v a d) * (res (l₂ d) (v' b d))⁻¹
    have ht : ∀ d, ∀ x ∈ O d, gm (𝟙 P) x _ (t d) = gm (𝟙 P) x _ (v a d) * (gm (𝟙 P) x _ (v' b d))⁻¹ :=
      fun d x hx ↦ by rw [map_mul, map_inv, gm_res _ x (l₁ d) hx, gm_res _ x (l₂ d) hx]
    obtain ⟨u, hu⟩ := glue_unit (D ⊓ (L.U a ⊓ M.U b)) O (fun _ ↦ inf_le_left) (fun x hx ↦ by
      obtain ⟨d, hd⟩ := h₀.cov x hx.1
      exact Opens.mem_iSup.2 ⟨d, hx, hd⟩) t fun d d' x hx ↦ by
        have k₁ := hv x (l₁ d hx.1).1 a a d d' hx.1.1.2.1 hx.1.1.2.1 hx.1.2 hx.2.2
        have k₂ := hv' x (l₂ d hx.1).1 b b d d' hx.1.1.2.2 hx.1.1.2.2 hx.1.2 hx.2.2
        rw [s₁ a x hx.1.1.2.1, one_mul] at k₁
        rw [s₂ b x hx.1.1.2.2, one_mul] at k₂
        rw [ht d x hx.1, ht d' x hx.2, ← k₁, ← k₂, mul_inv, mul_mul_mul_comm, mul_inv_cancel, mul_one]
    refine ⟨u, fun x hx d ha hb hd ↦ ?_⟩
    have hO : x ∈ O d := ⟨⟨hx, ha, hb⟩, hd⟩
    rw [← gm_res _ x (inf_le_left : O d ≤ _) hO, hu, ht d x hO, inv_mul_cancel_right]
  choose u hu using H
  exact ⟨u, fun x hx a b d ↦ hu a b x hx d⟩

theorem gm_self_of_isOn {P : Scheme.{0}} {W : P.Opens} {L : LB P} (hL : IsOn W L) (a : L.ι) (x : P)
    (hx : x ∈ L.U a) : gm (𝟙 P) x _ (L.g a a) = 1 :=
  mul_eq_left.1 (hL.coc x a a a hx hx hx)

theorem exists_cocycle {X P : Scheme.{0}} [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] [IsReduced X] (U : X.Opens)
    [IsDominant U.ι] (p : P ⟶ X) [Smooth p] [GeometricallyIntegral p] {e : X ⟶ P} (he : e ≫ p = 𝟙 X)
    {L₀ : LB P} (h₀ : IsOn (p ⁻¹ᵁ U) L₀) (r₀ : RigD e L₀) {Ix : Type} (V : Ix → X.Opens) (L : Ix → LB P)
    (hL : ∀ i, IsOn (p ⁻¹ᵁ V i) (L i)) (r : ∀ i, RigD e (L i)) (v : ∀ i, Cmp (p ⁻¹ᵁ (V i ⊓ U)) (L i) L₀)
    (hv : ∀ i, IsoOn _ (L i) L₀ (v i)) (hn : ∀ i, PicGlue.Norm e _ (L i) L₀ (v i) (r i) r₀) :
    ∃ w : ∀ i k, Cmp (p ⁻¹ᵁ V i ⊓ p ⁻¹ᵁ V k) (L i) (L k), (∀ i k, IsoOn _ (L i) (L k) (w i k)) ∧
      ∀ (i j k : Ix) (x : P) (a : (L i).ι) (b : (L j).ι) (c : (L k).ι), x ∈ (L i).U a → x ∈ (L j).U b →
        x ∈ (L k).U c → gm (𝟙 P) x _ (w i j a b) * gm (𝟙 P) x _ (w j k b c) = gm (𝟙 P) x _ (w i k a c) := by
  have hm : ∀ i a, ∀ x ∈ p ⁻¹ᵁ U, x ∈ (L i).U a → x ∈ p ⁻¹ᵁ (V i ⊓ U) := fun i a x hx ha ↦ ⟨(hL i).le a ha, hx⟩
  choose u hu using fun i k ↦ exists_cmp_comp h₀ (v i) (v k) (hv i) (hv k) (hm i) (hm k)
    (gm_self_of_isOn (hL i)) (gm_self_of_isOn (hL k))
  have hui : ∀ i k, IsoOn _ (L i) (L k) (u i k) := fun i k x hx a a' b b' ha ha' hb hb' ↦ by
    obtain ⟨d, hd⟩ := h₀.cov x hx
    have k₁ := hv i x (hm i a x hx ha) a a' d d ha ha' hd hd
    have k₂ := hv k x (hm k b x hx hb) b b' d d hb hb' hd hd
    rw [gm_self_of_isOn h₀ d x hd, mul_one] at k₁ k₂
    have e₁ := hu i k x hx a b d ha hb hd
    have e₂ := hu i k x hx a' b' d ha' hb' hd
    apply mul_right_cancel (b := gm (𝟙 P) x _ (v k b' d))
    rw [mul_assoc, ← k₂, e₁, mul_assoc, e₂, k₁]
  have hun : ∀ i k, PicGlue.Norm e _ (L i) (L k) (u i k) (r i) (r k) := fun i k y a b hy ha hb ↦ by
    obtain ⟨d, hd⟩ := h₀.cov _ hy
    have k₁ := hn i y a d (hm i a _ hy ha) ha hd
    have k₂ := hn k y b d (hm k b _ hy hb) hb hd
    have e₁ := congrArg (Units.map (e.stalkMap y).hom.toMonoidHom) (hu i k _ hy a b d ha hb hd)
    rw [map_mul, ← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ U ⊓ ((L i).U a ⊓ (L k).U b)) ⟨hy, ha, hb⟩,
      ← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ (V k ⊓ U) ⊓ ((L k).U b ⊓ L₀.U d)) ⟨hm k b _ hy hb, hb, hd⟩,
      ← germ_pull_eq_stalkMap e y (p ⁻¹ᵁ (V i ⊓ U) ⊓ ((L i).U a ⊓ L₀.U d)) ⟨hm i a _ hy ha, ha, hd⟩] at e₁
    rw [← k₁, ← k₂, ← e₁, mul_assoc]
  choose w hw using fun i k ↦ exists_cmp_ext U p he (hL i) (hL k) (u i k) (hui i k) (r i) (r k) (hun i k)
    (p ⁻¹ᵁ V i ⊓ p ⁻¹ᵁ V k)
  refine ⟨w, fun i k x hx a a' b b' ha ha' hb hb' ↦ ?_, fun i j k x a b c ha hb hc ↦ ?_⟩
  · refine gm_mul_of_dense U p _ _ _ _ (fun z hz h₁ h₂ h₃ h₄ ↦ ?_) x ⟨hx, ha, hb⟩ ⟨hb, hb'⟩ ⟨ha, ha'⟩
      ⟨hx, ha', hb'⟩
    rw [hw i k z hz a b h₁.1 h₁.2.1 h₁.2.2, hw i k z hz a' b' h₄.1 h₄.2.1 h₄.2.2]
    exact hui i k z hz a a' b b' h₃.1 h₃.2 h₂.1 h₂.2
  · have := gm_mul_of_dense U p (w i j a b) (w j k b c) (w i k a c) (1 : Γ(P, ⊤)ˣ) (fun z hz h₁ h₂ h₃ _ ↦ by
      obtain ⟨d, hd⟩ := h₀.cov z hz
      rw [map_one, mul_one, hw i j z hz a b h₁.1 h₁.2.1 h₁.2.2, hw j k z hz b c h₂.1 h₂.2.1 h₂.2.2,
        hw i k z hz a c h₃.1 h₃.2.1 h₃.2.2]
      apply mul_right_cancel (b := gm (𝟙 P) z _ (v k c d))
      rw [mul_assoc, hu j k z hz b c d h₂.2.1 h₂.2.2 hd, hu i j z hz a b d h₁.2.1 h₁.2.2 hd,
        hu i k z hz a c d h₃.2.1 h₃.2.2 hd]) x
      ⟨⟨(hL i).le a ha, (hL j).le b hb⟩, ha, hb⟩ ⟨⟨(hL j).le b hb, (hL k).le c hc⟩, hb, hc⟩
      ⟨⟨(hL i).le a ha, (hL k).le c hc⟩, ha, hc⟩ trivial
    rwa [map_one, mul_one] at this

end GlobalTheory.DenseGlue
