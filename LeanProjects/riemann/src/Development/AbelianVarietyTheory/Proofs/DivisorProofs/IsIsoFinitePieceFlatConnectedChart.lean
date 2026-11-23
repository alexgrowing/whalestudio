import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoOfFiniteEtaleOfExistsUniqueLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FlatChartDeg

theorem isIso_app_of_flat {X Y S T : Scheme.{0}} {p : X ⟶ S} {f : T ⟶ S} {g : Y ⟶ X} {q : Y ⟶ T}
    (H : IsPullback g q p f) [Flat f] [QuasiCompact p] [QuasiSeparated p]
    (hp : ∀ V : S.Opens, IsIso (p.app V)) (U : T.Opens) : IsIso (q.app U) := by
  refine GlobalTheory.ProperFunctions.isIso_app_of_isBasis q
    (fun V : {V : T.affineOpens // ∃ W : S.affineOpens, V.1 ≤ f ⁻¹ᵁ W.1} ↦ V.1.1) ?_ ?_ U
  · rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (a := x) (u := (U ⊓ f ⁻¹ᵁ W : T.Opens))
        ⟨hx, hxW⟩ (U ⊓ f ⁻¹ᵁ W).2
    exact ⟨V, ⟨⟨⟨V, hV⟩, ⟨W, hW⟩, fun y hy ↦ (hVU hy).2⟩, rfl⟩, hxV, fun y hy ↦ (hVU hy).1⟩
  · rintro ⟨V, W, hVW⟩
    have : IsAffine V.1 := V.2
    have : IsAffine W.1 := W.2
    have H1 := (isPullback_morphismRestrict q V.1).flip.paste_horiz H
    have hw : ((q ⁻¹ᵁ V.1).ι ≫ g) ≫ p = (q ∣_ V.1 ≫ f.resLE W.1 V.1 hVW) ≫ W.1.ι := by
      rw [H1.w, Category.assoc, Scheme.Hom.resLE_comp_ι]
    let H2 := (isPullback_morphismRestrict p W.1).flip
    have : IsIso (p ∣_ W.1).appTop := by
      rw [morphismRestrict_appTop]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hp (W.1.ι ''ᵁ ⊤)) (by rw [eqToHom_op]; exact Functor.map_isIso _ _)
    refine GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback (p := p ∣_ W.1) (f := f.resLE W.1 V.1 hVW)
      (g := H2.lift _ _ hw) (IsPullback.of_right ?_ (H2.lift_snd _ _ _) H2)
    rw [H2.lift_fst, Scheme.Hom.resLE_comp_ι]
    exact H1

theorem preconnectedSpace_of_surjective_appTop {Z T : Scheme.{0}} (r : Z ⟶ T) [PreconnectedSpace T]
    (hr : Function.Bijective r.appTop.hom) : PreconnectedSpace Z := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨e, he, hes⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z s hs
  obtain ⟨e, rfl⟩ := hr.2 e
  have he' : e * e = e := hr.1 (by rw [map_mul, he])
  have h1 : T.basicOpen e ⊓ T.basicOpen (1 - e) = ⊥ := by
    rw [← Scheme.basicOpen_mul, mul_sub, _root_.mul_one, he', sub_self, Scheme.basicOpen_zero]
  have h2 : T.basicOpen e ⊔ T.basicOpen (1 - e) = ⊤ := by
    refine top_le_iff.mp ?_
    have := T.basicOpen_add_le e (1 - e)
    rwa [add_sub_cancel, T.basicOpen_of_isUnit isUnit_one] at this
  have hcl : IsClopen (T.basicOpen e : Set T) := by
    refine ⟨⟨?_⟩, (T.basicOpen e).2⟩
    have : (T.basicOpen e : Set T)ᶜ = T.basicOpen (1 - e) := by
      ext x
      constructor
      · intro hx
        have : x ∈ T.basicOpen e ⊔ T.basicOpen (1 - e) := by rw [h2]; trivial
        exact (TopologicalSpace.Opens.mem_sup.mp this).resolve_left hx
      · intro hx hx'
        have : x ∈ T.basicOpen e ⊓ T.basicOpen (1 - e) := ⟨hx', hx⟩
        rw [h1] at this
        exact this
    rw [this]
    exact (T.basicOpen (1 - e)).2
  have h3 : s = r ⁻¹' (T.basicOpen e : Set T) := by
    rw [← hes]
    exact congrArg (fun O : Z.Opens => (O : Set Z)) (Scheme.preimage_basicOpen_top r e).symm
  rcases isClopen_iff.mp hcl with h | h
  · left; rw [h3, h, Set.preimage_empty]
  · right; rw [h3, h, Set.preimage_univ]

theorem isIso_of_isAffineHom {Z T : Scheme.{0}} (f : Z ⟶ T) [IsAffineHom f] (hf : ∀ V : T.Opens, IsIso (f.app V)) :
    IsIso f := by
  rw [← MorphismProperty.isomorphisms.iff, IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    _ (iSup_affineOpens_eq_top T)]
  intro V
  have : IsAffine V.1 := V.2
  have : IsAffine (f ⁻¹ᵁ V.1) := V.2.preimage f
  have : IsIso (f ∣_ V.1).appTop := by
    rw [morphismRestrict_appTop]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (hf (V.1.ι ''ᵁ ⊤)) (by rw [eqToHom_op]; exact Functor.map_isIso _ _)
  refine (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme) (arrowIsoSpecΓOfIsAffine _)).2 ?_
  exact inferInstanceAs (IsIso (Spec.map (f ∣_ V.1).appTop))

theorem flat_affineSpace (S : Scheme.{0}) (n : ℕ) : Flat (𝔸(Fin n; S) ↘ S) := by
  have hF : MorphismProperty.IsStableUnderBaseChange @Flat.{0} := inferInstance
  refine hF.of_isPullback (IsPullback.of_hasPullback _ _).flip ?_
  have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
  have : Flat (Spec.map (CommRingCat.ofHom (MvPolynomial.C : ULift.{0} ℤ →+* MvPolynomial (Fin n) (ULift.{0} ℤ)))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2
      ((RingHom.flat_algebraMap_iff (R := ULift ℤ) (S := MvPolynomial (Fin n) (ULift ℤ))).2 inferInstance)
  rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C))]
  infer_instance

theorem exists_geometricPoint (Z : Scheme.{0}) (z : Z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (s : Sp Ω ⟶ Z), ∀ y, s y = z := by
  refine ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z)))) ≫
      Z.fromSpecResidueField z, fun y => ?_⟩
  rw [Scheme.Hom.comp_apply]
  exact Scheme.fromSpecResidueField_apply _ _

theorem isIso_finite_piece : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S X : Scheme.{0}) (π : S ⟶ Sp R) (U : Over (Sp R)) (a : X ⟶ U.left) (b : X ⟶ S) (g : ℕ) (τ : U.left ⟶ 𝔸(Fin g; Sp R)) (c : X ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) π), IsProper π → Surjective π → Function.Bijective π.appTop.hom → LocallyOfFiniteType U.hom → IsSeparated U.hom → IsProper a → (∀ V : U.left.Opens, Function.Bijective (a.app V).hom) → τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom → c ≫ pullback.fst _ _ = a ≫ τ → c ≫ pullback.snd _ _ = b → Etale c → ∀ x : U.left, U.hom x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ b = p' ≫ b → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ U.hom = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ b = s) → ∀ (T : Scheme.{0}) (h : T ⟶ 𝔸(Fin g; Sp R)) (W : (pullback τ h).Opens) (p : ↥(pullback τ h)), Flat h → PreconnectedSpace T → p ∈ W → pullback.fst τ h p = x → IsFinite (W.ι ≫ pullback.snd τ h) → (∀ w ∈ W, pullback.snd τ h w = pullback.snd τ h p → w = p) → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ T), Set.range t = {pullback.snd τ h p} → ∃! w : Sp Ω ⟶ W.toScheme, w ≫ W.ι ≫ pullback.snd τ h = t) → IsIso (W.ι ≫ pullback.snd τ h) := by
  intro R _ _ _ _ S X π U a b g τ c hπ hπs hπb hUft hUsep ha haO hτ hc1 hc2 hc x hx hinj hsurj T h W p hh hT hpW hpx hfin hone huniq
  let α := 𝔸(Fin g; Sp R) ↘ Sp R
  have hbπ : b ≫ π = a ≫ τ ≫ α := by
    rw [← hc2, Category.assoc, ← pullback.condition, ← Category.assoc, hc1, Category.assoc]
  let s₁ := pullback.fst π (h ≫ α)
  let s₂ := pullback.snd π (h ≫ α)
  have HS : IsPullback s₁ s₂ π (h ≫ α) := .of_hasPullback _ _
  let m : pullback π (h ≫ α) ⟶ pullback α π := pullback.lift (s₂ ≫ h) s₁ (by rw [Category.assoc, HS.w])
  have Hm : IsPullback m s₂ (pullback.fst α π) h := by
    refine IsPullback.of_right (h₁₂ := pullback.snd α π) (v₁₃ := π) (h₂₂ := α) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback α π).flip
    rw [pullback.lift_snd]
    exact HS
  let x₁ := pullback.fst a (pullback.fst τ h)
  let x₂ := pullback.snd a (pullback.fst τ h)
  have HX : IsPullback x₁ x₂ a (pullback.fst τ h) := .of_hasPullback _ _
  have HX' : IsPullback x₁ (x₂ ≫ pullback.snd τ h) (a ≫ τ) h := HX.paste_vert (.of_hasPullback τ h)
  let n : pullback a (pullback.fst τ h) ⟶ pullback π (h ≫ α) := pullback.lift (x₁ ≫ b) (x₂ ≫ pullback.snd τ h) (by
    rw [Category.assoc, hbπ, ← Category.assoc a, ← Category.assoc x₁, HX'.w, Category.assoc])
  have hn1 : n ≫ s₁ = x₁ ≫ b := pullback.lift_fst _ _ _
  have hn2 : n ≫ s₂ = x₂ ≫ pullback.snd τ h := pullback.lift_snd _ _ _
  have Hn : IsPullback x₁ n c m := by
    refine IsPullback.of_bot (v₂₁ := s₂) (v₂₂ := pullback.fst α π) (h₃₁ := h) ?_ ?_ Hm
    · rw [hn2, hc1]
      exact HX'
    · apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hc1, pullback.lift_fst, HX'.w, ← hn2, Category.assoc]
      · rw [Category.assoc, Category.assoc, hc2, pullback.lift_snd, hn1]
  have : Etale n := MorphismProperty.of_isPullback Hn hc
  let w₁ := pullback.fst x₂ W.ι
  let w₂ := pullback.snd x₂ W.ι
  have HW₀ : IsPullback w₁ w₂ x₂ W.ι := .of_hasPullback _ _
  have HW : IsPullback (w₁ ≫ x₁) w₂ a (W.ι ≫ pullback.fst τ h) := HW₀.paste_horiz HX
  have hq1 : (w₁ ≫ n) ≫ s₁ = (w₁ ≫ x₁) ≫ b := by rw [Category.assoc, hn1, Category.assoc]
  have hq2 : (w₁ ≫ n) ≫ s₂ = w₂ ≫ W.ι ≫ pullback.snd τ h := by
    rw [Category.assoc, hn2, ← Category.assoc, HW₀.w, Category.assoc]
  have hqe : Etale (w₁ ≫ n) := inferInstance
  have : IsProper w₂ := MorphismProperty.of_isPullback HW ha
  have : IsProper s₂ := MorphismProperty.of_isPullback HS hπ
  have : IsProper ((w₁ ≫ n) ≫ s₂) := by rw [hq2]; infer_instance
  have : IsProper (w₁ ≫ n) := IsProper.of_comp _ s₂
  have := GlobalTheory.TangentCrit.locallyQuasiFinite_of_formallyUnramified (w₁ ≫ n)
  have hqf : IsFinite (w₁ ≫ n) := IsFinite.of_isProper_of_locallyQuasiFinite _
  have : Flat α := flat_affineSpace _ _
  have hs₂ := GlobalTheory.Mum.app_bijective_of_flat_baseChange R S T _ π (h ≫ α) s₂ s₁ inferInstance inferInstance hπb
    inferInstance HS.flip
  have hconn := preconnectedSpace_of_surjective_appTop s₂ (hs₂ ⊤)
  have hs₂s : Surjective s₂ := MorphismProperty.of_isPullback HS hπs
  obtain ⟨z, hz⟩ := s₂.surjective (pullback.snd τ h p)
  obtain ⟨Ω, _, _, s, hs⟩ := exists_geometricPoint _ z
  obtain ⟨o⟩ : Nonempty (Sp Ω) := inferInstance
  have hrange : ∀ {Y : Scheme.{0}} (u : Sp Ω ⟶ Y) (y : Y), (∀ o', u o' = y) → Set.range u = {y} := by
    intro Y u y hu
    ext y'
    constructor
    · rintro ⟨o', rfl⟩
      exact hu o'
    · rintro rfl
      exact ⟨o, hu o⟩
  obtain ⟨w, hw, hwu⟩ := huniq Ω (s ≫ s₂) (hrange _ _ fun o' => by rw [Scheme.Hom.comp_apply, hs, hz])
  have hwp : ∀ o', W.ι (w o') = p := fun o' => by
    refine hone _ (w o').2 ?_
    change pullback.snd τ h (W.ι (w o')) = _
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply, hs, hz]
  have hξ : Set.range (w ≫ W.ι ≫ pullback.fst τ h) = {x} := hrange _ _ fun o' => by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hwp, hpx]
  obtain ⟨y, hy1, hy2⟩ := hsurj Ω (w ≫ W.ι ≫ pullback.fst τ h) (s ≫ s₁) hξ (by
    rw [← hτ, Category.assoc s, HS.w, ← Category.assoc s, ← hw]
    simp only [Category.assoc]
    rw [pullback.condition_assoc])
  have hiso : IsIso (w₁ ≫ n) := by
    refine GlobalTheory.Mum.isIso_of_finite_etale_of_existsUnique_lift _ _ _ hqf hqe hconn Ω s ⟨HW.lift y w hy1, ?_, ?_⟩
    · apply HS.hom_ext
      · rw [Category.assoc, hq1, HW.lift_fst_assoc, hy2]
      · rw [Category.assoc, hq2, HW.lift_snd_assoc, hw]
    · intro y' hy'
      have e1 : y' ≫ w₂ = w := hwu _ (by
        change (y' ≫ w₂) ≫ _ = _
        rw [Category.assoc, ← hq2, ← hy', Category.assoc y'])
      have e2 : (y' ≫ w₁ ≫ x₁) ≫ a = w ≫ W.ι ≫ pullback.fst τ h := by
        rw [Category.assoc, HW.w, ← e1, Category.assoc]
      apply HW.hom_ext
      · rw [HW.lift_fst]
        refine hinj Ω _ _ (by rw [e2]; exact hξ) (e2.trans hy1.symm) ?_
        rw [hy2, Category.assoc, ← hq1, ← hy', Category.assoc y']
      · rw [HW.lift_snd, e1]
  have hw₂ := isIso_app_of_flat HW (fun V => (ConcreteCategory.isIso_iff_bijective _).mpr (haO V))
  refine isIso_of_isAffineHom _ fun V => ?_
  have h1 : IsIso ((w₂ ≫ W.ι ≫ pullback.snd τ h).app V) := by
    rw [← hq2, Scheme.Hom.comp_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ ((ConcreteCategory.isIso_iff_bijective _).mpr (hs₂ V))
      (inferInstanceAs (IsIso ((w₁ ≫ n).app (s₂ ⁻¹ᵁ V))))
  rw [Scheme.Hom.comp_app] at h1
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (hw₂ ((W.ι ≫ pullback.snd τ h) ⁻¹ᵁ V)) h1

end GlobalTheory.Mum.FlatChartDeg
