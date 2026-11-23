import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomEqOneOfNilpotent
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsPullbackCompIsoMonHom
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPushoutQuotientMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsMonHomSplitTorusOfSqEqBot

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusLift

section General

variable {S S' S'' : Scheme.{0}}

theorem map_left_fst (p : S' ⟶ S) {V W : Over S} (f : V ⟶ W) :
    ((Over.pullback p).map f).left ≫ pullback.fst W.hom p = pullback.fst V.hom p ≫ f.left := by
  simp only [Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

theorem hom_ext_fst (p : S' ⟶ S) {Z : Over S'} {W : Over S} {a b : Z ⟶ (Over.pullback p).obj W}
    (h : a.left ≫ pullback.fst W.hom p = b.left ≫ pullback.fst W.hom p) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext h
  have ha := Over.w a
  have hb := Over.w b
  simp only [Over.pullback_obj_hom] at ha hb
  simp [ha, hb]

theorem map_eq_iff {s : S'' ⟶ S'} {p : S' ⟶ S} {q : S'' ⟶ S} (h : q = s ≫ p) {V W : Over S}
    (f g : V ⟶ W) : (Over.pullback q).map f = (Over.pullback q).map g ↔
      (Over.pullback s).map ((Over.pullback p).map f) =
        (Over.pullback s).map ((Over.pullback p).map g) := by
  subst h
  constructor
  · intro hfg
    have h1 := (Over.pullbackComp s p).hom.naturality f
    have h2 := (Over.pullbackComp s p).hom.naturality g
    simp only [Functor.comp_map] at h1 h2
    apply (cancel_epi ((Over.pullbackComp s p).hom.app V)).1
    rw [← h1, ← h2, hfg]
  · intro hfg
    have h1 := (Over.pullbackComp s p).inv.naturality f
    have h2 := (Over.pullbackComp s p).inv.naturality g
    simp only [Functor.comp_map] at h1 h2
    apply (cancel_epi ((Over.pullbackComp s p).inv.app V)).1
    rw [← h1, ← h2, hfg]

private theorem pullback_pullback_hom_ext {s : S'' ⟶ S'} {p : S' ⟶ S} {G : Over S} {Z : Over S''}
    {a b : Z ⟶ (Over.pullback s).obj ((Over.pullback p).obj G)}
    (h : a.left ≫ pullback.fst _ s ≫ pullback.fst G.hom p = b.left ≫ pullback.fst _ s ≫ pullback.fst G.hom p) :
    a = b := by
  apply hom_ext_fst
  apply pullback.hom_ext
  · simpa using h
  · have ha := Over.w a
    have hb := Over.w b
    simp only [Over.pullback_obj_hom] at ha hb
    simp only [Category.assoc, Over.pullback_obj_left, Over.pullback_obj_hom] at *
    rw [pullback.condition, reassoc_of% ha, reassoc_of% hb]

private theorem pullbackComp_hom_fst_fst (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) :
    ((Over.pullbackComp s p).hom.app G).left ≫ pullback.fst _ s ≫ pullback.fst G.hom p =
      pullback.fst G.hom (s ≫ p) := by
  have h := congrArg (fun x => x.left) (conjugateEquiv_counit (Over.mapPullbackAdj (s ≫ p))
    ((Over.mapPullbackAdj s).comp (Over.mapPullbackAdj p)) (Over.mapComp s p).symm.hom G)
  simpa [Over.pullbackComp] using h

theorem isMonHom_pullbackComp (s : S'' ⟶ S') (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    IsMonHom (M := (Over.pullback (s ≫ p)).obj G)
      (N := (Over.pullback s).obj ((Over.pullback p).obj G))
      ((Over.pullbackComp s p).hom.app G) := by
  obtain ⟨e, he, hc⟩ := GlobalTheory.exists_pullback_comp_iso_monHom s p (s ≫ p) rfl G
  have : (Over.pullbackComp s p).hom.app G = e.hom := by
    apply pullback_pullback_hom_ext
    rw [hc, pullbackComp_hom_fst_fst]
  rw [this]
  exact he

private theorem isMonHom_iff_of_conj_iso {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' : C}
    [MonObj M] [MonObj M'] [MonObj N] [MonObj N'] (a : M ⟶ M') (b : N ⟶ N') [IsIso a] [IsIso b]
    (ha : IsMonHom a) (hb : IsMonHom b) (g : M ⟶ N) (g' : M' ⟶ N') (hg : g ≫ b = a ≫ g') :
    IsMonHom g ↔ IsMonHom g' := by
  constructor
  · intro h
    have e : g' = (asIso a).inv ≫ g ≫ b := by simp [hg]
    rw [e]
    infer_instance
  · intro h
    have e : g = a ≫ g' ≫ (asIso b).inv := by simp [← reassoc_of% hg]
    rw [e]
    infer_instance

theorem isMonHom_map_iff {s : S'' ⟶ S'} {p : S' ⟶ S} {q : S'' ⟶ S} (h : q = s ≫ p)
    {V W : Over S} [GrpObj V] [GrpObj W] (f : V ⟶ W) : IsMonHom ((Over.pullback q).map f) ↔
      IsMonHom ((Over.pullback s).map ((Over.pullback p).map f)) := by
  subst h
  exact isMonHom_iff_of_conj_iso _ _ (isMonHom_pullbackComp s p V) (isMonHom_pullbackComp s p W) _ _
    ((Over.pullbackComp s p).hom.naturality f)

theorem preimage_eq_top_of_surjective {X Y Z : Scheme.{0}} (i : X ⟶ Y) [Surjective i] (f : Y ⟶ Z)
    {U : Z.Opens} (h : (i ≫ f) ⁻¹ᵁ U = ⊤) : f ⁻¹ᵁ U = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := i.surjective y
  have hx : x ∈ (i ≫ f) ⁻¹ᵁ U := by rw [h]; trivial
  simpa using hx

end General

theorem surjective_specMap {A C : CommRingCat.{0}} (β : A ⟶ C) (hβ : Function.Surjective β)
    (h : IsNilpotent (RingHom.ker β.hom)) : Surjective (Spec.map β) := by
  obtain ⟨n, hn⟩ := h
  have hh : IsHomeomorph (PrimeSpectrum.comap β.hom) := by
    refine PrimeSpectrum.isHomeomorph_comap β.hom (fun x => ⟨1, one_pos, ?_⟩) ?_
    · obtain ⟨y, rfl⟩ := hβ x
      exact ⟨y, by simp⟩
    · intro x hx
      have hxn : x ^ n ∈ RingHom.ker β.hom ^ n := Ideal.pow_mem_pow hx n
      rw [hn, Ideal.zero_eq_bot, Ideal.mem_bot] at hxn
      exact mem_nilradical.2 ⟨n, hxn⟩
  exact ⟨hh.surjective⟩

theorem isAffine_splitTorus (A : Type) [CommRing A] (X : Type) [AddCommGroup X] :
    IsAffine (splitTorus (Spec (CommRingCat.of A)) X).left := by
  have := GlobalTheory.TorusNil.isIso_torusPt_of A X
  have : IsAffine (GlobalTheory.TorusNil.sp A (AddMonoidAlgebra A X)).left := by
    dsimp [GlobalTheory.TorusNil.sp]
    infer_instance
  exact IsAffine.of_isIso (inv (GlobalTheory.TorusNil.torusPt A X (AddMonoidAlgebra.of A X)).left)

theorem exists_lift {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [Smooth G.hom]
    (g : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        (splitTorus (Spec (CommRingCat.of A)) X) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G)
    {W : G.left.Opens} (hW : IsAffineOpen W) (hg : (g.left ≫ pullback.fst _ _) ⁻¹ᵁ W = ⊤) :
    ∃ f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, f.left ⁻¹ᵁ W = ⊤ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f = g := by
  have := isAffine_splitTorus A X
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)
  obtain ⟨f, hf⟩ := GlobalTheory.NilpotentLift.main A J hJ G (splitTorus (Spec (CommRingCat.of A)) X)
    (g.left ≫ pullback.fst _ _) (by
      have hw := Over.w g
      simp only [Over.pullback_obj_hom] at hw
      rw [Category.assoc, pullback.condition (f := G.hom), reassoc_of% hw]
      exact pullback.condition.symm) ⟨W, hW, hg⟩
  refine ⟨f, ?_, ?_⟩
  · apply preimage_eq_top_of_surjective
      (pullback.fst (splitTorus (Spec (CommRingCat.of A)) X).hom
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    rw [hf]
    exact hg
  · apply hom_ext_fst
    rw [map_left_fst, hf]

private theorem exists_factor_through_quotient_of_surjective {A : Type} [CommRing A] (J : Ideal A) {C : CommRingCat.{0}}
    (β : CommRingCat.of A ⟶ C) (hβ : Function.Surjective β) (hker : RingHom.ker β.hom = J) :
    ∃ (g0 : C ⟶ CommRingCat.of (A ⧸ J)) (d0 : CommRingCat.of (A ⧸ J) ⟶ C),
      β ≫ g0 = CommRingCat.ofHom (Ideal.Quotient.mk J) ∧
        CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ d0 = β := by
  subst hker
  let e := RingHom.quotientKerEquivOfSurjective (f := β.hom) hβ
  refine ⟨CommRingCat.ofHom e.symm.toRingHom, CommRingCat.ofHom e.toRingHom, ?_, ?_⟩
  · ext a
    change e.symm (β.hom a) = Ideal.Quotient.mk _ a
    rw [RingEquiv.symm_apply_eq]
    rfl
  · ext a
    rfl

private theorem pullback_map_eq_iff_and_isMonHom_iff {S S' S'' : Scheme.{0}} {p : S' ⟶ S} {q : S'' ⟶ S} (s : S'' ⟶ S')
    (t : S' ⟶ S'') (hq : q = s ≫ p) (hp : p = t ≫ q) {V W : Over S} [GrpObj V] [GrpObj W]
    (f g : V ⟶ W) :
    ((Over.pullback p).map f = (Over.pullback p).map g ↔
        (Over.pullback q).map f = (Over.pullback q).map g) ∧
      (IsMonHom ((Over.pullback p).map f) ↔ IsMonHom ((Over.pullback q).map f)) := by
  refine ⟨⟨fun h => (map_eq_iff hq f g).2 (by rw [h]), fun h => (map_eq_iff hp f g).2 (by rw [h])⟩,
    ⟨fun h => (isMonHom_map_iff hq f).2 (by infer_instance),
      fun h => (isMonHom_map_iff hp f).2 (by infer_instance)⟩⟩

private theorem preimage_eq_univ_of_pullback_map_eq {S S' : Scheme.{0}} (p : S' ⟶ S) [Surjective p] {V W : Over S}
    (f g : V ⟶ W) (h : (Over.pullback p).map f = (Over.pullback p).map g) (U : W.left.Opens)
    (hf : f.left ⁻¹ᵁ U = ⊤) : g.left ⁻¹ᵁ U = ⊤ := by
  apply preimage_eq_top_of_surjective (pullback.fst V.hom p)
  rw [← map_left_fst p g, ← h, map_left_fst p f, Scheme.Hom.comp_preimage, hf,
    Scheme.Hom.preimage_top]

private theorem exists_isMonHom_lift_of_isMonHom_baseChange (X : Type) [AddCommGroup X] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), J ^ (n + 1) = ⊥ →
      ∀ {C : CommRingCat.{0}} (β : CommRingCat.of A ⟶ C), Function.Surjective β →
      RingHom.ker β.hom = J → ∀ (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G]
        [Smooth G.hom] (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G),
        IsMonHom ((Over.pullback (Spec.map β)).map f) → ∀ W : G.left.Opens, IsAffineOpen W →
        f.left ⁻¹ᵁ W = ⊤ → ∃ f' : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom f' ∧
          (Over.pullback (Spec.map β)).map f' = (Over.pullback (Spec.map β)).map f := by
  induction n with
  | zero =>
    intro A _ _ J hJ C β hβ hker G _ _ _ f hf W hW hfW
    obtain ⟨g0, d0, hg0, hd0⟩ := exists_factor_through_quotient_of_surjective J β hβ hker
    have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) = Spec.map g0 ≫ Spec.map β := by
      rw [← hg0, Spec.map_comp]
    have hp : Spec.map β = Spec.map d0 ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) := by
      rw [← hd0, Spec.map_comp]
    have hJ2 : J ^ 2 = ⊥ := by
      rw [pow_one] at hJ
      rw [hJ, pow_two, Ideal.mul_bot]
    obtain ⟨f', hf'1, hf'2⟩ := GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot A J hJ2 X G f
      ((pullback_map_eq_iff_and_isMonHom_iff _ _ hq hp f f).2.1 hf)
    exact ⟨f', hf'1, (pullback_map_eq_iff_and_isMonHom_iff _ _ hq hp f' f).1.2 hf'2⟩
  | succ n ih =>
    intro A _ _ J hJ C β hβ hker G _ _ _ f hf W hW hfW
    obtain ⟨I, hIdef⟩ : ∃ I : Ideal A, I = J ^ (n + 1) := ⟨_, rfl⟩
    have hI2 : I ^ 2 = ⊥ := by
      rw [eq_bot_iff, ← hJ, hIdef, ← pow_mul]
      exact Ideal.pow_le_pow_right (by omega)
    have hIJ : I ≤ J := hIdef ▸ Ideal.pow_le_self (by omega)
    have hItop : I ≠ ⊤ := by
      intro h
      rw [h, pow_two, Ideal.top_mul] at hI2
      exact top_ne_bot hI2
    have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hItop
    have : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
    have hIker : I ≤ RingHom.ker β.hom := hker ▸ hIJ
    let β' : CommRingCat.of (A ⧸ I) ⟶ C :=
      CommRingCat.ofHom (Ideal.Quotient.lift I β.hom (fun a ha => (RingHom.mem_ker).1 (hIker ha)))
    have hββ : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫ β' = β := by
      ext a
      rfl
    have hβ' : Function.Surjective β' := by
      intro c
      obtain ⟨a, rfl⟩ := hβ c
      exact ⟨Ideal.Quotient.mk I a, rfl⟩
    have hker' : RingHom.ker β'.hom = J.map (Ideal.Quotient.mk I) := by
      simp only [β', CommRingCat.hom_ofHom]
      rw [← hker]
      exact Ideal.ker_quotient_lift _ hIker
    have hJ' : (J.map (Ideal.Quotient.mk I)) ^ (n + 1) = ⊥ := by
      rw [← Ideal.map_pow, ← hIdef, Ideal.map_quotient_self]
    have hSpec : Spec.map β = Spec.map β' ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
      rw [← hββ, Spec.map_comp]
    have hsurjβ' : Surjective (Spec.map β') :=
      surjective_specMap β' hβ' ⟨n + 1, by rw [hker', hJ', Ideal.zero_eq_bot]⟩
    have hInil : IsNilpotent I := ⟨2, by rw [hI2, Ideal.zero_eq_bot]⟩
    have : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G).hom := by
      show Smooth (pullback.snd G.hom _)
      infer_instance
    obtain ⟨e, he, -⟩ := GlobalTheory.splitTorus_baseChange (Spec (CommRingCat.of A))
      (Spec (CommRingCat.of (A ⧸ I))) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) X
    obtain ⟨f₁, hf₁def⟩ : ∃ f₁, f₁ = e.hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f := ⟨_, rfl⟩
    let W' : ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G).left.Opens :=
      pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) ⁻¹ᵁ W
    have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    have : IsClosedImmersion (pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) :=
      inferInstance
    have hW' : IsAffineOpen W' := hW.preimage _
    have hf₁W : f₁.left ⁻¹ᵁ W' = ⊤ := by
      have h1 : f₁.left ≫ pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) =
          (e.hom.left ≫ pullback.fst _ _) ≫ f.left := by
        rw [hf₁def, Over.comp_left, Category.assoc, map_left_fst, Category.assoc]
      change (f₁.left ≫ pullback.fst G.hom _) ⁻¹ᵁ W = ⊤
      rw [h1, Scheme.Hom.comp_preimage, hfW, Scheme.Hom.preimage_top]
    have hf₁ : IsMonHom ((Over.pullback (Spec.map β')).map f₁) := by
      have h2 : IsMonHom ((Over.pullback (Spec.map β')).map
          ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map f)) :=
        (isMonHom_map_iff hSpec f).1 hf
      rw [hf₁def, Functor.map_comp]
      infer_instance
    obtain ⟨f₂, hf₂, hf₂eq⟩ := ih (A ⧸ I) (J.map (Ideal.Quotient.mk I)) hJ' β' hβ' hker'
      ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).obj G) f₁ hf₁ W' hW' hf₁W
    have hf₂W : f₂.left ⁻¹ᵁ W' = ⊤ := preimage_eq_univ_of_pullback_map_eq (Spec.map β') f₁ f₂ hf₂eq.symm W' hf₁W
    obtain ⟨F, -, hF⟩ := exists_lift I hInil X G (e.inv ≫ f₂) hW (by
      change e.inv.left ⁻¹ᵁ (f₂.left ⁻¹ᵁ W') = ⊤
      rw [hf₂W]
      rfl)
    have hFmon : IsMonHom ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map F) := by
      rw [hF]
      infer_instance
    obtain ⟨F', hF'1, hF'2⟩ := GlobalTheory.exists_isMonHom_splitTorus_of_sq_eq_bot A I hI2 X G F hFmon
    refine ⟨F', hF'1, ?_⟩
    rw [map_eq_iff hSpec, hF'2, hF, Functor.map_comp, hf₂eq, hf₁def, Functor.map_comp,
      ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

theorem exists_correction {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] : IsNilpotent J → IsLocalRing A → ∀ {C : CommRingCat.{0}}
      (β : CommRingCat.of A ⟶ C), Function.Surjective β → RingHom.ker β.hom = J →
      ∀ (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
        (f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G),
        IsMonHom ((Over.pullback (Spec.map β)).map f) → ∀ W : G.left.Opens, IsAffineOpen W →
        f.left ⁻¹ᵁ W = ⊤ → ∃ f' : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom f' ∧
          (Over.pullback (Spec.map β)).map f' = (Over.pullback (Spec.map β)).map f := by
  intro _ hloc C β hβ hker G _ _ _ f hf W hW hfW
  obtain ⟨n, hn⟩ := hJ
  cases n with
  | zero =>
    exfalso
    rw [pow_zero, Ideal.one_eq_top, Ideal.zero_eq_bot] at hn
    exact top_ne_bot hn
  | succ n =>
    exact exists_isMonHom_lift_of_isMonHom_baseChange X n A J (by rw [hn, Ideal.zero_eq_bot]) β hβ hker G f hf W hW hfW

theorem exists_affineOpen {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (G : Over (Spec (CommRingCat.of A)))
    (W : (pullback G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).Opens)
    (hW : IsAffineOpen W) : ∃ U : G.left.Opens, IsAffineOpen U ∧
      pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) ⁻¹ᵁ U = W := by
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    surjective_specMap _ Ideal.Quotient.mk_surjective (by simpa using hJ)
  let i := pullback.fst G.hom (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion i := inferInstanceAs (IsClosedImmersion (pullback.fst _ _))
  have hemb : Topology.IsClosedEmbedding i.base := i.isClosedEmbedding
  have hbij : Function.Bijective i.base := ⟨hemb.injective, i.surjective⟩
  have hopen : IsOpen (i.base '' (W : Set _)) := by
    rw [← compl_compl (i.base '' (W : Set _)), ← Set.image_compl_eq hbij]
    exact (hemb.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl
  let U : G.left.Opens := ⟨_, hopen⟩
  have hU : i ⁻¹ᵁ U = W := by
    ext x
    change i.base x ∈ i.base '' (W : Set _) ↔ x ∈ W
    exact hemb.injective.mem_set_image
  refine ⟨U, ?_, hU⟩
  have hW' : IsAffineOpen (i ⁻¹ᵁ U) := hU ▸ hW
  have : IsAffine (pullback (U.ι ≫ G.hom) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) := by
    have : IsAffine (i ⁻¹ᵁ U) := hW'
    exact IsAffine.of_isIso ((pullbackRightPullbackFstIso G.hom _ U.ι).inv ≫
      (pullbackSymmetry _ _).hom ≫ (pullbackRestrictIsoRestrict i U).hom)
  exact GlobalTheory.isAffine_of_isAffine_pullback_quotient_of_isNilpotent A J hJ (Over.mk (U.ι ≫ G.hom)) this

theorem main : ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (i₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj (splitTorus (Spec (CommRingCat.of A)) X) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G), IsMonHom i₀ → (∃ W : ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G).left.Opens, IsAffineOpen W ∧ i₀.left ⁻¹ᵁ W = ⊤) → ∃! i : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom i ∧ (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map i = i₀ := by
  intro A _ _ J hJ X _ G _ _ _ i₀ hi₀ ⟨W, hW, hW0⟩
  obtain ⟨U, hU, hUW⟩ := exists_affineOpen J hJ G W hW
  obtain ⟨f, hfU, hf⟩ := exists_lift J hJ X G i₀ hU (by
    rw [Scheme.Hom.comp_preimage, hUW]
    exact hW0)
  obtain ⟨f', hf'1, hf'2⟩ := exists_correction J hJ X hJ inferInstance
    (CommRingCat.ofHom (Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective (by simp) G f
    (by rw [hf]; exact hi₀) U hU hfU
  refine ⟨f', ⟨hf'1, hf'2.trans hf⟩, ?_⟩
  rintro i ⟨hi1, hi2⟩
  open CategoryTheory.GrpObj in
  have hmon : IsMonHom (i * f'⁻¹) := by
    rw [Hom.mul_def]
    infer_instance
  open CategoryTheory.GrpObj in
  have hmap : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map (i * f'⁻¹) =
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map (toUnit _ ≫ η[G]) := by
    rw [Functor.map_mul, Functor.map_inv', hi2, hf'2, hf, mul_inv_cancel, ← Hom.one_def, Functor.map_one]
  open CategoryTheory.GrpObj in
  have key := GlobalTheory.splitTorus_hom_eq_one_of_nilpotent A J hJ X G (i * f'⁻¹) hmon hmap
  open CategoryTheory.GrpObj in
  rw [← Hom.one_def, mul_inv_eq_one] at key
  exact key

end GlobalTheory.TorusLift
