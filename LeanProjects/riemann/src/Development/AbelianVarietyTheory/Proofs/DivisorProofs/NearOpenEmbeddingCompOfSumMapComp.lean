import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomExtOfAgreeOnFibreDenseOpenSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleSpaceOfSmoothFieldOfConnectedSpace
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.DescFix

set_option backward.isDefEq.respectTransparency false

theorem smooth_of_comp_mono {W X G : Scheme.{0}} (m : W ⟶ X) (e : X ⟶ G) [Mono e] [hs : Smooth (m ≫ e)] : Smooth m := by
  have : IsPullback (𝟙 W) m (m ≫ e) e := IsPullback.of_horiz_isIso_mono ⟨by simp⟩
  exact MorphismProperty.of_isPullback (P := @Smooth) this hs

theorem smooth_mul {T : Scheme.{0}} (G : Over T) [GrpObj G] [Smooth G.hom] : Smooth (μ[G]).left := by
  let σ : G ⊗ G ≅ G ⊗ G :=
    { hom := lift (fst G G * snd G G) (snd G G)
      inv := lift (fst G G * (snd G G)⁻¹) (snd G G)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv]
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }
  have h : μ[G] = σ.hom ≫ fst G G := by
    simp [σ, Hom.mul_def]
  have h₁ : Smooth (fst G G).left := inferInstanceAs (Smooth (pullback.fst G.hom G.hom))
  have h₂ : IsIso σ.hom.left := inferInstanceAs (IsIso ((Over.forget T).mapIso σ).hom)
  rw [h, Over.comp_left]
  infer_instance

theorem isPreirreducible_fibre {X T : Scheme.{0}} (f : X ⟶ T) [Smooth f] [GeometricallyConnected f] (t : T) :
    IsPreirreducible (f ⁻¹' {t}) := by
  have : IrreducibleSpace (f.fiber t) :=
    GlobalTheory.irreducibleSpace_of_smooth_field_of_connectedSpace (T.residueField t) (f.fiber t) (f.fiberToSpecResidueField t)
      (inferInstanceAs (Smooth (pullback.snd _ _))) inferInstance
  rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
  exact (PreirreducibleSpace.isPreirreducible_univ).image _ (f.fiberι t).continuous.continuousOn

theorem eq_of_smooth_comp {W X T Y : Scheme.{0}} (p : X ⟶ T) [Smooth p] (hp : ∀ t : T, IsPreirreducible (p ⁻¹' {t}))
    (m : W ⟶ X) [Smooth m] [Surjective (m ≫ p)] (q : Y ⟶ T) [IsSeparated q] (f g : X ⟶ Y) (hfg : f ≫ q = g ≫ q)
    (h : m ≫ f = m ≫ g) : f = g := by
  let P : X.Opens := ⟨Set.range m, m.isOpenMap.isOpen_range⟩
  refine GlobalTheory.T.hom_ext_of_agree_on_fibreDense_open_smooth X T Y p q P (fun x => ?_) f g hfg ?_
  · obtain ⟨w, hw⟩ := (m ≫ p).surjective (p x)
    have := subset_closure_inter_of_isPreirreducible_of_isOpen (hp (p x)) P.2 ⟨m w, by simpa using hw, w, rfl⟩
    rw [Set.inter_comm] at this
    exact this rfl
  · let l : W ⟶ P.toScheme := IsOpenImmersion.lift P.ι m (by simp [P])
    have hl : l ≫ P.ι = m := IsOpenImmersion.lift_fac _ _ _
    have : Smooth (l ≫ P.ι) := by rw [hl]; infer_instance
    have : Smooth l := smooth_of_comp_mono l P.ι
    have : Surjective l := ⟨fun y => by
      obtain ⟨w, hw⟩ := y.2
      refine ⟨w, P.ι.isOpenEmbedding.injective ?_⟩
      rw [← Scheme.Hom.comp_apply, hl]
      exact hw⟩
    have : Epi l := Flat.epi_of_flat_of_surjective l
    rw [← cancel_epi l, ← Category.assoc, ← Category.assoc, hl, h]

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem isOpenImmersion_emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    IsOpenImmersion (Desc.emb N p hp).left := by
  have h₁ : IsPullback (Desc.toS N p hp) (pullback.snd N.U.hom (pullback.fst π π ≫ π)) (pullback.snd N.U.hom π) p := by
    refine IsPullback.of_right (h₁₂ := pullback.fst N.U.hom π) (h₂₂ := π) (v₁₃ := N.U.hom) ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback _ _)
    rw [hp, Desc.toS, pullback.lift_fst]
    exact IsPullback.of_hasPullback _ _
  have h₂ : IsPullback (Desc.toS N p hp) (Desc.embL N p hp) N.u (pullback.fst G.hom p) := by
    refine IsPullback.of_bot (v₂₁ := pullback.snd G.hom p) (v₂₂ := G.hom) (h₃₁ := p) ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback _ _)
    rw [N.u_over, Desc.embL, pullback.lift_snd]
    exact h₁
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) h₂ N.isOpen

theorem surjective_of_closedFibre [GrpObj G] [Surjective π] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens)
    (hV : ∀ z : (N.U ⊗ N.U).left, (N.U ⊗ N.U).hom z = closedPoint R → z ∈ V) :
    Surjective (V.ι ≫ (N.U ⊗ N.U).hom) := by
  have := N.smooth
  have : Smooth (N.U ⊗ N.U).hom := inferInstanceAs (Smooth (pullback.fst N.U.hom N.U.hom ≫ N.U.hom))
  obtain ⟨s, hs⟩ := π.surjective (closedPoint R)
  have he : (η[G]).left ≫ G.hom = 𝟙 S := Over.w η[G]
  have he' : G.hom ((η[G]).left s) = s := by
    rw [← Scheme.Hom.comp_apply, he]; rfl
  obtain ⟨x, hx⟩ := N.all ((η[G]).left s) (by rw [he', hs])
  have h₁ : N.U.hom (pullback.fst N.U.hom π x) = closedPoint R := by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, ← N.u_over, Scheme.Hom.comp_apply, hx, he', hs]
  let z : (N.U ⊗ N.U).left := (lift (𝟙 N.U) (𝟙 N.U)).left (pullback.fst N.U.hom π x)
  have hz : (N.U ⊗ N.U).hom z = closedPoint R := by
    rw [← h₁, ← Scheme.Hom.comp_apply, Over.w]
  let O : TopologicalSpace.Opens (PrimeSpectrum R) :=
    ⟨Set.range (V.ι ≫ (N.U ⊗ N.U).hom), (V.ι ≫ (N.U ⊗ N.U).hom).isOpenMap.isOpen_range⟩
  have hO : O = ⊤ := (closedPoint_mem_iff O).1 ⟨⟨z, hV z hz⟩, hz⟩
  exact ⟨fun t => (hO.ge (Set.mem_univ t) : t ∈ O)⟩

def toSq (N : Near π G) : (Desc.UT N ⊗ Desc.UT N).left ⟶ (N.U ⊗ N.U).left :=
  pullback.lift ((fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π))
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π)) (by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, ← Category.assoc _ _ (_ ≫ π)]
      exact congrArg (· ≫ _) ((Over.w (fst (Desc.UT N) (Desc.UT N))).trans (Over.w (snd (Desc.UT N) (Desc.UT N))).symm))

theorem toSq_fst (N : Near π G) : toSq N ≫ (fst N.U N.U).left =
    (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π) := pullback.lift_fst _ _ _

theorem toSq_snd (N : Near π G) : toSq N ≫ (snd N.U N.U).left =
    (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π) := pullback.lift_snd _ _ _

theorem toSq_hom (N : Near π G) : toSq N ≫ (N.U ⊗ N.U).hom =
    (Desc.UT N ⊗ Desc.UT N).hom ≫ pullback.fst π π ≫ π := by
  rw [← Over.w (fst N.U N.U), ← Category.assoc, toSq_fst, Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (· ≫ _) (Over.w (fst (Desc.UT N) (Desc.UT N)))

theorem surjective_preimage (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) [Surjective (V.ι ≫ (N.U ⊗ N.U).hom)] :
    Surjective ((toSq N ⁻¹ᵁ V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) := by
  let a := V.ι ≫ (N.U ⊗ N.U).hom
  let b := pullback.fst π π ≫ π
  let Z : Over (pullback π π) := Over.mk (pullback.snd a b)
  let k₁ : Z ⟶ Desc.UT N := Over.homMk (pullback.lift (pullback.fst a b ≫ V.ι ≫ (fst N.U N.U).left) (pullback.snd a b) (by
    rw [Category.assoc, Category.assoc, Over.w]; exact pullback.condition)) (pullback.lift_snd _ _ _)
  let k₂ : Z ⟶ Desc.UT N := Over.homMk (pullback.lift (pullback.fst a b ≫ V.ι ≫ (snd N.U N.U).left) (pullback.snd a b) (by
    rw [Category.assoc, Category.assoc, Over.w]; exact pullback.condition)) (pullback.lift_snd _ _ _)
  let k : pullback a b ⟶ (Desc.UT N ⊗ Desc.UT N).left := (lift k₁ k₂).left
  have hk : k ≫ toSq N = pullback.fst a b ≫ V.ι := by
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (toSq_fst N)).trans ?_)
      have : k ≫ (fst (Desc.UT N) (Desc.UT N)).left = k₁.left := congrArg (·.left) (lift_fst k₁ k₂)
      rw [← Category.assoc, this]
      exact (pullback.lift_fst _ _ _).trans (Category.assoc _ _ _).symm
    · refine (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (toSq_snd N)).trans ?_)
      have : k ≫ (snd (Desc.UT N) (Desc.UT N)).left = k₂.left := congrArg (·.left) (lift_snd k₁ k₂)
      rw [← Category.assoc, this]
      exact (pullback.lift_fst _ _ _).trans (Category.assoc _ _ _).symm
  have hk' : k ≫ (Desc.UT N ⊗ Desc.UT N).hom = pullback.snd a b := Over.w (lift k₁ k₂)
  refine ⟨fun t => ?_⟩
  obtain ⟨z, hz⟩ := (pullback.snd a b).surjective t
  refine ⟨⟨k z, ?_⟩, ?_⟩
  · show toSq N (k z) ∈ V
    rw [← Scheme.Hom.comp_apply, hk]
    exact (pullback.fst a b z).2
  · rw [← hz, ← hk']
    rfl

theorem exists_factor [GrpObj G] [Surjective π] (N : Near π G) (hN : N.Law) :
    ∃ (W : (Desc.UT N ⊗ Desc.UT N).left.Opens) (m : W.toScheme ⟶ (Desc.UT N).left),
      Surjective (W.ι ≫ (Desc.UT N ⊗ Desc.UT N).hom) ∧
      ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π),
        m ≫ (Desc.emb N p hp).left = W.ι ≫ (Desc.sum N p hp).left := by
  obtain ⟨V, m, hV, hm, law⟩ := hN
  have := surjective_of_closedFibre N V hV
  let W := toSq N ⁻¹ᵁ V
  let v : W.toScheme ⟶ V.toScheme := toSq N ∣_ V
  have hv : v ≫ V.ι = W.ι ≫ toSq N := morphismRestrict_ι _ _
  let τ : W.toScheme ⟶ pullback π π := W.ι ≫ (Desc.UT N ⊗ Desc.UT N).hom
  let m' : W.toScheme ⟶ pullback N.U.hom (pullback.fst π π ≫ π) := pullback.lift (v ≫ m) τ (by
    rw [Category.assoc, hm, ← Category.assoc, hv, Category.assoc, toSq_hom, Category.assoc])
  refine ⟨W, m', surjective_preimage N V, fun p hp => ?_⟩
  let J : Over.mk τ ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk W.ι rfl
  have lift₀ : ∀ x : Over.mk τ ⟶ (Over.pullback p).obj G,
      ∃ x₀ : Over.mk (τ ≫ p) ⟶ G, x₀.left = x.left ≫ pullback.fst G.hom p := fun x =>
    ⟨Over.homMk (x.left ≫ pullback.fst G.hom p) ((Category.assoc _ _ _).trans
      ((congrArg (x.left ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (Over.w x))))), rfl⟩
  have pt : ∀ (c : Over.mk τ ⟶ Desc.UT N), N.Pt (τ ≫ p) (c.left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π))
      ((c ≫ Desc.emb N p hp).left ≫ pullback.fst G.hom p) := fun c =>
    ⟨c.left ≫ Desc.toS N p hp,
      (Category.assoc _ _ _).trans (congrArg (c.left ≫ ·) (pullback.lift_fst _ _ _)),
      (Category.assoc _ _ _).trans ((congrArg (c.left ≫ ·) (pullback.lift_snd _ _ _)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (Over.w c)))),
      (Category.assoc _ _ _).trans (((Category.assoc _ _ _).trans
        (congrArg (c.left ≫ ·) (pullback.lift_fst _ _ _))).symm)⟩
  obtain ⟨x₀, hx₀⟩ := lift₀ ((J ≫ fst _ _) ≫ Desc.emb N p hp)
  obtain ⟨y₀, hy₀⟩ := lift₀ ((J ≫ snd _ _) ≫ Desc.emb N p hp)
  have hx := pt (J ≫ fst _ _)
  have hy := pt (J ≫ snd _ _)
  rw [← hx₀] at hx
  rw [← hy₀] at hy
  have ex : v ≫ V.ι ≫ (fst N.U N.U).left = (J ≫ fst _ _).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π) := by
    rw [← Category.assoc, hv, Category.assoc, toSq_fst]
    exact (Category.assoc _ _ _).symm
  have ey : v ≫ V.ι ≫ (snd N.U N.U).left = (J ≫ snd _ _).left ≫ pullback.fst N.U.hom (pullback.fst π π ≫ π) := by
    rw [← Category.assoc, hv, Category.assoc, toSq_snd]
    exact (Category.assoc _ _ _).symm
  rw [← ex] at hx
  rw [← ey] at hy
  obtain ⟨x₁, h₁, h₂, h₃⟩ := law _ v (τ ≫ p) x₀ y₀ hx hy
  have hmul := (isGrpPullback_pullback G p).2 (Over.mk τ) _ _ x₀ y₀ hx₀ hy₀
  have hsum : ((J ≫ fst _ _) ≫ Desc.emb N p hp) * ((J ≫ snd _ _) ≫ Desc.emb N p hp) = J ≫ Desc.sum N p hp := by
    rw [Desc.sum, MonObj.comp_mul, Category.assoc, Category.assoc]
  rw [hsum] at hmul
  have e₁ : x₁ = m' ≫ Desc.toS N p hp := by
    apply pullback.hom_ext
    · rw [h₁, Category.assoc, Desc.toS, pullback.lift_fst, pullback.lift_fst]
    · rw [h₂, Category.assoc m', Desc.toS, pullback.lift_snd, ← Category.assoc m', pullback.lift_snd]
  apply pullback.hom_ext
  · refine (Category.assoc _ _ _).trans ((congrArg (m' ≫ ·) (pullback.lift_fst _ _ _)).trans ?_)
    rw [← Category.assoc, ← e₁, h₃]
    exact hmul
  · refine (Category.assoc _ _ _).trans ((congrArg (m' ≫ ·) (pullback.lift_snd _ _ _)).trans ?_)
    refine (pullback.lift_snd _ _ _).trans ?_
    exact ((Category.assoc _ _ _).trans (congrArg (W.ι ≫ ·) (Over.w (Desc.sum N p hp)))).symm

theorem emb_comp_of_sum_comp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (S : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (G' : Over S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ N : Near π G', N.Law → ∀ (p p' : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) (hp' : p' ≫ π = pullback.fst π π ≫ π), ∀ φ : (Over.pullback p).obj G' ⟶ (Over.pullback p').obj G', Desc.sum N p hp ≫ φ = Desc.sum N p' hp' → Desc.emb N p hp ≫ φ = Desc.emb N p' hp' := by
  intro R _ _ _ _ S π _ hπ _ G _ _ hG N hN p p' hp hp' φ hφ
  obtain ⟨W, m, hW, hm⟩ := exists_factor N hN
  have := hG.smooth
  have := hG.separated
  have := hG.geomConnected
  have := N.smooth
  have he := isOpenImmersion_emb N p hp
  have s₁ : Smooth ((Over.pullback p).obj G).hom := inferInstanceAs (Smooth (pullback.snd G.hom p))
  have c₁ : GeometricallyConnected ((Over.pullback p).obj G).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd G.hom p))
  have s₂ : IsSeparated ((Over.pullback p').obj G).hom := inferInstanceAs (IsSeparated (pullback.snd G.hom p'))
  have s₃ : Smooth (Desc.UT N).hom := inferInstanceAs (Smooth (pullback.snd _ _))
  have s₄ : Smooth (Desc.sum N p hp).left := by
    have h : Desc.sum N p hp = (Desc.emb N p hp ⊗ₘ Desc.emb N p hp) ≫ μ[(Over.pullback p).obj G] := by
      rw [Desc.sum, Hom.mul_def, lift_fst_comp_snd_comp]
    have := smooth_mul ((Over.pullback p).obj G)
    have : IsOpenImmersion (Desc.emb N p hp ⊗ₘ Desc.emb N p hp).left := by
      rw [Over.tensorHom_left]
      infer_instance
    rw [h, Over.comp_left]
    infer_instance
  have s₅ : Smooth (m ≫ (Desc.emb N p hp).left) := by
    rw [hm]; infer_instance
  have s₆ : Smooth m := smooth_of_comp_mono m (Desc.emb N p hp).left
  have s₇ : Surjective (m ≫ (Desc.UT N).hom) := by
    rw [← Over.w (Desc.emb N p hp), ← Category.assoc, hm, Category.assoc, Over.w]
    exact hW
  have hirr : ∀ t, IsPreirreducible ((Desc.UT N).hom ⁻¹' {t}) := fun t => by
    have := (isPreirreducible_fibre ((Over.pullback p).obj G).hom t).preimage
      (Desc.emb N p hp).left.isOpenEmbedding
    rw [← Over.w (Desc.emb N p hp)]
    exact this
  ext1
  refine eq_of_smooth_comp (Desc.UT N).hom hirr m ((Over.pullback p').obj G).hom _ _
    ((Over.w _).trans (Over.w _).symm) ?_
  rw [Over.comp_left, ← Category.assoc, hm, hm, Category.assoc, ← Over.comp_left, hφ]

end GlobalTheory.Mum.DescFix
