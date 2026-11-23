import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreUniformisationDataIsEvenCubicalOnClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeHomEqOfKerLeOfNilpotentReductionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusHomEqOfNilpotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOnTorusDescendsAlongLocalHomStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusExtensionDescends
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosedFibreSplitOfArcDataFiniteExtension
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDVRResidueGaloisAutomorphisms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitExtDatumOfSplitTorusExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMemCommonChart
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusHomPullbackLocalTrivial
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ESecCompOfIsGrpPullback

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EvenDesc

theorem exists_artinian {k K O : Type} [Field k] [Field K] [Algebra k K] [FiniteDimensional k K] [Normal k K]
    [CommRing O] [IsLocalRing O] (a b : K →+* O) (h : a.comp (algebraMap k K) = b.comp (algebraMap k K)) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsLocalRing A) (_ : IsArtinianRing A) (a' b' : K →+* A) (ψ : A →+* O)
      (τ : K ≃ₐ[k] K), ψ.comp a' = a ∧ ψ.comp b' = b ∧ a'.comp (algebraMap k K) = b'.comp (algebraMap k K) ∧
      (residue A).comp b' = ((residue A).comp a').comp (τ : K →+* K) := by
  letI : Algebra k O := (a.comp (algebraMap k K)).toAlgebra
  let a₁ : K →ₐ[k] O := { a with commutes' := fun _ => rfl }
  let b₁ : K →ₐ[k] O := { b with commutes' := fun r => (RingHom.congr_fun h r).symm }
  let f := Algebra.TensorProduct.productMap a₁ b₁
  let A := f.range
  have : Module.Finite k A := Module.Finite.of_surjective f.rangeRestrict.toLinearMap f.rangeRestrict_surjective
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have u : ∀ x : A, IsUnit (x : O) → IsUnit x := fun x hx =>
    IsArtinianRing.isUnit_of_mem_nonZeroDivisors (mem_nonZeroDivisors_iff_right.2 fun y hy =>
      Subtype.ext (hx.mul_left_eq_zero.1 (congrArg Subtype.val hy)))
  have : IsLocalRing A := IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x =>
    (IsLocalRing.isUnit_or_isUnit_one_sub_self (x : O)).imp (u x) (u (1 - x))
  let a' : K →ₐ[k] A := f.rangeRestrict.comp Algebra.TensorProduct.includeLeft
  let b' : K →ₐ[k] A := f.rangeRestrict.comp Algebra.TensorProduct.includeRight
  let r : A →ₐ[k] ResidueField A := IsScalarTower.toAlgHom k A _
  letI : Algebra K (ResidueField A) := (r.comp a').toRingHom.toAlgebra
  have : IsScalarTower k K (ResidueField A) := .of_algebraMap_eq fun x => ((r.comp a').commutes x).symm
  refine ⟨A, _, ‹_›, inferInstance, a', b', A.val, (r.comp b').restrictNormal' K, ?_, ?_, ?_, ?_⟩
  · ext x; simp [a', f, a₁]
  · ext x; simp [b', f, b₁]
  · exact a'.comp_algebraMap.trans b'.comp_algebraMap.symm
  · exact RingHom.ext fun x => ((r.comp b').restrictNormal_commutes K x).symm

theorem normal_of_isInvariant (A B G : Type) [CommRing A] [CommRing B] [Algebra A B] [Group G]
    [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G] [SMulCommClass G A B]
    (k K : Type) [Field k] [Field K] [Algebra k K] (p : A →+* k) (q : B →+* K)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : ∀ x, algebraMap k K (p x) = q (algebraMap A B x)) :
    Normal k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : G, ∀ x, q (σ • x) = τ (q x) := by
  let P : Ideal A := RingHom.ker p
  let Q : Ideal B := RingHom.ker q
  have : P.IsPrime := RingHom.ker_isPrime p
  have : Q.IsPrime := RingHom.ker_isPrime q
  have : Q.LiesOver P := ⟨by
    ext x
    simp only [P, Q, Ideal.under, Ideal.mem_comap, RingHom.mem_ker, ← h, map_eq_zero]⟩
  let _ : Algebra (A ⧸ P) k := (RingHom.kerLift p).toAlgebra
  let _ : Algebra (B ⧸ Q) K := (RingHom.kerLift q).toAlgebra
  let _ : Algebra (A ⧸ P) K := ((algebraMap k K).comp (RingHom.kerLift p)).toAlgebra
  have : IsScalarTower (A ⧸ P) k K := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (A ⧸ P) (B ⧸ Q) K := .of_algebraMap_eq fun x => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact h x
  have : FaithfulSMul (A ⧸ P) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective p)
  have : FaithfulSMul (B ⧸ Q) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective q)
  have : IsFractionRing (A ⧸ P) k := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hp z
    exact ⟨Ideal.Quotient.mk P x, 1, by rw [map_one, div_one]; rfl⟩
  have : IsFractionRing (B ⧸ Q) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hq z
    exact ⟨Ideal.Quotient.mk Q x, 1, by rw [map_one, div_one]; rfl⟩
  refine ⟨Ideal.IsFractionRing.normal G P Q k K, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := IsFractionRing.stabilizerHom_surjective G P Q k K τ
  exact ⟨σ.1, fun x => (IsFractionRing.stabilizerHom_apply_apply_mk G P Q k K σ x).symm⟩

open GlobalTheory.UU GlobalTheory.SplitTorus in

theorem exists_baseChange {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G]
    [GrpObj B] {G' B' : Over S'} [GrpObj G'] [GrpObj B'] {F : G'.left ⟶ G.left} {p : B'.left ⟶ B.left}
    (hF : IsGrpPullback G' G f F) (hB : IsGrpPullback B' B f p) (q : G ⟶ B) (i : splitTorus S X ⟶ G) [IsMonHom q]
    [IsMonHom i] (H : IsPullback i (toUnit _) q η[B]) :
    ∃ (q' : G' ⟶ B') (i' : splitTorus S' X ⟶ G'), IsPullback F q'.left q.left p ∧
      bcMap f X ≫ i.left = i'.left ≫ F ∧ IsMonHom q' ∧ IsMonHom i' ∧ IsPullback i' (toUnit _) q' η[B'] := by
  obtain ⟨i', hi, -⟩ := existsUnique_torusCompat hF.1 i
  have w : (F ≫ q.left) ≫ B.hom = G'.hom ≫ f := by rw [Category.assoc, Over.w, hF.1.w]
  let q' : G' ⟶ B' := Over.homMk (hB.1.lift _ _ w) (hB.1.lift_snd _ _ w)
  have hq : q'.left ≫ p = F ≫ q.left := hB.1.lift_fst _ _ w
  have sq : IsPullback F q'.left q.left p := by
    refine IsPullback.of_bot ?_ hq.symm hB.1
    rw [Over.w, Over.w]; exact hF.1
  have e₁ : bcMap f X ≫ i.left = i'.left ≫ F := torusCompat_iff.1 hi
  refine ⟨q', i', sq, e₁, isMonHom_of_over_isMonHom hF hB q q' hq, hi.isMonHom hF, ?_⟩
  have k₀ : IsPullback i.left (splitTorus S X).hom q.left (η[B]).left := by
    have := H.map (Over.forget S)
    rw [← Rosenlicht.toUnit_left]
    exact this
  have k₁ := (isPullback_bcMap f X).paste_horiz k₀
  have e₂ := eSec_comp_of_isGrpPullback hB
  have w' : i'.left ≫ q'.left = (splitTorus S' X).hom ≫ (η[B']).left := by
    refine hB.1.hom_ext ?_ ?_
    · rw [Category.assoc, hq, ← Category.assoc, ← e₁, k₁.w]
      exact (congrArg (_ ≫ ·) e₂.symm).trans (Category.assoc _ _ _).symm
    · rw [Category.assoc, Over.w, Over.w, Category.assoc, Over.w]
      exact (Category.comp_id _).symm
  rw [e₁] at k₁
  have k₂ : IsPullback i'.left (splitTorus S' X).hom q'.left (η[B']).left :=
    IsPullback.of_right (k₁.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp) (by simpa using e₂.symm)) w' sq
  rw [← Rosenlicht.toUnit_left] at k₂ w'
  exact IsPullback.of_map (Over.forget S') (Over.OverMorphism.ext w') k₂

section Descent

open GlobalTheory.UU GlobalTheory.SplitTorus

variable {k K : Type} [Field k] [Field K] [Algebra k K] {G₀ B₀ : Over (Sp k)} [GrpObj G₀] [IsCommMonObj G₀] [GrpObj B₀]
  (hB₀ : IsAbelianScheme B₀) {G B : Over (Sp K)} [GrpObj G] [GrpObj B] {X : Type} [AddCommGroup X]
  {φG : G.left ⟶ G₀.left} {φ : B.left ⟶ B₀.left} (hG : IsGrpPullback G G₀ (spMap (algebraMap k K)) φG)
  (hB : IsGrpPullback B B₀ (spMap (algebraMap k K)) φ) (q : G ⟶ B) (i : splitTorus (Sp K) X ⟶ G) [IsMonHom q]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left] [IsMonHom i] (H : IsPullback i (toUnit _) q η[B])
  (hinv : ∀ (τ : K ≃ₐ[k] K) (s : G.left ⟶ G.left), s ≫ φG = φG → s ≫ G.hom = G.hom ≫ spMap (τ : K →+* K) →
    s ≫ q.left ≫ φ = q.left ≫ φ ∧ bcMap (spMap (τ : K →+* K)) X ≫ i.left = i.left ≫ s)

include hB₀ hG hB H hinv in

theorem agree_artinian {A : Type} [CommRing A] [IsLocalRing A] [IsArtinianRing A] (a b : K →+* A) (τ : K ≃ₐ[k] K)
    (hab : a.comp (algebraMap k K) = b.comp (algebraMap k K))
    (hτ : (residue A).comp b = ((residue A).comp a).comp (τ : K →+* K)) :
    bcMap (spMap a) X ≫ i.left ≫ φG = bcMap (spMap b) X ≫ i.left ≫ φG ∧
    ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp A) (x y : Z ⟶ G.left), x ≫ G.hom = z ≫ spMap a → y ≫ G.hom = z ≫ spMap b →
      x ≫ φG = y ≫ φG → x ≫ q.left ≫ φ = y ≫ q.left ≫ φ := by
  have hn : IsNilpotent (RingHom.ker (residue A)) := by
    rw [ker_residue, ← jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  obtain ⟨s, hsa⟩ : ∃ s, spMap a ≫ spMap (algebraMap k K) = s := ⟨_, rfl⟩
  have hsb : spMap b ≫ spMap (algebraMap k K) = s := by rw [← hsa, ← spMap_comp, ← spMap_comp, hab]
  have lift : ∀ {Y₀ : Over (Sp k)} [GrpObj Y₀] {Y : Over (Sp K)} [GrpObj Y] {ψ : Y.left ⟶ Y₀.left},
      IsGrpPullback Y Y₀ (spMap (algebraMap k K)) ψ → ∀ c : K →+* A, spMap c ≫ spMap (algebraMap k K) = s →
      ∃ g : ((Over.pullback s).obj Y₀).left ⟶ Y.left, g ≫ ψ = pullback.fst Y₀.hom s ∧
        IsGrpPullback ((Over.pullback s).obj Y₀) Y (spMap c) g := by
    intro Y₀ _ Y _ ψ h c hc
    have w : pullback.fst Y₀.hom s ≫ Y₀.hom = (pullback.snd Y₀.hom s ≫ spMap c) ≫ spMap (algebraMap k K) := by
      rw [Category.assoc, hc, pullback.condition]
    exact ⟨h.1.lift _ _ w, h.1.lift_fst _ _ w, h.cancel
      ((isGrpPullback_pullback Y₀ s).congr hc.symm (h.1.lift_fst _ _ w).symm) (h.1.lift_snd _ _ w)⟩
  obtain ⟨ga, ga₁, hga⟩ := lift hG a hsa
  obtain ⟨gb, gb₁, hgb⟩ := lift hG b hsb
  obtain ⟨ba, ba₁, hba⟩ := lift hB a hsa
  obtain ⟨bb, bb₁, hbb⟩ := lift hB b hsb
  obtain ⟨qa, ia, qa₁, ia₁, mqa, mia, ka⟩ := exists_baseChange hga hba q i H
  obtain ⟨qb, ib, qb₁, ib₁, mqb, mib, kb⟩ := exists_baseChange hgb hbb q i H
  have τα : spMap (τ : K →+* K) ≫ spMap (algebraMap k K) = spMap (algebraMap k K) :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext τ.commutes))
  have w : φG ≫ G₀.hom = (G.hom ≫ spMap (τ : K →+* K)) ≫ spMap (algebraMap k K) := by
    rw [Category.assoc, τα, hG.1.w]
  have t₁ := hG.1.lift_fst _ _ w
  have t₂ := hG.1.lift_snd _ _ w
  obtain ⟨v₁, v₂⟩ := hinv τ _ t₁ t₂
  generalize hG.1.lift _ _ w = t at t₁ t₂ v₁ v₂
  have rτ : spMap (residue A) ≫ spMap b = (spMap (residue A) ≫ spMap a) ≫ spMap (τ : K →+* K) := by
    rw [← spMap_comp, ← spMap_comp, ← spMap_comp, hτ]
  have ea : ia.left ≫ pullback.fst G₀.hom s = bcMap (spMap a) X ≫ i.left ≫ φG := by
    rw [← ga₁, ← Category.assoc, ← ia₁, Category.assoc]
  have eb : ib.left ≫ pullback.fst G₀.hom s = bcMap (spMap b) X ≫ i.left ≫ φG := by
    rw [← gb₁, ← Category.assoc, ← ib₁, Category.assoc]
  have ei : ia = ib := by
    refine GlobalTheory.T.splitTorus_hom_eq_of_bcMap_comp_eq A _ (residue A) residue_surjective hn X _ ia ib mia mib (pullback.hom_ext ?_ ?_)
    · rw [Category.assoc, Category.assoc]
      erw [ea, eb]
      rw [← Category.assoc, ← bcMap_comp, ← Category.assoc (bcMap _ X) (bcMap _ X), ← bcMap_comp, rτ,
        bcMap_comp _ (spMap (τ : K →+* K)), Category.assoc, reassoc_of% v₂, t₁]
    · rw [Category.assoc, Category.assoc]
      exact congrArg _ ((Over.w ia).trans (Over.w ib).symm)
  have fa : qa.left ≫ pullback.fst B₀.hom s = ga ≫ q.left ≫ φ := by
    rw [← ba₁, ← Category.assoc, ← qa₁.w, Category.assoc]
  have fb : qb.left ≫ pullback.fst B₀.hom s = gb ≫ q.left ≫ φ := by
    rw [← bb₁, ← Category.assoc, ← qb₁.w, Category.assoc]
  have eq : qa = qb := by
    refine GlobalTheory.T.abelianScheme_hom_eq_of_ker_le_of_nilpotent_reduction A _ (residue A) residue_surjective hn _ _ (GlobalTheory.isAbelianScheme_pullback_obj _ _ hB₀) qa qb mqa mqb
      (MorphismProperty.of_isPullback (P := @Flat) qa₁ ‹_›)
      (MorphismProperty.of_isPullback (P := @Surjective) qa₁ ‹_›)
      (MorphismProperty.of_isPullback (P := @QuasiCompact) qa₁ ‹_›) (fun T x hx => ?_) (pullback.hom_ext ?_ ?_)
    · subst ei
      rw [← ka.lift_fst x (toUnit _) hx, Category.assoc, kb.w, ← Category.assoc, Hom.one_def,
        toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    · rw [Category.assoc, Category.assoc]
      erw [fa, fb]
      have : pullback.fst ((Over.pullback s).obj G₀).hom (spMap (residue A)) ≫ gb =
          pullback.fst ((Over.pullback s).obj G₀).hom (spMap (residue A)) ≫ ga ≫ t := by
        refine hG.1.hom_ext ?_ ?_
        · simp only [Category.assoc, t₁, ga₁, gb₁]
        · simp only [Category.assoc]
          rw [t₂, hgb.1.w, reassoc_of% hga.1.w, pullback.condition_assoc, pullback.condition_assoc, rτ,
            Category.assoc]
      rw [reassoc_of% this, v₁]
    · rw [Category.assoc, Category.assoc]
      exact congrArg _ ((Over.w qa).trans (Over.w qb).symm)
  refine ⟨by rw [← ea, ← eb, ei], fun Z z x y hx hy e => ?_⟩
  have ex := hga.1.lift_fst x z hx
  have ez := hga.1.lift_snd x z hx
  generalize hga.1.lift x z hx = u at ex ez
  have ey : u ≫ gb = y := by
    refine hG.1.hom_ext ?_ ?_
    · rw [Category.assoc, gb₁, ← ga₁, reassoc_of% ex, e]
    · rw [Category.assoc, hgb.1.w, reassoc_of% ez, hy]
  rw [← ex, ← ey, Category.assoc, Category.assoc, ← fa, ← fb, eq]

include hB₀ hG hB H hinv in

theorem nonempty_tq_of_normal [FiniteDimensional k K] [Normal k K] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Nonempty (TQ G₀ X) := by
  have key : ∀ (O : CommRingCat.{0}) [IsLocalRing O] (u v : Spec O ⟶ Sp K),
      u ≫ spMap (algebraMap k K) = v ≫ spMap (algebraMap k K) →
      ∃ (A : Type) (_ : CommRing A) (a b : K →+* A) (z : Spec O ⟶ Sp A), u = z ≫ spMap a ∧ v = z ≫ spMap b ∧
        bcMap (spMap a) X ≫ i.left ≫ φG = bcMap (spMap b) X ≫ i.left ≫ φG ∧
        ∀ (Z : Scheme.{0}) (z : Z ⟶ Sp A) (x y : Z ⟶ G.left), x ≫ G.hom = z ≫ spMap a → y ≫ G.hom = z ≫ spMap b →
          x ≫ φG = y ≫ φG → x ≫ q.left ≫ φ = y ≫ q.left ≫ φ := by
    intro O _ u v h
    obtain ⟨u, rfl⟩ := Spec.map_surjective u
    obtain ⟨v, rfl⟩ := Spec.map_surjective v
    rw [← Spec.map_comp, ← Spec.map_comp] at h
    obtain ⟨A, _, _, _, a, b, ψ, τ, ha, hb, hab, hτ⟩ :=
      exists_artinian u.hom v.hom (congrArg CommRingCat.Hom.hom (Spec.map_injective h))
    refine ⟨A, _, a, b, spMap ψ, ?_, ?_, agree_artinian hB₀ hG hB q i H hinv a b τ hab hτ⟩
    · rw [← spMap_comp, ha]; rfl
    · rw [← spMap_comp, hb]; rfl
  haveI h₁ : Flat (spMap (algebraMap k K)) := inferInstance
  haveI h₂ : Surjective (spMap (algebraMap k K)) := inferInstance
  haveI h₃ : QuasiCompact (spMap (algebraMap k K)) := inferInstance
  have hT := isPullback_bcMap (spMap (algebraMap k K)) X
  obtain ⟨⟨g₁, g₂⟩, g₃⟩ := ExtDescent.fpqc_of_isPullback hG.1
  obtain ⟨⟨t₁, t₂⟩, t₃⟩ := ExtDescent.fpqc_of_isPullback hT
  have cq : ∀ {Z : Scheme.{0}} (x y : Z ⟶ G.left), x ≫ φG = y ≫ φG → x ≫ q.left ≫ φ = y ≫ q.left ≫ φ := by
    intro Z x y e
    refine hom_ext_of_fromSpecStalk fun p => ?_
    obtain ⟨A, _, a, b, z, hu, hv, -, h⟩ := key _ ((Z.fromSpecStalk p ≫ x) ≫ G.hom) ((Z.fromSpecStalk p ≫ y) ≫ G.hom)
      (by simp only [Category.assoc]; rw [← hG.1.w, reassoc_of% e, ← Category.assoc y, ← e, Category.assoc])
    simpa only [Category.assoc] using h _ z _ _ hu hv (by rw [Category.assoc, e, Category.assoc])
  have ci : ∀ {Z : Scheme.{0}} (x y : Z ⟶ (splitTorus (Sp K) X).left),
      x ≫ bcMap (spMap (algebraMap k K)) X = y ≫ bcMap (spMap (algebraMap k K)) X →
      x ≫ i.left ≫ φG = y ≫ i.left ≫ φG := by
    intro Z x y e
    refine hom_ext_of_fromSpecStalk fun p => ?_
    obtain ⟨A, _, a, b, z, hu, hv, h, -⟩ := key _ ((Z.fromSpecStalk p ≫ x) ≫ (splitTorus (Sp K) X).hom)
      ((Z.fromSpecStalk p ≫ y) ≫ (splitTorus (Sp K) X).hom)
      (by simp only [Category.assoc]; rw [← hT.w, reassoc_of% e, ← Category.assoc y, ← e, Category.assoc])
    have ex := (isPullback_bcMap (spMap a) X).lift_fst _ z hu
    have ez := (isPullback_bcMap (spMap a) X).lift_snd _ z hu
    generalize (isPullback_bcMap (spMap a) X).lift _ z hu = u at ex ez
    have hab : z ≫ spMap a ≫ spMap (algebraMap k K) = z ≫ spMap b ≫ spMap (algebraMap k K) := by
      rw [← reassoc_of% hu, ← reassoc_of% hv, ← hT.w, reassoc_of% e]
    have ey : u ≫ bcMap (spMap b) X = Z.fromSpecStalk p ≫ y := by
      refine hT.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, ← e, ← reassoc_of% ex, ← bcMap_comp, ← bcMap_comp]
        refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
        · simp only [Category.assoc, bcMap_hom]
          rw [reassoc_of% ez, reassoc_of% ez, hab]
        · simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, bcMap_charUnit]
      · rw [Category.assoc, bcMap_hom, reassoc_of% ez, hv]
    rw [← reassoc_of% ex, ← reassoc_of% ey, h]
  have hq' := EffectiveEpi.fac φG (q.left ≫ φ) cq
  have hi' := EffectiveEpi.fac (bcMap (spMap (algebraMap k K)) X) (i.left ≫ φG) ci
  generalize EffectiveEpi.desc φG (q.left ≫ φ) cq = q' at hq'
  generalize EffectiveEpi.desc (bcMap (spMap (algebraMap k K)) X) (i.left ≫ φG) ci = i' at hi'
  have wq : q' ≫ B₀.hom = G₀.hom := by
    rw [← cancel_epi φG, ← Category.assoc, hq', Category.assoc, hB.1.w, ← Category.assoc, Over.w, hG.1.w]
  have wi : i' ≫ G₀.hom = (splitTorus (Sp k) X).hom := by
    rw [← cancel_epi (bcMap (spMap (algebraMap k K)) X), ← Category.assoc, hi', Category.assoc, hG.1.w,
      ← Category.assoc, Over.w, hT.w]
  obtain ⟨a₁, a₂, a₃, a₄, a₅, a₆⟩ := splitTorus_extension_descends k K (algebraMap k K) G B G₀ B₀ X
    φG φ hG hB q i (Over.homMk q' wq) (Over.homMk i' wi) hq' hi' ‹_› ‹_› ‹_› ‹_› ‹_› H
  obtain ⟨O, a, b, c, h⟩ := exists_gtDatum_of_splitTorus_extension (Sp k) X G₀ B₀ hB₀ _ _ a₁ a₅ a₂ a₃ a₄ a₆
  obtain ⟨d, -⟩ := h hB₀
  obtain ⟨Q, -⟩ := exists_tq_of_gtDatum _ _ _ d
  exact ⟨Q⟩

end Descent

set_option maxHeartbeats 800000 in

theorem nonempty_tq {R R' : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R']
    {ρ : R →+* R'} (hfin : ρ.Finite) (hgal : IsGal ρ) {D : DegData R (maximalIdeal R)}
    {D' : DegData R' (maximalIdeal R')} {hD : IsPullDeg ρ D.toPre D'.toPre} {A' : PolAV (Sp (FractionRing R'))}
    {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {U' : Unif (maximalIdeal R') D' A' G'} (a : GalAct ρ hD U')
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {β : G'.left ⟶ G.left} (hβ : IsGrpPullback G' G (spMap ρ) β)
    (hinv : ∀ σ, a.act σ ≫ β = β) : Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) D'.toPre.X) := by
  have hp : maximalIdeal R ^ (0 + 1) = maximalIdeal R := pow_one _
  have hp' : maximalIdeal R' ^ (0 + 1) = maximalIdeal R' := pow_one _
  haveI : (maximalIdeal R ^ (0 + 1)).IsMaximal := by rw [hp]; infer_instance
  haveI : (maximalIdeal R' ^ (0 + 1)).IsMaximal := by rw [hp']; infer_instance
  letI := Ideal.Quotient.field (maximalIdeal R ^ (0 + 1))
  letI := Ideal.Quotient.field (maximalIdeal R' ^ (0 + 1))
  let α : R ⧸ maximalIdeal R ^ (0 + 1) →+* R' ⧸ maximalIdeal R' ^ (0 + 1) :=
    Ideal.quotientMap _ ρ (by
      rw [hp, hp']; exact Ideal.map_le_iff_le_comap.1 (ResidueGalois.map_maximalIdeal_le ρ hfin.to_isIntegral))
  have hα : α.comp (Ideal.Quotient.mk _) = (Ideal.Quotient.mk _).comp ρ := Ideal.quotientMap_comp_mk _
  letI := α.toAlgebra
  have hfd : FiniteDimensional (R ⧸ maximalIdeal R ^ (0 + 1)) (R' ⧸ maximalIdeal R' ^ (0 + 1)) := by
    have : (α.comp (Ideal.Quotient.mk _)).Finite := by
      rw [hα]; exact (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective).comp hfin
    exact RingHom.Finite.of_comp_finite this
  obtain ⟨hn, haut⟩ : Normal (R ⧸ maximalIdeal R ^ (0 + 1)) (R' ⧸ maximalIdeal R' ^ (0 + 1)) ∧
      ∀ τ : (R' ⧸ maximalIdeal R' ^ (0 + 1)) ≃ₐ[R ⧸ maximalIdeal R ^ (0 + 1)] (R' ⧸ maximalIdeal R' ^ (0 + 1)),
        ∃ σ : Gal ρ, ∀ x, Ideal.Quotient.mk _ (σ.1 x) = τ (Ideal.Quotient.mk _ x) := by
    letI := ρ.toAlgebra
    have := hgal.1
    have : Algebra.IsInvariant R R' (Gal ρ) := ⟨fun x hx => hgal.2 x fun σ hσ => hx ⟨σ, hσ⟩⟩
    have : SMulCommClass (Gal ρ) R R' := ⟨fun σ r x => by
      show σ.1 (ρ r * x) = ρ r * σ.1 x
      rw [map_mul, σ.2 r]⟩
    exact normal_of_isInvariant R R' (Gal ρ) (R ⧸ maximalIdeal R ^ (0 + 1)) (R' ⧸ maximalIdeal R' ^ (0 + 1))
      (Ideal.Quotient.mk _) (Ideal.Quotient.mk _)
      Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective (fun _ => rfl)
  have sq : thick R' (maximalIdeal R') 0 ≫ spMap ρ = spMap α ≫ thick R (maximalIdeal R) 0 :=
    (spMap_comp ρ _).symm.trans ((congrArg spMap hα.symm).trans (spMap_comp _ α))
  obtain ⟨bD, hbD⟩ : ∃ bD, bD = hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf ρ) := ⟨_, rfl⟩
  have gG : IsGrpPullback (thickObj R' (maximalIdeal R') 0 G') G (spMap α ≫ thick R (maximalIdeal R) 0)
      ((fstG (maximalIdeal R') 0 G').left ≫ β) :=
    ((isGrpPullback_pullback G' (thick R' (maximalIdeal R') 0)).comp hβ).congr sq rfl
  have gB : IsGrpPullback (thickObj R' (maximalIdeal R') 0 D'.toPre.P.A) D.toPre.P.A
      (spMap α ≫ thick R (maximalIdeal R) 0) (pullback.fst D'.toPre.P.A.hom (thick R' (maximalIdeal R') 0) ≫ bD) :=
    ((isGrpPullback_pullback D'.toPre.P.A (thick R' (maximalIdeal R') 0)).comp (pull_grp hD)).congr sq (by rw [hbD])
  obtain ⟨φG, G₁, G₂⟩ : ∃ φG : (thickObj R' (maximalIdeal R') 0 G').left ⟶ (thickObj R (maximalIdeal R) 0 G).left,
      φG ≫ pullback.fst G.hom (thick R (maximalIdeal R) 0) = (fstG (maximalIdeal R') 0 G').left ≫ β ∧
      φG ≫ (thickObj R (maximalIdeal R) 0 G).hom = (thickObj R' (maximalIdeal R') 0 G').hom ≫ spMap α :=
    ⟨pullback.lift _ _ (gG.1.w.trans (Category.assoc _ _ _).symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  obtain ⟨φB, B₁, B₂⟩ : ∃ φB : (thickObj R' (maximalIdeal R') 0 D'.toPre.P.A).left ⟶
      (thickObj R (maximalIdeal R) 0 D.toPre.P.A).left,
      φB ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
        pullback.fst D'.toPre.P.A.hom (thick R' (maximalIdeal R') 0) ≫ bD ∧
      φB ≫ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).hom =
        (thickObj R' (maximalIdeal R') 0 D'.toPre.P.A).hom ≫ spMap α :=
    ⟨pullback.lift _ _ (gB.1.w.trans (Category.assoc _ _ _).symm), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have := (U'.gt 0).q_affine
  have := (U'.gt 0).q_hom
  have := (U'.gt 0).q_flat
  have := (U'.gt 0).q_surj
  have := (U'.gt 0).i_hom
  refine nonempty_tq_of_normal (GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb)
    ((isGrpPullback_pullback G (thick R (maximalIdeal R) 0)).cancel (gG.congr rfl G₁.symm) G₂)
    ((isGrpPullback_pullback D.toPre.P.A (thick R (maximalIdeal R) 0)).cancel (gB.congr rfl B₁.symm) B₂)
    (U'.gt 0).q (U'.gt 0).i (U'.gt 0).isKernel (fun τ s s₁ s₂ => ?_)
  obtain ⟨σ, σ₂⟩ := haut τ
  obtain ⟨h, bc, hbc, hPU, hxe, hov⟩ := a.unif σ
  have σt : thick R' (maximalIdeal R') 0 ≫ spMap (Gal.hom σ) = spMap (τ : _ →+* _) ≫ thick R' (maximalIdeal R') 0 :=
    (spMap_comp _ _).symm.trans ((congrArg spMap (RingHom.ext σ₂)).trans (spMap_comp _ _))
  have τα : spMap (τ : _ →+* _) ≫ spMap α = spMap α :=
    (spMap_comp _ _).symm.trans (congrArg spMap (RingHom.ext τ.commutes))
  have c₀ : (fstG (maximalIdeal R') 0 G').left ≫ G'.hom =
    (thickObj R' (maximalIdeal R') 0 G').hom ≫ thick R' (maximalIdeal R') 0 := pullback.condition
  have hs : (fstG (maximalIdeal R') 0 G').left ≫ a.act σ = s ≫ (fstG (maximalIdeal R') 0 G').left := by
    refine hβ.1.hom_ext ?_ ?_
    · rw [Category.assoc, hinv, Category.assoc, ← G₁, reassoc_of% s₁]
    · rw [Category.assoc, (a.cart σ).1.w, reassoc_of% c₀, σt, Category.assoc, c₀, reassoc_of% s₂]
  have rel := fun (T : Scheme.{0}) (z : T ⟶ (thickObj R' (maximalIdeal R') 0 G').left) =>
    SplitAtTrait.pull_rel hPU 0 id (Equiv.refl _) hxe z (z ≫ s) (by rw [hbc, hs, Category.assoc])
  have pq : (U'.gt 0).pG.left = (U'.gt 0).q.left ≫ pullback.fst D'.toPre.P.A.hom (thick R' (maximalIdeal R') 0) := rfl
  constructor
  · apply pullback.hom_ext
    · have r₁ := congrArg (· ≫ bD) (rel _ (𝟙 _)).1
      have r₂ := hov bD _ hbD rfl
      rw [Category.id_comp, Category.id_comp, Category.assoc, r₂, pq] at r₁
      simp only [Category.assoc] at r₁ ⊢
      rw [B₁]; exact r₁.symm
    · have wq : (U'.gt 0).q.left ≫ (thickObj R' (maximalIdeal R') 0 D'.toPre.P.A).hom =
        (thickObj R' (maximalIdeal R') 0 G').hom := Over.w _
      have B₂' : φB ≫ pullback.snd D.toPre.P.A.hom (thick R (maximalIdeal R) 0) =
        (thickObj R' (maximalIdeal R') 0 D'.toPre.P.A).hom ≫ spMap α := B₂
      simp only [Category.assoc]
      rw [B₂', reassoc_of% wq, reassoc_of% s₂, τα]
  · obtain ⟨τ₁, k₁, k₂⟩ := ((rel _ (U'.gt 0).i.left).2 (fun x => (charUnit _ _ x).val)).1
      ⟨𝟙 _, Category.id_comp _, fun x => by rw [Scheme.Hom.id_appTop]; rfl⟩
    rw [← k₁]
    congr 1
    have wi : (U'.gt 0).i.left ≫ (thickObj R' (maximalIdeal R') 0 G').hom = (splitTorus _ D'.toPre.X).hom := Over.w _
    refine SplitAtTrait.torus_ext _ _ ?_ fun x => ?_
    · rw [GlobalTheory.SplitTorus.bcMap_hom, ← wi, reassoc_of% k₁, s₂, Category.assoc]
    · exact (GlobalTheory.UU.bcMap_charUnit _ x).trans (k₂ x).symm

theorem evenOn_of_galAct : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∀ P : GlobalTheory.UU.CP G, LBIso U'.LG.L (P.L.L.pull β) → EvenOn P := by
  intro R _ _ _ _ R' _ _ _ ρ hρ hgal D D' hD A' G' _ _ hG' U' a G _ _ β hG hβ hinv P hP
  have hloc : IsLocalHom ρ := ((local_hom_TFAE ρ).out 2 0).1 (ResidueGalois.map_maximalIdeal_le ρ hρ.2.2.to_isIntegral)
  have hp : IsProper (pullback.snd G'.hom (jK R')) := by
    have e : pullback.snd G'.hom (jK R') = U'.gen.hom.left ≫ A'.A.hom := (Over.w U'.gen.hom).symm
    have : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    exact e ▸ MorphismProperty.comp_mem @IsProper U'.gen.hom.left A'.A.hom inferInstance A'.isAb.proper
  obtain ⟨w, hw⟩ := U'.ext
  let U := GlobalTheory.ValueForm.toPreU U'.toUnifPre GlobalTheory.firstFiveLaws.1.globalFns hG' w hw
  exact GlobalTheory.T.evenOnTorus_descends_along_localHom R R' ρ hloc G hG G' β hβ hp P U.P hP (GlobalTheory.T.preUniformisationData_isEvenCubicalOnClosedFibre R' _ _ _ U) _
    (nonempty_tq hρ.2.2 hgal a hβ hinv)

end GlobalTheory.Mum.EvenDesc
