import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatTors.TorsExt

theorem mem_of_integral (S K F B : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [Field K] [Algebra S K]
    [IsFractionRing S K] [Field F] [Algebra S F] [Algebra K F] [IsScalarTower S K F] [CommRing B] [Algebra S B]
    [Module.Finite S B] [Module.Projective S B] (c : K ⊗[S] B) (w : integralClosure S F ⊗[S] B)
    (h : Algebra.TensorProduct.map (IsScalarTower.toAlgHom S K F) (AlgHom.id S B) c =
      Algebra.TensorProduct.map (integralClosure S F).val (AlgHom.id S B) w) :
    ∃ b : B, c = (1 : K) ⊗ₜ[S] b := by
  obtain ⟨n, p, s, -, -, hps⟩ := Module.Finite.exists_comp_eq_id_of_projective S B
  let ev : ∀ (X : Type) [CommRing X] [Algebra S X], Fin n → X ⊗[S] B →ₗ[S] X := fun X _ _ i =>
    (TensorProduct.rid S X).toLinearMap ∘ₗ LinearMap.lTensor X (LinearMap.proj i ∘ₗ s)
  have nat : ∀ (X : Type) [CommRing X] [Algebra S X] (f : X →ₐ[S] F) (i : Fin n) (x : X ⊗[S] B),
      ev F i (Algebra.TensorProduct.map f (AlgHom.id S B) x) = f (ev X i x) := by
    intro X _ _ f i x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [ev]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hi : ∀ i, ∃ r : S, algebraMap S K r = ev K i c := by
    intro i
    apply IsIntegrallyClosed.isIntegral_iff.1
    apply (isIntegral_algHom_iff (IsScalarTower.toAlgHom S K F) (algebraMap K F).injective).1
    rw [← nat K, h, nat]
    exact (ev _ i w).2
  choose r hr using hi
  have hc : ∀ x : K ⊗[S] B, x = ∑ i, ev K i x ⊗ₜ[S] p (Pi.single i 1) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have hb : b = ∑ i, s b i • p (Pi.single i 1) := by
        conv_lhs => rw [← LinearMap.id_apply (R := S) b, ← hps, LinearMap.comp_apply, pi_eq_sum_univ' (s b), map_sum]
        simp
      conv_lhs => rw [hb, TensorProduct.tmul_sum]
      simp [ev, TensorProduct.smul_tmul]
    | add a b ha hb =>
      simp only [map_add, TensorProduct.add_tmul, Finset.sum_add_distrib]
      rw [← ha, ← hb]
  refine ⟨∑ i, r i • p (Pi.single i 1), ?_⟩
  rw [hc c, TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hr, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]

theorem ext_of_geom {D : Type} [CommRing D] [_root_.IsReduced D] {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsSeparated s]
    (f g : Sp D ⟶ Y) (hs : f ≫ s = g ≫ s)
    (h : ∀ (F : Type) [Field F] [IsAlgClosed F] (φ : D →+* F), spMap φ ≫ f = spMap φ ≫ g) : f = g := by
  refine ext_of_fromSpecResidueField_eq f g s Set.univ dense_univ (fun x _ => ?_) hs
  let k := (Sp D).residueField x
  let σ : k →+* AlgebraicClosure k := algebraMap _ _
  have : Flat (Spec.map (CommRingCat.ofHom σ)) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (Spec.map (CommRingCat.ofHom σ)) :=
    ⟨fun y => ⟨IsLocalRing.closedPoint _, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have := Flat.epi_of_flat_of_surjective (Spec.map (CommRingCat.ofHom σ))
  rw [← cancel_epi (Spec.map (CommRingCat.ofHom σ))]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Spec.map (CommRingCat.ofHom σ) ≫ (Sp D).fromSpecResidueField x)
  have := h (AlgebraicClosure k) φ.hom
  simp only [spMap, CommRingCat.ofHom_hom] at this
  rw [← Category.assoc, ← Category.assoc, ← hφ]
  exact this

theorem exists_chart {N W : Scheme.{0}} (q : N ⟶ W) [IsAffineHom q] (S : Type) [CommRing S] (j : Sp S ⟶ W) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra S B) (g : Sp B ⟶ N), IsPullback g (spMap (algebraMap S B)) q j := by
  have : IsAffine (pullback q j) := isAffine_of_isAffineHom (pullback.snd q j)
  let e := (pullback q j).isoSpec
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (e.inv ≫ pullback.snd q j)
  letI : Algebra S Γ(pullback q j, ⊤) := φ.hom.toAlgebra
  refine ⟨Γ(pullback q j, ⊤), inferInstance, inferInstance, e.inv ≫ pullback.fst q j, ?_⟩
  have h : spMap (algebraMap S Γ(pullback q j, ⊤)) = e.inv ≫ pullback.snd q j := hφ
  rw [h]
  exact IsPullback.of_iso_pullback ⟨by simp [pullback.condition]⟩ e.symm rfl rfl

section Affine

variable {X : Scheme.{0}} {S : Type} [CommRing S] (σ : Sp S ⟶ X)

abbrev spO (A : Type) [CommRing A] [Algebra S A] : Over X := Over.mk (spMap (algebraMap S A) ≫ σ)

def spH {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (φ : A →ₐ[S] A') :
    spO σ A' ⟶ spO σ A :=
  Over.homMk (spMap φ.toRingHom) (by
    change spMap φ.toRingHom ≫ spMap (algebraMap S A) ≫ σ = spMap (algebraMap S A') ≫ σ
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact φ.comp_algebraMap)

theorem spH_left {A A' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] (φ : A →ₐ[S] A') :
    (spH σ φ).left = spMap φ.toRingHom := rfl

theorem spH_comp {A A' A'' : Type} [CommRing A] [Algebra S A] [CommRing A'] [Algebra S A'] [CommRing A'']
    [Algebra S A''] (φ : A →ₐ[S] A') (ψ : A' →ₐ[S] A'') : spH σ (ψ.comp φ) = spH σ ψ ≫ spH σ φ := by
  ext1
  change spMap _ = spMap _ ≫ spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem exists_ext_affine (K B C : Type) [IsDomain S] [IsIntegrallyClosed S] [Field K] [Algebra S K]
    [IsFractionRing S K] [CommRing B] [Algebra S B] [Module.Finite S B] [Module.Projective S B]
    [Algebra.Etale K (K ⊗[S] B)] [Nontrivial (K ⊗[S] B)] [CommRing C] [Algebra S C] [Module.Finite S C]
    (G : Over X) [GrpObj G] [IsCommMonObj G] [IsSeparated G.hom] (k : ℕ) (n : spO σ C ⟶ G) (hn : n ^ k = 1)
    (univ : ∀ (A : Type) [CommRing A] [Algebra S A] (x : spO σ A ⟶ G), x ^ k = 1 →
      ∃! φ : C →ₐ[S] A, spH σ φ ≫ n = x)
    (u : spO σ (K ⊗[S] B) ⟶ G) (d : spO σ (B ⊗[S] B) ⟶ G) (hu : u ^ k = 1) (hd : d ^ k = 1)
    (H : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra S F] [Algebra K F] [IsScalarTower S K F]
      (a b : K ⊗[S] B →ₐ[S] F), spH σ a ≫ u = (spH σ b ≫ u) *
        (spH σ (Algebra.TensorProduct.productMap (a.comp Algebra.TensorProduct.includeRight)
          (b.comp Algebra.TensorProduct.includeRight)) ≫ d)) :
    ∃ v : spO σ B ⟶ G, spH σ Algebra.TensorProduct.includeRight ≫ v = u := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[S] B)
  letI := Ideal.Quotient.field m
  let F := AlgebraicClosure ((K ⊗[S] B) ⧸ m)
  let b₀ : K ⊗[S] B →ₐ[S] F := IsScalarTower.toAlgHom S (K ⊗[S] B) F
  obtain ⟨μ₀, hμ, -⟩ := univ _ u hu
  let O := integralClosure S F
  let β : B →ₐ[S] O := (b₀.comp Algebra.TensorProduct.includeRight).codRestrict O fun x =>
    (Algebra.IsIntegral.isIntegral (R := S) x).map _
  let γ₀ : C →ₐ[S] O := (b₀.comp μ₀).codRestrict O fun x =>
    (Algebra.IsIntegral.isIntegral (R := S) x).map _
  let w : spO σ (O ⊗[S] B) ⟶ G := (spH σ (Algebra.TensorProduct.includeLeft.comp γ₀) ≫ n) *
    (spH σ (Algebra.TensorProduct.productMap Algebra.TensorProduct.includeRight
      (Algebra.TensorProduct.includeLeft.comp β)) ≫ d)
  have hw : w ^ k = 1 := by
    simp only [w]
    rw [mul_pow, ← MonObj.comp_pow, ← MonObj.comp_pow, hn, hd]
    simp
  obtain ⟨ω, hω, -⟩ := univ _ w hw
  let iK : K ⊗[S] B →ₐ[S] F ⊗[S] B := Algebra.TensorProduct.map (IsScalarTower.toAlgHom S K F) (AlgHom.id S B)
  let iO : O ⊗[S] B →ₐ[S] F ⊗[S] B := Algebra.TensorProduct.map O.val (AlgHom.id S B)
  have hred : _root_.IsReduced (F ⊗[S] B) := by
    have := Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[K] (K ⊗[S] B))
    exact isReduced_of_injective _ (Algebra.TensorProduct.cancelBaseChange S K F F B).symm.injective
  have key : spH σ iK ≫ u = spH σ iO ≫ w := by
    ext1
    refine ext_of_geom G.hom _ _ (by rw [Over.w, Over.w]) fun F' _ _ φ => ?_
    letI : Algebra S F' := (φ.comp (algebraMap S (F ⊗[S] B))).toAlgebra
    letI : Algebra K F' := (φ.comp (algebraMap K (F ⊗[S] B))).toAlgebra
    have : IsScalarTower S K F' := IsScalarTower.of_algebraMap_eq fun x =>
      congrArg φ (IsScalarTower.algebraMap_apply S K (F ⊗[S] B) x)
    let φ' : F ⊗[S] B →ₐ[S] F' := ⟨φ, fun _ => rfl⟩
    have h := H F' (φ'.comp iK) (φ'.comp (Algebra.TensorProduct.includeLeft.comp b₀))
    suffices spH σ φ' ≫ spH σ iK ≫ u = spH σ φ' ≫ spH σ iO ≫ w from congrArg CommaMorphism.left this
    rw [← Category.assoc, ← spH_comp, h, ← Category.assoc, ← spH_comp]
    simp only [w]
    rw [MonObj.comp_mul, ← hμ]
    simp only [← Category.assoc, ← spH_comp]
    congr 3
    ext x
    · simp [iK, iO]
    · simp [iO, β, ← Algebra.TensorProduct.one_def]
      rfl
  have hμω : iK.comp μ₀ = iO.comp ω := by
    refine (univ _ (spH σ iK ≫ u) (by rw [← MonObj.comp_pow, hu]; simp)).unique ?_ ?_
    · rw [spH_comp, Category.assoc, hμ]
    · rw [spH_comp, Category.assoc, hω, key]
  have hB : ∀ z : C, μ₀ z ∈ (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B).range := fun z => by
    obtain ⟨b, hb⟩ := mem_of_integral S K F B (μ₀ z) (ω z) (DFunLike.congr_fun hμω z)
    exact ⟨b, hb.symm⟩
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B) :=
    Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective S K)
  let e := AlgEquiv.ofInjective _ hinj
  refine ⟨spH σ (e.symm.toAlgHom.comp (μ₀.codRestrict _ hB)) ≫ n, ?_⟩
  rw [← Category.assoc, ← spH_comp, ← hμ]
  congr 2
  ext z
  exact congrArg Subtype.val (e.apply_symm_apply ⟨μ₀ z, hB z⟩)

end Affine

section Global

variable {R : Type} [CommRing R] [IsDomain R] {W : (Sp R).Opens} {G : Over (Sp R)} [GrpObj G] {k : ℕ}

theorem tors_univ {Z : Over W.toScheme} {n : overW W Z ⟶ G}
    (univ : ∀ (T : Over W.toScheme) (x : overW W T ⟶ G), x ^ k = 1 → ∃! h : T ⟶ Z, (Over.map W.ι).map h ≫ n = x)
    (T : Over (Sp R)) (t : T.left ⟶ W.toScheme) (ht : t ≫ W.ι = T.hom) (x : T ⟶ G) (hx : x ^ k = 1) :
    ∃! h : T.left ⟶ Z.left, h ≫ Z.hom = t ∧ h ≫ n.left = x.left := by
  let i : overW W (Over.mk t) ⟶ T := Over.homMk (𝟙 T.left) ((Category.id_comp _).trans ht.symm)
  obtain ⟨h, h1, h2⟩ := univ (Over.mk t) (i ≫ x) (by rw [← MonObj.comp_pow, hx]; simp)
  refine ⟨h.left, ⟨Over.w h, (congrArg CommaMorphism.left h1).trans (Category.id_comp _)⟩, fun h' hh => ?_⟩
  exact congrArg CommaMorphism.left (h2 (Over.homMk h' hh.1)
    (Over.OverMorphism.ext (hh.2.trans (Category.id_comp _).symm)))

theorem exists_ext_local [IsCommMonObj G] [IsSeparated G.hom] (hG : TorsFiniteFlat G W k) (N : Over W.toScheme)
    (hN : FinFlatEt N) (hs : Surjective N.hom) (u : genPart (overW W N) ⟶ G) (d : overW W (N ⊗ N) ⟶ G)
    (hu : u ^ k = 1) (hd : d ^ k = 1)
    (H : ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
      (a b : TF (R := R) F ⟶ genPart (overW W N)) (c : TF (R := R) F ⟶ overW W (N ⊗ N)),
      c ≫ (Over.map W.ι).map (fst N N) = a ≫ genι _ → c ≫ (Over.map W.ι).map (snd N N) = b ≫ genι _ →
      a ≫ u = (b ≫ u) * (c ≫ d))
    (S : Type) [CommRing S] [IsDomain S] [IsNoetherianRing S] [IsIntegrallyClosed S] [Algebra R S]
    [Algebra S (FractionRing R)] [IsScalarTower R S (FractionRing R)] [IsFractionRing S (FractionRing R)]
    (j : Sp S ⟶ W.toScheme) (hj : j ≫ W.ι = spMap (algebraMap R S)) :
    ∃ (T : Scheme.{0}) (g : T ⟶ N.left) (q : T ⟶ Sp S), IsPullback g q N.hom j ∧
      ∃ (e : (genPart (overW W N)).left ⟶ T) (v : T ⟶ G.left), e ≫ g = (genι _).left ∧
        v ≫ G.hom = g ≫ (overW W N).hom ∧ e ≫ v = u.left := by
  obtain ⟨Z, n, hZ, -, hn, univ⟩ := hG
  obtain ⟨hN1, hN2, hN3⟩ := hN
  obtain ⟨B, _, _, g, hg⟩ := exists_chart N.hom S j
  obtain ⟨C, _, _, z, hz⟩ := exists_chart Z.hom S j
  let K := FractionRing R
  let σ : Sp S ⟶ Sp R := j ≫ W.ι
  have : Module.Finite S B := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1
    (MorphismProperty.of_isPullback (P := @IsFinite) hg hN1))
  have : Module.Finite S C := RingHom.finite_algebraMap.1 ((IsFinite.SpecMap_iff _).1
    (MorphismProperty.of_isPullback (P := @IsFinite) hz hZ))
  have : Module.Flat S B := RingHom.flat_algebraMap_iff.1 (Flat.SpecMap_iff.1
    (MorphismProperty.of_isPullback (P := @Flat) hg hN2))
  have : Module.FinitePresentation S B := Module.finitePresentation_of_finite S B
  have : Module.Projective S B := Module.Flat.projective_of_finitePresentation
  have hK : spMap (algebraMap S K) ≫ σ = jK R := by
    simp only [σ]
    rw [hj, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hA0 := (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S K B)).flip.paste_horiz hg
  have hA1 : IsPullback (spMap (algebraMap S K) ≫ j) (𝟙 _) W.ι (jK R) :=
    IsPullback.of_vert_isIso_mono ⟨by rw [Category.id_comp, Category.assoc]; exact hK⟩
  have hA : IsPullback (spMap (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B).toRingHom ≫ g)
      (spMap (algebraMap K (K ⊗[S] B))) (overW W N).hom (jK R) := by
    have := hA0.paste_vert hA1
    rw [Category.comp_id] at this
    exact this
  have : Algebra.Etale K (K ⊗[S] B) := by
    rw [← RingHom.etale_algebraMap]
    refine (HasRingHomProperty.Spec_iff (P := @Etale) (φ := CommRingCat.ofHom (algebraMap K (K ⊗[S] B)))).1 ?_
    change Etale (spMap (algebraMap K (K ⊗[S] B)))
    rw [← hA.isoPullback_hom_snd]
    infer_instance
  have : Nontrivial (K ⊗[S] B) := by
    obtain ⟨y, -⟩ := (MorphismProperty.of_isPullback (P := @Surjective) hA0 hs).surj (IsLocalRing.closedPoint K)
    exact PrimeSpectrum.nonempty_iff_nontrivial.1 ⟨y⟩
  let gO : spO σ B ⟶ overW W N := Over.homMk g (by
    change g ≫ N.hom ≫ W.ι = _ ≫ j ≫ W.ι
    rw [← Category.assoc, hg.w, Category.assoc])
  let zO : spO σ C ⟶ overW W Z := Over.homMk z (by
    change z ≫ Z.hom ≫ W.ι = _ ≫ j ≫ W.ι
    rw [← Category.assoc, hz.w, Category.assoc])
  let EO : spO σ (K ⊗[S] B) ⟶ genPart (overW W N) := Over.homMk hA.isoPullback.hom (by
    change hA.isoPullback.hom ≫ pullback.fst _ _ ≫ _ = _
    rw [← Category.assoc, hA.isoPullback_hom_fst]
    exact Over.w (spH σ (Algebra.TensorProduct.includeRight : B →ₐ[S] K ⊗[S] B) ≫ gO))
  have hEO : EO ≫ genι _ = spH σ Algebra.TensorProduct.includeRight ≫ gO :=
    Over.OverMorphism.ext hA.isoPullback_hom_fst
  let hB : ∀ φ : B →ₐ[S] B ⊗[S] B, Over.mk (spMap (algebraMap S (B ⊗[S] B)) ≫ j) ⟶ N := fun φ =>
    Over.homMk (spH σ φ ≫ gO).left (by
      rw [← cancel_mono W.ι, Category.assoc]
      exact (Over.w (spH σ φ ≫ gO)).trans (Category.assoc _ _ _).symm)
  let l := lift (hB Algebra.TensorProduct.includeLeft) (hB Algebra.TensorProduct.includeRight)
  let lO : spO σ (B ⊗[S] B) ⟶ overW W (N ⊗ N) := Over.homMk l.left (by
    change l.left ≫ (N ⊗ N).hom ≫ W.ι = _ ≫ j ≫ W.ι
    rw [← Category.assoc, Over.w l]
    exact Category.assoc _ _ _)
  have hl1 : lO ≫ (Over.map W.ι).map (fst N N) = spH σ Algebra.TensorProduct.includeLeft ≫ gO :=
    Over.OverMorphism.ext (congrArg CommaMorphism.left (lift_fst (hB Algebra.TensorProduct.includeLeft)
      (hB Algebra.TensorProduct.includeRight)) :)
  have hl2 : lO ≫ (Over.map W.ι).map (snd N N) = spH σ Algebra.TensorProduct.includeRight ≫ gO :=
    Over.OverMorphism.ext (congrArg CommaMorphism.left (lift_snd (hB Algebra.TensorProduct.includeLeft)
      (hB Algebra.TensorProduct.includeRight)) :)
  obtain ⟨v, hv⟩ := exists_ext_affine σ K B C G k (zO ≫ n) (by rw [← MonObj.comp_pow, hn]; simp)
    (fun A _ _ x hx => by
      obtain ⟨h, ⟨h1, h2⟩, h3⟩ := tors_univ univ _ (spMap (algebraMap S A) ≫ j) (Category.assoc _ _ _) x hx
      obtain ⟨φ, hφ⟩ := Spec.map_surjective (hz.lift h _ h1)
      have e1 : Spec.map φ ≫ z = h := by rw [hφ, hz.lift_fst]
      have e2 : Spec.map φ ≫ spMap (algebraMap S C) = spMap (algebraMap S A) := by rw [hφ, hz.lift_snd]
      rw [← Spec.map_comp] at e2
      have e3 := congrArg CommRingCat.Hom.hom (Spec.map_injective e2)
      let φ' : C →ₐ[S] A := ⟨φ.hom, fun s => DFunLike.congr_fun e3 s⟩
      refine ⟨φ', Over.OverMorphism.ext ?_, fun ψ hψ => ?_⟩
      · change Spec.map φ ≫ z ≫ n.left = x.left
        rw [← Category.assoc, e1, h2]
      · have w1 : spMap ψ.toRingHom ≫ spMap (algebraMap S C) = spMap (algebraMap S A) := by
          rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
          exact ψ.comp_algebraMap
        have e4 : spMap ψ.toRingHom ≫ z = h := h3 _ ⟨by
          rw [Category.assoc, hz.w, ← Category.assoc, w1], by
          rw [Category.assoc]; exact congrArg CommaMorphism.left hψ⟩
        have e5 : spMap ψ.toRingHom = Spec.map φ := hz.hom_ext (by rw [e4, e1]) (by
          rw [w1, ← Spec.map_comp, e2])
        have e6 := congrArg CommRingCat.Hom.hom (Spec.map_injective e5)
        exact AlgHom.ext fun c => DFunLike.congr_fun e6 c)
    (EO ≫ u) (lO ≫ d) (by rw [← MonObj.comp_pow, hu]; simp) (by rw [← MonObj.comp_pow, hd]; simp)
    (fun F _ _ _ _ _ a b => by
      let i : spO σ F ⟶ TF (R := R) F := Over.homMk (𝟙 _) (by
        change 𝟙 _ ≫ spMap (algebraMap K F) ≫ jK R = spMap (algebraMap S F) ≫ σ
        rw [Category.id_comp, ← hK, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
          ← IsScalarTower.algebraMap_eq])
      let i' : TF (R := R) F ⟶ spO σ F := Over.homMk (𝟙 _) (by
        have := Over.w i
        exact (Category.id_comp _).trans (this.symm.trans (Category.id_comp _)))
      have hi : i ≫ i' = 𝟙 _ := Over.OverMorphism.ext (Category.id_comp _)
      have h := H F (i' ≫ spH σ a ≫ EO) (i' ≫ spH σ b ≫ EO)
        (i' ≫ spH σ (Algebra.TensorProduct.productMap (a.comp Algebra.TensorProduct.includeRight)
          (b.comp Algebra.TensorProduct.includeRight)) ≫ lO)
        (by simp only [Category.assoc, hl1, hEO]
            simp only [← Category.assoc (spH σ _), ← spH_comp, Algebra.TensorProduct.productMap_left])
        (by simp only [Category.assoc, hl2, hEO]
            simp only [← Category.assoc (spH σ _), ← spH_comp, Algebra.TensorProduct.productMap_right])
      have h' := congrArg (i ≫ ·) h
      simp only [MonObj.comp_mul, Category.assoc, reassoc_of% hi] at h'
      exact h')
  refine ⟨_, g, _, hg, hA.isoPullback.inv ≫ (spH σ Algebra.TensorProduct.includeRight).left, v.left, ?_, ?_, ?_⟩
  · rw [Category.assoc, Iso.inv_comp_eq]
    exact (congrArg CommaMorphism.left hEO).symm
  · exact (Over.w v).trans (Over.w gO).symm
  · rw [Category.assoc, Iso.inv_comp_eq]
    exact congrArg CommaMorphism.left hv

end Global

end GlobalTheory.FlatTors.TorsExt

namespace GlobalTheory.FlatTors

open TorsExt

theorem exists_tors_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (W : (Sp R).Opens) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (k : ℕ), IsSeparated G.hom → TorsFiniteFlat G W k → ∀ N : Over W.toScheme, FinFlatEt N → Surjective N.hom → ∀ (u : genPart (overW W N) ⟶ G) (d : overW W (N ⊗ N) ⟶ G), u ^ k = 1 → d ^ k = 1 → (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (a b : TF (R := R) F ⟶ genPart (overW W N)) (c : TF (R := R) F ⟶ overW W (N ⊗ N)), c ≫ (Over.map W.ι).map (fst N N) = a ≫ genι _ → c ≫ (Over.map W.ι).map (snd N N) = b ≫ genι _ → a ≫ u = (b ≫ u) * (c ≫ d)) → ∃ v : overW W N ⟶ G, v ^ k = 1 ∧ genι _ ≫ v = u := by
  intro R _ _ _ _ W G _ _ k hsep hG N hN hs u d hu hd H
  have loc : ∀ x : N.left, ∃ (T : Scheme.{0}) (g : T ⟶ N.left), IsOpenImmersion g ∧ (∃ y, g y = x) ∧
      ∃ (e : (genPart (overW W N)).left ⟶ T) (v : T ⟶ G.left), e ≫ g = (genι _).left ∧
        v ≫ G.hom = g ≫ (overW W N).hom ∧ e ≫ v = u.left := by
    intro x
    let p : PrimeSpectrum R := W.ι (N.hom x)
    have hp : p ∈ W := (N.hom x).2
    obtain ⟨_, ⟨f, rfl⟩, hpf, hfW⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp W.isOpen
    have hf : f ≠ 0 := by
      rintro rfl
      exact hpf p.asIdeal.zero_mem
    have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
    let S := Localization.Away f
    have : IsDomain S := IsLocalization.isDomain_localization hle
    have : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S _ hle
    have : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers f) S inferInstance
    letI : Algebra S (FractionRing R) := IsLocalization.localizationAlgebraOfSubmonoidLe S (FractionRing R) _ _ hle
    have : IsScalarTower R S (FractionRing R) :=
      IsLocalization.localization_isScalarTower_of_submonoid_le S (FractionRing R) _ _ hle
    have : IsFractionRing S (FractionRing R) :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers f) S (FractionRing R)
    have hop : IsOpenImmersion (spMap (algebraMap R S)) := IsOpenImmersion.of_isLocalization f
    have hr : Set.range (spMap (algebraMap R S)) = (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum R)) :=
      PrimeSpectrum.localization_away_comap_range S f
    let j : Sp S ⟶ W.toScheme := IsOpenImmersion.lift W.ι (spMap (algebraMap R S)) (by
      rw [hr, Scheme.Opens.range_ι]; exact hfW)
    have hj : j ≫ W.ι = spMap (algebraMap R S) := IsOpenImmersion.lift_fac _ _ _
    have hjo : IsOpenImmersion j := by
      have : IsOpenImmersion (j ≫ W.ι) := by rw [hj]; exact hop
      exact IsOpenImmersion.of_comp j W.ι
    obtain ⟨T, g, q, hg, h⟩ := exists_ext_local hG N hN hs u d hu hd H S j hj
    refine ⟨T, g, MorphismProperty.of_isPullback (P := @IsOpenImmersion) hg.flip hjo, ?_, h⟩
    obtain ⟨s, hs⟩ : p ∈ Set.range (spMap (algebraMap R S)) := by rw [hr]; exact hpf
    have hs' : N.hom x = j s := W.ι.injective (by rw [← Scheme.Hom.comp_apply j, hj]; exact hs.symm)
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hg x s hs'
    exact ⟨y, hy⟩
  choose T g hg hy e v he hv hu' using loc
  have hfl : Flat (overW W N).hom := by
    have := hN.2.1
    change Flat (N.hom ≫ W.ι)
    infer_instance
  have hj : IsSchemeTheoreticallyDominant (jK R) := schDom_spec_map _ (IsFractionRing.injective R _)
  have hdom : IsSchemeTheoreticallyDominant (genι (overW W N)).left :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.fst (overW W N).hom (jK R)))
  have hqc : QuasiCompact (genι (overW W N)).left :=
    inferInstanceAs (QuasiCompact (pullback.fst (overW W N).hom (jK R)))
  let 𝒰 : N.left.OpenCover := Scheme.Cover.mkOfCovers N.left T g (fun x => ⟨x, hy x⟩) hg
  have hc : ∀ x y, pullback.fst (g x) (g y) ≫ v x = pullback.snd (g x) (g y) ≫ v y := by
    intro x y
    let r : pullback (g x) (g y) ⟶ (overW W N).left := pullback.fst (g x) (g y) ≫ g x
    have : IsOpenImmersion r := inferInstanceAs (IsOpenImmersion (pullback.fst (g x) (g y) ≫ g x))
    refine ext_of_schDom G.hom ?_ (pullback.fst r (genι (overW W N)).left) ?_
    · rw [Category.assoc, Category.assoc, hv, hv, ← Category.assoc, pullback.condition, Category.assoc]
    · have h1 : pullback.fst r (genι (overW W N)).left ≫ pullback.fst (g x) (g y) =
          pullback.snd r (genι (overW W N)).left ≫ e x := by
        rw [← cancel_mono (g x), Category.assoc, Category.assoc, he]
        exact pullback.condition
      have h2 : pullback.fst r (genι (overW W N)).left ≫ pullback.snd (g x) (g y) =
          pullback.snd r (genι (overW W N)).left ≫ e y := by
        rw [← cancel_mono (g y), Category.assoc, Category.assoc, he, ← pullback.condition]
        exact pullback.condition
      rw [← Category.assoc, h1, ← Category.assoc, h2, Category.assoc, Category.assoc, hu', hu']
  let v₀ : N.left ⟶ G.left := 𝒰.glueMorphisms v hc
  have hv₀ : ∀ x, g x ≫ v₀ = v x := fun x => 𝒰.ι_glueMorphisms v hc x
  have hov : v₀ ≫ G.hom = (overW W N).hom := 𝒰.hom_ext _ _ fun x => by
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ G.hom) (hv₀ x)).trans (hv x))
  let V : overW W N ⟶ G := Over.homMk v₀ hov
  have hV : genι _ ≫ V = u := by
    ext1
    change (genι (overW W N)).left ≫ v₀ = u.left
    by_cases hne : Nonempty N.left
    · obtain ⟨x⟩ := hne
      rw [← he x, Category.assoc, hv₀, hu']
    · have : IsEmpty (genPart (overW W N)).left := ⟨fun y => hne ⟨(genι (overW W N)).left y⟩⟩
      exact (isInitialOfIsEmpty).hom_ext _ _
  refine ⟨V, ?_, hV⟩
  ext1
  refine ext_of_schDom G.hom (by rw [Over.w, Over.w]) (genι (overW W N)).left ?_
  have : genι _ ≫ V ^ k = genι _ ≫ 1 := by
    rw [MonObj.comp_pow, hV, hu]
    simp
  exact congrArg CommaMorphism.left this

end GlobalTheory.FlatTors
