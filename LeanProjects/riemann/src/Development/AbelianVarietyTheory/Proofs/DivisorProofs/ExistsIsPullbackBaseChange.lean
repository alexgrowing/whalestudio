import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteAndFlatTorsion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.NatCardAlgHomEqFinrankOfIsReducedOfIsFractionRin

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct Coalgebra Bialgebra WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme mulN)
open GlobalTheory.DeRham (spOver spOver_comp)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianPDiv

open PDiv

variable {O : Type} [CommRing O] {A : Over (Sp O)} [GrpObj A]

def IsUnivTorsion (N : ℕ) {R : Type} [CommRing R] [Algebra O R] (y : SpAlg O R ⟶ A) : Prop :=
  y ^ N = 1 ∧ ∀ (B : Type) [CommRing B] [Algebra O B] (z : SpAlg O B ⟶ A), z ^ N = 1 →
    ∃! φ : R →ₐ[O] B, spOver φ ≫ y = z

section Scheme

variable {N : ℕ} {R : Type} [CommRing R] [Algebra O R]

theorem one_left (B : Type) [CommRing B] [Algebra O B] :
    (1 : SpAlg O B ⟶ A).left = spMap (algebraMap O B) ≫ η[A].left := by
  rw [Hom.one_def, Over.comp_left]; rfl

theorem isUnivTorsion_of_isPullback (y : SpAlg O R ⟶ A)
    (h : IsPullback y.left (spMap (algebraMap O R)) (mulN A N).left η[A].left) :
    IsUnivTorsion N y := by
  have key : ∀ (B : Type) [CommRing B] [Algebra O B] (z : SpAlg O B ⟶ A), z ^ N = 1 ↔
      z.left ≫ (mulN A N).left = spMap (algebraMap O B) ≫ η[A].left := fun B _ _ z => by
    rw [← Over.comp_left, GrpTangent.comp_mulN, ← one_left]
    exact ⟨congrArg _, Over.OverMorphism.ext⟩
  refine ⟨(key R y).2 h.w, fun B _ _ z hz => ?_⟩
  have hw := (key B z).1 hz
  obtain ⟨χ, hχ⟩ := Spec.map_surjective (R := .of R) (S := .of B) (h.lift _ _ hw)
  have hc : CommRingCat.ofHom (algebraMap O R) ≫ χ = CommRingCat.ofHom (algebraMap O B) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hχ]
    exact h.lift_snd _ _ hw
  refine ⟨⟨χ.hom, fun r => congr(($hc).hom r)⟩, Over.OverMorphism.ext ?_, fun φ hφ => ?_⟩
  · change Spec.map χ ≫ y.left = z.left
    rw [hχ]
    exact h.lift_fst _ _ hw
  · have h₅ : spMap (φ : R →+* B) = Spec.map χ := by
      rw [hχ]
      refine h.hom_ext ?_ ?_
      · exact (congrArg Over.Hom.left hφ).trans (h.lift_fst _ _ hw).symm
      · exact (Over.w (spOver φ)).trans (h.lift_snd _ _ hw).symm
    have h₆ := Spec.map_injective h₅
    exact AlgHom.ext fun a => congr(($h₆).hom a)

theorem exists_isPullback (hA : IsAbelianScheme A) (hN : 1 ≤ N) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (y : SpAlg O R ⟶ A), Module.Finite O R ∧
      Module.Projective O R ∧
      IsPullback y.left (spMap (algebraMap O R)) (mulN A N).left η[A].left := by
  obtain ⟨h1, h2⟩ := AbTorsionAnyBase.isFinite_and_flat_mulA _ A hA N hN
  rw [ReciprocityTheory.ChartRestriction.G.Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
  have := hA.smooth
  have : LocallyOfFinitePresentation ((mulN A N).left ≫ A.hom) := by rw [Over.w]; infer_instance
  have h3 := TangentCrit.locallyOfFinitePresentation_of_comp (mulN A N).left A.hom
  let e : Sp O ⟶ A.left := η[A].left
  let X := pullback (mulN A N).left e
  have : IsAffine X := isAffine_of_isAffineHom (pullback.snd (mulN A N).left e)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ pullback.snd (mulN A N).left e)
  have H : IsPullback (X.isoSpec.inv ≫ pullback.fst (mulN A N).left e) (Spec.map ψ)
      (mulN A N).left e := by
    rw [hψ]
    refine (IsPullback.of_hasPullback (mulN A N).left e).of_iso X.isoSpec (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  have f1 : ψ.hom.Finite := (IsFinite.SpecMap_iff _).1 (MorphismProperty.of_isPullback (P := @IsFinite) H h1)
  have f2 : ψ.hom.Flat := (HasRingHomProperty.Spec_iff (P := @Flat)).1
    (MorphismProperty.of_isPullback (P := @Flat) H h2)
  have f3 : ψ.hom.FinitePresentation := (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).1
    (MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H h3)
  let _ : Algebra O Γ(X, ⊤) := ψ.hom.toAlgebra
  have : Module.Finite O Γ(X, ⊤) := f1
  have : Module.Flat O Γ(X, ⊤) := f2
  have : Algebra.FinitePresentation O Γ(X, ⊤) := f3
  have := Module.FinitePresentation.of_finite_of_finitePresentation O Γ(X, ⊤)
  refine ⟨Γ(X, ⊤), inferInstance, inferInstance,
    Over.homMk (X.isoSpec.inv ≫ pullback.fst (mulN A N).left e) ?_, inferInstance,
    Module.Flat.projective_of_finitePresentation, H⟩
  have h4 : e ≫ A.hom = 𝟙 _ := Over.w η[A]
  rw [← Over.w (mulN A N), ← Category.assoc, H.w, Category.assoc, h4, Category.comp_id]
  rfl

theorem exists_isPullback_baseChange (y : SpAlg O R ⟶ A)
    (h : IsPullback y.left (spMap (algebraMap O R)) (mulN A N).left η[A].left)
    (K : Type) [CommRing K] [Algebra O K] :
    ∃ y' : SpAlg K (K ⊗[O] R) ⟶ (Over.pullback (spMap (algebraMap O K))).obj A,
      IsPullback y'.left (spMap (algebraMap K (K ⊗[O] R)))
        (mulN ((Over.pullback (spMap (algebraMap O K))).obj A) N).left
        η[(Over.pullback (spMap (algebraMap O K))).obj A].left := by
  let t := spMap (algebraMap O K)
  let B := (Over.pullback t).obj A
  have P1 : IsPullback (spMap (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := R)).toRingHom)
      (spMap (algebraMap K (K ⊗[O] R))) (spMap (algebraMap O R)) t :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct O K R)).flip
  have P2 := P1.paste_horiz h
  have w : pullback.fst A.hom t ≫ (mulN A N).left = (mulN B N).left ≫ pullback.fst A.hom t := by
    rw [← GrpTangent.pullback_map_mulN]
    exact (pullback.lift_fst _ _ _).symm
  have Q : IsPullback (pullback.fst A.hom t) (mulN B N).left (mulN A N).left (pullback.fst A.hom t) := by
    refine IsPullback.of_bot ?_ w (IsPullback.of_hasPullback A.hom t)
    rw [Over.w (mulN A N)]
    exact (Over.w (mulN B N)).symm ▸ IsPullback.of_hasPullback A.hom t
  rw [← GrpTangent.one_pullback_left_fst] at P2
  let l := Q.lift _ (spMap (algebraMap K (K ⊗[O] R)) ≫ η[B].left) (P2.w.trans (Category.assoc _ _ _).symm)
  have hl : l ≫ (mulN B N).left = spMap (algebraMap K (K ⊗[O] R)) ≫ η[B].left := Q.lift_snd _ _ _
  have h4 : η[B].left ≫ B.hom = 𝟙 _ := Over.w η[B]
  refine ⟨Over.homMk l ?_, IsPullback.of_right ?_ hl Q⟩
  · rw [← Over.w (mulN B N), ← Category.assoc]
    refine (congrArg (· ≫ B.hom) hl).trans ?_
    rw [Category.assoc, h4]
    exact Category.comp_id _
  · exact (Q.lift_fst _ _ (P2.w.trans (Category.assoc _ _ _).symm)).symm ▸ P2

theorem finrank_eq_of_field {K : Type} [Field K] [IsAlgClosed K] {B : Over (Sp K)} [GrpObj B]
    (hB : IsAbelianScheme B) {g : ℕ} (hg : SmoothOfRelativeDimension g B.hom) (hN : (N : K) ≠ 0)
    {S : Type} [CommRing S] [Algebra K S] (y : SpAlg K S ⟶ B)
    (h : IsPullback y.left (spMap (algebraMap K S)) (mulN B N).left η[B].left) :
    Module.finrank K S = N ^ (2 * g) := by
  have := hB.comm
  have := hB.smooth
  have he : Etale (mulN B N).left := GrpTangent.etale_mulN B (by
    simpa using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
  have : Algebra.Etale K S := RingHom.etale_algebraMap.1 ((HasRingHomProperty.Spec_iff (P := @Etale)).1
    (MorphismProperty.of_isPullback (P := @Etale) h he))
  have hy := isUnivTorsion_of_isPullback y h
  rw [← natCard_algHom_eq_finrank_of_etale K S K,
    ← UU.TorsionCount.card_torsion_points_unconditional K B g N hB hg hN]
  let i : SpAlg K K ≅ 𝟙_ (Over (Sp K)) := Over.isoMk (Iso.refl _) (by
    exact (Category.comp_id _).trans (Cris.spMap_id K).symm)
  refine Nat.card_eq_of_bijective (fun φ => ⟨i.inv ≫ spOver φ ≫ y, by
    rw [← MonObj.comp_pow, ← MonObj.comp_pow, hy.1, MonObj.comp_one, MonObj.comp_one]⟩) ⟨fun φ ψ e => ?_, fun x => ?_⟩
  · exact (hy.2 K (spOver ψ ≫ y) (by rw [← MonObj.comp_pow, hy.1, MonObj.comp_one])).unique
      ((cancel_epi i.inv).1 (congrArg Subtype.val e)) rfl
  · obtain ⟨φ, hφ, -⟩ := hy.2 K (i.hom ≫ x.1) (by rw [← MonObj.comp_pow, x.2, MonObj.comp_one])
    exact ⟨φ, Subtype.ext (by simp only [hφ, Iso.inv_hom_id_assoc])⟩

theorem exists_isUnivTorsion [IsDomain O] (hA : IsAbelianScheme A) {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) (hN : (N : O) ≠ 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (y : SpAlg O R ⟶ A), Module.Finite O R ∧
      Module.Projective O R ∧ IsUnivTorsion N y ∧
      ∀ q : PrimeSpectrum O, Module.rankAtStalk R q = N ^ (2 * g) := by
  obtain ⟨R, _, _, y, h1, h2, h⟩ := exists_isPullback (N := N) hA
    (Nat.one_le_iff_ne_zero.2 (by rintro rfl; exact hN Nat.cast_zero))
  refine ⟨R, inferInstance, inferInstance, y, h1, h2, isUnivTorsion_of_isPullback y h, fun q => ?_⟩
  let K := AlgebraicClosure (FractionRing O)
  have hi : Function.Injective (algebraMap O K) :=
    (algebraMap (FractionRing O) K).injective.comp (IsFractionRing.injective O _)
  obtain ⟨y', h'⟩ := exists_isPullback_baseChange y h K
  have hr := finrank_eq_of_field (ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback _ A hA)
    ((smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
      (IsPullback.of_hasPullback A.hom (spMap (algebraMap O K))) hg)
    (by rw [← map_natCast (algebraMap O K)]; exact (map_ne_zero_iff _ hi).2 hN) y' h'
  rw [← Module.rankAtStalk_eq_of_le_of_finite_of_flat R
      (p := PrimeSpectrum.comap (algebraMap O K) ⊥) (q := q) ?_, ← Module.rankAtStalk_baseChange,
    Module.rankAtStalk_eq_finrank_of_free, hr]
  · rfl
  · intro a ha
    have ha' : algebraMap O K a = 0 := ha
    rw [(map_eq_zero_iff _ hi).1 ha']
    exact zero_mem _

end Scheme

namespace IsUnivTorsion

variable {N : ℕ} {R : Type} [CommRing R] [Algebra O R] {y : SpAlg O R ⟶ A} (h : IsUnivTorsion N y)
  {B : Type} [CommRing B] [Algebra O B]

include h

theorem comp_pow (φ : R →ₐ[O] B) : (spOver φ ≫ y) ^ N = 1 := by
  rw [← MonObj.comp_pow, h.1, MonObj.comp_one]

theorem inj {φ ψ : R →ₐ[O] B} (e : spOver φ ≫ y = spOver ψ ≫ y) : φ = ψ :=
  (h.2 B _ (h.comp_pow ψ)).unique e rfl

def lift (z : SpAlg O B ⟶ A) (hz : z ^ N = 1) : R →ₐ[O] B := (h.2 B z hz).exists.choose

theorem lift_y (z : SpAlg O B ⟶ A) (hz : z ^ N = 1) : spOver (h.lift z hz) ≫ y = z :=
  (h.2 B z hz).exists.choose_spec

theorem comp_lift_y {C : Type} [CommRing C] [Algebra O C] (f : B →ₐ[O] C) (z : SpAlg O B ⟶ A) (hz : z ^ N = 1) :
    spOver (f.comp (h.lift z hz)) ≫ y = spOver f ≫ z := by
  rw [← spOver_comp, Category.assoc, lift_y]

def counitMap : R →ₐ[O] O := h.lift 1 (one_pow _)

def antipodeMap : R →ₐ[O] R := h.lift y⁻¹ (by rw [inv_pow, h.1, inv_one])

theorem counitMap_y (f : O →ₐ[O] B) : spOver (f.comp h.counitMap) ≫ y = 1 := by
  rw [counitMap, comp_lift_y, MonObj.comp_one]

variable [IsCommMonObj A]

def comulMap : R →ₐ[O] R ⊗[O] R :=
  h.lift ((spOver Algebra.TensorProduct.includeLeft ≫ y) * (spOver Algebra.TensorProduct.includeRight ≫ y))
    (by rw [mul_pow, h.comp_pow, h.comp_pow, _root_.mul_one])

theorem comulMap_y (f : R ⊗[O] R →ₐ[O] B) : spOver (f.comp h.comulMap) ≫ y =
    (spOver (f.comp Algebra.TensorProduct.includeLeft) ≫ y) *
      (spOver (f.comp Algebra.TensorProduct.includeRight) ≫ y) := by
  rw [comulMap, comp_lift_y, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, spOver_comp, spOver_comp]

theorem comulMap_y' (f : R ⊗[O] R →ₐ[O] B) (φ ψ : R →ₐ[O] B) (h₁ : ∀ a, f (a ⊗ₜ 1) = φ a)
    (h₂ : ∀ a, f (1 ⊗ₜ a) = ψ a) : spOver (f.comp h.comulMap) ≫ y = (spOver φ ≫ y) * (spOver ψ ≫ y) := by
  rw [comulMap_y, show f.comp Algebra.TensorProduct.includeLeft = φ from AlgHom.ext h₁,
    show f.comp Algebra.TensorProduct.includeRight = ψ from AlgHom.ext h₂]

@[reducible] def bialgebra : Bialgebra O R :=
  .ofAlgHom h.comulMap h.counitMap
    (h.inj (by
      let i₁ : R →ₐ[O] R ⊗[O] (R ⊗[O] R) := Algebra.TensorProduct.includeLeft
      let j : R ⊗[O] R →ₐ[O] R ⊗[O] (R ⊗[O] R) := Algebra.TensorProduct.includeRight
      let k : R ⊗[O] R →ₐ[O] R ⊗[O] (R ⊗[O] R) :=
        Algebra.TensorProduct.map (AlgHom.id O R) Algebra.TensorProduct.includeLeft
      rw [← AlgHom.comp_assoc, h.comulMap_y' _ (k.comp h.comulMap) (j.comp Algebra.TensorProduct.includeRight)
          (fun a => ?_) (fun a => by simp [j, Algebra.TensorProduct.one_def]),
        h.comulMap_y' (Algebra.TensorProduct.map (AlgHom.id O R) h.comulMap) i₁ (j.comp h.comulMap) (fun a => by simp [i₁]) (fun a => by simp [j]),
        h.comulMap_y' k i₁ (j.comp Algebra.TensorProduct.includeLeft) (fun a => by simp [k, i₁, Algebra.TensorProduct.one_def])
          (fun a => by simp [k, j]), h.comulMap_y j, _root_.mul_assoc]
      simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      generalize h.comulMap a = c
      induction c with
      | zero => simp
      | add c d hc hd => simp only [add_tmul, map_add, hc, hd]
      | tmul b c => simp [k]))
    (h.inj (by
      rw [h.comulMap_y' _ ((Algebra.ofId O _).comp h.counitMap) (Algebra.TensorProduct.lid O R).symm
        (fun a => by simp [Algebra.ofId_apply]) (fun a => by simp), counitMap_y, _root_.one_mul]))
    (h.inj (by
      rw [h.comulMap_y' _ (Algebra.TensorProduct.rid O O R).symm ((Algebra.ofId O _).comp h.counitMap)
        (fun a => by simp) (fun a => (Algebra.TensorProduct.includeRight (R := O) (A := R) (B := O)).commutes (h.counitMap a)),
        counitMap_y, _root_.mul_one]))

@[reducible] def hopfAlgebra : HopfAlgebra O R :=
  letI := h.bialgebra
  .ofAlgHom h.antipodeMap
    (h.inj (by
      refine (h.comulMap_y' _ h.antipodeMap (AlgHom.id O R)
        (fun a => (Algebra.TensorProduct.lift_tmul ..).trans (by simp))
        (fun a => (Algebra.TensorProduct.lift_tmul ..).trans (by simp))).trans
        (Eq.trans ?_ (h.counitMap_y _).symm)
      rw [antipodeMap, lift_y, spOver_id, Category.id_comp, inv_mul_cancel]))
    (h.inj (by
      refine (h.comulMap_y' _ (AlgHom.id O R) h.antipodeMap
        (fun a => (Algebra.TensorProduct.lift_tmul ..).trans (by simp))
        (fun a => (Algebra.TensorProduct.lift_tmul ..).trans (by simp))).trans
        (Eq.trans ?_ (h.counitMap_y _).symm)
      rw [antipodeMap, lift_y, spOver_id, Category.id_comp, mul_inv_cancel]))

theorem isCocomm : letI := h.hopfAlgebra; IsCocomm O R := by
  let _ := h.hopfAlgebra
  have e : (Algebra.TensorProduct.comm O R R).toAlgHom.comp h.comulMap = (AlgHom.id O _).comp h.comulMap :=
    h.inj (by
      rw [h.comulMap_y' _ Algebra.TensorProduct.includeRight Algebra.TensorProduct.includeLeft
        (fun a => by simp) (fun a => by simp), h.comulMap_y' _ Algebra.TensorProduct.includeLeft
        Algebra.TensorProduct.includeRight (fun a => by simp) (fun a => by simp), mul_comm])
  exact ⟨LinearMap.ext fun a => DFunLike.congr_fun e a⟩

theorem mul_y : letI := h.hopfAlgebra; ∀ φ ψ : WithConv (R →ₐ[O] B),
    spOver (φ * ψ).ofConv ≫ y = (spOver φ.ofConv ≫ y) * (spOver ψ.ofConv ≫ y) := by
  let _ := h.hopfAlgebra
  intro φ ψ
  rw [← h.comulMap_y' (Algebra.TensorProduct.lift φ.ofConv ψ.ofConv fun _ _ => Commute.all _ _) _ _
    (fun a => by simp) (fun a => by simp)]
  exact congrArg (spOver · ≫ y) (AlgHom.ext (AlgHom.convMul_apply φ ψ))

theorem pow_y : letI := h.hopfAlgebra; ∀ (φ : WithConv (R →ₐ[O] B)) (k : ℕ),
    spOver (φ ^ k).ofConv ≫ y = (spOver φ.ofConv ≫ y) ^ k := by
  let _ := h.hopfAlgebra
  exact fun φ k => map_pow (MonoidHom.mk' (fun φ : WithConv (R →ₐ[O] B) => spOver φ.ofConv ≫ y) h.mul_y) φ k

theorem exists_res {M : ℕ} {S : Type} [CommRing S] [Algebra O S] {x : SpAlg O S ⟶ A} (h' : IsUnivTorsion M x)
    (hy : y ^ M = 1) : letI := h.hopfAlgebra; letI := h'.hopfAlgebra; haveI := h'.isCocomm;
    ∃ r : S →ₐc[O] R, Function.Surjective r ∧ RingHom.ker r = torsionIdeal O S N ∧
      spOver (r : S →ₐ[O] R) ≫ x = y := by
  let _ := h.hopfAlgebra
  let _ := h'.hopfAlgebra
  have := h'.isCocomm
  let r := h'.lift y hy
  have hr : spOver r ≫ x = y := h'.lift_y _ _
  have hc : ∀ {C : Type} [CommRing C] [Algebra O C] (f : R →ₐ[O] C), spOver (f.comp r) ≫ x = spOver f ≫ y :=
    fun f => h'.comp_lift_y f _ _
  have ht : ∀ {C : Type} [CommRing C] [Algebra O C] (f : S →ₐ[O] C),
      torsionIdeal O S N ≤ RingHom.ker f ↔ (spOver f ≫ x) ^ N = 1 := fun {C} _ _ f => by
    rw [torsionIdeal_le_ker_iff, ← ofConv_toConv f, ← h'.pow_y, ofConv_toConv,
      ← h'.counitMap_y (Algebra.ofId O C)]
    exact ⟨fun e => by rw [e]; rfl, fun e => ofConv_injective (h'.inj e)⟩
  let π := Ideal.Quotient.mkₐ O (torsionIdeal O S N)
  have hπ := (ht π).1 fun a ha => Ideal.Quotient.eq_zero_iff_mem.2 ha
  let s := h.lift _ hπ
  have hs : s.comp r = π := h'.inj ((hc s).trans (h.lift_y _ _))
  have hk : torsionIdeal O S N ≤ RingHom.ker r := (ht r).2 (by rw [hr, h.1])
  let r' : (S ⧸ torsionIdeal O S N) →ₐ[O] R := Ideal.Quotient.liftₐ _ r hk
  have hr' : r'.comp π = r := Ideal.Quotient.liftₐ_comp _ _ _
  have hs' : r'.comp s = AlgHom.id O R := h.inj (by
    rw [h.comp_lift_y, ← Category.assoc, spOver_comp, hr', hr, spOver_id, Category.id_comp])
  refine ⟨.ofAlgHom r (h'.inj ?_) (h'.inj ?_), fun b => ?_, le_antisymm (fun a ha => ?_) hk, hr⟩
  · exact (hc _).trans ((h.counitMap_y (AlgHom.id O O)).trans (h'.counitMap_y (AlgHom.id O O)).symm)
  · refine (h'.comulMap_y' _ (Algebra.TensorProduct.includeLeft.comp r)
      (Algebra.TensorProduct.includeRight.comp r) (fun a => by simp) (fun a => by simp)).trans ?_
    rw [hc, hc, hc]
    exact (h.comulMap_y (AlgHom.id O _)).symm
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (s b)
    refine ⟨a, (DFunLike.congr_fun hr' a).symm.trans ?_⟩
    exact (congrArg r' ha).trans (DFunLike.congr_fun hs' b)
  · have ha' : r a = 0 := ha
    have : π a = 0 := by rw [← hs, AlgHom.comp_apply, ha', map_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.1 this

end IsUnivTorsion

theorem exists_pDivGroup (p : ℕ) (O : Type) [CommRing O] [IsDomain O] (hp : (p : O) ≠ 0)
    (A : Over (Sp O)) [GrpObj A] (hA : IsAbelianScheme A) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ G : PDivGroup p O, G.height = 2 * g ∧ Nonempty (G.TorsionTower A) := by
  have := hA.comm
  choose R _ _ y h1 h2 h hr using fun n : ℕ => exists_isUnivTorsion (N := p ^ n) hA hg
    (by rw [Nat.cast_pow]; exact pow_ne_zero _ hp)
  choose r r1 r2 r3 using fun n : ℕ => (h n).exists_res (h (n + 1)) (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := 2 * g
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := fun n q => (hr n q).trans (pow_mul _ _ _).symm
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, rfl, ⟨{
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }⟩⟩

end GlobalTheory.AbelianPDiv
