import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
import Development.AutomorphicSpectrum.ParallelStatements.ParallelGeometry.TensorOrderReduction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharacterSectionMultiplicative
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorusPointOverFractionField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.TranslateEq

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.TensorOrderReduction
open scoped TensorProduct

variable {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T]

theorem valAt_top {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (s : Γ(X, ⊤)) :
    valAt x ⊤ le_top s = (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (x.appTop.hom s) := by
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]

theorem chart_sep [Finite T] (Γ : QFGroup R T) (B : Type) [CommRing B] [Algebra R B]
    (c : Spec (CommRingCat.of B) ⟶ Γ.G.left) [IsOpenImmersion c]
    (hc : c ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B))) :
    ∃ (I : Type) (_ : Finite I) (τ : I → T) (e : I → B →ₐ[R] FractionRing R),
      (∀ i, Spec.map (CommRingCat.ofHom (e i).toRingHom) ≫ c = (Γ.pt (τ i)).left) ∧
      ∀ b, (∀ i, e i b = 0) → b = 0 := by
  classical
  let I := {t : T // Set.range (Γ.pt t).left ⊆ Set.range c}
  have lift : ∀ i : I, ∃ e : B →ₐ[R] FractionRing R,
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ c = (Γ.pt i.1).left := by
    intro i
    let g := IsOpenImmersion.lift c (Γ.pt i.1).left i.2
    have hg : g ≫ c = (Γ.pt i.1).left := IsOpenImmersion.lift_fac _ _ _
    let φ : B →+* FractionRing R := (Spec.preimage g).hom
    have hφ : Spec.map (CommRingCat.ofHom φ) = g := Spec.map_preimage g
    have hcomp : φ.comp (algebraMap R B) = algebraMap R (FractionRing R) := by
      have h1 : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap R B))) =
          Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) := by
        rw [CommRingCat.ofHom_comp, Spec.map_comp, hφ, ← hc, ← Category.assoc, hg]
        exact Over.w (Γ.pt i.1)
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    refine ⟨{ φ with commutes' := fun r => congr($hcomp r) }, ?_⟩
    exact (congrArg (· ≫ c) hφ).trans hg
  choose e he using lift
  refine ⟨I, inferInstance, Subtype.val, e, he, fun b hb => ?_⟩
  haveI : Flat Γ.G.hom := Γ.flat
  haveI : Module.Flat R B := by
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R B))) := hc ▸ inferInstance
    rw [Flat.SpecMap_iff] at this
    exact (RingHom.flat_algebraMap_iff).1 this
  haveI : IsReduced (pullback Γ.G.hom (genPt R).hom) := Γ.gen_reduced
  have hred : _root_.IsReduced (B ⊗[R] FractionRing R) := by
    have h1 : IsReduced (pullback (c ≫ Γ.G.hom) (genPt R).hom) :=
      isReduced_of_isOpenImmersion ((pullbackRightPullbackFstIso Γ.G.hom (genPt R).hom c).inv ≫ pullback.snd _ _)
    rw [hc] at h1
    have h2 : IsReduced (pullback (Spec.map (CommRingCat.ofHom (algebraMap R B)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) := h1
    have h3 := isReduced_of_isOpenImmersion (pullbackSpecIso R B (FractionRing R)).inv
    exact (affine_isReduced_iff _).1 h3
  have hinj : Function.Injective
      (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] FractionRing R) :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R (FractionRing R))
  apply hinj
  rw [map_zero]
  refine IsNilpotent.eq_zero (nilpotent_iff_mem_prime.2 fun Q hQ => ?_)
  let P : Spec (CommRingCat.of B) := PrimeSpectrum.comap
    (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] FractionRing R).toRingHom ⟨Q, hQ⟩
  have hP : (Γ.G.hom (c P)).asIdeal = ⊥ := by
    rw [← Scheme.Hom.comp_apply, hc]
    refine eq_bot_iff.2 fun r hr => ?_
    have h1 : (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] FractionRing R) (algebraMap R B r) ∈ Q := hr
    rw [AlgHom.commutes, ← (Algebra.TensorProduct.includeRight :
      FractionRing R →ₐ[R] B ⊗[R] FractionRing R).commutes] at h1
    by_contra h0
    have h2 : algebraMap R (FractionRing R) r ≠ 0 := fun h =>
      h0 ((injective_iff_map_eq_zero _).1 (IsFractionRing.injective R (FractionRing R)) r h)
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 ((Ne.isUnit h2).map _))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hP
  have hr : Set.range (Γ.pt t).left ⊆ Set.range c := by
    rintro _ ⟨y, rfl⟩
    exact ⟨P, by rw [← hx, Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) x y]⟩
  have hPx : Spec.map (CommRingCat.ofHom (e ⟨t, hr⟩).toRingHom) x = P :=
    c.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, he, hx])
  have hbP : b ∈ P.asIdeal := by
    rw [← hPx]
    change e ⟨t, hr⟩ b ∈ PrimeSpectrum.asIdeal x
    rw [hb]
    exact Ideal.zero_mem _
  exact hbP

theorem sec_zero [Finite T] (Γ : QFGroup R T) (s : Γ(Γ.G.left, ⊤))
    (hs : ∀ t, valAt (Γ.pt t).left ⊤ le_top s = 0) : s = 0 := by
  let 𝒰 := Γ.G.left.affineOpenCover
  refine Scheme.OpenCover.ext_elem s 0 𝒰.openCover fun k => ?_
  rw [map_zero]
  let c : Spec (CommRingCat.of (𝒰.X k)) ⟶ Γ.G.left := 𝒰.f k
  haveI : IsOpenImmersion c := 𝒰.openCover.map_prop k
  letI : Algebra R (𝒰.X k) := (Spec.preimage (c ≫ Γ.G.hom)).hom.toAlgebra
  obtain ⟨I, _, τ, e, he, hi⟩ := chart_sep Γ (𝒰.X k) c (Spec.map_preimage (c ≫ Γ.G.hom)).symm
  have h0 := hi ((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).hom (c.appTop s)) fun i => by
    have h1 := hs (τ i)
    rw [← he i, valAt_top, Scheme.Hom.comp_appTop] at h1
    exact (congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (e i).toRingHom)) (c.appTop s))).symm.trans h1
  have h2 := congr((Scheme.ΓSpecIso (CommRingCat.of (𝒰.X k))).inv $h0)
  rw [Iso.hom_inv_id_apply, map_zero] at h2
  exact h2

theorem chart_pair [Finite T] (Γ : QFGroup R T) (A₁ A₂ : Type) [CommRing A₁] [CommRing A₂]
    (c₁ : Spec (CommRingCat.of A₁) ⟶ Γ.G.left) (c₂ : Spec (CommRingCat.of A₂) ⟶ Γ.G.left)
    (o₁ : IsOpenImmersion c₁) (o₂ : IsOpenImmersion c₂) (u : Γ(pullback (c₁ ≫ Γ.G.hom) (c₂ ≫ Γ.G.hom), ⊤))
    (hu : ∀ (a b : T) (w : Spec (CommRingCat.of (FractionRing R)) ⟶ pullback (c₁ ≫ Γ.G.hom) (c₂ ≫ Γ.G.hom)),
      w ≫ pullback.fst _ _ ≫ c₁ = (Γ.pt a).left → w ≫ pullback.snd _ _ ≫ c₂ = (Γ.pt b).left → w.appTop u = 0) :
    u = 0 := by
  letI : Algebra R A₁ := (Spec.preimage (c₁ ≫ Γ.G.hom)).hom.toAlgebra
  letI : Algebra R A₂ := (Spec.preimage (c₂ ≫ Γ.G.hom)).hom.toAlgebra
  have h₁ : c₁ ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R A₁)) :=
    (Spec.map_preimage (c₁ ≫ Γ.G.hom)).symm
  have h₂ : c₂ ≫ Γ.G.hom = Spec.map (CommRingCat.ofHom (algebraMap R A₂)) :=
    (Spec.map_preimage (c₂ ≫ Γ.G.hom)).symm
  haveI : Flat Γ.G.hom := Γ.flat
  haveI : Module.Flat R A₁ := by
    have : Flat (Spec.map (CommRingCat.ofHom (algebraMap R A₁))) := h₁ ▸ inferInstance
    rw [Flat.SpecMap_iff] at this
    exact (RingHom.flat_algebraMap_iff).1 this
  obtain ⟨I, _, τ, e, he, hi⟩ := chart_sep Γ A₁ c₁ h₁
  obtain ⟨J, _, τ', f, hf, hj⟩ := chart_sep Γ A₂ c₂ h₂
  refine CharMul.pullback_sep e f hi hj _ _ h₁ h₂ u fun i j w hw₁ hw₂ => hu (τ i) (τ' j) w ?_ ?_
  · rw [← Category.assoc, hw₁, he]
  · rw [← Category.assoc, hw₂, hf]

theorem sec_prod_zero [Finite T] (Γ : QFGroup R T) (u : Γ((Γ.G ⊗ Γ.G).left, ⊤))
    (hu : ∀ a b, (lift (Γ.pt a) (Γ.pt b)).left.appTop u = 0) : u = 0 := by
  let 𝒰 := Γ.G.left.affineOpenCover
  refine Scheme.OpenCover.ext_elem (X := pullback Γ.G.hom Γ.G.hom) u 0
    (Scheme.Pullback.openCoverOfLeftRight 𝒰.openCover 𝒰.openCover Γ.G.hom Γ.G.hom) fun ij => ?_
  rw [map_zero]
  obtain ⟨i, j⟩ := ij
  refine chart_pair Γ (𝒰.X i) (𝒰.X j) (𝒰.f i) (𝒰.f j) (𝒰.openCover.map_prop i) (𝒰.openCover.map_prop j) _
    fun a b w h₁ h₂ => ?_
  have hw : w ≫ (Scheme.Pullback.openCoverOfLeftRight 𝒰.openCover 𝒰.openCover Γ.G.hom Γ.G.hom).f (i, j) =
      (lift (Γ.pt a) (Γ.pt b)).left := by
    rw [Over.lift_left, Scheme.Pullback.openCoverOfLeftRight_f]
    apply pullback.hom_ext
    · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (pullback.lift_fst _ _ _).symm)
      exact (congrArg (w ≫ ·) (pullback.lift_fst _ _ _)).trans h₁
    · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (pullback.lift_snd _ _ _).symm)
      exact (congrArg (w ≫ ·) (pullback.lift_snd _ _ _)).trans h₂
  have h0 := hu a b
  rw [← hw] at h0
  have e := congr($(Scheme.Hom.comp_appTop w
    ((Scheme.Pullback.openCoverOfLeftRight 𝒰.openCover 𝒰.openCover Γ.G.hom Γ.G.hom).f (i, j))) u)
  exact e.symm.trans h0

def pullSec {A : Type} [CommRing A] {X : Scheme.{0}} (j : X ⟶ Spec (CommRingCat.of A)) (f : A) : Γ(X, ⊤) :=
  j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)

theorem valAt_pullSec {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}} (j : X ⟶ Spec (CommRingCat.of A))
    (x : Spec (CommRingCat.of B) ⟶ X) (f : A) : valAt x ⊤ le_top (pullSec j f) = valSpec (x ≫ j) f :=
  ValEmb.valAt_pull j x (Spec.preimage (x ≫ j)).hom (Spec.map_preimage _).symm f

theorem hasValues_pullSec (Γ : QFGroup R T) {A : Subalgebra R (T → R)} {j : Γ.G.left ⟶ Spec (CommRingCat.of A)}
    (hj : Γ.IsEmb A j) (f : A) : Γ.HasValues (pullSec j f) (f : T → R) := fun t =>
  ValEmb.valAt_pull j (Γ.pt t).left _ (hj.pt t) f

theorem isHomEmb_of_isEmb [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R))
    (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) (hj : Γ.IsEmb A j) : IsHomEmb Γ A j := by
  intro B _ β y z f m a b hf
  have univ : (fst Γ.G Γ.G * snd Γ.G Γ.G).left.appTop (pullSec j f) =
      ∑ k, (fst Γ.G Γ.G).left.appTop (pullSec j (a k)) * (snd Γ.G Γ.G).left.appTop (pullSec j (b k)) := by
    rw [← sub_eq_zero]
    refine sec_prod_zero Γ _ fun s t => ?_
    rw [map_sub, map_sum, CharMul.pull, comp_mul, lift_fst, lift_snd, ← map_mul,
      CharMul.appTop_pt Γ _ _ (hasValues_pullSec Γ hj f), hf, map_sum, map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, map_mul, CharMul.pull, CharMul.pull, lift_fst, lift_snd,
      CharMul.appTop_pt Γ _ _ (hasValues_pullSec Γ hj (a k)), CharMul.appTop_pt Γ _ _ (hasValues_pullSec Γ hj (b k))]
  have h := congrArg (lift y z).left.appTop univ
  rw [CharMul.pull, comp_mul, lift_fst, lift_snd, map_sum] at h
  rw [← valAt_pullSec, valAt_top]
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← valAt_pullSec, ← valAt_pullSec, valAt_top, valAt_top, ← map_mul]
  congr 1
  rw [map_mul, CharMul.pull, CharMul.pull, lift_fst, lift_snd]

theorem exists_inducesOnPts (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left} (hi : Γ.IsTorsionAlong G x N i)
    (a : G ⟶ G) [IsMonHom a] : ∃ aT : T →* T, InducesOnPts Γ i a aT := by
  let p : T → (Over.mk ((genPt R).hom ≫ x) ⟶ G) := fun t =>
    Over.homMk ((Γ.pt t).left ≫ i) (by
      change ((Γ.pt t).left ≫ i) ≫ G.hom = (genPt R).hom ≫ x
      rw [Category.assoc, hi.isOver, ← Category.assoc, Over.w (Γ.pt t)])
  have hp : ∀ t, (p t).left = (Γ.pt t).left ≫ i := fun t => rfl
  have ex : ∀ t, ∃ u, (Γ.pt u).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left := by
    intro t
    have h1 : p t ^ N = 1 := (hi.kernel _ (p t)).2 ⟨Γ.pt t, rfl⟩
    have h2 : (p t ≫ a) ^ N = 1 := by
      rw [← MonObj.pow_comp, h1, MonObj.one_comp]
    obtain ⟨y, hy⟩ := (hi.kernel _ (p t ≫ a)).1 h2
    obtain ⟨u, hu⟩ := QFGroup.exists_eq_comp_pt R T Γ (FractionRing R) (RingHom.id _) y.left (Over.w y)
    refine ⟨u, ?_⟩
    have hu' : y.left = (Γ.pt u).left := by simpa using hu
    rw [← hu', hy, Over.comp_left, hp, Category.assoc]
  choose α hα using ex
  have inj : ∀ s t, (Γ.pt s).left ≫ i = (Γ.pt t).left ≫ i → s = t := by
    intro s t h
    have h' := hi.inj _ _ _ h
    let q : Spec (CommRingCat.of (FractionRing R)) := (⊥ : PrimeSpectrum (FractionRing R))
    exact Γ.pt_inj _ _ q q (by rw [h'])
  have hmul : ∀ s t, p (s * t) = p s * p t := by
    intro s t
    ext1
    rw [hi.mul _ (Γ.pt s) (Γ.pt t) (p s) (p t) rfl rfl, hp, map_mul]
  have hpa : ∀ t, p (α t) = p t ≫ a := by
    intro t
    ext1
    rw [hp, hα, Over.comp_left, hp, Category.assoc]
  refine ⟨MonoidHom.mk' α fun s t => inj _ _ ?_, hα⟩
  rw [← hp, ← hp, hmul, hpa, hpa, hpa, hmul, MonObj.mul_comp]

theorem valAt_add_one {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (a : Γ(X, ⊤)) : valAt x ⊤ le_top (a + 1) = valAt x ⊤ le_top a + 1 := by
  simp only [valAt_top, map_add, map_one]

theorem valAt_sub_one {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (a : Γ(X, ⊤)) : valAt x ⊤ le_top (a - 1) = valAt x ⊤ le_top a - 1 := by
  simp only [valAt_top, map_sub, map_one]

theorem valAt_sub' {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X)
    (a b : Γ(X, ⊤)) : valAt x ⊤ le_top (a - b) = valAt x ⊤ le_top a - valAt x ⊤ le_top b := by
  simp only [valAt_top, map_sub]

theorem valAt_mul {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a * b) = valAt x U h a * valAt x U h b := by
  simp [valAt]

section Omega

variable (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S}
  (i : Γ.G.left ⟶ G.left) {L : Type} [AddCommGroup L] [Module R L] (M : LieModel G x L) (N : ℕ)

theorem isDerAtOne_iff [Finite T] (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)))
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L) :
    Γ.IsDerAtOne i M N (f.1.1 : T → R) w ↔ ∀ e : L, ∃ v, IsRedTan Γ i M N e v ∧
      valSpec (B := DualNumber (R ⧸ Ideal.span {(N : R)})) (v ≫ j) (f : Γ.btOrder ⊤) =
        TrivSqZeroExt.inr (Ideal.Quotient.mk (Ideal.span {(N : R)}) (w e)) := by
  have h1 : (f.1.1 : T → R) 1 = 0 := f.2
  constructor
  · rintro ⟨s, hs, h⟩ e
    obtain ⟨v, h₁, h₂, h₃⟩ := h e
    refine ⟨v, ⟨h₁, h₂⟩, ?_⟩
    rw [h1, map_zero, TrivSqZeroExt.inl_zero, zero_add] at h₃
    rw [← h₃]
    have hz : s - pullSec j f.1 = 0 := sec_zero Γ _ fun t => by
      rw [valAt_sub', hs t, hasValues_pullSec Γ hj f.1 t, sub_self]
    rw [sub_eq_zero.1 hz, valAt_pullSec]
  · intro h
    refine ⟨pullSec j f.1, hasValues_pullSec Γ hj f.1, fun e => ?_⟩
    obtain ⟨v, ⟨h₁, h₂⟩, h₃⟩ := h e
    refine ⟨v, h₁, h₂, ?_⟩
    rw [h1, map_zero, TrivSqZeroExt.inl_zero, zero_add, valAt_pullSec, h₃]

theorem char_mem_of_isHT (χ : T →* Rˣ) (w : Module.Dual R L) (h : Γ.IsHT i M N χ w) :
    (fun t => ((χ t : Rˣ) : R)) ∈ Γ.btOrder ⊤ := by
  obtain ⟨s, hs, -⟩ := h
  refine Algebra.subset_adjoin fun t g _ => ⟨⊤, trivial, pullSec Γ.G.hom ((χ t : Rˣ) : R) * s, fun u hu => ?_⟩
  have h1 : valAt (Γ.pt u).left ⊤ hu (pullSec Γ.G.hom ((χ t : Rˣ) : R)) =
      algebraMap R (FractionRing R) ((χ t : Rˣ) : R) :=
    ValEmb.valAt_pull Γ.G.hom (Γ.pt u).left _ (Over.w (Γ.pt u)) _
  rw [valAt_mul, h1, hs u, ← map_mul]
  simp

theorem isHT_iff_isDerAtOne (χ : T →* Rˣ) (w : Module.Dual R L) :
    Γ.IsHT i M N χ w ↔ Γ.IsDerAtOne i M N (fun t => ((χ t : Rˣ) : R) - 1) w := by
  constructor
  · rintro ⟨s, hs, h⟩
    refine ⟨s - 1, fun t => ?_, fun e => ?_⟩
    · rw [valAt_sub_one, hs t, map_sub, map_one]
    · obtain ⟨v, h₁, h₂, h₃⟩ := h e
      refine ⟨v, h₁, h₂, ?_⟩
      rw [valAt_sub_one, h₃]
      simp
  · rintro ⟨s, hs, h⟩
    refine ⟨s + 1, fun t => ?_, fun e => ?_⟩
    · rw [valAt_add_one, hs t]
      simp
    · obtain ⟨v, h₁, h₂, h₃⟩ := h e
      refine ⟨v, h₁, h₂, ?_⟩
      rw [valAt_add_one, h₃]
      simp [add_comm]

omit [IsDomain R] in
theorem mem_span_smul_top {V : Type} [AddCommGroup V] [Module R V] (w : V) :
    w ∈ Ideal.span {(N : R)} • (⊤ : Submodule R V) ↔ ∃ u, w = N • u := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]
  exact ⟨fun ⟨u, h⟩ => ⟨u, h.symm⟩, fun ⟨u, h⟩ => ⟨u, h.symm⟩⟩

theorem omega_iff [Finite T] (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)))
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) :
    (∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤),
        (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L),
          θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧
        (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧
        ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ) ↔
      ∃ θ : OmegaMod R L N ≃ₗ[R] omega (Γ.btOrder ⊤), IsOmegaIso Γ i M N (Γ.btOrder ⊤) j θ := by
  constructor
  · rintro ⟨θ, ⟨hs, hd⟩, hk, hχ⟩
    have hker : Ideal.span {(N : R)} • (⊤ : Submodule R (Module.Dual R L)) = LinearMap.ker θ := by
      ext w
      rw [mem_span_smul_top, LinearMap.mem_ker, hk]
    let θ' : OmegaMod R L N ≃ₗ[R] omega (Γ.btOrder ⊤) :=
      (Submodule.quotEquivOfEq _ _ hker).trans (θ.quotKerEquivOfSurjective hs)
    have hθ : ∀ w, θ' (Submodule.Quotient.mk w) = θ w := fun w => rfl
    refine ⟨θ', fun w f => ?_, fun χ w => ⟨fun h => ⟨char_mem_of_isHT Γ i M N χ w h, ?_⟩, fun ⟨hm, h⟩ => ?_⟩⟩
    · rw [hθ, hd, isDerAtOne_iff Γ i M N j hj]
    · rw [hθ, hχ χ w h]
    · rw [hθ, OrderApi.dlogChar_of_mem _ _ hm, hd] at h
      exact (isHT_iff_isDerAtOne Γ i M N χ w).2 h
  · rintro ⟨θ, hd, hχ⟩
    refine ⟨θ.toLinearMap ∘ₗ Submodule.mkQ _, ⟨θ.surjective.comp (Submodule.mkQ_surjective _), fun f w => ?_⟩,
      fun w => ?_, fun χ w h => ((hχ χ w).1 h).2⟩
    · rw [isDerAtOne_iff Γ i M N j hj]
      exact hd w f
    · rw [← mem_span_smul_top (R := R), ← Submodule.Quotient.mk_eq_zero]
      exact θ.map_eq_zero_iff

end Omega

theorem endo_iff (Γ : QFGroup R T) {S : Scheme.{0}} {G : Over S} [GrpObj G]
    {x : Spec (CommRingCat.of R) ⟶ S} {N : ℕ} {i : Γ.G.left ⟶ G.left} (hi : Γ.IsTorsionAlong G x N i)
    (A : Subalgebra R (T → R)) :
    (∀ (a : G ⟶ G) [IsMonHom a] (α : T →* T), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) →
      ∀ f ∈ A, (fun t => f (α t)) ∈ A) ↔
    ∀ a : G ⟶ G, IsMonHom a → ∃ aT : T →* T, InducesOnPts Γ i a aT ∧ ∀ f ∈ A, (fun t => f (aT t)) ∈ A := by
  constructor
  · intro h a ha
    obtain ⟨aT, haT⟩ := exists_inducesOnPts Γ hi a
    exact ⟨aT, haT, h a aT haT⟩
  · intro h a ha α hα
    obtain ⟨aT, haT, h'⟩ := h a ha
    rw [InducesOnPts.unique hi hα haT]
    exact h'

omit [IsDomain R] [CommGroup T] in

theorem tensor_iff {R' : Type} [CommRing R'] [Algebra R R'] (A : Subalgebra R (T → R))
    (A' : Subalgebra R' (T → R')) :
    (∃ e : R' ⊗[R] A ≃ₐ[R'] A', ∀ (a : A) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t)) ↔
      IsTensorOrder A A' := by
  refine exists_congr fun e => ⟨fun h r f t => ?_, fun h a t => by rw [h, _root_.one_mul]⟩
  have : r ⊗ₜ[R] f = r • ((1 : R') ⊗ₜ[R] f) := by simp [TensorProduct.smul_tmul']
  rw [this, map_smul, ← h]
  rfl

theorem exists_emb_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)) (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ (ev : R' ⊗[R] A →ₐ[R'] (T → R')), (∀ (a : A) (t : T), ev (1 ⊗ₜ[R] a) t = algebraMap R R' (a.1 t)) → ∃ j' : Γ'.G.left ⟶ Spec (CommRingCat.of (R' ⊗[R] A)), IsOpenImmersion j' ∧ (∀ t : T, (Γ'.pt t).left ≫ j' = Spec.map (CommRingCat.ofHom ((algebraMap R' (FractionRing R')).comp ((Pi.evalRingHom (fun _ : T => R') t).comp ev.toRingHom)))) ∧ ∀ (Q : PrimeSpectrum (R' ⊗[R] A)) (g : Γ.G.left), (∀ a : A, (1 : R') ⊗ₜ[R] a ∈ Q.asIdeal ↔ a ∈ (j g).asIdeal) → ∃ g' : Γ'.G.left, j' g' = Q := by
  intro R _ _ T _ Γ A j hj ho R' _ _ _ Γ' F hF ev hev
  let iL : R' →+* R' ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  let iR : A →+* R' ⊗[R] A := (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := A)).toRingHom
  have sq : IsPullback (Spec.map (CommRingCat.ofHom iL)) (Spec.map (CommRingCat.ofHom iR))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))) (Spec.map (CommRingCat.ofHom (algebraMap R A))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct R R' A)
  have w : Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R R')) =
      (F ≫ j) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
    rw [Category.assoc, hj.isOver, hF.cart.w]
  let j' := sq.lift Γ'.G.hom (F ≫ j) w
  have h1 : j' ≫ Spec.map (CommRingCat.ofHom iL) = Γ'.G.hom := sq.lift_fst _ _ _
  have h2 : j' ≫ Spec.map (CommRingCat.ofHom iR) = F ≫ j := sq.lift_snd _ _ _
  have sq' : IsPullback F j' j (Spec.map (CommRingCat.ofHom iR)) := by
    refine IsPullback.of_bot ?_ h2.symm sq.flip
    rw [h1, hj.isOver]
    exact hF.cart
  refine ⟨j', MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq' ho, fun t => ?_, fun Q g hQ => ?_⟩
  · obtain ⟨B, _, i, k, k', σ, hk, hki, hki', -, hσ, hσ'⟩ := hF.pts
    refine sq.hom_ext ?_ ?_
    · rw [Category.assoc, h1, Over.w (Γ'.pt t), ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      change Spec.map _ = _
      congr 2
      ext r
      exact congrArg (algebraMap R' (FractionRing R')) (congrFun (ev.commutes r) t).symm
    · obtain ⟨ρ, hρ⟩ := Spec.map_surjective (σ t ≫ j)
      have e1 : ρ ≫ CommRingCat.ofHom k = CommRingCat.ofHom ((algebraMap R (FractionRing R)).comp
          ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)) := Spec.map_injective (by
        rw [Spec.map_comp, hρ, ← Category.assoc, hσ, hj.pt t])
      have e2 : ∀ a : A, ρ.hom a = i (a.1 t) := fun a => hk (by
        have : k (ρ.hom a) = algebraMap R (FractionRing R) (a.1 t) := congrArg (fun φ => φ.hom a) e1
        exact this.trans (congrArg (fun φ : R →+* FractionRing R => φ (a.1 t)) hki).symm)
      rw [Category.assoc, h2, ← Category.assoc, ← hσ', Category.assoc, ← hρ, ← Spec.map_comp, ← Spec.map_comp]
      congr 1
      ext a
      change k' (ρ.hom a) = algebraMap R' (FractionRing R') (ev (1 ⊗ₜ[R] a) t)
      rw [e2, hev]
      exact congrArg (fun φ : R →+* FractionRing R' => φ (a.1 t)) hki'
  · have hg : j g = Spec.map (CommRingCat.ofHom iR) Q := by
      apply PrimeSpectrum.ext
      ext a
      exact (hQ a).symm
    obtain ⟨g', -, h⟩ := Scheme.exists_preimage_of_isPullback sq' g Q hg
    exact ⟨g', h⟩

theorem ev_injective : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (C : Type) [CommRing C] [Algebra R C] (ev : C →ₐ[R] (T → R)) (τ : T → (C ≃+* C)), (∀ (t : T) (c : C) (h : T), ev (τ t c) h = ev c (t * h)) → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of C)), IsOpenImmersion j → (∀ t : T, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp ev.toRingHom)))) → (∀ P : PrimeSpectrum C, ∃ (t : T) (g : Γ.G.left), ∀ c : C, c ∈ P.asIdeal ↔ τ t c ∈ (j g).asIdeal) → Function.Injective ev := by
  intro R _ _ T _ _ Γ C _ _ ev τ hτ j ho hpt hc
  rw [injective_iff_map_eq_zero]
  intro c hc0
  have hz : ∀ t, pullSec j (τ t c) = 0 := fun t =>
    sec_zero Γ _ fun u => by
      refine (ValEmb.valAt_pull j (Γ.pt u).left _ (hpt u) (τ t c)).trans ?_
      change algebraMap R (FractionRing R) (ev (τ t c) u) = 0
      rw [hτ, hc0, Pi.zero_apply, map_zero]
  by_contra hne
  have hI : (Submodule.span C {c}).annihilator ≠ ⊤ := by
    rw [Ne, Submodule.annihilator_eq_top_iff, Submodule.span_singleton_eq_bot]
    exact hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨t, g, hg⟩ := hc ⟨m, hm.isPrime⟩
  have h1 : (Spec (CommRingCat.of C)).presheaf.germ ⊤ (j g) trivial
      ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (τ t c)) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (j.stalkMap g)).1
    rw [map_zero]
    have := Scheme.Hom.germ_stalkMap_apply j ⊤ g trivial ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (τ t c))
    rw [this]
    have h0 : j.app ⊤ ((Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (τ t c)) = 0 := hz t
    rw [h0, map_zero]
  let p : PrimeSpectrum C := j g
  letI : Algebra C ((Spec (CommRingCat.of C)).presheaf.stalk p) := StructureSheaf.stalkAlgebra C p
  haveI : IsLocalization.AtPrime ((Spec (CommRingCat.of C)).presheaf.stalk p) p.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk C p
  have h2 : algebraMap C ((Spec (CommRingCat.of C)).presheaf.stalk p) (τ t c) = 0 := h1
  obtain ⟨u, hu⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl _ _).1 h2
  apply u.2
  have : (τ t).symm u ∈ m := hle (by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
    apply (τ t).injective
    rw [map_mul, RingEquiv.apply_symm_apply, hu, map_zero])
  have := (hg _).1 this
  rwa [RingEquiv.apply_symm_apply] at this

theorem valAt_res {B : Type} [CommRing B] {X : Scheme.{0}} (y : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (hUV : U ≤ V) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ y ⁻¹ᵁ V) (s : Γ(X, V)) :
    valAt y U h (X.presheaf.map (homOfLE hUV).op s) = valAt y V h' s := by
  unfold valAt
  rw [← Scheme.Hom.map_appLE y h (homOfLE hUV).op]
  rfl

theorem valAt_image {B : Type} [CommRing B] {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
    (y : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (y ≫ j) ⁻¹ᵁ (j ''ᵁ U))
    (s : Γ(X, U)) : valAt (y ≫ j) (j ''ᵁ U) h' ((j.appIso U).inv s) = valAt y U h s := by
  have h1 : (y ≫ j).appLE (j ''ᵁ U) ⊤ h' = (j.appIso U).hom ≫ y.appLE U ⊤ h := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
  have h3 : (j.appIso U).hom ((j.appIso U).inv s) = s := Iso.inv_hom_id_apply _ _
  unfold valAt
  rw [h1]
  exact congrArg (fun z => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((y.appLE U ⊤ h).hom z)) h3

theorem exists_frac {C : Type} [CommRing C] (V : (Spec (CommRingCat.of C)).Opens) (s : Γ(Spec (CommRingCat.of C), V))
    (p : Spec (CommRingCat.of C)) (hp : p ∈ V) :
    ∃ u a : C, u ∉ p.asIdeal ∧ ∀ (K : Type) [Field K] (ρ : C →+* K), (ρ u = 0 → ρ a = 0) ∧ (ρ u ≠ 0 →
      ∃ h : ⊤ ≤ (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ V, valAt (Spec.map (CommRingCat.ofHom ρ)) V h s * ρ u = ρ a) := by
  have hU := isAffineOpen_top (Spec (CommRingCat.of C))
  obtain ⟨f, hf, hpf⟩ := hU.exists_basicOpen_le ⟨p, hp⟩ trivial
  obtain ⟨u, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv).2 f
  haveI := hU.isLocalization_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of C)).inv u)
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj ((Scheme.ΓSpecIso (CommRingCat.of C)).inv u)
    ((Spec (CommRingCat.of C)).presheaf.map (homOfLE hf).op s)
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv).2 a
  have hmem : ∀ q : Spec (CommRingCat.of C), q ∈ (Spec (CommRingCat.of C)).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of C)).inv u) ↔ u ∉ q.asIdeal := fun q => by
    rw [basicOpen_eq_of_affine]
    rfl
  refine ⟨u ^ (n + 1), a * u, fun h => (hmem p).1 hpf (p.isPrime.mem_of_pow_mem _ h), fun K _ ρ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [map_pow] at h
    rw [map_mul, pow_eq_zero_iff (Nat.succ_ne_zero n) |>.1 h, mul_zero]
  · have hu : ρ u ≠ 0 := fun h0 => h (by rw [map_pow, h0, zero_pow (Nat.succ_ne_zero n)])
    have hb : ⊤ ≤ (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ (Spec (CommRingCat.of C)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of C)).inv u) := fun q _ => (hmem _).2 fun hq => by
      have hq' : ρ u ∈ PrimeSpectrum.asIdeal q := hq
      rw [@Ideal.eq_bot_of_prime K _ (PrimeSpectrum.asIdeal q) (PrimeSpectrum.isPrime q)] at hq'
      exact hu hq'
    have hV : ⊤ ≤ (Spec.map (CommRingCat.ofHom ρ)) ⁻¹ᵁ V := fun q hq => hf (hb hq)
    refine ⟨hV, ?_⟩
    have hv : ∀ c : C, valAt (Spec.map (CommRingCat.ofHom ρ)) _ hb
        (algebraMap Γ(Spec (CommRingCat.of C), ⊤) _ ((Scheme.ΓSpecIso (CommRingCat.of C)).inv c)) = ρ c := fun c =>
      (valAt_res _ le_top hb le_top _).trans
        (ValEmb.valAt_pull (𝟙 _) (Spec.map (CommRingCat.ofHom ρ)) ρ (Category.comp_id _) c)
    have e := congrArg (valAt (Spec.map (CommRingCat.ofHom ρ)) _ hb) ha
    rw [valAt_mul, valAt_res _ hf hb hV, ← map_pow, ← map_pow, hv, hv] at e
    rw [pow_succ, map_mul, map_mul, ← _root_.mul_assoc, e]

theorem exists_ev_eq : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (C : Type) [CommRing C] [Algebra R C] (ev : C →ₐ[R] (T → R)) (τ : T → (C ≃+* C)), (∀ (t : T) (c : C) (h : T), ev (τ t c) h = ev c (t * h)) → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of C)), IsOpenImmersion j → (∀ t : T, (Γ.pt t).left ≫ j = Spec.map (CommRingCat.ofHom ((algebraMap R (FractionRing R)).comp ((Pi.evalRingHom (fun _ : T => R) t).comp ev.toRingHom)))) → (∀ P : PrimeSpectrum C, ∃ (t : T) (g : Γ.G.left), ∀ c : C, c ∈ P.asIdeal ↔ τ t c ∈ (j g).asIdeal) → ∀ f ∈ Γ.btSet ⊤, ∃ c : C, ev c = f := by
  intro R _ _ T _ _ Γ C _ _ ev τ hτ j ho hpt hc f hf
  let I : Ideal C :=
    { carrier := {a | ∃ b, ev b = ev a * f}
      add_mem' := by
        rintro a a' ⟨b, hb⟩ ⟨b', hb'⟩
        exact ⟨b + b', by rw [map_add, map_add, hb, hb', add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨b, hb⟩
        exact ⟨c * b, by rw [smul_eq_mul, map_mul, map_mul, hb, _root_.mul_assoc]⟩ }
  by_cases hI : I = ⊤
  · obtain ⟨b, hb⟩ : (1 : C) ∈ I := hI ▸ Submodule.mem_top
    exact ⟨b, by rw [hb, map_one, _root_.one_mul]⟩
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hI
  obtain ⟨t, g, hg⟩ := hc ⟨m, hm.isPrime⟩
  obtain ⟨U, hgU, s, hs⟩ := hf t g trivial
  obtain ⟨u, a, hu, H⟩ := exists_frac (j ''ᵁ U) ((j.appIso U).inv s) (j g) ⟨g, hgU, rfl⟩
  have key : ∀ h, ev a h = ev u h * f (t * h) := by
    intro h
    apply IsFractionRing.injective R (FractionRing R)
    obtain ⟨H0, H1⟩ := H (FractionRing R) ((algebraMap R (FractionRing R)).comp
      ((Pi.evalRingHom (fun _ : T => R) h).comp ev.toRingHom))
    by_cases h0 : algebraMap R (FractionRing R) (ev u h) = 0
    · rw [map_mul, h0, zero_mul]
      exact H0 h0
    · have H2 := H1 h0
      rw [← hpt h] at H2
      obtain ⟨hV, e⟩ := H2
      have hU : ⊤ ≤ (Γ.pt h).left ⁻¹ᵁ U := fun q hq => by
        obtain ⟨z, hz, hz'⟩ := hV hq
        have : z = (Γ.pt h).left q := j.isOpenEmbedding.injective (hz'.trans (Scheme.Hom.comp_apply _ _ _))
        rw [this] at hz
        exact hz
      rw [valAt_image j _ U hU, hs h hU] at e
      rw [map_mul, mul_comm]
      exact e.symm
  have hmem : (τ t).symm u ∈ m := hle ⟨(τ t).symm a, by
    funext z
    obtain ⟨z, rfl⟩ : ∃ y, z = t * y := ⟨t⁻¹ * z, by simp⟩
    rw [Pi.mul_apply, ← hτ, ← hτ, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, key]⟩
  have := (hg _).1 hmem
  rw [RingEquiv.apply_symm_apply] at this
  exact absurd this hu

theorem translate_mem (Γ : QFGroup R T) (t : T) (f : T → R) (hf : f ∈ Γ.btOrder ⊤) :
    (fun h => f (t * h)) ∈ Γ.btOrder ⊤ := by
  induction hf using Algebra.adjoin_induction with
  | mem g hg =>
    refine Algebra.subset_adjoin fun s y hy => ?_
    simpa [_root_.mul_assoc] using hg (t * s) y hy
  | algebraMap r => exact Subalgebra.algebraMap_mem _ r
  | add a b _ _ ha hb => exact Subalgebra.add_mem _ ha hb
  | mul a b _ _ ha hb => exact Subalgebra.mul_mem _ ha hb

def translate (Γ : QFGroup R T) (t : T) : Γ.btOrder ⊤ ≃ₐ[R] Γ.btOrder ⊤ where
  toFun f := ⟨fun h => f.1 (t * h), translate_mem Γ t f.1 f.2⟩
  invFun f := ⟨fun h => f.1 (t⁻¹ * h), translate_mem Γ t⁻¹ f.1 f.2⟩
  left_inv f := by ext h; simp
  right_inv f := by ext h; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

theorem isTensorOrder_of_cover [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)))
    (hj : Γ.IsEmb (Γ.btOrder ⊤) j) (ho : IsOpenImmersion j) (hc : Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤)
    (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left)
    (hF : Γ'.IsBaseChange Γ (algebraMap R R') F) : IsTensorOrder (Γ.btOrder ⊤) (Γ'.btOrder ⊤) := by
  let ev : R' ⊗[R] (Γ.btOrder ⊤) →ₐ[R'] (T → R') :=
    Algebra.TensorProduct.lift (Algebra.ofId R' (T → R'))
      (Pi.algHom R _ fun t => (Algebra.ofId R R').comp (evalAt (Γ.btOrder ⊤) t)) fun _ _ => Commute.all _ _
  have hev : ∀ (r : R') (a : Γ.btOrder ⊤) (t : T), ev (r ⊗ₜ[R] a) t = r * algebraMap R R' (a.1 t) :=
    fun r a t => rfl
  let τ : T → (R' ⊗[R] (Γ.btOrder ⊤) ≃+* R' ⊗[R] (Γ.btOrder ⊤)) := fun t =>
    (Algebra.TensorProduct.congr (AlgEquiv.refl : R' ≃ₐ[R] R') (translate Γ t)).toRingEquiv
  have hτ1 : ∀ t (r : R') (a : Γ.btOrder ⊤), τ t (r ⊗ₜ[R] a) = r ⊗ₜ[R] translate Γ t a := fun t r a => rfl
  have hτ : ∀ t c h, ev (τ t c) h = ev c (t * h) := by
    intro t c h
    induction c using TensorProduct.induction_on with
    | zero => simp
    | tmul r a => rw [hτ1, hev, hev]; rfl
    | add a b ha hb => rw [map_add, map_add, map_add, Pi.add_apply, Pi.add_apply, ha, hb]
  obtain ⟨j', ho', hpt, hQ⟩ := exists_emb_baseChange R T Γ _ j hj ho R' Γ' F hF ev fun a t => by rw [hev, _root_.one_mul]
  have hcov : ∀ P : PrimeSpectrum (R' ⊗[R] (Γ.btOrder ⊤)), ∃ (t : T) (g : Γ'.G.left),
      ∀ c, c ∈ P.asIdeal ↔ τ t c ∈ (j' g).asIdeal := by
    intro P
    obtain ⟨t, g, -, hg⟩ := hc (PrimeSpectrum.comap
      (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := Γ.btOrder ⊤)).toRingHom P)
    obtain ⟨g', hg'⟩ := hQ (PrimeSpectrum.comap (τ t).symm.toRingHom P) g fun a => by
      rw [← hg ((translate Γ t).symm a) a fun h =>
        congrArg (fun z : Γ.btOrder ⊤ => z.1 h) ((translate Γ t).apply_symm_apply a).symm]
      rfl
    refine ⟨t, g', fun c => ?_⟩
    rw [hg']
    change c ∈ P.asIdeal ↔ (τ t).symm (τ t c) ∈ P.asIdeal
    rw [RingEquiv.symm_apply_apply]
  have hinj := ev_injective R' T Γ' _ ev τ hτ j' ho' hpt hcov
  have hsurj := exists_ev_eq R' T Γ' _ ev τ hτ j' ho' hpt hcov
  have hr : ev.range = Γ'.btOrder ⊤ := by
    refine le_antisymm ?_ (Algebra.adjoin_le fun f hf => hsurj f hf)
    rintro _ ⟨c, rfl⟩
    refine Algebra.subset_adjoin fun t g _ => ⟨⊤, trivial, pullSec j' (τ t c), fun u hu => ?_⟩
    refine (ValEmb.valAt_pull j' (Γ'.pt u).left _ (hpt u) (τ t c)).trans ?_
    exact congrArg (algebraMap R' (FractionRing R')) (hτ t c u)
  exact ⟨(AlgEquiv.ofInjective ev hinj).trans (Subalgebra.equivOfEq _ _ hr), hev⟩

theorem conclusion_iff [Finite T] (Γ : QFGroup R T) {S : Scheme.{0}} (G : Over S) [GrpObj G]
    (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left) (hi : Γ.IsTorsionAlong G x N i) :
    (IsHopfOrder (Γ.btOrder ⊤) ∧
    (∃ j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)), Γ.IsEmb (Γ.btOrder ⊤) j ∧ IsOpenImmersion j ∧
      Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ ∧ (IsProper (pullback.snd G.hom x) → IsIso j)) ∧
    (IsUnit (N : R) → Γ.btOrder ⊤ = ⊤) ∧
    (∀ (a : G ⟶ G) [IsMonHom a] (α : T →* T), (∀ t, (Γ.pt (α t)).left ≫ i = (Γ.pt t).left ≫ i ≫ a.left) →
      ∀ f ∈ Γ.btOrder ⊤, (fun t => f (α t)) ∈ Γ.btOrder ⊤) ∧
    (∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left),
      Γ'.IsBaseChange Γ (algebraMap R R') F →
      ∃ e : R' ⊗[R] (Γ.btOrder ⊤) ≃ₐ[R'] Γ'.btOrder ⊤,
        ∀ (a : Γ.btOrder ⊤) (t : T), (e (1 ⊗ₜ a)).1 t = algebraMap R R' (a.1 t)) ∧
    ∀ (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L),
      ∃ θ : Module.Dual R L →ₗ[R] omega (Γ.btOrder ⊤),
        (Function.Surjective θ ∧ ∀ (f : augIdeal (Γ.btOrder ⊤)) (w : Module.Dual R L),
          θ w = (augIdeal (Γ.btOrder ⊤)).toCotangent f ↔ Γ.IsDerAtOne i M N (f.1.1 : T → R) w) ∧
        (∀ w, θ w = 0 ↔ ∃ u, w = N • u) ∧
        ∀ (χ : T →* Rˣ) (w : Module.Dual R L), Γ.IsHT i M N χ w → θ w = dlogChar (Γ.btOrder ⊤) χ) ↔
    Conclusion Γ G x N i := by
  constructor
  · rintro ⟨h1, ⟨j, hj, ho, hc, hp⟩, h3, h4, h5, h6⟩
    exact ⟨h1, ⟨j, hj, ho, isHomEmb_of_isEmb Γ _ j hj, hc, hp,
      fun L _ _ M => (omega_iff Γ i M N j hj).1 (h6 L M)⟩, h3, (endo_iff Γ hi _).1 h4,
      fun R' _ _ _ _ Γ' F hF => (tensor_iff _ _).1 (h5 R' Γ' F hF)⟩
  · rintro ⟨h1, ⟨j, hj, ho, -, hc, hp, h6⟩, h3, h4, -⟩
    exact ⟨h1, ⟨j, hj, ho, hc, hp⟩, h3, (endo_iff Γ hi _).2 h4,
      fun R' _ _ _ Γ' F hF => (tensor_iff _ _).2 (isTensorOrder_of_cover Γ j hj ho hc R' Γ' F hF),
      fun L _ _ M => (omega_iff Γ i M N j hj).2 (h6 L M)⟩

theorem lemmaBT_iff : GlobalTheory.CompanionTheory.Ar.BT.LemmaBT ↔ GlobalTheory.CompanionTheory.IndefiniteRowSideFullHecke.TensorOrderReduction.LemmaBT :=
  ⟨fun h R _ _ _ _ T _ _ S G _ _ hG x N Γ i hi => (conclusion_iff Γ G x N i hi).1 (h R T Γ S G x N i hi hG),
    fun h R _ _ _ _ T _ _ Γ S G _ _ x N i hi hG => (conclusion_iff Γ G x N i hi).2 (h R T S G hG x N Γ i hi)⟩

end GlobalTheory.CompanionTheory.Ar.BT.TranslateEq
