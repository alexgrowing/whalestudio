import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SpMapComp

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsRootParam

open Polynomial in

abbrev CycRing (n : ℕ) : Type := AdjoinRoot (cyclotomic n ℤ)

open Polynomial in
theorem root_pow (n : ℕ) : AdjoinRoot.root (cyclotomic n ℤ) ^ n = 1 := by
  have h := (AdjoinRoot.mk_eq_zero (f := cyclotomic n ℤ)).mpr (cyclotomic.dvd_X_pow_sub_one n ℤ)
  rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one] at h
  exact sub_eq_zero.mp h

open Polynomial in

def cycUnit {n : ℕ} (hn : 0 < n) : (CycRing n)ˣ :=
  Units.ofPowEqOne (AdjoinRoot.root (cyclotomic n ℤ)) n (root_pow n) hn.ne'

open Polynomial in
theorem cycUnit_val {n : ℕ} (hn : 0 < n) : (cycUnit hn : CycRing n) = AdjoinRoot.root (cyclotomic n ℤ) := rfl

theorem cycUnit_pow {n : ℕ} (hn : 0 < n) : cycUnit hn ^ n = 1 := by
  ext
  rw [Units.val_pow_eq_pow_val, cycUnit_val, root_pow, Units.val_one]

open Polynomial in
theorem isPrimitiveRoot_map {n : ℕ} (hn : 0 < n) {K : Type} [Field K] (hK : (n : K) ≠ 0) (β : CycRing n →+* K) :
    IsPrimitiveRoot (Units.map β.toMonoidHom (cycUnit hn)) n := by
  have : NeZero (n : K) := ⟨hK⟩
  have hr : (cyclotomic n K).IsRoot (β (AdjoinRoot.root (cyclotomic n ℤ))) := by
    have h := congrArg β (AdjoinRoot.eval₂_root (cyclotomic n ℤ))
    rw [Polynomial.hom_eval₂, map_zero, RingHom.ext_int (β.comp (AdjoinRoot.of _)) (Int.castRingHom K),
      ← Polynomial.eval_map, Polynomial.map_cyclotomic_int] at h
    exact h
  rw [← IsPrimitiveRoot.coe_units_iff]
  have hv : ((Units.map β.toMonoidHom (cycUnit hn) : Kˣ) : K) = β (AdjoinRoot.root (cyclotomic n ℤ)) := by
    simp [cycUnit_val]
  rw [hv]
  exact (Polynomial.isRoot_cyclotomic_iff).mp hr

open Polynomial in
theorem exists_map_eq {n : ℕ} (hn : 0 < n) {K : Type} [Field K] {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ n) :
    ∃ β : CycRing n →+* K, Units.map β.toMonoidHom (cycUnit hn) = ζ := by
  have h : (cyclotomic n ℤ).eval₂ (Int.castRingHom K) (ζ : K) = 0 := by
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic_int]
    exact (IsPrimitiveRoot.coe_units_iff.mpr hζ).isRoot_cyclotomic hn
  refine ⟨AdjoinRoot.lift (Int.castRingHom K) (ζ : K) h, Units.ext ?_⟩
  simp [cycUnit_val]

open Polynomial in
theorem isFinite_cyc (n : ℕ) : IsFinite (spMap (algebraMap ℤ (CycRing n))) := by
  have hf : Module.Finite ℤ (CycRing n) := (AdjoinRoot.powerBasis' (cyclotomic.monic n ℤ)).finite
  dsimp only [spMap]
  rw [IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr hf

theorem isUnit_natCast_of_hom {X Y : Scheme.{0}} (f : X ⟶ Y) {n : ℕ} (h : IsUnit (n : Γ(Y, ⊤))) :
    IsUnit (n : Γ(X, ⊤)) := by
  have h' := h.map f.appTop.hom
  rwa [map_natCast] at h'

theorem natCast_ne_zero_of_isUnit {K : Type} [Field K] {n : ℕ} (h : IsUnit (n : Γ(Sp K, ⊤))) : (n : K) ≠ 0 := by
  have h' := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
  rw [map_natCast] at h'
  exact h'.ne_zero

theorem isUnit_natCast_basicOpen (S : Scheme.{0}) (n : ℕ) :
    IsUnit (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) := by
  have h : IsUnit (n : Γ(S, S.basicOpen (n : Γ(S, ⊤)))) := by
    have h0 := S.toRingedSpace.isUnit_res_basicOpen (n : Γ(S, ⊤))
    rwa [map_natCast] at h0
  have e : (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) =
      (S.basicOpen (n : Γ(S, ⊤))).topIso.inv.hom (n : Γ(S, S.basicOpen (n : Γ(S, ⊤)))) :=
    (map_natCast _ n).symm
  rw [e]
  exact h.map _

theorem range_subset_basicOpen {S : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ} (hK : (n : K) ≠ 0) :
    Set.range x ⊆ Set.range (S.basicOpen (n : Γ(S, ⊤))).ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  have hK' : IsUnit (n : Γ(Sp K, ⊤)) := by
    have h1 := (Ne.isUnit hK).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    rwa [map_natCast] at h1
  have hu : IsUnit (x.app ⊤ (n : Γ(S, ⊤))) := by
    rw [map_natCast]
    have h1 := hK'.map ((Sp K).presheaf.map (homOfLE (le_top : x ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
    rwa [map_natCast] at h1
  have h := Scheme.preimage_basicOpen x (n : Γ(S, ⊤))
  rw [(Sp K).basicOpen_of_isUnit hu] at h
  show y ∈ x ⁻¹ᵁ S.basicOpen (n : Γ(S, ⊤))
  rw [h]
  trivial

theorem unitOn_inj {k : Type} [CommRing k] : Function.Injective (unitOn (R := k)) := by
  intro a b h
  apply Units.ext
  have h1 := congrArg (fun u : Γ(Sp k, ⊤)ˣ => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom (u : Γ(Sp k, ⊤))) h
  simpa [unitOn] using h1

private theorem exists_lift_of_range_subset_closure_image_finite {W U S : Scheme.{0}} (q : W ⟶ U) [IsFinite q] (f : U ⟶ S) [IsOpenImmersion f]
    {C : Set W} (hC : IsClosed C) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ U)
    (hx : Set.range (x ≫ f) ⊆ closure ((q ≫ f) '' C)) : ∃ w : Sp K ⟶ W, w ≫ q = x ∧ Set.range w ⊆ C := by
  let pt : Sp K := IsLocalRing.closedPoint K
  obtain ⟨c, hcC, hc⟩ : ∃ c ∈ C, q c = x pt := by
    have h1 : (x ≫ f) pt ∈ closure ((q ≫ f) '' C) := hx ⟨pt, rfl⟩
    have e : (q ≫ f) '' C = f '' (q '' C) := by
      ext y
      simp
    rw [e] at h1
    have h2 : x pt ∈ closure (q '' C) := by
      rw [f.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image]
      simpa [Scheme.Hom.comp_apply] using h1
    rw [(q.isClosedMap C hC).closure_eq] at h2
    exact h2
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback c pt hc
  have := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q x)
  have hS : IsClosed ((pullback.fst q x) ⁻¹' C) := hC.preimage (pullback.fst q x).continuous
  obtain ⟨z', hz'C, hz'⟩ := hS.exists_closed_singleton ⟨z, by simpa [Set.mem_preimage, hz1] using hcC⟩
  refine ⟨pointOfClosedPoint (pullback.snd q x) z' hz' ≫ pullback.fst q x, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  · rintro _ ⟨a, rfl⟩
    simpa [Scheme.Hom.comp_apply] using hz'C

private theorem lift_lemma' {S : Scheme.{0}} {K : Type} [Field K] (x : Sp K ⟶ S) {n : ℕ} (hK : (n : K) ≠ 0) :
    ∃ xU : Sp K ⟶ (S.basicOpen (n : Γ(S, ⊤)) : Scheme.{0}), xU ≫ (S.basicOpen (n : Γ(S, ⊤))).ι = x :=
  ⟨_, IsOpenImmersion.lift_fac _ x (range_subset_basicOpen x hK)⟩

set_option maxHeartbeats 1000000 in
private theorem main_lemma_3 : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  intro S G _ _ n La _ _ _ hG hn
  have hU : IsUnit (n : Γ(S.basicOpen (n : Γ(S, ⊤)), ⊤)) := isUnit_natCast_basicOpen S n
  have hGU : IsAbelianScheme ((Over.pullback (S.basicOpen (n : Γ(S, ⊤))).ι).obj G) :=
    Out.TLinPf.isAb_pullback _ G hG
  have hP := isGrpPullback_pullback G (S.basicOpen (n : Γ(S, ⊤))).ι
  obtain ⟨Z₀, et₀, hfin, -, hadd₀, hpow₀, huniv₀⟩ :=
    GlobalTheory.exists_finiteEtale_latticeTorsionHom _ ((Over.pullback (S.basicOpen (n : Γ(S, ⊤))).ι).obj G) n La hGU hU
  have hcyc := isFinite_cyc n
  have hp1 : IsFinite (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n)))) :=
    by infer_instance
  let ZU : Over (S.basicOpen (n : Γ(S, ⊤)) : Scheme.{0}) :=
    Over.mk (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n))) ≫ Z₀.hom)
  let r : ZU ⟶ Z₀ := Over.homMk (pullback.fst _ _)
  have hWu : IsUnit (n : Γ(ZU.left, ⊤)) := isUnit_natCast_of_hom ZU.hom hU
  refine ⟨Over.mk (ZU.hom ≫ (S.basicOpen (n : Γ(S, ⊤))).ι), fun a => GlobalTheory.ObjPull.pushEquiv hP ZU (r ≫ et₀ a),
    Units.map (GlobalTheory.LevCover.fnOn (pullback.snd (specZIsTerminal.from Z₀.left)
      (spMap (algebraMap ℤ (CycRing n))))).toMonoidHom (cycUnit hn), hWu, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a a'
    dsimp only
    rw [hadd₀, comp_mul, map_mul]
  · intro a
    dsimp only
    rw [← map_pow, ← comp_pow, hpow₀]
    simp
  · rw [← map_pow, cycUnit_pow, map_one]
  · intro K _ h ζ hζ
    obtain ⟨β, hβ⟩ := GlobalTheory.LevCover.exists_spMap (h ≫ pullback.snd _ _)
    rw [GlobalTheory.LevCover.map_fnOn _ h β hβ] at hζ
    rw [← unitOn_inj hζ]
    exact isPrimitiveRoot_map hn (natCast_ne_zero_of_isUnit (isUnit_natCast_of_hom h hWu)) β
  · intro K _ x et' ζ hK hadd hpow hζ
    obtain ⟨xU, hxU⟩ := lift_lemma' (S := S) (K := K) (n := n) x hK
    let e : Over.mk ((Over.mk xU).hom ≫ (S.basicOpen (n : Γ(S, ⊤))).ι) ⟶ Over.mk x :=
      Over.homMk (𝟙 _) (by simpa using hxU.symm)
    obtain ⟨h₀, hh₀, -⟩ := huniv₀ (Over.mk xU) (fun a => (GlobalTheory.ObjPull.pushEquiv hP _).symm (e ≫ et' a))
      (fun a a' => by rw [hadd, comp_mul, map_mul])
      (fun a => by rw [← map_pow, ← comp_pow, hpow]; simp)
    obtain ⟨β, hβ⟩ := exists_map_eq hn hζ
    let hW : Sp K ⟶ ZU.left := pullback.lift h₀.left (spMap β) (specZIsTerminal.hom_ext _ _)
    have hW1 : hW ≫ pullback.fst _ _ = h₀.left := pullback.lift_fst _ _ _
    have hW2 : hW ≫ pullback.snd _ _ = spMap β := pullback.lift_snd _ _ _
    refine ⟨Over.homMk hW ?_, ?_, ?_⟩
    · show hW ≫ (pullback.fst _ _ ≫ Z₀.hom) ≫ _ = x
      rw [← Category.assoc, ← Category.assoc, hW1, Over.w h₀]
      exact hxU
    · intro a
      apply Over.OverMorphism.ext
      have h1 := GlobalTheory.ObjPull.pushEquiv_symm_left hP _ (e ≫ et' a)
      rw [← hh₀ a] at h1
      have h2 : (e ≫ et' a).left = (et' a).left := by simp [e]
      show hW ≫ (GlobalTheory.ObjPull.pushEquiv hP ZU (r ≫ et₀ a)).left = (et' a).left
      rw [GlobalTheory.ObjPull.pushEquiv_left, ← h2, ← h1, Over.comp_left, Over.comp_left, ← hW1]
      simp only [Category.assoc]
      rfl
    · show Units.map hW.appTop.hom.toMonoidHom _ = _
      rw [GlobalTheory.LevCover.map_fnOn _ hW β hW2, hβ]
  · intro C hC K _ _ x hK hcl
    obtain ⟨xU, hxU⟩ := lift_lemma' (S := S) (K := K) (n := n) x hK
    have : IsFinite Z₀.hom := hfin
    have : IsFinite ZU.hom := by
      show IsFinite (pullback.fst (specZIsTerminal.from Z₀.left) (spMap (algebraMap ℤ (CycRing n))) ≫ Z₀.hom)
      infer_instance
    obtain ⟨w, hw, hwC⟩ := exists_lift_of_range_subset_closure_image_finite ZU.hom (S.basicOpen (n : Γ(S, ⊤))).ι hC xU
      (by rw [hxU]; exact hcl)
    refine ⟨Over.homMk w ?_, hwC⟩
    show w ≫ ZU.hom ≫ _ = x
    rw [← Category.assoc, hw, hxU]

end GlobalTheory.TorsRootParam

namespace GlobalTheory

open TorsRootParam in

theorem exists_latticeTorsionHom_primitiveRoot_param : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La], IsAbelianScheme G → 0 < n → ∃ (Z : Over S) (et : La → (Z ⟶ G)) (c : Γ(Z.left, ⊤)ˣ), IsUnit (n : Γ(Z.left, ⊤)) ∧ (∀ a a', et (a + a') = et a * et a') ∧ (∀ a, et a ^ n = 1) ∧ c ^ n = 1 ∧ (∀ (K : Type) [Field K] (h : Sp K ⟶ Z.left) (ζ : Kˣ), Units.map h.appTop.hom.toMonoidHom c = unitOn ζ → IsPrimitiveRoot ζ n) ∧ (∀ (K : Type) [Field K] (x : Sp K ⟶ S) (et' : La → (Over.mk x ⟶ G)) (ζ : Kˣ), (n : K) ≠ 0 → (∀ a a', et' (a + a') = et' a * et' a') → (∀ a, et' a ^ n = 1) → IsPrimitiveRoot ζ n → ∃ h : Over.mk x ⟶ Z, (∀ a, h ≫ et a = et' a) ∧ Units.map h.left.appTop.hom.toMonoidHom c = unitOn ζ) ∧ ∀ (C : Set Z.left), IsClosed C → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), (n : K) ≠ 0 → Set.range x ⊆ closure (Z.hom '' C) → ∃ h : Over.mk x ⟶ Z, Set.range h.left ⊆ C := by
  exact main_lemma_3

end GlobalTheory
