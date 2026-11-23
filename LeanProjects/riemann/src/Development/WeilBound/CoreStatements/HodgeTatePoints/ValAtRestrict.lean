import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace PositivityTheory.HtPt.Unc

noncomputable def valHom {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* B :=
  (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom.comp (x.appLE U ⊤ h).hom

theorem valHom_apply {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) : valHom x U h s = valAt x U h s := rfl

theorem valAt_restrict {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) {U V : X.Opens}
    (i : V ⟶ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) (hU : ⊤ ≤ x ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt x V hV ((X.presheaf.map i.op).hom s) = valAt x U hU s :=
  congrArg (fun φ => (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom (φ.hom s)) (x.map_appLE hV i.op)

theorem top_le_of_le {Y X : Scheme.{0}} (x : Y ⟶ X) {U V : X.Opens} (i : V ≤ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ U := fun _ hz => i (hV hz)

theorem top_le_of_mem {K : Type} [Field K] {X : Scheme.{0}} (x : Spec (CommRingCat.of K) ⟶ X) {U : X.Opens}
    (z : Spec (CommRingCat.of K)) (hz : x z ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := fun w _ => by
  have e : w = z := Subsingleton.elim (α := PrimeSpectrum K) w z
  subst e
  exact hz

theorem sec_inj : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (s : Γ(Γ.G.left, U)), (∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = 0) → s = 0 := by
  intro R _ _ T _ _ Γ U s hs
  have := Γ.flat
  have := Γ.gen_reduced
  have hdom : IsDominant (genPt R).hom :=
    ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2 (by
      change RingHom.ker (algebraMap R (FractionRing R)) ≤ _
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
      exact bot_le)⟩
  have : IsSchemeTheoreticallyDominant (genPt R).hom := .of_isDominant _
  have : QuasiCompact (genPt R).hom :=
    inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  let j := pullback.fst Γ.G.hom (genPt R).hom
  apply j.app_injective U
  rw [map_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  intro z hz
  exfalso
  have hz' : j z ∈ Γ.G.left.basicOpen s := hz
  have hgen : (Γ.G.hom (j z)).asIdeal = ⊥ := by
    have e : Γ.G.hom (j z) = (genPt R).hom (pullback.snd Γ.G.hom (genPt R).hom z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    rw [e]
    generalize pullback.snd Γ.G.hom (genPt R).hom z = w
    have hw : PrimeSpectrum.asIdeal (R := FractionRing R) w = ⊥ :=
      (Ideal.eq_bot_or_top _).resolve_right (PrimeSpectrum.isPrime (R := FractionRing R) w).ne_top
    change Ideal.comap (algebraMap R (FractionRing R)) (PrimeSpectrum.asIdeal (R := FractionRing R) w) = ⊥
    rw [hw]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))
  obtain ⟨t, x, hx⟩ := Γ.pt_onto _ hgen
  rw [← hx] at hz'
  have h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U := top_le_of_mem _ x (Γ.G.left.basicOpen_le s hz')
  have h0 : (Γ.pt t).left.appLE U ⊤ h s = 0 := by
    apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).1
    rw [map_zero]
    exact hs t h
  have h1 := Scheme.basicOpen_appLE (Γ.pt t).left ⊤ U h s
  rw [h0, Scheme.basicOpen_zero] at h1
  have h2 : x ∈ (⊤ : (genPt R).left.Opens) ⊓ (Γ.pt t).left ⁻¹ᵁ Γ.G.left.basicOpen s := ⟨trivial, hz'⟩
  rw [← h1] at h2
  exact h2

theorem reg_iff : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens) (f : T → FractionRing R), (∀ g ∈ U, Γ.RegularAt f g) ↔ ∃ s : Γ(Γ.G.left, U), ∀ (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ U), valAt (Γ.pt t).left U h s = f t := by
  intro R _ _ T _ _ Γ U f
  refine ⟨fun h => ?_, fun ⟨s, hs⟩ g hg => ⟨U, hg, s, hs⟩⟩
  choose W hW s hs using fun g : U => h g.1 g.2
  let V : U → Γ.G.left.Opens := fun g => W g ⊓ U
  let sf : ∀ g : U, Γ(Γ.G.left, V g) := fun g =>
    (Γ.G.left.presheaf.map (homOfLE (inf_le_left : V g ≤ W g)).op).hom (s g)
  have hsf : ∀ (g : U) (t : T) (h : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V g), valAt (Γ.pt t).left (V g) h (sf g) = f t :=
    fun g t h => (valAt_restrict _ _ h (top_le_of_le _ inf_le_left h) _).trans (hs g t _)
  have hcomp : TopCat.Presheaf.IsCompatible Γ.G.left.sheaf.1 V sf := by
    intro a b
    have := sec_inj R T Γ (V a ⊓ V b)
      ((Γ.G.left.presheaf.map (homOfLE (inf_le_left : V a ⊓ V b ≤ V a)).op).hom (sf a) -
        (Γ.G.left.presheaf.map (homOfLE (inf_le_right : V a ⊓ V b ≤ V b)).op).hom (sf b)) (fun t h => by
          rw [← valHom_apply, map_sub, valHom_apply, valHom_apply,
            valAt_restrict _ _ h (top_le_of_le _ inf_le_left h),
            valAt_restrict _ _ h (top_le_of_le _ inf_le_right h), hsf, hsf, sub_self])
    exact sub_eq_zero.1 this
  obtain ⟨σ, hσ, -⟩ := Γ.G.left.sheaf.existsUnique_gluing' V U (fun g => homOfLE inf_le_right)
    (fun g hg => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, hg⟩, hW ⟨g, hg⟩, hg⟩) sf hcomp
  refine ⟨σ, fun t ht => ?_⟩
  let x : Spec (CommRingCat.of (FractionRing R)) := default
  let g : U := ⟨(Γ.pt t).left x, ht (Set.mem_univ x)⟩
  have hg : ⊤ ≤ (Γ.pt t).left ⁻¹ᵁ V g := top_le_of_mem (Γ.pt t).left x ⟨hW g, g.2⟩
  exact (valAt_restrict _ (homOfLE (inf_le_right : V g ≤ U)) hg ht σ).symm.trans
    ((congrArg (valAt (Γ.pt t).left (V g) hg) (hσ g)).trans (hsf g t hg))

theorem finite_le : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (U U' : X.Opens), IsFinite (U.ι ≫ f) → (∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U') → U ≤ U' := by
  intro R _ _ X f U U' hU hU' x hx
  let x' : U.toScheme := ⟨x, hx⟩
  have hc : IsClosed ((U.ι ≫ f) '' closure {x'}) := (U.ι ≫ f).isClosedMap _ isClosed_closure
  have hs : (U.ι ≫ f) x' ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint (R := R) _
  obtain ⟨y, hy, e⟩ := hs.mem_closed hc ⟨x', subset_closure rfl, rfl⟩
  have h1 : U.ι x' ⤳ U.ι y := (specializes_iff_mem_closure.2 hy).map U.ι.continuous
  exact h1.mem_open U'.isOpen (hU' _ (by rw [← Scheme.Hom.comp_apply]; exact e))

end PositivityTheory.HtPt.Unc
