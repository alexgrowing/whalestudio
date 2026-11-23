import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FirstChernCoboundary
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

universe w w' w''

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace AffineRelativeForms

section Abstract

variable {R : Type} [CommRing R]

theorem les_one {K : Cx.{w} R} {L : Cx.{w'} R} {M : Cx.{w''} R} (f : Cx.Hom K L (RingHom.id R))
    (g : Cx.Hom L M (RingHom.id R)) (hf : ∀ n, Function.Injective (f.f n)) (hfg : ∀ n, Function.Exact (f.f n) (g.f n))
    (hg : ∀ n, Function.Surjective (g.f n)) (a : ℕ) (hL : ∀ j, j ≠ a → Subsingleton (L.H j))
    (hM : ∀ j, j ≠ a → Subsingleton (M.H j)) (hga : Function.Surjective (g.mapH a)) :
    (∀ j, j ≠ a → Subsingleton (K.H j)) ∧ Function.Injective (f.mapH a) ∧
      ∀ x, x ∈ Set.range (f.mapH a) ↔ g.mapH a x = 0 := by
  obtain ⟨δ, -, h0, hfg', hgδ, hδf⟩ := CrystallineSemistableComparison.P.les f g hf hfg hg
  refine ⟨fun j hj => ?_, ?_, fun x => (hfg' a x).symm⟩
  · suffices h : ∀ x : K.H j, x = 0 from ⟨fun x y => by rw [h x, h y]⟩
    intro x
    have hx : f.mapH j x = 0 := by
      have := hL j hj
      exact Subsingleton.elim _ _
    cases j with
    | zero => exact h0 (by rw [hx, map_zero])
    | succ k =>
      obtain ⟨y, rfl⟩ := (hδf k x).1 hx
      by_cases hk : k = a
      · subst hk
        obtain ⟨z, rfl⟩ := hga y
        exact (hgδ k _).2 ⟨z, rfl⟩
      · have := hM k hk
        rw [Subsingleton.elim y 0, map_zero]
  · cases a with
    | zero => exact h0
    | succ k =>
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨y, rfl⟩ := (hδf k x).1 hx
      have := hM k (by omega)
      rw [Subsingleton.elim y 0, map_zero]

end Abstract

section Ses

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
  (U Q : ObjectProperty C)

def liftQ (hQ : Cosieve Q) {n : ℕ} (s : ComposableArrows U.FullSubcategory n) (hs : Q (s.obj 0).obj) :
    ComposableArrows (U ⊓ Q).FullSubcategory n :=
  ObjectProperty.lift (U ⊓ Q) (s ⋙ U.ι) fun j =>
    show U (s.obj j).obj ∧ Q (s.obj j).obj from ⟨(s.obj j).property, hQ (s.map (homOfLE (Fin.zero_le j))).hom hs⟩

theorem res_surj (hQ : Cosieve Q) (hle : U ⊓ Q ≤ U) (n : ℕ) : Function.Surjective ((resU F hle).pullC n) := by
  classical
  intro z
  refine ⟨fun s => if hs : Q (s.obj 0).obj then z (liftQ U Q hQ s hs) else 0, ?_⟩
  funext s
  have hs : Q ((s ⋙ ObjectProperty.ιOfLE hle).obj 0).obj := (s.obj 0).property.2
  change (if hs : Q ((s ⋙ ObjectProperty.ιOfLE hle).obj 0).obj then z (liftQ U Q hQ _ hs) else 0) = z s
  rw [dif_pos hs]
  rfl

theorem res_exact (hQ : Cosieve Q) (hle : U ⊓ Q ≤ U) (ι : Cx.Hom (RC F U hQ) (CH.cx (U.ι ⋙ F)) (RingHom.id R))
    (hι : ∀ n x, ι.f n x = x.1) (n : ℕ) : Function.Exact (ι.f n) ((resU F hle).pullC n) := by
  intro y
  constructor
  · intro hy
    refine ⟨⟨y, fun s hs => ?_⟩, hι n _⟩
    exact congrFun hy (liftQ U Q hQ s hs)
  · rintro ⟨x, rfl⟩
    rw [hι]
    funext s
    exact x.2 (s ⋙ ObjectProperty.ιOfLE hle) (s.obj 0).property.2

end Ses

end AffineRelativeForms

open AffineRelativeForms in
theorem affRelOf_pf : AffRelOf := by
  intro hSite hOn hAff hNat hForm K _ _ W Z q i _ hQ V d d' hc hc' a
  have : Mono i := inferInstance
  have hS := hSite K W Z W q i i
  have h0 : ∀ T, inU (i ≫ q) (i ⁻¹ᵁ V) T → inU q V ((smS i rfl).G.obj T) := fun T h => (hS.2.2.2.2.1 V T).1 h
  have h2 : ∀ T, inU q V ((smS i rfl).G.obj T) → inU (i ≫ q) (i ⁻¹ᵁ V) T := fun T h => (hS.2.2.2.2.1 V T).2 h
  have hOnW : ∀ T, On q i ((smS i rfl).G.obj T) := by
    intro T
    refine (hS.2.2.2.2.2 T).1 ?_
    obtain ⟨w, hw⟩ : ∃ w, w = pt (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T := ⟨_, rfl⟩
    exact ⟨pullback.lift w w rfl, by rw [pullback.lift_snd, hw]⟩
  have h1 : ∀ T, inU (i ≫ q) (i ⁻¹ᵁ V) T → (inU q V ⊓ On q i) ((smS i rfl).G.obj T) :=
    fun T h => show inU q V _ ∧ On q i _ from ⟨h0 T h, hOnW T⟩
  have hBij := hOn K W Z q i (inU q V) (inU (i ≫ q) (i ⁻¹ᵁ V)) h1 h2 a
  obtain ⟨hVsub, e0, he0, he0b⟩ := hAff K Z q V d hc a
  obtain ⟨hWsub, e', he', he'b⟩ := hAff K W (i ≫ q) (i ⁻¹ᵁ V) d' hc' a
  obtain ⟨φ, hφ, hnat⟩ := hNat K Z W q (i ≫ q) i rfl V (i ⁻¹ᵁ V) le_rfl h0
  have hφs : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := i.app_surjective V hc.some.affine y
    exact ⟨x, by rw [hφ, Scheme.Hom.appLE_eq_app]; exact hx⟩
  have hFL := ((hForm K (Sec q V) (Sec (i ≫ q) (i ⁻¹ᵁ V)) a).2 φ).2.2 hφs
  have hker : RingHom.ker φ = (show Ideal (Sec q V) from RingHom.ker (i.app V).hom) := by
    ext g
    show g ∈ RingHom.ker φ ↔ g ∈ RingHom.ker (i.app V).hom
    rw [RingHom.mem_ker, RingHom.mem_ker, hφ, Scheme.Hom.appLE_eq_app]
    exact Iff.rfl
  have hle : inU q V ⊓ On q i ≤ inU q V := fun T h => h.1
  have hcomp : ∀ n x, (morV i rfl a h1).pull n ((resU (G q a) hle).hom.mapH n x) = (morV i rfl a h0).pull n x := by
    intro n x
    obtain ⟨z, hz, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj _ n).1 x
    rfl
  have hM : ∀ j, j ≠ a → Subsingleton ((CH.cx ((inU q V ⊓ On q i).ι ⋙ G q a)).H j) := by
    intro j hj
    have := hWsub j hj
    exact (hBij j).1.subsingleton
  have hga : Function.Surjective ((resU (G q a) hle).hom.mapH a) := by
    intro y
    obtain ⟨ω', hω'⟩ := he'b.2 ((morV i rfl a h1).pull a y)
    obtain ⟨ω, rfl⟩ := hFL.1 ω'
    refine ⟨e0 ω, (hBij a).1 ?_⟩
    rw [hcomp, hnat a e0 e' he0 he' ω]
    exact hω'
  have key : ∀ ι : Cx.Hom (RC (G q a) (inU q V) hQ) (CH.cx ((inU q V).ι ⋙ G q a)) (RingHom.id K),
      (∀ n x, ι.f n x = x.1) →
      (∀ j, j ≠ a → Subsingleton ((RC (G q a) (inU q V) hQ).H j)) ∧ Function.Injective (ι.mapH a) ∧
        ∀ x, x ∈ Set.range (ι.mapH a) ↔ (resU (G q a) hle).hom.mapH a x = 0 := by
    intro ι hι
    exact les_one ι (resU (G q a) hle).hom
      (fun n x y h => Subtype.ext (by rw [← hι, ← hι]; exact h))
      (fun n => res_exact (G q a) (inU q V) (On q i) hQ hle ι hι n)
      (fun n => res_surj (G q a) (inU q V) (On q i) hQ hle n) a hVsub hM hga
  let ι0 : Cx.Hom (RC (G q a) (inU q V) hQ) (CH.cx ((inU q V).ι ⋙ G q a)) (RingHom.id K) :=
    ⟨fun n => (relS ((inU q V).ι ⋙ G q a) (fun T => On q i T.obj) n).subtype, fun n x => rfl⟩
  refine ⟨(key ι0 fun _ _ => rfl).1, fun e he ι hι => ⟨(key ι hι).2.1, fun ω => ?_⟩⟩
  rw [(key ι hι).2.2, ← hker, ← hFL.2 ω]
  constructor
  · intro h
    apply he'b.1
    rw [← hnat a e e' he he' ω, ← hcomp, h, map_zero, map_zero]
  · intro h
    apply (hBij a).1
    rw [hcomp, hnat a e e' he he' ω, h, map_zero, map_zero]

end CrystallineSemistableComparison.Onto

end
