import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HodgeKill
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {K : Type} [CommRing K] {W Z Y : Scheme.{0}}

def inU (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) : ObjectProperty (Thick (smFun Z q)) :=
  InU (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) V

theorem cosieve_bot {C : Type 1} [Category.{0} C] : Cosieve (⊥ : ObjectProperty C) := fun _ _ _ h => h

def Sec (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) : Type := Γ(Z, V)

instance (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) : CommRing (Sec q V) := inferInstanceAs (CommRing Γ(Z, V))

instance (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) : Algebra K (Sec q V) := (strV q V : K →+* Γ(Z, V)).toAlgebra

abbrev HV (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) (a j : ℕ) : Type 1 := HU (G q a) (inU q V) j

structure Lifts (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) where
  v : ∀ T : (inU q V).FullSubcategory, Sec q V → T.obj.B
  hv : ∀ T g, Ideal.Quotient.mk T.obj.J (v T g) =
    ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T.obj T.property g

def Lifts.form {q : Z ⟶ Spec (CommRingCat.of K)} {V : Z.Opens} (Λ : Lifts q V) {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V)
    (s : ComposableArrows (inU q V).FullSubcategory a) : (s.obj (Fin.last a)).obj.B :=
  Λ.v _ g₀ * ∏ k : Fin a, ((s.map (homOfLE (Fin.le_last k.succ))).hom.φ (Λ.v _ (g k)) -
    (s.map (homOfLE (Fin.le_last k.castSucc))).hom.φ (Λ.v _ (g k)))

def IsForm (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) {a : ℕ} (g₀ : Sec q V) (g : Fin a → Sec q V) (c : HV q V a a) : Prop :=
  ∀ Λ : Lifts q V, Rep ((thFil (smFun Z q) (a : ℤ)).res (inU q V).ι) ((thFil (smFun Z q) ((a : ℤ) + 1)).res (inU q V).ι)
    (Λ.form g₀ g) c

def IsOm (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) (a : ℕ) (e : Om K (Sec q V) a →ₗ[K] HV q V a a) : Prop :=
  ∀ g₀ g, IsForm q V g₀ g (e (form K g₀ g))

def RC.mor {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {F : C ⥤ ModuleCat.{0} R}
    {F' : C' ⥤ ModuleCat.{0} R} (m : CH.Mor F F' (RingHom.id R)) {U Q : ObjectProperty C} {U' Q' : ObjectProperty C'}
    (hQ : Cosieve Q) (hQ' : Cosieve Q') (h : ∀ T, U' T → U (m.G.obj T)) (h' : ∀ T, Q' T → Q (m.G.obj T)) :
    Cx.Hom (RC F U hQ) (RC F' U' hQ') (RingHom.id R) where
  f n := ((morU m h).pullC n).restrict fun z hz s hs => by
    have := hz (s ⋙ (morU m h).G) (h' _ hs)
    change (morU m h).τ _ (z (s ⋙ (morU m h).G)) = 0
    rw [this, map_zero]
  comm n x := Subtype.ext ((morU m h).d_pullC n x.1)

def morG {p : Z ⟶ Spec (CommRingCat.of K)} {q : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z) (hu : u ≫ p = q) (a : ℕ) :
    CH.Mor (G p a) (G q a) (RingHom.id K) :=
  (smS u hu).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ)) (b' := thFil _ ((a : ℤ) + 1))
    (fun _ _ hx => hx) fun _ _ hx => hx

def morV {p : Z ⟶ Spec (CommRingCat.of K)} {q : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z) (hu : u ≫ p = q) (a : ℕ)
    {U : ObjectProperty (Thick (smFun Z p))} {U' : ObjectProperty (Thick (smFun Y q))}
    (h : ∀ T, U' T → U ((smS u hu).G.obj T)) : CH.Mor (U.ι ⋙ G p a) (U'.ι ⋙ G q a) (RingHom.id K) :=
  morU (morG u hu a) h

def pullRC {p : Z ⟶ Spec (CommRingCat.of K)} {q : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z) (hu : u ≫ p = q) (a : ℕ)
    {U Q : ObjectProperty (Thick (smFun Z p))} {U' Q' : ObjectProperty (Thick (smFun Y q))} (hQ : Cosieve Q) (hQ' : Cosieve Q')
    (h : ∀ T, U' T → U ((smS u hu).G.obj T)) (h' : ∀ T, Q' T → Q ((smS u hu).G.obj T)) :
    Cx.Hom (RC (G p a) U hQ) (RC (G q a) U' hQ') (RingHom.id K) :=
  RC.mor (morG u hu a) hQ hQ' h h'

def SiteLaws : Prop := ∀ (K : Type) [CommRing K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) (u : Y ⟶ Z),
  (∀ V, Cosieve (inU q V)) ∧ Cosieve (On q i) ∧ (∀ T, inU q ⊤ T) ∧ (∀ V V' T, inU q (V ⊓ V') T ↔ inU q V T ∧ inU q V' T) ∧
  (∀ V T, inU (u ≫ q) (u ⁻¹ᵁ V) T ↔ inU q V ((smS u rfl).G.obj T)) ∧
  ∀ T, On (u ≫ q) (pullback.snd i u) T ↔ On q i ((smS u rfl).G.obj T)

def OnIso : Prop := ∀ (K : Type) [CommRing K] (W Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) [Mono i]
  (U : ObjectProperty (Thick (smFun Z q))) (U' : ObjectProperty (Thick (smFun W (i ≫ q))))
  (h : ∀ T, U' T → (U ⊓ On q i) ((smS i rfl).G.obj T)), (∀ T, U ((smS i rfl).G.obj T) → U' T) →
  ∀ a n, Function.Bijective ((morV i rfl a h).pull n)

def ZarAbs : Prop := ∀ (K : Type) [Field K] (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (ι : Type) (V : Z.Opens)
  (U : ι → Z.Opens), (⨆ α, U α) = V → ∀ (h : (fun T => ∃ α, inU q (U α) T) ≤ inU q V) (a n : ℕ),
  Function.Bijective ((resU (G q a) h).pull n)

def ZarRel : Prop := ∀ (K : Type) [Field K] (W Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z) [Mono i]
  (hQ : Cosieve (On q i)) (ι : Type) (V : Z.Opens) (U : ι → Z.Opens), (⨆ α, U α) = V →
  ∀ (h : (fun T => ∃ α, inU q (U α) T) ≤ inU q V) (a n : ℕ), Function.Bijective ((RC.res (G q a) hQ h).mapH n)

def AffOm : Prop := ∀ (K : Type) [Field K] [CharZero K] (Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (V : Z.Opens) (d : ℕ),
  Nonempty (Coord q V d) → ∀ a, (∀ j, j ≠ a → Subsingleton (HV q V a j)) ∧
    ∃ e : Om K (Sec q V) a →ₗ[K] HV q V a a, IsOm q V a e ∧ Function.Bijective e

def OmNat : Prop := ∀ (K : Type) [Field K] (Z Y : Scheme.{0}) (p : Z ⟶ Spec (CommRingCat.of K)) (q : Y ⟶ Spec (CommRingCat.of K))
  (u : Y ⟶ Z) (hu : u ≫ p = q) (V : Z.Opens) (V' : Y.Opens) (hV : V' ≤ u ⁻¹ᵁ V)
  (h : ∀ T, inU q V' T → inU p V ((smS u hu).G.obj T)),
  ∃ φ : Sec p V →ₐ[K] Sec q V', (∀ g, φ g = (u.appLE V V' hV).hom g) ∧ ∀ (a : ℕ) e e', IsOm p V a e → IsOm q V' a e' →
    ∀ ω, (morV u hu a h).pull a (e ω) = e' (omMap φ a ω)

def AffRel : Prop := ∀ (K : Type) [Field K] [CharZero K] (W Z : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z)
  [IsClosedImmersion i] (hQ : Cosieve (On q i)) (V : Z.Opens) (d d' : ℕ), Nonempty (Coord q V d) →
  Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) d') → ∀ a, (∀ j, j ≠ a → Subsingleton ((RC (G q a) (inU q V) hQ).H j)) ∧
    ∀ e, IsOm q V a e → ∀ ι : Cx.Hom (RC (G q a) (inU q V) hQ) (CH.cx ((inU q V).ι ⋙ G q a)) (RingHom.id K),
      (∀ n x, ι.f n x = x.1) → Function.Injective (ι.mapH a) ∧
        ∀ ω, e ω ∈ Set.range (ι.mapH a) ↔ ω ∈ relOm K (show Ideal (Sec q V) from RingHom.ker (i.app V).hom) a

def ChartLaws : Prop := ∀ (K : Type) [Field K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z)
  [IsClosedImmersion i] (π : Y ⟶ Z) (d : ℕ) (V : Z.Opens) (c : BChart q i π d V),
  (∀ V' : Z.Opens, ∀ h : V' ≤ V, IsAffineOpen V' → ∃ c' : BChart q i π d V', (∀ j, c'.t j = rs h (c.t j)) ∧
    ∀ k, c'.C k = c.C k ⊓ π ⁻¹ᵁ V') ∧
  Nonempty (Coord q V (c.n + d)) ∧ Nonempty (Coord (i ≫ q) (i ⁻¹ᵁ V) c.n) ∧
  ∀ (k : Fin d) (D : Y.Opens) (h : D ≤ c.C k), IsAffineOpen D → Nonempty (Coord (π ≫ q) D (c.n + d)) ∧
    Nonempty (Coord (pullback.snd i π ≫ π ≫ q) (pullback.snd i π ⁻¹ᵁ D) (c.n + d - 1)) ∧
    RingHom.ker ((pullback.snd i π).app D).hom = Ideal.span {(π.appLE V D (h.trans (c.C_le k))).hom (c.t k)} ∧
    ∀ (a : ℕ) (ω : Om K (Sec (π ≫ q) D) a),
      (show Sec (π ≫ q) D from (π.appLE V D (h.trans (c.C_le k))).hom (c.t k)) • ω = 0 → ω = 0

def ChartBij : Prop := ∀ (K : Type) [Field K] [CharZero K] (W Z Y : Scheme.{0}) (q : Z ⟶ Spec (CommRingCat.of K)) (i : W ⟶ Z)
  [IsClosedImmersion i] (π : Y ⟶ Z) (d : ℕ), 0 < d → ∀ (V : Z.Opens), Nonempty (BChart q i π d V) →
  ∀ (hQ : Cosieve (On q i)) (hQ' : Cosieve (On (π ≫ q) (pullback.snd i π))) (a : ℕ) h h' (n : ℕ),
  Function.Bijective ((pullRC π rfl a (U := inU q V) (U' := inU (π ≫ q) (π ⁻¹ᵁ V)) hQ hQ' h h').mapH n)

end CrystallineSemistableComparison.Onto

end
