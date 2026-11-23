import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FirstChernCoboundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris
open GlobalTheory.CatH (face toLast)

universe w v u

namespace CrystallineSemistableComparison.Onto

open Pb HT

namespace RelativeFormLift

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R)

def liftS {Q : ObjectProperty C} (hQ : Cosieve Q) {n : ℕ} (s : ComposableArrows C n) (hs : Q (s.obj 0)) :
    ComposableArrows Q.FullSubcategory n :=
  Q.lift s fun k => hQ (s.map (homOfLE (Fin.zero_le _))) hs

open Classical in

def extZ {Q : ObjectProperty C} (hQ : Cosieve Q) {n : ℕ} (b : CH.Cn (Q.ι ⋙ F) n) : CH.Cn F n :=
  fun s => if hs : Q (s.obj 0) then b (liftS hQ s hs) else 0

theorem d_extZ {Q : ObjectProperty C} (hQ : Cosieve Q) {n : ℕ} (b : CH.Cn (Q.ι ⋙ F) n) (s : ComposableArrows C (n + 1))
    (hs : Q (s.obj 0)) : CH.d F n (extZ F hQ b) s = CH.d (Q.ι ⋙ F) n b (liftS hQ s hs) := by
  change ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (toLast i s)).hom (extZ F hQ b (face i s)) =
    ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • ((Q.ι ⋙ F).map (toLast i (liftS hQ s hs))).hom (b (face i (liftS hQ s hs)))
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Q ((face i s).obj 0) := hQ (s.map (homOfLE (Fin.zero_le _))) hs
  have e : extZ F hQ b (face i s) = b (liftS hQ (face i s) h) := dif_pos h
  rw [e]
  rfl

end RelativeFormLift

open RelativeFormLift in

theorem relLiftOf_pf : RelLiftOf := by
  intro hS hO K _ W Z q i _ a n y hy
  have hQ : Cosieve (On q i) := (hS K W Z W q i i).2.1
  have hQ' : Cosieve ((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i) :=
    fun _ _ f h => ⟨trivial, hQ f h.2⟩
  have h : ∀ T, (⊤ : ObjectProperty (Thick (smFun W (i ≫ q)))) T →
      ((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i) ((smS i rfl).G.obj T) := fun T _ =>
    ⟨trivial, ((hS K W Z W q i i).2.2.2.2.2 T).1
      ⟨pullback.lift (pt (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T)
        (pt (γ := dividedPowersBot K) (p := 0) (q := i ≫ q) (κ := Ideal.Quotient.mk ⊥) T) rfl,
        pullback.lift_snd _ _ _⟩⟩
  have hbij := hO K W Z q i ⊤ ⊤ h (fun _ _ => trivial) a n
  obtain ⟨⟨z₀, hz₀⟩, hy0⟩ := Submodule.Quotient.mk_surjective
    (((CH.cx (G q a)).B n).submoduleOf ((CH.cx (G q a)).Z n)) (show (CH.cx (G q a)).H n from y)
  have hz₀' : CH.d (G q a) n z₀ = 0 := hz₀
  subst hy0
  set w₀ := (CH.Mor.restrict (G q a) ((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i).ι).pullC n z₀ with hw
  have hw₀ : CH.d _ n w₀ = 0 := by rw [hw, CH.Mor.d_pullC, hz₀', map_zero]
  have e1 : (morV i rfl a h).pull n ((CH.cx _).cls w₀ hw₀) =
      (CH.Mor.restrict (G (i ≫ q) a) (⊤ : ObjectProperty (Thick (smFun W (i ≫ q)))).ι).pull n
        (pullH i rfl a n (Submodule.Quotient.mk ⟨z₀, hz₀⟩)) := rfl
  have e2 : (morV i rfl a h).pull n ((CH.cx _).cls w₀ hw₀) = 0 := by
    rw [e1, hy, map_zero]
  have e3 : (CH.cx _).cls w₀ hw₀ = 0 := hbij.1 (by rw [e2, map_zero])
  have e4 : w₀ ∈ (CH.cx (((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i).ι ⋙ G q a)).B n :=
    (Submodule.Quotient.mk_eq_zero (((CH.cx _).B n).submoduleOf ((CH.cx _).Z n))
      (x := (⟨w₀, hw₀⟩ : (CH.cx (((⊤ : ObjectProperty (Thick (smFun Z q))) ⊓ On q i).ι ⋙ G q a)).Z n))).1 e3
  cases n with
  | zero =>
    have e5 : w₀ = 0 := (Submodule.mem_bot K).1 e4
    refine ⟨z₀, hz₀', fun s hs => ?_, rfl⟩
    exact congrFun e5 (liftS hQ' s ⟨trivial, hs⟩)
  | succ m =>
    obtain ⟨b', hb'⟩ := e4
    have hz : CH.d (G q a) (m + 1) (z₀ - CH.d (G q a) m (extZ (G q a) hQ' b')) = 0 := by
      rw [map_sub, hz₀', CH.d_d, sub_zero]
    refine ⟨z₀ - CH.d (G q a) m (extZ (G q a) hQ' b'), hz, fun s hs => ?_, ?_⟩
    · change z₀ s - CH.d (G q a) m (extZ (G q a) hQ' b') s = 0
      rw [d_extZ (G q a) hQ' b' s ⟨trivial, hs⟩]
      rw [hb']
      exact sub_self _
    · show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      rw [Submodule.Quotient.eq]
      refine ⟨-extZ (G q a) hQ' b', ?_⟩
      rw [map_neg]
      change -(CH.d (G q a) m (extZ (G q a) hQ' b')) = (z₀ - CH.d (G q a) m (extZ (G q a) hQ' b')) - z₀
      abel

end CrystallineSemistableComparison.Onto

end
