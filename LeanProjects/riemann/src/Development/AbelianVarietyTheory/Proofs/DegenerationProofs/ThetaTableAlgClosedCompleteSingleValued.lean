import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThetaConst
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFramesOnUniformisedModelFibre
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section

namespace GlobalTheory.OneBasis

variable {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F]
  [Algebra (FractionRing R) F]

theorem exists_isTorsFrame_closed [CharZero R] [IsAlgClosed F] (hLaw : Laws) {ρ : LB.Gen (A.L.pull (eSec A.A))}
    (hρ : ρ.IsGen) {n : ℕ} (hn : Odd n) (x : TFK (R := R) F ⟶ A.A) (hx : x ^ n = 1) :
    ∃ e, IsTorsFrame A ρ n x e := by
  let T := TFK (R := R) F
  have : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hu : IsUnit ((n ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hn.pos.ne'))
  obtain ⟨y, hy⟩ : ∃ y : T ⟶ A.A, y ^ n = x :=
    TorusExt.exists_pow_eq_of_noetherian (S := Sp (FractionRing R)) (k := F) T.hom hLaw.mulN A hn.pos.ne' x
  have hy' : y ^ (n ^ 2) = 1 := by rw [sq, pow_mul, hy, hx]
  obtain ⟨hex, -⟩ := hLaw.symLift _ A (n ^ 2) hn.pow hu T y hy'
  obtain ⟨V, hV, θ₀, hθ₀⟩ := hex p
  obtain ⟨h, hh⟩ := GlobalLift.exists_section (T := T) hV
  obtain ⟨θ, hθ⟩ := GlobalLift.exists_symLift_pull A.isLB h hθ₀
  rw [← Category.assoc, hh, Category.id_comp] at hθ
  exact exists_isTorsFrame_of_symLift hLaw _ A ρ hρ n hn T y x hy' hy θ hθ

omit [IsDomain R] in

theorem exists_valAt (hLaw : Laws) {k : ℕ} (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) {e} (he : LB.Gen.IsGen e) :
    ∃ c, ValAt t x e c := by
  obtain ⟨v, hv, -⟩ := hLaw.evVal _ A k x e he t
  obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 v
  refine ⟨c, fun z J hJ => ?_⟩
  have := FrameMove.sval_valueAt hv (𝟙 _) hJ
  rw [Category.id_comp] at this
  exact this

end GlobalTheory.OneBasis

namespace GlobalTheory

theorem tab_full_uniq : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m n r : ℕ), Odd m → Odd n → ∀ (th : SecA A F 1) (τ : Fin r → SecA A F (m ^ 2)), (∀ t, ∃! a, Cmb τ a t) → (tab ρ m th τ).Full (m ^ 2) n ∧ (tab ρ m th τ).Uniq (m ^ 2) n := by
  intro hLL R _ _ _ A F _ _ _ ρ hρ m n r hm hn th τ hτ
  have H := existsUnique_thetaConst hLL R A F ρ hρ
  refine ⟨⟨fun x hx => ?_, fun j x hx => ?_, fun j x hx => ?_⟩, fun x a ha => ?_, fun j x c hc => ?_⟩
  · obtain ⟨q, hq, -⟩ := H m hm th x hx
    obtain ⟨a, ha, -⟩ := hτ q.1
    exact ⟨a, hx, q.1, q.2, hq, ha⟩
  · obtain ⟨q, hq, -⟩ := H (n ^ j) hn.pow th x hx
    exact ⟨q.2, hx, q.1, hq⟩
  · obtain ⟨e, he⟩ := exists_isTorsFrame_closed A F hLL.1 hρ (hn.pow (n := j)) x hx
    choose l hl using fun i => exists_valAt A F hLL.1 (τ i) x he.2.1
    exact ⟨l, e, he, hl⟩
  · obtain ⟨hx, t, c, ht, ha⟩ := ha
    refine ⟨hx, ?_⟩
    rintro a' ⟨-, t', c', ht', ha'⟩
    have e : t' = t := congrArg Prod.fst ((H m hm th x hx).unique (y₁ := (t', c')) (y₂ := (t, c)) ht' ht)
    subst e
    exact (hτ t').unique ha' ha
  · obtain ⟨hx, t, ht⟩ := hc
    refine ⟨hx, ?_⟩
    rintro c' ⟨-, t', ht'⟩
    exact congrArg Prod.snd ((H (n ^ j) hn.pow th x hx).unique (y₁ := (t', c')) (y₂ := (t, c)) ht' ht)

end GlobalTheory
end
