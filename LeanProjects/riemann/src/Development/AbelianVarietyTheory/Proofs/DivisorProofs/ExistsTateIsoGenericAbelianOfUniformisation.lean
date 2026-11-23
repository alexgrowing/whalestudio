import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevel

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem exists_tateIso_toA : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
  (I : (letI := H.starRing; TateIsoQ D P.D.toPre P.oD F)),
  ∃ J : TateIso D F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ (letI := H.starRing; P.oA.act a))
      (fun n g g' z => Out.WeilIs P.A.A P.A.L n g g' (unitOn z)),
    (∀ n, J.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ a, P.ToA F n (I.ev n a) (J.ev n a) := by
  intro E _ _ _ H D R _ _ _ hR t P F _ _ _ I
  letI := H.starRing
  have hA : AdmBase R (maximalIdeal R) := hR.1
  have h0 : CharZero R := hR.2
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hA t P
  choose f f₁ f₂ f₃ f₄ f₅ f₆ using hT F
  obtain ⟨ev, ev0, evp⟩ : ∃ ev : ℕ → D.La → (TFK (R := R) F ⟶ P.A.A), (∀ a, ev 0 a = 1) ∧
      ∀ n (hn : 0 < n) a, ev n a = f n hn (I.ev n a) :=
    ⟨fun n a => if hn : 0 < n then f n hn (I.ev n a) else 1, fun a => dif_neg (lt_irrefl 0),
      fun n hn a => dif_pos hn⟩
  have add : ∀ n a b, ev n (a + b) = ev n a * ev n b := fun n a b => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ev0, ev0, ev0, _root_.one_mul]
    · rw [evp n hn, evp n hn, evp n hn, f₄ n hn _ _ _ (I.add n hn a b)]
  have zero : ∀ n, ev n 0 = 1 := fun n => by
    have := add n 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have tors : ∀ n (hn : 0 < n) p, f n hn p ^ n = 1 := fun n hn p => by
    obtain ⟨w, hw⟩ := P.U.ext
    exact ((f₁ n hn p _).2 rfl w hw).1
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := ev, add := add
            lin := fun n c a => ?_, ker := fun n hn a => ?_, onto := fun n hn x => ⟨fun hx => ?_, ?_⟩
            tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ },
    fun _ => rfl, fun j hj x => (f₁ j hj _ _).2 (evp j hj x)⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ev0, ev0]
      have := P.oA.hom c
      exact (MonObj.one_comp _).symm
    · rw [evp n hn, evp n hn, f₅ n hn _ _ _ (I.lin n hn c a)]
  · rw [← zero n, evp n hn, evp n hn, f₃, I.ker n hn]
    simp only [zero_add]
  · obtain ⟨p, hp⟩ := f₂ n hn x hx
    obtain ⟨a, ha⟩ := I.onto n hn p
    exact ⟨a, by rw [evp n hn, (f₃ n hn _ _).2 ha, hp]⟩
  · rintro ⟨a, rfl⟩
    rw [evp n hn, tors]
  · obtain ⟨q, q₁, q₂, q₃⟩ := I.tower n m hn hm a
    have hN := Nat.mul_pos hn hm
    have h := (GlobalTheory.LevelCompat.qkToAkU_level GlobalTheory.firstFiveLaws R _ hA P.D P.A t.G t.semi P.U F n m _ hn hm rfl q
      (I.ev (n * m) a) _).2 q₁ q₂ ((f₁ _ hN _ _).2 rfl)
    rw [evp _ hN, evp n hn, (f₁ n hn _ _).1 h, (f₃ n hn _ _).2 q₃]
  · have h := (f₆ n hn _ _ _).1 (I.isom n hn a b)
    rw [← evp, ← evp] at h
    exact h

end GlobalTheory.LowDat
