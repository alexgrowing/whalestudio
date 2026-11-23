import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModN
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TateIsometryOfFiniteLevelIsometries
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLevelIsometryOfDenseGeometricPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem tateIso_spread : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  (P : PolAV (Sp R)) (act : 𝓞 E → (P.A ⟶ P.A)) (o : Type) [CommRing o] (s : Sp R ⟶ Sp o) (z : o) (k : ℕ), 0 < k →
  Module.finrank ℤ D.La = 2 * P.g → ∀ (pt : D.La → (𝟙_ (Over (Sp R)) ⟶ P.A))
  (F : Type) [Field F] [CharZero F] (x₀ : Sp F ⟶ Sp R) (β₀ : o →+* F), DenseRange x₀ → x₀ ≫ s = spMap β₀ →
  ∀ I₀ : TateIso D F (Over.mk x₀ ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
  (I₀.ζ k : F) = β₀ z → (∀ a, toUnit _ ≫ pt a = I₀.ev k a) →
  ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ Sp R) (β : o →+* K), x ≫ s = spMap β →
  ∃ I : TateIso D K (Over.mk x ⟶ P.A) (fun a g => g ≫ act a) (fun n g g' c => Out.WeilIs P.A P.L n g g' (unitOn c)),
    (I.ζ k : K) = β z ∧ ∀ a, toUnit _ ≫ pt a = I.ev k a := by
  intro E _ _ _ H D R _ _ _ P act o _ s z k hk hrk pt F _ _ x₀ β₀ hd hx₀ I₀ hζ₀ hev₀ K _ _ _ x β hx
  have hL : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have := P.isAb.comm
  have hu : ∀ {L : Type} [Field L] (y : Sp L ⟶ Sp R),
      (Over.homMk y (by simp) : Over.mk y ⟶ Out.baseOver (Sp R)) = toUnit (Over.mk y) := fun y =>
    Over.OverMorphism.ext ((Over.w (toUnit (Over.mk y))).symm.trans (Category.comp_id _))
  have hcard : ∀ n, 0 < n → Nat.card {w : Over.mk x ⟶ P.A // w ^ n = 1} = n ^ Module.finrank ℤ D.La := fun n hn => by
    rw [hrk]
    exact (hL.mulN _ P n hn).2.2.2.2 K x (Nat.cast_ne_zero.2 hn.ne')
  obtain ⟨I, hI, hA⟩ := GlobalTheory.TateTower.tateIso_of_levels E H D K (Over.mk x ⟶ P.A) (fun c w => w ≫ act c)
    (fun n w w' c => Out.WeilIs P.A P.L n w w' (unitOn c)) k (β z) _ (fun a : D.La => a)
    (fun a => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ pt a) hk
    (fun n hn => Nat.finite_of_card_ne_zero (by rw [hcard n hn]; positivity))
    (fun n m w w' c hn hm hw hw' h => by
      have e : unitOn (c ^ m) = unitOn c ^ m := map_pow _ _ _
      have u : IsUnit ((n * m : ℕ) : K) := (Nat.cast_ne_zero.2 (Nat.mul_pos hn hm).ne').isUnit
      have u' := u.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      rw [map_natCast] at u'
      rw [e]
      exact PELFamily.weilIs_lower P hL.weil hm u' hw hw' h)
    (fun m hm => by
      have hn := Nat.mul_pos hk hm
      obtain ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := GlobalTheory.exists_levelIsometry_of_dense hL E H D (Sp R) P act o s z _
        (fun a : D.La => a) pt (k * m) m hn (Dense.mono (fun p hp =>
          ⟨F, inferInstance, x₀, β₀, I₀.ζ (k * m), I₀.ev (k * m), Nat.cast_ne_zero.2 hn.ne', hp, hx₀,
            I₀.ζ_prim _ hn, I₀.add _, fun v => (I₀.onto _ hn _).2 ⟨v, rfl⟩, I₀.lin _, I₀.isom _ hn,
            by rw [← hζ₀, ← I₀.ζ_pow k m hk hm, Units.val_pow_eq_pow_val],
            fun i => (I₀.tower k m hk hm _).trans ((hev₀ i).symm.trans (by rw [hu]))⟩) hd)
        K x β (Nat.cast_ne_zero.2 hn.ne') hx
      obtain ⟨h₈, h₉⟩ := GlobalTheory.TorsIsometry.ker_and_onto E H D K (Over.mk x ⟶ P.A)
        (fun w w' c => Out.WeilIs P.A P.L (k * m : ℕ) w w' (unitOn c)) (k * m) ζ ev hn (hcard _ hn)
        (fun _ _ _ h => PELFamily.eq_one_of_weilIs_one P hL.weil h) h₁ h₂ h₃ h₅
      exact ⟨ζ, ev, h₁, h₂, h₄, h₈, h₉, h₅, h₆, h₇⟩)
  exact ⟨I, hI, fun a => Eq.trans (by rw [hu]) (hA a).symm⟩

end GlobalTheory.LowDat
