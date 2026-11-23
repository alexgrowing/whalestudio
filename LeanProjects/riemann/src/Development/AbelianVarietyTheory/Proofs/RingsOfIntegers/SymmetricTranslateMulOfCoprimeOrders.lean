import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniqueSymmetricTranslateOddLevel
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EqOfSqEqOfOdd
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UniversalWeilPairingPullbackExistsUnique
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem weilIs_eq_one_of_coprime (hW : WeilSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) (k : ℕ)
    {T : Over S} (hk : IsUnit (k : Γ(T.left, ⊤))) (a b : T ⟶ P.A) (m m' : ℕ) (ha : a ^ k = 1) (hb : b ^ k = 1)
    (hc : Nat.Coprime m m') (ham : a ^ m = 1) (hbm : b ^ m' = 1) (e : Γ(T.left, ⊤)ˣ)
    (he : WeilIs P.A P.L k a b e) : e = 1 := by
  have h₁ : e ^ m = 1 := by
    obtain ⟨hex, hmul, -, -⟩ := hW S P k T
    obtain ⟨c₁, hc₁, hu⟩ := hex 1 b (one_pow k) hb
    have h₂ := hmul 1 1 b c₁ c₁ hc₁ hc₁
    rw [_root_.mul_one] at h₂
    obtain rfl : c₁ = 1 := mul_eq_left.1 (hu _ h₂)
    have hpow : ∀ j : ℕ, WeilIs P.A P.L k (a ^ j) b (e ^ j) := fun j => by
      induction j with
      | zero => rw [pow_zero, pow_zero]; exact hc₁
      | succ j ih => rw [pow_succ, pow_succ]; exact hmul _ _ _ _ _ ih he
    have h := hpow m
    rw [ham] at h
    exact hu _ h
  have h₂ : e ^ m' = 1 := by
    have hbg : b ^ Nat.gcd k m' = 1 := pow_gcd_eq_one.2 ⟨hb, hbm⟩
    obtain ⟨n, hn⟩ := Nat.gcd_dvd_left k m'
    obtain ⟨n', hn'⟩ := Nat.gcd_dvd_right k m'
    generalize Nat.gcd k m' = g at hbg hn hn'
    subst hn
    have h := ((hW S P g T).2.2.2 n a b e hk ha hbg).1 (by exact_mod_cast he)
    have hg := GlobalTheory.UnivPairing.weilIs_pow_eq_one hW P g (a ^ n) b (by rw [← pow_mul, mul_comm]; exact ha) hbg e h
    rw [hn', pow_mul, hg, one_pow]
  have h := pow_gcd_eq_one.2 ⟨h₁, h₂⟩
  rwa [hc.gcd_eq_one, pow_one] at h

theorem moves_mul_of_coprime : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (k : ℕ), Odd k → ∀ (a b : (ptO Xo x ⟶ Xo.univ.t.G)) (m m' : ℕ), a ^ k = 1 → b ^ k = 1 → Nat.Coprime m m' → a ^ m = 1 → b ^ m' = 1 → ∀ F F₁ F₂ : SecN Xo x k, Moves Xo b F F₁ → (Moves Xo a F₁ F₂ ↔ Moves Xo (a * b) F F₂) := by
  intro E _ _ _ H Dw l Xo S _ x k hk a b m m' ha hb hc ham hbm F F₁ F₂ h₁
  have hW : WeilSt := GlobalTheory.firstFiveLaws.1.weil
  have := UnivPol.isLocallyNoetherian Xo
  have hu : IsUnit (k : Γ((ptO Xo x).left, ⊤)) := by
    have h := (UnivPol.isUnit_natCast Xo k hk.pos).map (ptO Xo x).hom.appTop.hom
    rwa [map_natCast] at h
  obtain ⟨e, he, -⟩ := (hW Xo.X (UnivPol.pol Xo) k (ptO Xo x)).1 a b ha hb
  have he1 : e = 1 := weilIs_eq_one_of_coprime hW (UnivPol.pol Xo) k hu a b m m' ha hb hc ham hbm e he
  obtain ⟨r, hr2, hrk, hr⟩ := GlobalTheory.PlaceInt.moves_mul E H Dw l Xo S x k hk a b e ha hb he
  have hr1 : toΓ S r = 1 := by
    rw [he1, Units.val_one] at hr2
    have h3 : toΓ S r ^ k = 1 := by rw [← map_pow, hrk, map_one]
    obtain ⟨n, rfl⟩ := hk
    rwa [pow_succ, pow_mul, hr2, one_pow, _root_.one_mul] at h3
  have key : ∀ G G' : SecN Xo x k, Moves Xo a F₁ G → Moves Xo (a * b) F G' → G = G' := by
    intro G G' hG hG'
    have h := hr F F₁ G G' h₁ hG hG'
    have h' : G.f = G'.f := funext fun j => by
      rw [h j, hr1]
      unfold liftFun
      rw [map_one, map_one, _root_.one_mul]
    cases G
    cases G'
    cases h'
    rfl
  have hab : (a * b) ^ k = 1 := by rw [mul_pow, ha, hb, _root_.mul_one]
  constructor
  · intro h
    obtain ⟨G, hG, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk (a * b) hab F).1
    rw [key F₂ G h hG]
    exact hG
  · intro h
    obtain ⟨G, hG, -⟩ := (GlobalTheory.existsUnique_moves E H Dw l Xo S x k hk a ha F₁).1
    rw [← key G F₂ hG h]
    exact hG

end GlobalTheory.PlaceInt
