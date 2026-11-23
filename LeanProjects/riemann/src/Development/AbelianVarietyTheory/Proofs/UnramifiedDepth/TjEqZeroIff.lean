import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TopLeAlgOverHom
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.TopLimitModules.LimJMemSmulTop

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AddCurve
open ReciprocityTheory.ChartRestriction.G.Pdiv.TL

namespace GlobalTheory.JetExpansion

variable {k : Type} [CommRing k] {κ : Type} [Finite κ]

def tj (m : ℕ) : MvPowerSeries κ k →ₐ[k] JetR k κ m :=
  (MvPowerSeries.truncTotalAlgHom κ k (m + 1)).restrictScalars k

theorem tj_eq_iff (m : ℕ) (f g : MvPowerSeries κ k) :
    tj m f = tj m g ↔ ∀ x : κ →₀ ℕ, x.degree < m + 1 → MvPowerSeries.coeff x f = MvPowerSeries.coeff x g :=
  limJ_tt_eq_iff m f g

theorem tj_ext {f g : MvPowerSeries κ k} (h : ∀ m, tj m f = tj m g) : f = g := by
  ext x
  exact (tj_eq_iff x.degree f g).1 (h _) x (Nat.lt_succ_self _)

theorem tj_eq_zero_iff (m : ℕ) (f : MvPowerSeries κ k) :
    tj m f = 0 ↔ f ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ k)) ^ (m + 1) := by
  rw [← GlobalTheory.germIdeal_eq_span, GlobalTheory.mem_germIdeal_pow_iff, ← map_zero (tj (k := k) (κ := κ) m), tj_eq_iff]
  simp only [map_zero]

theorem exists_tj (p : ∀ m, JetR k κ m) (hp : ∀ m, jetTruncR k κ m (p (m + 1)) = p m) :
    ∃ f : MvPowerSeries κ k, ∀ m, tj m f = p m := by
  choose P hP using fun m => Ideal.Quotient.mk_surjective (p m)
  have hck : ∀ (u : κ →₀ ℕ) m, u.degree ≤ m → (P m).coeff u = (P u.degree).coeff u := by
    intro u m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      rw [← ih]
      have h1 : (Ideal.Quotient.mk _ (P m) : JetR k κ m) = Ideal.Quotient.mk _ (P (m + 1)) := by
        rw [hP, ← hp m, ← hP]
        rfl
      exact ((limJ_mk_eq_iff m _ _).1 h1 u (by omega)).symm
  refine ⟨fun u => (P u.degree).coeff u, fun m => ?_⟩
  rw [← hP m]
  refine (limJ_mk_eq_iff m (MvPowerSeries.truncTotal (m + 1) _) _).2 fun u hu => ?_
  exact (MvPowerSeries.coeff_truncTotal _ hu).trans (hck u m (by omega)).symm

theorem exists_expansion : ∀ (k : Type) [CommRing k] (g : ℕ), 0 < g → ∀ (A : Type) [CommRing A] [Algebra k A] (I : Ideal A) (τ : ∀ m : ℕ, A →ₐ[k] JetR k (Fin 1 × Fin g) m), (∀ m a, jetTruncR k _ m (τ (m + 1) a) = τ m a) → (∀ m, Function.Surjective (τ m)) → (∀ m a, τ m a = 0 ↔ a ∈ I ^ (m + 1)) → ∃ j : A →ₐ[k] PS k 1 g, (∀ (m : ℕ) (a : A), j a ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin g → PS k 1 g)) ^ m ↔ a ∈ I ^ m) ∧ (∀ (m : ℕ) (s : PS k 1 g), ∃ a : A, j a - s ∈ Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin g → PS k 1 g)) ^ m) ∧ ∀ (a : A) (s : PS k 1 g), (∀ m, τ m a = psJet m s) → j a = s := by
  intro k _ g hg A _ _ I τ hc hs hk
  choose F hF using fun a : A => exists_tj (fun m => τ m a) (fun m => hc m a)
  let j : A →ₐ[k] PS k 1 g :=
    { toFun := F
      map_one' := tj_ext fun m => by rw [hF, map_one, map_one]
      map_mul' := fun a b => tj_ext fun m => by rw [map_mul, hF, hF, hF, map_mul]
      map_zero' := tj_ext fun m => by rw [hF, map_zero, map_zero]
      map_add' := fun a b => tj_ext fun m => by rw [map_add, hF, hF, hF, map_add]
      commutes' := fun r => tj_ext fun m => by rw [hF, AlgHom.commutes, AlgHom.commutes] }
  have hj : ∀ m a, tj m (j a) = τ m a := fun m a => hF a m
  refine ⟨j, fun m a => ?_, fun m s => ?_, fun a s h => ?_⟩
  · rcases m with _ | m
    · simp
    · rw [← tj_eq_zero_iff, hj, hk]
  · obtain ⟨a, ha⟩ := hs m (tj m s)
    refine ⟨a, Ideal.pow_le_pow_right (Nat.le_succ m) ?_⟩
    rw [← tj_eq_zero_iff, map_sub, hj, ha, sub_self]
  · refine tj_ext fun m => ?_
    rw [hj, h, limJ_psJet_eq Nat.one_pos hg]
    rfl

end GlobalTheory.JetExpansion
