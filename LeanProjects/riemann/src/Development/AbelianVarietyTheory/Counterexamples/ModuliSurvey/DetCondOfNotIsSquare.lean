import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DetCondCheck

theorem epsScale_fst_snd {k : Type} [Field k] (c : k) (x : DualNumber k) :
    (epsScale c x).fst = x.fst ∧ (epsScale c x).snd = c * x.snd := by
  constructor <;> simp [epsScale]

theorem lieMult_unique {k O : Type} [Field k] [CommRing O] {G : Over (Sp k)} [GrpObj G]
    [IsCommMonObj G] (a : OAct O G) (τ : O →+* k) {n m : ℕ}
    (hn : LieMult a (𝟙 _) τ n) (hm : LieMult a (𝟙 _) τ m) : n = m := by
  obtain ⟨b⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff a τ n).mp hn
  obtain ⟨b'⟩ := (GlobalTheory.Serre.Lie.lieMult_id_iff a τ m).mp hm
  simpa using (Module.finrank_eq_card_basis b).symm.trans (Module.finrank_eq_card_basis b')

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem map_rt_eq_neg (H : Host E) {k : Type} [Field k] {ρ : k} (hρ : ρ ^ 2 = -(H.d : k))
    (τ : 𝓞 E →+* k) (h : τ H.rt ≠ ρ) : τ H.rt = -ρ := by
  have h1 : (τ H.rt) ^ 2 = ρ ^ 2 := by rw [← map_pow, H.rt_sq, hρ]; simp
  exact (sq_eq_sq_iff_eq_or_eq_neg.mp h1).resolve_left h

theorem ne_neg (H : Host E) {k : Type} [Field k] [CharZero k] {ρ : k}
    (hρ : ρ ^ 2 = -(H.d : k)) : ρ ≠ -ρ := by
  intro h
  have h0 : ρ = 0 := by linear_combination h / 2
  have : (H.d : k) = 0 := by rw [h0] at hρ; simpa using hρ
  exact H.d_prime.ne_zero (by exact_mod_cast this)

theorem detCond_of_not_isSquare {H : Host E} (D : Datum H) {S : Scheme.{0}} {G : Over S} [GrpObj G]
    (a : OAct (𝓞 E) G) {k : Type} [Field k] (hk : ¬ IsSquare (-(H.d : k))) (t : Sp k ⟶ S) (ρ : k) :
    DetCond D a t ρ := fun τ =>
  (hk ⟨τ H.rt, by rw [← sq, ← map_pow, H.rt_sq]; simp⟩).elim

theorem nonempty_ringHom (k : Type) [Field k] [CharZero k] [IsAlgClosed k] :
    Nonempty (𝓞 E →+* k) :=
  ⟨((IsAlgClosed.lift : E →ₐ[ℚ] k) : E →+* k).comp (algebraMap (𝓞 E) E)⟩

end GlobalTheory.DetCondCheck
