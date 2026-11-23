import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProdUpdateDiv

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Sm

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

theorem chartSub_div_mem {F : Type} [Field F] {κ : Type} (x : κ → F) (c j : κ) :
    x j / x c ∈ chartSub x c :=
  Algebra.subset_adjoin ⟨j, rfl⟩

theorem chartSub_le_of_forall {F : Type} [Field F] {κ : Type} {x : κ → F} {c : κ} {T : Subring F}
    (h : ∀ j, x j / x c ∈ T) : chartSub x c ≤ T := by
  intro a ha
  have ha' : a ∈ Algebra.adjoin ℤ (Set.range fun j => x j / x c) := ha
  induction ha' using Algebra.adjoin_induction with
  | mem b hb =>
    obtain ⟨j, rfl⟩ := hb
    exact h j
  | algebraMap n => simpa using intCast_mem T n
  | add b d _ _ hb hd => exact T.add_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))
  | mul b d _ _ hb hd => exact T.mul_mem (hb (Subalgebra.mem_toSubring.2 ‹_›)) (hd (Subalgebra.mem_toSubring.2 ‹_›))

theorem locSub_le_of {F : Type} [Field F] {R T : Subring F} {a : F} (h : R ≤ T) (ha : a⁻¹ ∈ T) :
    locSub R a ≤ T :=
  Subring.closure_le.2 (Set.union_subset h (Set.singleton_subset_iff.2 ha))

theorem flagCoord_div_eq {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {κ : Type}
    (x : κ → Ω) {S : Type} [Fintype S] {r n m : S → ℕ}
    {φ : ∀ s, Fin (n s) → Module.Dual Ω E} {cc : ∀ s, Fin (r s) → E}
    {M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω} {T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω}
    {c₀ : κ} (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (hx : x c₀ ≠ 0)
    (h : ∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) (k : κ)
    (J' : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) :
    flagCoord κ x φ cc ((k, J') : FlagIx κ n r) / flagCoord κ x φ cc ((c₀, J) : FlagIx κ n r) =
      algebraMap Ω (GenField Ω r) (x k / x c₀) *
        ∏ q : (Σ s, Fin (r s)), stepMinor (flagB M T q.1) q.2 (J' q) / stepMinor (flagB M T q.1) q.2 (J q) := by
  have hi : algebraMap Ω (GenField Ω r) (x c₀) ≠ 0 := (map_ne_zero _).2 hx
  rw [flagCoord_eq x h k J', flagCoord_eq x h c₀ J, map_div₀, mul_div_mul_comm,
    ← Finset.prod_div_distrib]
  congr 1
  refine Finset.prod_congr rfl fun q _ => ?_
  exact mul_div_mul_left _ _ (pow_ne_zero _ (pow_ne_zero _ hi))

theorem chartRing_eq_ratioRing : ∀ (Ω : Type) [Field Ω] (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type)
    (x : κ → Ω) (S : Type) [Fintype S] (r n m : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (cc : ∀ s, Fin (r s) → E) (M : ∀ s, Matrix (Fin (n s)) (Fin (r s)) Ω)
    (T : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (c₀ : κ)
    (J : (q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1)) (g : Ω), x c₀ ≠ 0 →
    g ∈ chartSub x c₀ → g ≠ 0 → (∀ s j l, φ s j (cc s l) = x c₀ ^ m s * (M s * T s) j l) →
    (∀ q, stepMinor (flagB M T q.1) q.2 (J q) ≠ 0) →
    algebraMap Ω (GenField Ω r) g ∈ chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ∧
    locSub (chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)) (algebraMap Ω (GenField Ω r) g) =
      ratioRing (locSub (chartSub x c₀) g) (flagB M T) J := by
  intro Ω _ E _ _ κ x S _ r n m φ cc M T c₀ J g hx hg hg0 h hJ
  classical
  set A := chartSub (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) with hA
  have hdiv := fun k J' => flagCoord_div_eq (m := m) x J hx h k J'

  have h1 : ∀ k, algebraMap Ω (GenField Ω r) (x k / x c₀) ∈ A := by
    intro k
    have e := hdiv k J
    have e1 : ∏ q : (Σ s, Fin (r s)),
        stepMinor (flagB M T q.1) q.2 (J q) / stepMinor (flagB M T q.1) q.2 (J q) = 1 :=
      Finset.prod_eq_one fun q _ => div_self (hJ q)
    rw [e1, _root_.mul_one] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r) ((k, J) : FlagIx κ n r)

  have h2 : ∀ (q : Σ s, Fin (r s)) (J' : Fin ((q.2 : ℕ) + 1) → Fin (n q.1)),
      stepMinor (flagB M T q.1) q.2 J' / stepMinor (flagB M T q.1) q.2 (J q) ∈ A := by
    intro q J'
    have e := hdiv c₀ (Function.update J q J')
    rw [div_self hx, map_one, _root_.one_mul, Finset.prod_div_distrib,
      prod_update_div (β := fun q : (Σ s, Fin (r s)) => Fin ((q.2 : ℕ) + 1) → Fin (n q.1))
        (fun q b => stepMinor (flagB M T q.1) q.2 b) J hJ q J'] at e
    rw [← e]
    exact chartSub_div_mem (flagCoord κ x φ cc) ((c₀, J) : FlagIx κ n r)
      ((c₀, Function.update J q J') : FlagIx κ n r)
  have himg : chartSub x c₀ ≤ A.comap (algebraMap Ω (GenField Ω r)) :=
    chartSub_le_of_forall fun j => h1 j
  have hgA : algebraMap Ω (GenField Ω r) g ∈ A := himg hg
  refine ⟨hgA, le_antisymm ?_ ?_⟩
  ·
    set R' := locSub (chartSub x c₀) g with hR'
    have him : ∀ b ∈ R', algebraMap Ω (GenField Ω r) b ∈ ratioRing R' (flagB M T) J := fun b hb =>
      Subring.subset_closure (Or.inl ⟨b, hb, rfl⟩)
    refine locSub_le_of (chartSub_le_of_forall ?_) ?_
    · rintro ⟨k, J'⟩
      rw [hdiv k J']
      refine Subring.mul_mem _ (him _ (le_locSub _ _ (chartSub_div_mem x c₀ k))) ?_
      exact Subring.prod_mem _ fun q _ => Subring.subset_closure (Or.inr ⟨q, J' q, rfl⟩)
    · rw [← map_inv₀]
      exact him _ (inv_mem_locSub _ _)
  · refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨b, hb, rfl⟩
      have hle : locSub (chartSub x c₀) g ≤
          (locSub A (algebraMap Ω (GenField Ω r) g)).comap (algebraMap Ω (GenField Ω r)) := by
        refine locSub_le_of (himg.trans fun a ha => le_locSub _ _ ha) ?_
        show algebraMap Ω (GenField Ω r) g⁻¹ ∈ locSub A (algebraMap Ω (GenField Ω r) g)
        rw [map_inv₀]
        exact inv_mem_locSub _ _
      exact hle hb
    · rintro _ ⟨q, J', rfl⟩
      exact le_locSub _ _ (h2 q J')

end GlobalTheory.CompanionTheory.Ar.FlagBun.Sm
