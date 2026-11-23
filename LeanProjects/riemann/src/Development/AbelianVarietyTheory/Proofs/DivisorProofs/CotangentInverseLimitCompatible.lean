import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompatLift

theorem exists_of_compat {O : Type} [CommRing O] (p : O) [IsPrecomplete (Ideal.span {p}) O]
    {W : Type} [AddCommGroup W] [Module O W] [Module.Finite O W]
    {C : ℕ → Type} [∀ n, AddCommGroup (C n)] [∀ n, Module O (C n)]
    (c : ∀ n, W →+ C n) (hsurj : ∀ n, Function.Surjective (c n))
    (hker : ∀ (n : ℕ) (w : W), c n w = 0 → w ∈ (Ideal.span {p ^ n} • ⊤ : Submodule O W))
    (hsmul : ∀ (n : ℕ) (a : O) (w : W), c n (a • w) = a • c n w)
    (hkill : ∀ (n : ℕ) (x : C n), p ^ n • x = 0)
    (u : ∀ n, C n) (hcomp : ∀ (n : ℕ) (w : W), c (n + 1) w = u (n + 1) → c n w = u n) :
    ∃ w : W, ∀ n, c n w = u n := by
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' O W
  have step : ∀ (n : ℕ) (a : Fin k → O), c n (f a) = u n → ∃ a' : Fin k → O,
      c (n + 1) (f a') = u (n + 1) ∧ ∃ b : Fin k → O, a' = a + p ^ n • b := by
    intro n a ha
    obtain ⟨w', hw'⟩ := hsurj (n + 1) (u (n + 1))
    have h1 : c n (w' - f a) = 0 := by rw [map_sub, hcomp n w' hw', ha, sub_self]
    have h2 := hker n _ h1
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h2
    obtain ⟨v, -, hv⟩ := h2
    obtain ⟨b, rfl⟩ := hf v
    refine ⟨a + p ^ n • b, ?_, b, rfl⟩
    rw [map_add, map_smul, hv, add_sub_cancel, hw']
  choose! g hg using step
  let a : ℕ → Fin k → O := fun n => Nat.rec 0 (fun m x => g m x) n
  have h0 : ∀ x : C 0, x = 0 := fun x => by simpa using hkill 0 x
  have ha : ∀ n, c n (f (a n)) = u n := by
    intro n
    induction n with
    | zero => rw [h0 (c 0 _), h0 (u 0)]
    | succ n ih => exact (hg n _ ih).1
  have hd : ∀ n, ∃ b : Fin k → O, a (n + 1) = a n + p ^ n • b := fun n => (hg n _ (ha n)).2
  have hcong : ∀ m n, m ≤ n → ∀ i, ∃ e : O, a n i = a m i + p ^ m * e := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact fun i => ⟨0, by simp⟩
    | succ n hmn ih =>
      intro i
      obtain ⟨e, he⟩ := ih i
      obtain ⟨b, hb⟩ := hd n
      refine ⟨e + p ^ (n - m) * b i, ?_⟩
      rw [hb, Pi.add_apply, Pi.smul_apply, smul_eq_mul, he, ← pow_mul_pow_sub p hmn]
      ring
  have hmem : ∀ (m : ℕ) (x y : O),
      x ≡ y [SMOD (Ideal.span {p} ^ m • ⊤ : Submodule O O)] ↔ ∃ e : O, y = x + p ^ m * e := by
    intro m x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩
      exact ⟨-e, by rw [mul_neg, mul_comm, he]; ring⟩
    · rintro ⟨e, rfl⟩
      exact ⟨-e, by ring⟩
  choose L hL using fun i => IsPrecomplete.prec' (I := Ideal.span {p}) (fun n => a n i)
    fun {m n} hmn => (hmem m _ _).2 (hcong m n hmn i)
  refine ⟨f L, fun n => ?_⟩
  choose e he using fun i => (hmem n _ _).1 (hL i n)
  have hLe : L = a n + p ^ n • e := funext fun i => by
    rw [he i, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hLe, map_add, map_smul, map_add, hsmul, hkill, add_zero, ha]

end GlobalTheory.CompatLift

namespace GlobalTheory.SqZeroPt

theorem cn_hits_compatible : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → (∀ n, Function.Surjective (cn t n)) → (∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A))) → (∀ (n : ℕ) (w : Wmod A), GlobalTheory.PDiv.cotMap (G.res n) (cn t (n + 1) w) = cn t n w) → (∀ (n : ℕ) (c : O) (w : Wmod A), cn t n (c • w) = c • cn t n w) → ∀ u : G.omega, ∃ w, ∀ n, cn t n w = u.1 n := by
  intro p O _ _ G A _ t hfin hsurj hker hres hsmul u
  exact GlobalTheory.CompatLift.exists_of_compat (p : O) (C := fun n => GlobalTheory.PDiv.Cot O (G.A n)) (cn t)
    hsurj hker hsmul (fun n x => G.pow_smul_cot n x) (fun n => u.1 n)
    fun n w hw => by rw [← hres n w, hw]; exact u.2 n

end GlobalTheory.SqZeroPt
