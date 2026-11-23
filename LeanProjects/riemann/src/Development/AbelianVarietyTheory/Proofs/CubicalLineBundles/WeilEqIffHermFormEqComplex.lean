import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.HermWeil

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem ex_natSmul (n : ℕ) (z : Fin g → ℂ) : u.ex ((n : ℂ) • z) = u.ex z ^ n := by
  induction n with
  | zero => simp [ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, u.ex_add, ih, pow_succ]

theorem ex_div_pow {n : ℕ} (hn : 0 < n) (a : u.Λ) : u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) ^ n = 1 := by
  rw [← ex_natSmul, smul_inv_smul₀ (Nat.cast_ne_zero.2 hn.ne')]
  exact (u.ker _).2 a.2

theorem exists_eq_ex_div {n : ℕ} (hn : 0 < n) (x : 𝟙_ (Over (Sp ℂ)) ⟶ A) (hx : x ^ n = 1) :
    ∃ a : u.Λ, x = u.ex ((n : ℂ)⁻¹ • (a : Fin g → ℂ)) := by
  obtain ⟨z, rfl⟩ := u.ex_onto x
  refine ⟨⟨(n : ℂ) • z, (u.ker _).1 (by rw [ex_natSmul, hx])⟩, ?_⟩
  rw [inv_smul_smul₀ (Nat.cast_ne_zero.2 hn.ne')]

theorem map_mem {B : Over (Sp ℂ)} [GrpObj B] {M : LB B.left} {g' : ℕ} (v : HolUnif B M g') {f : A ⟶ B}
    {F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)} (hF : ∀ z, v.ex (F z) = u.ex z ≫ f) (a : u.Λ) : F a ∈ v.Λ := by
  rw [← v.ker, hF, (u.ker _).2 a.2, ← ex_zero u, ← hF, map_zero, ex_zero]

end Unif

def rootVal (m : ℤ) (n : ℕ) : ℂˣ :=
  Units.mk0 (Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / n)) (Complex.exp_ne_zero _)

theorem eq_of_rootVal {m m' : ℤ} (h : ∀ n : ℕ, 0 < n → rootVal m n = rootVal m' n) : m = m' := by
  have key : ∀ n : ℕ, 0 < n → (n : ℤ) ∣ m' - m := by
    intro n hn
    have e := congrArg Units.val (h n hn)
    simp only [rootVal, Units.val_mk0] at e
    obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 e
    have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    refine ⟨k, ?_⟩
    have : ((m' - m : ℤ) : ℂ) = ((n * k : ℤ) : ℂ) := by
      push_cast
      refine mul_left_cancel₀ Complex.two_pi_I_ne_zero ?_
      field_simp at hk
      linear_combination (2 * Real.pi * Complex.I) * hk
    exact_mod_cast this
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key ((m' - m).natAbs + 1) (Nat.succ_pos _))
    (by rw [Int.natAbs_natCast]; omega)
  omega

theorem hermForm_eq_of_im {p q a b : ℕ} (HA : Matrix (Fin a) (Fin a) ℂ) (HB : Matrix (Fin b) (Fin b) ℂ)
    (F₁ : (Fin p → ℂ) →ₗ[ℂ] (Fin a → ℂ)) (F₂ : (Fin q → ℂ) →ₗ[ℂ] (Fin a → ℂ))
    (G₁ : (Fin p → ℂ) →ₗ[ℂ] (Fin b → ℂ)) (G₂ : (Fin q → ℂ) →ₗ[ℂ] (Fin b → ℂ))
    {S : Set (Fin p → ℂ)} {T : Set (Fin q → ℂ)} (hS : Submodule.span ℝ S = ⊤) (hT : Submodule.span ℝ T = ⊤)
    (h : ∀ z ∈ S, ∀ w ∈ T, (hermForm HA (F₁ z) (F₂ w)).im = (hermForm HB (G₁ z) (G₂ w)).im) (z w) :
    hermForm HA (F₁ z) (F₂ w) = hermForm HB (G₁ z) (G₂ w) := by
  have him : ∀ z w, (hermForm HA (F₁ z) (F₂ w)).im = (hermForm HB (G₁ z) (G₂ w)).im := by
    intro z w
    have hz : z ∈ Submodule.span ℝ S := hS ▸ Submodule.mem_top
    have hw : w ∈ Submodule.span ℝ T := hT ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem z hz =>
      induction hw using Submodule.span_induction with
      | mem w hw => exact h z hz w hw
      | zero => simp [hermForm]
      | add x y _ _ hx hy =>
        simp only [hermForm, map_add, star_add, Matrix.mulVec_add, dotProduct_add, Complex.add_im] at hx hy ⊢
        rw [hx, hy]
      | smul r x _ hx =>
        rw [← Complex.coe_smul]
        simp only [hermForm, map_smul, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul,
          Complex.star_def, Complex.conj_ofReal, Complex.im_ofReal_mul] at hx ⊢
        rw [hx]
    | zero => simp [hermForm]
    | add x y _ _ hx hy =>
      simp only [hermForm, map_add, add_dotProduct, Complex.add_im] at hx hy ⊢
      rw [hx, hy]
    | smul r x _ hx =>
      rw [← Complex.coe_smul]
      simp only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, Complex.im_ofReal_mul] at hx ⊢
      rw [hx]
  refine Complex.ext ?_ (him z w)
  have e := him (Complex.I • z) w
  simpa only [hermForm, map_smul, smul_dotProduct, smul_eq_mul, Complex.I_mul_im] using e

theorem weilIs_iff (hU : ThetaUnifAV) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g)
    {Hm : Matrix (Fin P.g) (Fin P.g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (a b : u.Λ) :
    ∃ m : ℤ, (m : ℝ) = (hermForm Hm a b).im ∧ ∀ (n : ℕ) (c : ℂˣ), 0 < n →
      (Out.WeilIs P.A P.L n (u.ex ((n : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((n : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) ↔
        c = rootVal m n) := by
  obtain ⟨Ef, hE, -, -, -, -, hW⟩ := GlobalTheory.AHWeil.tangent_and_weil_of_isAH hU P P.g u Hm χ h
  refine ⟨Ef a b, hE a b, fun n c hn => ⟨fun hc => ?_, fun hc => hW n a b c hn (by rw [hc]; rfl)⟩⟩
  exact weilIs_unique_fieldPoint (Sp ℂ) P.A P.L P.isLB ℂ (𝟙 _) n _ _ c _ hc (hW n a b (rootVal (Ef a b) n) hn rfl)

end GlobalTheory.CM.HermWeil

namespace GlobalTheory.CM
open HermWeil

theorem weilEq_iff_hermForm_eq : ThetaUnifAV → Out.Laws → ∀ (X Y A B : Out.PolAV (Sp ℂ)) (uX : HolUnif X.A X.L X.g) (uY : HolUnif Y.A Y.L Y.g) (uA : HolUnif A.A A.L A.g) (uB : HolUnif B.A B.L B.g) (HA : Matrix (Fin A.g) (Fin A.g) ℂ) (HB : Matrix (Fin B.g) (Fin B.g) ℂ) (χA : uA.Λ → ℂ) (χB : uB.Λ → ℂ), uA.IsAH HA χA → uB.IsAH HB χB →
  ∀ (f₁ : X.A ⟶ A.A) (f₂ : Y.A ⟶ A.A) (g₁ : X.A ⟶ B.A) (g₂ : Y.A ⟶ B.A) (F₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (F₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin A.g → ℂ)) (G₁ : (Fin X.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)) (G₂ : (Fin Y.g → ℂ) →ₗ[ℂ] (Fin B.g → ℂ)),
  (∀ z, uA.ex (F₁ z) = uX.ex z ≫ f₁) → (∀ z, uA.ex (F₂ z) = uY.ex z ≫ f₂) → (∀ z, uB.ex (G₁ z) = uX.ex z ≫ g₁) → (∀ z, uB.ex (G₂ z) = uY.ex z ≫ g₂) →
  (WeilEq A.L f₁ f₂ B.L g₁ g₂ (𝟙 (Sp ℂ)) ↔ ∀ z w, hermForm HA (F₁ z) (F₂ w) = hermForm HB (G₁ z) (G₂ w)) := by
  intro hU _ X Y A B uX uY uA uB HA HB χA χB hA hB f₁ f₂ g₁ g₂ F₁ F₂ G₁ G₂ h₁ h₂ h₃ h₄
  have key : ∀ (a : uX.Λ) (b : uY.Λ), ∃ m m' : ℤ, (m : ℝ) = (hermForm HA (F₁ a) (F₂ b)).im ∧
      (m' : ℝ) = (hermForm HB (G₁ a) (G₂ b)).im ∧ ∀ (n : ℕ) (c : ℂˣ), 0 < n →
      (Out.WeilIs A.A A.L n (uX.ex ((n : ℂ)⁻¹ • (a : Fin X.g → ℂ)) ≫ f₁)
        (uY.ex ((n : ℂ)⁻¹ • (b : Fin Y.g → ℂ)) ≫ f₂) (unitOn c) ↔ c = rootVal m n) ∧
      (Out.WeilIs B.A B.L n (uX.ex ((n : ℂ)⁻¹ • (a : Fin X.g → ℂ)) ≫ g₁)
        (uY.ex ((n : ℂ)⁻¹ • (b : Fin Y.g → ℂ)) ≫ g₂) (unitOn c) ↔ c = rootVal m' n) := by
    intro a b
    obtain ⟨m, hm, hw⟩ := weilIs_iff hU A uA hA ⟨_, map_mem uX uA h₁ a⟩ ⟨_, map_mem uY uA h₂ b⟩
    obtain ⟨m', hm', hw'⟩ := weilIs_iff hU B uB hB ⟨_, map_mem uX uB h₃ a⟩ ⟨_, map_mem uY uB h₄ b⟩
    refine ⟨m, m', hm, hm', fun n c hn => ?_⟩
    rw [← h₁, ← h₂, ← h₃, ← h₄, map_smul, map_smul, map_smul, map_smul]
    exact ⟨hw n c hn, hw' n c hn⟩
  constructor
  · intro h
    refine hermForm_eq_of_im HA HB F₁ F₂ G₁ G₂ uX.full uY.full fun a ha b hb => ?_
    obtain ⟨m, m', hm, hm', hw⟩ := key ⟨a, ha⟩ ⟨b, hb⟩
    rw [← hm, ← hm', eq_of_rootVal (m := m) (m' := m') fun n hn => ?_]
    exact (hw n _ hn).2.1 ((h n _ _ _ hn (ex_div_pow uX hn ⟨a, ha⟩) (ex_div_pow uY hn ⟨b, hb⟩)).1
      ((hw n _ hn).1.2 rfl))
  · intro h n x y c hn hx hy
    obtain ⟨a, rfl⟩ := exists_eq_ex_div uX hn x hx
    obtain ⟨b, rfl⟩ := exists_eq_ex_div uY hn y hy
    obtain ⟨m, m', hm, hm', hw⟩ := key a b
    obtain rfl : m = m' := by
      have : (m : ℝ) = m' := by rw [hm, hm', h]
      exact_mod_cast this
    exact (hw n c hn).1.trans (hw n c hn).2.symm

end GlobalTheory.CM
end
