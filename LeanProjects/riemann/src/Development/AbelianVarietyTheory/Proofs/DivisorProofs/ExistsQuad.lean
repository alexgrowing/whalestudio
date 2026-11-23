import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.PsiFrame

theorem char_ext {X G : Type} [AddCommGroup X] [CommGroup G] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (f g : X → G)
    (hf : ∀ a b, f (a + b) = f a * f b) (hg : ∀ a b, g (a + b) = g a * g b) (h : ∀ l, f (bX l) = g (bX l)) (χ : X) :
    f χ = g χ := by
  let F : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (f x)) (fun a b => by simp [hf])
  let G' : X →+ Additive G := AddMonoidHom.mk' (fun x => Additive.ofMul (g x)) (fun a b => by simp [hg])
  have : F.toIntLinearMap = G'.toIntLinearMap := bX.ext fun l => by simp [F, G', h]
  have := LinearMap.congr_fun this χ
  simpa [F, G'] using this

def eu (z : ℂ) : ℂˣ := Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)

theorem eu_add (z w : ℂ) : eu (z + w) = eu z * eu w := by
  ext; simp [eu, Complex.exp_add]

theorem co_add {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a b : X) :
    co bX (a + b) = co bX a + co bX b := by
  ext l; simp [co]

theorem co_neg {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (a : X) :
    co bX (-a) = - co bX a := by
  ext l; simp [co]

theorem co_basis {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (l : Fin r) :
    co bX (bX l) = Pi.single l 1 := by
  ext l'
  by_cases h : l' = l
  · subst h; simp [co]
  · simp [co, h, Finsupp.single_apply, Ne.symm h]

theorem exists_quad {X : Type} [AddCommGroup X] {r : ℕ} (bX : Module.Basis (Fin r) ℤ X) (Ψ : X → ℂˣ)
    (hev : ∀ a, Ψ (-a) = Ψ a)
    (hb : ∀ a a' b, Ψ (a + a' + b) / Ψ (a + a') / Ψ b = (Ψ (a + b) / Ψ a / Ψ b) * (Ψ (a' + b) / Ψ a' / Ψ b)) :
    ∃ (t : Matrix (Fin r) (Fin r) ℂ) (b2 : Fin r → ℂ), t.IsSymm ∧ Half b2 ∧ ∀ χ, (Ψ χ : ℂ) =
      Complex.exp (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
  classical
  set T : X → X → ℂˣ := fun a b => Ψ (a + b) / Ψ a / Ψ b with hT
  have Ts : ∀ a b, T a b = T b a := fun a b => by simp only [hT, add_comm a b, div_right_comm]
  have Tl : ∀ a a' b, T (a + a') b = T a b * T a' b := hb
  have Tr : ∀ a b b', T a (b + b') = T a b * T a b' := fun a b b' => by rw [Ts, Tl, Ts b, Ts b']
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  let t : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun l l' => Complex.log (T (bX l) (bX l')) / (2 * Real.pi * Complex.I)
  have ts : t.IsSymm := by
    ext l l'; simp [t, Ts (bX l)]
  have hs : ∀ u v : Fin r → ℂ, u ⬝ᵥ t *ᵥ v = v ⬝ᵥ t *ᵥ u := fun u v => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ts.eq, dotProduct_comm]
  have TQ : ∀ a b, T a b = eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)) := by
    intro a b
    refine char_ext bX (fun a => T a b) (fun a => eu (2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tl _ _ _) (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) a
    refine char_ext bX (fun b => T (bX l) b) (fun b => eu (2 * Real.pi * Complex.I * (co bX (bX l) ⬝ᵥ t *ᵥ co bX b)))
      (fun _ _ => Tr _ _ _) (fun _ _ => by rw [co_add, Matrix.mulVec_add, dotProduct_add, mul_add, eu_add])
      (fun l' => ?_) b
    ext
    have : Pi.single l 1 ⬝ᵥ t *ᵥ Pi.single l' 1 = t l l' := by simp
    simp only [co_basis, this, eu, Units.val_mk0, t, Matrix.of_apply]
    rw [mul_div_cancel₀ _ hc, Complex.exp_log (Units.ne_zero _)]
  let φ : X → ℂˣ := fun χ => Ψ χ / eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ))
  have φadd : ∀ a b, φ (a + b) = φ a * φ b := by
    intro a b
    have h1 : Ψ (a + b) = T a b * Ψ a * Ψ b := by
      simp only [hT]; rw [mul_right_comm, div_mul_cancel, div_mul_cancel]
    have h2 : (Real.pi * Complex.I * (co bX (a + b) ⬝ᵥ t *ᵥ co bX (a + b)) : ℂ) =
        2 * Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX b) + Real.pi * Complex.I * (co bX a ⬝ᵥ t *ᵥ co bX a) +
          Real.pi * Complex.I * (co bX b ⬝ᵥ t *ᵥ co bX b) := by
      rw [co_add, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hs (co bX b) (co bX a)]
      ring
    simp only [φ]
    rw [h1, h2, eu_add, eu_add, ← TQ, _root_.mul_assoc, _root_.mul_assoc, mul_div_mul_left_eq_div, div_mul_div_comm]
  have φev : ∀ a, φ (-a) = φ a := fun a => by
    simp only [φ, hev, co_neg, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  have φ0 : φ 0 = 1 := by
    have := φadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have φsq : ∀ a, (φ a : ℂ) = 1 ∨ (φ a : ℂ) = -1 := fun a => by
    have := φadd a (-a)
    rw [add_neg_cancel, φ0, φev] at this
    have h2 : (φ a : ℂ) * φ a = 1 := by rw [← Units.val_mul, ← this, Units.val_one]
    exact mul_self_eq_one_iff.1 h2
  let b2 : Fin r → ℂ := fun l => if (φ (bX l) : ℂ) = 1 then 0 else 1 / 2
  refine ⟨t, b2, ts, fun l => ?_, fun χ => ?_⟩
  · simp only [b2]; split_ifs <;> simp
  · have : φ χ = eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      refine char_ext bX φ (fun χ => eu (2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2))) φadd
        (fun _ _ => by rw [co_add, add_dotProduct, mul_add, eu_add]) (fun l => ?_) χ
      ext
      simp only [co_basis, single_dotProduct, _root_.one_mul, eu, Units.val_mk0, b2]
      split_ifs with h
      · simp [h]
      · rw [(φsq _).resolve_left h, show (2 * Real.pi * Complex.I * (1 / 2) : ℂ) = Real.pi * Complex.I by ring,
          Complex.exp_pi_mul_I]
    have h2 : Ψ χ = eu (Real.pi * Complex.I * (co bX χ ⬝ᵥ t *ᵥ co bX χ) + 2 * Real.pi * Complex.I * (co bX χ ⬝ᵥ b2)) := by
      rw [eu_add, ← this]; simp only [φ]; rw [mul_div_cancel]
    rw [h2]; rfl

theorem exists_cd (N : NumD ℂ) (g' r : ℕ) (bX : Module.Basis (Fin r) ℤ N.X) (e : AB N.toNumB g') (hc : e.Cub) (hs : e.Sym) :
    ∃ d : CD N g' r bX, d.toAB = e := by
  classical
  choose z hz using fun l => e.onto (N.c (bX l))
  let t12 : Matrix (Fin g') (Fin r) ℂ := Matrix.of fun i l => z l i
  let w : N.X → Fin g' → ℂ := fun χ => t12 *ᵥ co bX χ
  have wadd : ∀ a b, w (a + b) = w a + w b := fun a b => by simp only [w, co_add, Matrix.mulVec_add]
  have wneg : ∀ a, w (-a) = - w a := fun a => by simp only [w, co_neg, Matrix.mulVec_neg]
  have ceq : ∀ χ, N.c χ = e.ex (w χ) := by
    refine char_ext bX N.c (fun χ => e.ex (w χ)) N.c_add (fun a b => by rw [wadd, e.ex_add]) (fun l => ?_)
    rw [← hz]; congr 1
    ext i; simp [w, co_basis, t12]
  obtain ⟨t, b2, ht, hb2, h⟩ := exists_quad bX (fun χ => N.ψ χ * e.fr (w χ))
    (fun a => by
      have h1 := N.even a
      have h2 := hs (w a)
      rw [wneg, ← h2, ← h1, ceq, _root_.mul_assoc])
    (fun a a' b => by
      have h1 := congrArg Additive.ofMul (N.bimult a a' b)
      have h2 := congrArg Additive.ofMul (hc (w a) (w a') (w b))
      apply Additive.ofMul.injective
      simp only [ceq, wadd, ofMul_mul, ofMul_div] at h1 h2 ⊢
      linear_combination (norm := abel) h1 - h2)
  exact ⟨{ toAB := e, cub := hc, sym := hs, t12 := t12, t22 := t, b2 := b2, toricPeriodBlock_isSymm := ht, hb2 := hb2, c_eq := ceq,
           ψ_eq := fun χ => by simpa using h χ }, rfl⟩

end GlobalTheory.MBLow.Cl.PsiFrame

end
