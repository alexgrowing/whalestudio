import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CubNSucc
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLawsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinear
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisingFactor

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.Nest
variable {O : Type} [CommRing O] (N : NumD O)

theorem wQ_nest {n k l : ℕ} (hk : Odd k) (hl : Odd l) (e : l = n * (k * n)) (p'' : N.QT l) (p : N.QT k)
    (hy : p''.1.1 = p.1.1 ^ n) (hg : p.1.2 = p''.1.2 ^ n) :
    N.wQ p * mulq N.θ N.σ n p''.1.2.b ^ k = N.wQ p'' := by
  subst e
  have hb : p.1.2.b = p''.1.2.b ^ n := by rw [hg, NumD.Gt.pow_b]
  have hc : N.c p.1.1.toAdd = p''.1.2.b ^ (k * n) := by
    rw [← N.QT_pow_b p, hb, ← pow_mul']
  have hy' : p''.1.1.toAdd = n • p.1.1.toAdd := by rw [hy, toAdd_pow]
  obtain ⟨hA, hB⟩ := (SymLift.wQ_iff N hk p (N.wQ p)).mp rfl
  refine (SymLift.wQ_iff N hl p'' _).mpr ⟨?_, ?_⟩
  · simp only [NumD.tk, hg, NumD.Gt.pow_b] at hA
    have ps := NumD.Gt.pow_s p''.1.2 n p.1.1.toAdd
    have ss := PsiQuadratic.s_nsmul N p''.1.2 n p.1.1.toAdd
    have db := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB n 0 p''.1.2.b p''.1.2.b).2.2.1
    have cm1 := CubeBalance.cubN_mul N.cub n (k * n) p''.1.2.b p''.1.2.b
    have cm2 := CubeBalance.cubN_mul N.cub k n p''.1.2.b p''.1.2.b
    have sw := CubeBalance.cubN_swap N.cub k n (p''.1.2.b ^ n) p''.1.2.b
    rw [hc] at ps ss
    rw [← pow_mul'] at sw
    simp only [NumD.tk]
    rw [hy']
    apply Additive.ofMul.injective
    replace hA := congrArg Additive.ofMul hA
    replace ps := congrArg Additive.ofMul ps
    replace ss := congrArg Additive.ofMul ss
    replace db := congrArg Additive.ofMul db
    replace cm1 := congrArg Additive.ofMul cm1
    replace cm2 := congrArg Additive.ofMul cm2
    replace sw := congrArg Additive.ofMul sw
    simp only [ofMul_mul, ofMul_pow] at hA ps ss db cm1 cm2 sw ⊢
    linear_combination (norm := module) hA - (k : ℤ) • db + sw + ps - ss - cm1 - (n : ℤ) • cm2
  · rw [hb] at hB
    have hψ := PsiQuadratic.ψ_nsmul N n p.1.1.toAdd
    have hm1 := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB n (k * n) p''.1.2.b p''.1.2.b).1
    have hm2 := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB k n p''.1.2.b p''.1.2.b).1
    rw [hc] at hψ
    rw [hy']
    apply Additive.ofMul.injective
    replace hB := congrArg Additive.ofMul hB
    replace hψ := congrArg Additive.ofMul hψ
    replace hm1 := congrArg Additive.ofMul hm1
    replace hm2 := congrArg Additive.ofMul hm2
    simp only [ofMul_mul, ofMul_pow] at hB hψ hm1 hm2 ⊢
    linear_combination (norm := module)
      ((n : ℤ) ^ 2) • hB - hψ - hm1 - ((n : ℤ) ^ 2) • hm2

theorem txT_nest : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (n m : ℕ), Odd n → Odd m → ∀ (p'' : N.QT ((n * m) ^ 2)) (p : N.QT (m ^ 2)), p''.1.1 = p.1.1 ^ n → p.1.2 = p''.1.2 ^ n → ∀ χ, N.txT (n * m) p'' χ = N.txT m p χ := by
  intro O _ N n m hn hm p'' p hy hg χ
  have hw := wQ_nest N hm.pow (hn.mul hm).pow (by ring) p'' p hy hg
  have hq := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m n p''.1.2.b p''.1.2.b).1
  rw [mul_comm m n] at hq
  have hb : p.1.2.b = p''.1.2.b ^ n := by rw [hg, NumD.Gt.pow_b]
  have hu : N.wQ p'' / mulq N.θ N.σ (n * m) p''.1.2.b = N.wQ p / mulq N.θ N.σ m p.1.2.b := by
    rw [← hw, hq, hb, mul_div_mul_right_eq_div]
  simp only [NumD.txT]
  rw [hu, hg, ← pow_mul]

end GlobalTheory.Ex.Nest
