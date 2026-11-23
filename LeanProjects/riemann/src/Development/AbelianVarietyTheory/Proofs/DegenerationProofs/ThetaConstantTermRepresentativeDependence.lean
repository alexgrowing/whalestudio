import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MulqLawsStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.DegenerationDataPsiQuadraticGeneratorsLinearStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormalisingFactorStatement
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.NumD
variable {O : Type} [CommRing O] (N : NumD O)

theorem vt_mul_io_shift (g : N.Gt) (w χ : N.X) :
    ((N.ψ w * g.s w : Oˣ) : O) * N.vt (g * N.io w) χ = N.vt g (χ + w) := by
  have e : N.c χ * (g * N.io w).b = N.c (χ + w) * g.b := by
    rw [Gt.mul_b, io_b, N.c_add, mul_assoc, mul_comm g.b]
  rw [vt, vt, e, ← mul_assoc, ← Units.val_mul]
  congr 2
  have a := congrArg Additive.ofMul (g.mult χ w)
  rw [Gt.mul_s, io_s, io_b, N.ψ_add, N.τ_symm w χ, N.cub.s12 (N.c χ) g.b]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a ⊢
  linear_combination (norm := abel) -a

theorem vt_mul_tor_shift (g : N.Gt) (t : Multiplicative N.X →* Oˣ) (χ : N.X) :
    N.vt (g * N.tor t) χ = (t (Multiplicative.ofAdd χ) : Oˣ) * N.vt g χ := by
  rw [vt, vt, mul_comm g, N.tor_mul_s_apply, Gt.mul_b, tor_b, one_mul, mul_left_comm (N.ψ χ), Units.val_mul, mul_assoc]

theorem tk_qTriv_right {k : ℕ} (p : N.QT k) (z : N.X) : N.tk p (N.qTriv k z) = p.1.2.s z ^ k :=
  ((GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N k z).2.2 p.1.2).1

theorem tk_qTriv_left {k : ℕ} (p : N.QT k) (z : N.X) : N.tk (N.qTriv k z) p = p.1.2.s z ^ k := by
  rw [← Gt.pow_s, N.mem_QT.1 p.2, io_s, N.τ_symm]
  rfl

theorem wQ_qTriv_odd {k : ℕ} (hk : Odd k) (z : N.X) : N.wQ (N.qTriv k z) = N.ψ z ^ k := by
  symm
  rw [(GlobalTheory.T.wQ_characterization_and_mul_relation O N k hk (N.qTriv k z) (N.qTriv k z)).1, tk_qTriv_right]
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N k z
  constructor
  · change _ * dbl N.θ N.σ (N.c z) ^ k = N.τ z z ^ k
    rw [h₁, mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]
  · change _ = N.ψ (k • z) * mulq N.θ N.σ k (N.c z)
    rw [h₂, ← pow_mul, sq]

theorem wQ_mul_qTriv_odd {k : ℕ} (hk : Odd k) (p : N.QT k) (z : N.X) :
    N.wQ (p * N.qTriv k z) = N.wQ p * N.ψ z ^ k * p.1.2.s z ^ k := by
  have h := (GlobalTheory.T.wQ_characterization_and_mul_relation O N k hk p (N.qTriv k z)).2.1
  rw [wp, tk_qTriv_right, tk_qTriv_left, div_self', one_pow, one_mul, N.wQ_qTriv_odd hk] at h
  exact h.symm

theorem txT_mul_qTriv {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (z χ : N.X) :
    N.txT m (p * N.qTriv (m ^ 2) z) χ = N.txT m p (χ + m • z) := by
  have e : (p * N.qTriv (m ^ 2) z).1.2 = p.1.2 * N.io z := rfl
  rw [txT, txT, N.wQ_mul_qTriv_odd hm.pow, e, mul_pow, ← N.io_nsmul, ← N.vt_mul_io_shift, ← mul_assoc,
    ← Units.val_mul]
  congr 2
  have h₁ := (GlobalTheory.T.mulq_dbl_cubN_relations O N.toNumB m 0 p.1.2.b (N.c z)).2.1
  obtain ⟨-, h₂, h₃⟩ := GlobalTheory.T.degenerationData_psi_quadratic_generators_linear O N m z
  have h₄ := congrArg (· ^ m) (h₃ p.1.2).1
  have h₅ := Gt.pow_s p.1.2 m (m • z)
  rw [N.c_nsmul] at h₅
  simp only [mul_pow, ← pow_mul, ← sq] at h₄
  rw [Gt.mul_b, io_b, h₁, ← h₂, ← h₄, ← h₅]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div]
  abel

theorem txT_mul_tor {m : ℕ} (hm : Odd m) (p p' : N.QT (m ^ 2)) (χ : N.X) (t : Multiplicative N.X →* Oˣ)
    (h : p'.1.1 = p.1.1) (h' : p'.1.2 = p.1.2 * N.tor t) :
    N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) *
      N.txT m p χ := by
  have ht : t ^ (m ^ 2) = 1 := by
    apply N.tor_injective
    have a := N.mem_QT.1 p'.2
    rw [h, h', mul_pow, N.mem_QT.1 p.2, mul_eq_left] at a
    rw [N.tor_pow, a, N.tor_one]
  obtain ⟨j, hj⟩ : Odd (m ^ 2) := hm.pow
  have hd : (m ^ 2 - 1) / 2 = j := by omega
  have hy : t p.1.1 ^ j * t p.1.1 ^ j * t p.1.1 = 1 := by
    rw [← pow_add, ← pow_succ, ← two_mul, ← hj, ← MonoidHom.pow_apply, ht, MonoidHom.one_apply]
  have hb : p'.1.2.b = p.1.2.b := by rw [h', Gt.mul_b, tor_b, mul_one]
  have hs : p'.1.2.s p.1.1.toAdd = t p.1.1 * p.1.2.s p.1.1.toAdd := by
    rw [h', mul_comm p.1.2, N.tor_mul_s_apply]
    rfl
  rw [txT, txT, wQ, wQ, NumB.wS, NumB.wS, hb, h, hs, h', mul_pow, ← N.tor_pow, vt_mul_tor_shift, hd,
    ← mul_assoc, ← mul_assoc, ← Units.val_mul, ← Units.val_mul]
  congr 2
  rw [ofAdd_add, ofAdd_toAdd, ofAdd_nsmul, map_mul, map_pow, MonoidHom.pow_apply]
  have a := congrArg Additive.ofMul hy
  apply Additive.ofMul.injective
  simp only [div_pow, mul_pow, ofMul_mul, ofMul_div, ofMul_one] at a ⊢
  linear_combination (norm := abel) -a

end GlobalTheory.Ex.NumD

namespace GlobalTheory.Ex

theorem txT_shift : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (m : ℕ), Odd m → ∀ (p p' : N.QT (m ^ 2)) (χ : N.X), (∀ z, p'.1.1.toAdd = p.1.1.toAdd + m ^ 2 • z → p'.1.2 = p.1.2 * N.io z → N.txT m p' χ = N.txT m p (χ + m • z)) ∧ (∀ t : Multiplicative N.X →* Oˣ, p'.1.1 = p.1.1 → p'.1.2 = p.1.2 * N.tor t → N.txT m p' χ = (t p.1.1 ^ ((m ^ 2 - 1) / 2) * t (Multiplicative.ofAdd (p.1.1.toAdd + m • χ)) : Oˣ) * N.txT m p χ) := by
  intro O _ N m hm p p' χ
  refine ⟨fun z h h' => ?_, fun t h h' => N.txT_mul_tor hm p p' χ t h h'⟩
  have e : p' = p * N.qTriv (m ^ 2) z := Subtype.ext (Prod.ext h h')
  rw [e, N.txT_mul_qTriv hm]

end GlobalTheory.Ex
