import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

namespace GlobalTheory.Ex.PhiOp

section Cube
variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U} (h : IsCub θ)
include h

theorem cub_four (u v u' v' x : A) :
    θ (u * v) (u' * v') x * θ u' v' x * θ u v x = θ (u * u') (v * v') x * θ u u' x * θ v v' x := by
  have a := h.coc (u * v) u' v' x
  have b := h.coc v u u' x
  have c := h.coc (u * u') v v' x
  rw [mul_comm v u, h.s01 v u, h.s01 v (u * u')] at b
  rw [mul_right_comm u u' v] at c
  have a' := congrArg Additive.ofMul a
  have b' := congrArg Additive.ofMul b
  have c' := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at a' b' c' ⊢
  linear_combination (norm := abel) b' + c' - a'

theorem cubN_mul (k : ℕ) (b b' x : A) :
    cubN θ k 1 (b * b') x * θ b b' x ^ k = θ (b ^ k) (b' ^ k) x * cubN θ k 1 b x * cubN θ k 1 b' x := by
  induction k with
  | zero => simp [cubN, h.face]
  | succ k ih =>
    have c := cub_four h (b ^ k) (b' ^ k) b b' x
    simp only [cubN, Finset.prod_range_succ, one_mul] at ih ⊢
    rw [mul_pow b b' k, pow_succ b, pow_succ b', pow_succ (θ b b' x)]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have c' := congrArg Additive.ofMul c
    simp only [ofMul_mul] at ih' c' ⊢
    linear_combination (norm := abel) ih' + c'

theorem factor_comp (k : ℕ) (a b b' x : A) :
    cubN θ k (a * b' ^ k) b x / θ (a * b' ^ k) x b * (cubN θ k a b' (x * b) / θ a (x * b) b') * θ a b b' =
      cubN θ k a (b * b') x / θ a x (b * b') * (θ a (b' ^ k) b * cubN θ k 1 b' b) := by
  have e₁ := h.N_add k a b' x b
  have e₂ := h.N_split k (a * b' ^ k) b x
  have e₃ := h.N_split k a b' x
  have e₄ := h.N_split k a (b * b') x
  have e₅ := h.N_split k a b' b
  have e₆ := cubN_mul h k b b' x
  have e₇ := h.coc a (b' ^ k) (b ^ k) x
  have e₈ := h.coc x b b' a
  have r : ∀ u v, θ u v a = θ a u v := fun u v => by rw [h.s12, h.s01]
  simp only [r] at e₈
  rw [mul_comm (b' ^ k), ← mul_pow, h.s01 (b' ^ k)] at e₇
  rw [h.s12 b' x b, h.s01 b' b x] at e₁
  have E := fun {p q : U} (e : p = q) => congrArg Additive.ofMul e
  have a₁ := E e₁; have a₂ := E e₂; have a₃ := E e₃; have a₄ := E e₄; have a₅ := E e₅; have a₆ := E e₆
  have a₇ := E e₇; have a₈ := E e₈
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ ⊢
  linear_combination (norm := abel) a₁ + a₂ + a₃ - a₄ + a₅ - a₆ + a₇ - a₈

end Cube

variable {O : Type} [CommRing O] (N : NumD O)

theorem s_nsmul (g : N.Gt) (k : ℕ) (y : N.X) : g.s (k • y) * cubN N.θ k 1 (N.c y) g.b = g.s y ^ k := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    have m := g.mult (k • y) y
    rw [N.c_nsmul] at m
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, one_mul, succ_nsmul, pow_succ, ← ih, ← mul_assoc, mul_right_comm, m,
      mul_right_comm]

theorem phi_phi {k : ℕ} (p p' : N.QT k) (w w' : Oˣ) (s : N.X → N.A → O) :
    N.phi p w (N.phi p' w' s) = N.phi (p * p') (w * w' * N.tk p p') s := by
  funext α x
  obtain ⟨β, rfl⟩ : ∃ β, α = β + p'.1.1.toAdd + p.1.1.toAdd :=
    ⟨α - p.1.1.toAdd - p'.1.1.toAdd, by abel⟩
  have y : (p * p').1.1.toAdd = p.1.1.toAdd + p'.1.1.toAdd := rfl
  have g : (p * p').1.2 = p.1.2 * p'.1.2 := rfl
  have e : β + p'.1.1.toAdd + p.1.1.toAdd - (p.1.1.toAdd + p'.1.1.toAdd) = β := by abel
  simp only [NumD.phi, y, g, e, add_sub_cancel_right, NumD.Gt.mul_b]
  rw [← mul_assoc, ← Units.val_mul, mul_assoc x]
  congr 2
  have m := p.1.2.mult β p'.1.1.toAdd
  have f := factor_comp N.cub k (N.c β) p.1.2.b p'.1.2.b x
  rw [← N.QT_pow_b p'] at m
  rw [NumD.Gt.mul_s, NumD.tk, N.c_add, ← N.QT_pow_b p', NumB.uV, NumB.uV, NumB.uV]
  have m' := congrArg Additive.ofMul m
  have f' := congrArg Additive.ofMul f
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at m' f' ⊢
  linear_combination (norm := abel) m' + f'

theorem phi_mul {k : ℕ} (p : N.QT k) (u w : Oˣ) (s : N.X → N.A → O) :
    N.phi p (u * w) s = (u : O) • N.phi p w s := by
  funext α x
  simp only [NumD.phi, Pi.smul_apply, smul_eq_mul, Units.val_mul]
  ring

theorem phi_comm {k : ℕ} (p p' : N.QT k) (w w' : Oˣ) (s : N.X → N.A → O) :
    N.phi p w (N.phi p' w' s) = (N.wp p p' : O) • N.phi p' w' (N.phi p w s) := by
  rw [phi_phi, phi_phi, ← phi_mul, mul_comm p' p, NumD.wp]
  congr 1
  rw [mul_comm w' w, mul_left_comm, div_mul_cancel]

theorem phi_triv {k : ℕ} (p : N.QT k) (s : N.X → N.A → O) (z : N.X) (hs : N.FE k s) (h₁ : p.1.1.toAdd = k • z)
    (h₂ : p.1.2 = N.io z) : N.phi p (N.ψ z ^ k) s = s := by
  funext α x
  have := hs z (α - k • z) x
  rw [sub_add_cancel] at this
  rw [this]
  simp only [NumD.phi, h₁, h₂, NumD.io_b, NumD.io_s]
  rw [mul_right_comm]

theorem fe_of_phi_triv {k : ℕ} (s : N.X → N.A → O) (h : ∀ z, N.phi (N.qTriv k z) (N.ψ z ^ k) s = s) :
    N.FE k s := by
  intro μ α x
  have := congrFun (congrFun (h μ) (α + k • μ)) x
  rw [← this]
  simp only [NumD.phi, NumD.qTriv, toAdd_ofAdd, add_sub_cancel_right, NumD.io_b, NumD.io_s]
  rw [mul_right_comm]

theorem wp_qTriv {k : ℕ} (z : N.X) (p : N.QT k) : N.wp (N.qTriv k z) p = 1 := by
  have a := NumD.Gt.pow_s p.1.2 k z
  rw [N.mem_QT.1 p.2, NumD.io_s, N.τ_symm] at a
  have b := s_nsmul N p.1.2 k z
  rw [NumD.wp, div_eq_one]
  exact a.trans b.symm

theorem fe_phi {k : ℕ} (p : N.QT k) (w : Oˣ) (s : N.X → N.A → O) (hs : N.FE k s) : N.FE k (N.phi p w s) :=
  fe_of_phi_triv N _ fun z => by
    rw [phi_comm, wp_qTriv, phi_triv N _ s z hs rfl rfl, Units.val_one, one_smul]

theorem phi_main : ∀ (O : Type) [CommRing O] (N : NumD O), ∀ (k : ℕ) (p p' : N.QT k) (w w' : Oˣ) (s : N.X → N.A → O), (N.FE k s → N.FE k (N.phi p w s)) ∧ N.phi p w (N.phi p' w' s) = N.phi (p * p') (w * w' * N.tk p p') s ∧ N.phi p w (N.phi p' w' s) = (N.wp p p' : O) • N.phi p' w' (N.phi p w s) ∧ ∀ z : N.X, N.FE k s → p.1.1.toAdd = k • z → p.1.2 = N.io z → N.phi p (N.ψ z ^ k) s = s :=
  fun _ _ N _ p p' w w' s =>
    ⟨fe_phi N p w s, phi_phi N p p' w w' s, phi_comm N p p' w w' s, fun z => phi_triv N p s z⟩

end GlobalTheory.Ex.PhiOp
