import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.MainNotions.CartierLocalBounds

open Formalism.BasicNotions

def rho (l : ℕ) : ℝ := 1 / ((l : ℝ) ^ 2 - 1)

def gam (l : ℕ) : ℝ := (l : ℝ) / ((l : ℝ) ^ 2 - 1)

def expE (l i : ℕ) : ℕ := 1 + l * ∑ t ∈ Finset.range ((i - 1) / 2), (l ^ 2) ^ t

def rad1 (l i : ℕ) : ℝ := rho l + ((l : ℝ) ^ i)⁻¹ / 2

def rad2 (l : ℕ) : ℝ := rho l + 1 / 2

def dlt (l i : ℕ) : ℝ := ((l : ℝ) ^ i)⁻¹ / 8

def vLe {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (b : ℝ) : Prop := (l : ℝ) ^ (-b) ≤ ‖x‖

def vGe {l : ℕ} [Fact l.Prime] (x : ℂ_[l]) (b : ℝ) : Prop := ‖x‖ ≤ (l : ℝ) ^ (-b)

section Jets

variable {C : Type} [Field C]

abbrev PVar (n0 : ℕ) := (Fin n0 × Fin n0) ⊕ (Fin n0 × Fin n0)

def detL (C : Type) [Field C] (n0 : ℕ) : MvPolynomial (PVar n0) C :=
  Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inl (b, c)))

def detR (C : Type) [Field C] (n0 : ℕ) : MvPolynomial (PVar n0) C :=
  Matrix.det (Matrix.of fun b c : Fin n0 => MvPolynomial.X (Sum.inr (b, c)))

def mfact {σ : Type} (m : σ →₀ ℕ) : ℕ := m.prod fun _ k => k.factorial

def jetAt0 {σ : Type} (P : MvPolynomial σ C) (g : MvPowerSeries σ C) : C :=
  ∑ m ∈ P.support, MvPolynomial.coeff m P * (mfact m : C) * MvPowerSeries.coeff m g

def mvExp {σ : Type} (h : MvPowerSeries σ C) : MvPowerSeries σ C :=
  fun m => ∑ k ∈ Finset.range (m.degree + 1), MvPowerSeries.coeff m (h ^ k) / (k.factorial : C)

def LamOf (C : Type) [Field C] (l i n0 : ℕ) (h : MvPowerSeries (PVar n0) C) (y : ℕ) : C :=
  jetAt0 (detL C n0 ^ (l ^ i * y) * detR C n0 ^ y) (mvExp h)

def dL {ι ι' : Type} [Fintype ι] (μ : (ι ⊕ ι') →₀ ℕ) : ℕ := ∑ c : ι, μ (Sum.inl c)

def dR {ι ι' : Type} [Fintype ι'] (μ : (ι ⊕ ι') →₀ ℕ) : ℕ := ∑ b : ι', μ (Sum.inr b)

def diffOp {σ : Type} (P Q : MvPolynomial σ C) : MvPolynomial σ C :=
  ∑ m ∈ P.support, ∑ a ∈ Q.support,
    if m ≤ a then
      MvPolynomial.monomial (a - m)
        (MvPolynomial.coeff m P * MvPolynomial.coeff a Q * ((mfact a : C) / (mfact (a - m) : C)))
    else 0

end Jets

def WeightGe {l : ℕ} [Fact l.Prime] (i : ℕ) {ι ι' : Type} [Fintype ι] [Fintype ι']
    (h1 : MvPowerSeries (ι ⊕ ι') ℂ_[l]) : Prop :=
  ∀ μ, vGe (MvPowerSeries.coeff μ h1)
    (1 / ((l : ℝ) - 1) - ((dL μ : ℝ) * (rad1 l i - dlt l i) + (dR μ : ℝ) * (rad2 l - dlt l i)))

def hP (l : ℕ) [Fact l.Prime] (i n0 : ℕ) (h1 : MvPowerSeries (PVar n0) ℂ_[l]) :
    MvPowerSeries (PVar n0) ℂ_[l] :=
  -(((l : ℂ_[l]) ^ expE l i)⁻¹) • (∑ b : Fin n0, ∑ c : Fin n0,
      MvPowerSeries.X (Sum.inl (b, c)) ^ (l ^ i) * MvPowerSeries.X (Sum.inr (b, c))) + h1

def ThmP : Prop :=
  ∃ C0 : ℝ, ∀ (l : ℕ) [Fact l.Prime], 5 ≤ l → ∀ i : ℕ, Odd i → ∀ n n0 : ℕ, 1 ≤ n → n0 ≤ n →
    ∀ h1 : MvPowerSeries (PVar n0) ℂ_[l], MvPowerSeries.constantCoeff h1 = 0 → WeightGe i h1 →
    ∀ Y0 : ℕ, ∃ y : ℕ, Y0 ≤ y ∧
      (y : ℝ) < Y0 + C0 * (n : ℝ) ^ 2 * ((i : ℝ) + Real.log ((n : ℝ) + 1)) ∧
      vLe (LamOf ℂ_[l] l i n0 (hP l i n0 h1) y)
        ((n0 : ℝ) * y * (((l : ℝ) ^ i + 1) * gam l - 1) + n * (Real.logb l n + 1))

def CayleyId : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (n0 s : ℕ),
    diffOp (detL C n0) (detL C n0 ^ (s + 1)) =
      ((∏ a ∈ Finset.range n0, ((s : C) + 1 + a))) • detL C n0 ^ s

def LPDual : Prop :=
  ∀ (l d : ℕ) [NeZero d], 2 ≤ l → Even d → ∀ Ds : ZMod d → ℝ, (∀ a, 0 ≤ Ds a) →
    IsGreatest {y : ℝ | ∃ sg : ZMod d → ℝ, (∀ a, 0 ≤ sg a ∧ sg a ≤ 1) ∧
        (∀ a (i : ℕ), Odd i → i < d → 1 ≤ (l : ℝ) ^ i * sg a + sg (a + (i : ZMod d))) ∧
        y = ∑ a, Ds a * (gam l - sg a)}
      (lpF l d Ds)

theorem fin_two_eq_one_sub (g g' : Fin 2) (h : g' ≠ g) : g' = 1 - g := by
  fin_cases g <;> fin_cases g' <;> simp_all

structure LocD (l : ℕ) [Fact l.Prime] (d : ℕ) [NeZero d] where

  five_le_l : 5 ≤ l

  d_even : Even d

  r : ℕ
  j : ℕ
  j' : ℕ
  rh : ℕ
  rh_le : rh ≤ j'

  rh_le_big : rh + j' ≤ r
  jj_le : j + j' ≤ r

  big : Fin 2 → ZMod d → Prop

  rk : Fin 2 → ZMod d → ℕ
  rk_big : ∀ g a, big g a → rk g a = r - j'
  rk_small : ∀ g a, ¬ big g a → rk g a = j'

  U : ∀ g a, Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])
  U_summand : ∀ g a, big g a → ∃ Q : Submodule 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l]), IsCompl (U g a) Q
  U_basis : ∀ g a, big g a → Nonempty (Module.Basis (Fin (r - j' - j)) 𝓞_ℂ_[l] (U g a))

  Chart : Type

  tan : Chart → ∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])

  chart_tan : ∀ b : (∀ g a, Module.Basis (Fin (rk g a)) 𝓞_ℂ_[l] (Fin (rk g a) → 𝓞_ℂ_[l])),
    ∃ χ : Chart, tan χ = b

  alC : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk g a) → ℂ_[l]
  alC_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → alC χ g b c s a = 0

  alC_zero : ∀ χ g b c k, alC χ g b c 0 b k = ((tan χ g b c k : 𝓞_ℂ_[l]) : ℂ_[l])

  beP : Chart → ∀ (g : Fin 2) (b : ZMod d), Fin (rk g b) → ℕ → ∀ a : ZMod d, Fin (rk (1 - g) a) → ℂ_[l]
  beP_type : ∀ χ g b c (s : ℕ) a, a ≠ b + (s : ZMod d) → beP χ g b c s a = 0

  beP_zero : ∀ χ g b c a, beP χ g b c 0 a = 0

  chart_mod : ∀ (χ : Chart)
    (x : ∀ g : Fin 2, ℕ → (Σ b : ZMod d, Fin (rk g b)) → (Σ b : ZMod d, Fin (rk g b)) → 𝓞_ℂ_[l]),
    (∀ g (s : ℕ) c b, b.1 ≠ c.1 + (s : ZMod d) → x g s c b = 0) →
    (∀ g, IsUnit (Matrix.of (x g 0)).det) →
    ∃ χ' : Chart,
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, alC χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * alC χ g b.1 b.2 (n - s) a k) ∧
      (∀ g (c : Σ b : ZMod d, Fin (rk g b)) (n : ℕ) a k, beP χ' g c.1 c.2 n a k =
        ∑ s ∈ Finset.range (n + 1), ∑ b : (Σ b : ZMod d, Fin (rk g b)),
          ((x g s c b : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (n - s)) * beP χ g b.1 b.2 (n - s) a k)

  tL : Chart → ∀ (g : Fin 2) (a : ZMod d), (Σ b : ZMod d, Fin (rk g b)) → MvPowerSeries (Fin (rk g a)) ℂ_[l]
  tL_const : ∀ χ g a x, MvPowerSeries.constantCoeff (tL χ g a x) = 0

  tL_log_same : ∀ χ g a (k : Fin (rk g a)) (μ : Fin (rk g a) →₀ ℕ),
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) =
      if μ = Finsupp.single k 1 then 1 else 0

  tL_log_other : ∀ χ g a a' (k : Fin (rk g a')) (μ : Fin (rk g a) →₀ ℕ), a' ≠ a →
    (∑ s ∈ Finset.range (μ.degree + 1), ∑ x : (Σ b : ZMod d, Fin (rk g b)),
      alC χ g x.1 x.2 s a' k * MvPowerSeries.coeff μ (tL χ g a x ^ (l ^ s))) = 0

  hL : ∀ (g : Fin 2) (a a' : ZMod d), MvPowerSeries (Fin (rk g a) ⊕ Fin (rk (1 - g) a')) ℂ_[l]

  Tt : Fin 2 → Type
  [instTt : ∀ g, AddCommGroup (Tt g)]
  [modTt : ∀ g, Module ℤ_[l] (Tt g)]
  Tt_free : ∀ g, Module.Free ℤ_[l] (Tt g)
  Tt_rank : ∀ g, Module.finrank ℤ_[l] (Tt g) = d * (r - rh)

  alHT : ∀ g, Tt g → ∀ a, (Fin (rk g a) → 𝓞_ℂ_[l]) →ₗ[𝓞_ℂ_[l]] 𝓞_ℂ_[l]

  chiG : Chart → ∀ g, Tt g → MvPowerSeries (Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l]

  chiG_leaf : ∀ χ g (t : Tt g) a,
    MvPowerSeries.subst (fun x => tL χ g a x)
        (MvPowerSeries.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) (chiG χ g t)) =
      mvExp (∑ k : Fin (rk g a), ((alHT g t a (Pi.single k 1) : 𝓞_ℂ_[l]) : ℂ_[l]) •
        (MvPowerSeries.X k : MvPowerSeries (Fin (rk g a)) ℂ_[l]))

  ev : Chart → ∀ N : ℕ,
    MvPolynomial (Fin N × Σ g : Fin 2, Σ a : ZMod d, Fin (rk g a)) 𝓞_ℂ_[l] →
    MvPowerSeries (Fin N × Σ g : Fin 2, Σ b : ZMod d, Fin (rk g b)) 𝓞_ℂ_[l] → ℂ_[l]

attribute [instance] LocD.instTt LocD.modTt

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def nn : ℕ := Λ.r - Λ.j' - Λ.j

def mm : ℕ := Λ.j + Λ.j'

def Alternating : Prop := ∀ a : ZMod d, (Λ.big 0 a ↔ Even a.val) ∧ (Λ.big 1 a ↔ ¬ Even a.val)

def AllBig : Prop := ∀ a : ZMod d, Λ.big 0 a

def bg (_Λ : LocD l d) (a : ZMod d) : Fin 2 := if Even a.val then 0 else 1

abbrev CoG (g : Fin 2) := Σ b : ZMod d, Fin (Λ.rk g b)

def zeP (χ : Λ.Chart) (g : Fin 2) (a a' : ZMod d) (b : Fin (Λ.rk (1 - g) a')) :
    MvPowerSeries (Fin (Λ.rk g a)) ℂ_[l] :=
  fun μ => -(∑ s ∈ Finset.range (μ.degree + 1), ∑ x : Λ.CoG g, ∑ k : Fin (Λ.rk (1 - g) a'),
    ((Λ.tan χ (1 - g) a' b k : 𝓞_ℂ_[l]) : ℂ_[l]) * Λ.beP χ g x.1 x.2 s a' k *
      MvPowerSeries.coeff μ (Λ.tL χ g a x ^ (l ^ s)))

end LocD

def hPull {l : ℕ} [Fact l.Prime] {N N' : ℕ} {ι ι' : Type} [Fintype ι] [Fintype ι']
    (H : MvPowerSeries (Fin N ⊕ Fin N') ℂ_[l]) (v : ι → Fin N → ℂ_[l]) (v' : ι' → Fin N' → ℂ_[l]) :
    MvPowerSeries (ι ⊕ ι') ℂ_[l] :=
  MvPowerSeries.subst
    (Sum.elim (fun k => ∑ c : ι, v c k • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') ℂ_[l]))
      (fun k => ∑ b : ι', v' b k • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') ℂ_[l]))) H

def embL {C : Type} [CommRing C] {ι ι' : Type} (f : MvPowerSeries ι C) : MvPowerSeries (ι ⊕ ι') C :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (Sum.inl k) : MvPowerSeries (ι ⊕ ι') C)) f

def embR {C : Type} [CommRing C] {ι ι' : Type} (f : MvPowerSeries ι' C) : MvPowerSeries (ι ⊕ ι') C :=
  MvPowerSeries.subst (fun k => (MvPowerSeries.X (Sum.inr k) : MvPowerSeries (ι ⊕ ι') C)) f

def hRows {C : Type} [CommRing C] (n0 : ℕ) (H : MvPowerSeries (Fin n0 ⊕ Fin n0) C) :
    MvPowerSeries (PVar n0) C :=
  ∑ ρ : Fin n0, MvPowerSeries.subst
    (Sum.elim (fun c => (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar n0) C))
      (fun b => MvPowerSeries.X (Sum.inr (ρ, b)))) H

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def hM (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) (i : ℕ) {n0 N' : ℕ} (e : Fin n0 → Fin (Λ.rk g a))
    (v' : Fin N' → Fin (Λ.rk (1 - g) (a + (i : ZMod d))) → 𝓞_ℂ_[l]) :
    MvPowerSeries (Fin n0 ⊕ Fin N') ℂ_[l] :=
  hPull (Λ.hL g a (a + (i : ZMod d))) (fun c k => ((Λ.tan χ g a (e c) k : 𝓞_ℂ_[l]) : ℂ_[l]))
    (fun b k => ((v' b k : 𝓞_ℂ_[l]) : ℂ_[l]))

def mainM (_Λ : LocD l d) (i : ℕ) {n0 N' : ℕ} (Φ : Fin N' → Fin n0 → ℂ_[l]) :
    MvPowerSeries (Fin n0 ⊕ Fin N') ℂ_[l] :=
  ((l : ℂ_[l]) ^ expE l i)⁻¹ • ∑ b : Fin N', ∑ c : Fin n0,
    Φ b c • (MvPowerSeries.X (Sum.inl c) ^ (l ^ i) * MvPowerSeries.X (Sum.inr b))

def MConcl (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) (i n0 : ℕ) (e : Fin n0 ↪ Fin (Λ.rk g a))
    (v' : Fin Λ.nn → Fin (Λ.rk (1 - g) (a + (i : ZMod d))) → 𝓞_ℂ_[l])
    (Φ : Fin Λ.nn → Fin n0 → ℂ_[l]) : Prop :=
  ((Λ.nn : ℤ) - ((i : ℤ) + 3) * Λ.mm ≤ n0 ∧ n0 ≤ Λ.nn) ∧
  Submodule.span 𝓞_ℂ_[l] (Set.range (fun c => Λ.tan χ g a (e c))) ≤ Λ.U g a ∧
  (∃ Q : Submodule 𝓞_ℂ_[l] (Fin (Λ.rk g a) → 𝓞_ℂ_[l]), Q ≤ Λ.U g a ∧
    Disjoint (Submodule.span 𝓞_ℂ_[l] (Set.range (fun c => Λ.tan χ g a (e c)))) Q ∧
    Submodule.span 𝓞_ℂ_[l] (Set.range (fun c => Λ.tan χ g a (e c))) ⊔ Q = Λ.U g a) ∧
  LinearIndependent 𝓞_ℂ_[l] v' ∧
  Submodule.span 𝓞_ℂ_[l] (Set.range v') = Λ.U (1 - g) (a + (i : ZMod d)) ∧
  (∀ c a'' k, Λ.alC χ g a (e c) 1 a'' k = 0) ∧
  (∀ b c, ‖Φ b c‖ ≤ 1) ∧
  (∀ (b : Fin Λ.nn) (c : Fin n0), b.val < n0 → Φ b c = if b.val = c.val then -1 else 0) ∧
  WeightGe i (Λ.hM χ g a i e v' - Λ.mainM i Φ) ∧
  (∀ μ, dR μ = 0 → MvPowerSeries.coeff μ (Λ.hM χ g a i e v' - Λ.mainM i Φ) = 0) ∧
  (i = 1 → ∀ μ, dL μ < l ^ 2 → dR μ < l →
    ‖MvPowerSeries.coeff μ (Λ.hM χ g a i e v' - Λ.mainM i Φ)‖ ≤ 1)

def LemmaMAt : Prop :=
  Λ.Alternating → ∀ (g : Fin 2) (a : ZMod d), Λ.big g a → ∀ i : ℕ, Odd i → i < d →
    ∃ (χ : Λ.Chart) (n0 : ℕ) (e : Fin n0 ↪ Fin (Λ.rk g a))
      (v' : Fin Λ.nn → Fin (Λ.rk (1 - g) (a + (i : ZMod d))) → 𝓞_ℂ_[l])
      (Φ : Fin Λ.nn → Fin n0 → ℂ_[l]), Λ.MConcl χ g a i n0 e v' Φ

def UBAt : Prop :=
  Λ.Alternating → ∀ (g : Fin 2) (a : ZMod d), Λ.big g a →
    ∀ (χ : Λ.Chart) (n0 : ℕ) (e : Fin n0 ↪ Fin (Λ.rk g a))
      (v' : Fin Λ.nn → Fin (Λ.rk (1 - g) (a + ((1 : ℕ) : ZMod d))) → 𝓞_ℂ_[l])
      (Φ : Fin Λ.nn → Fin n0 → ℂ_[l]), Λ.MConcl χ g a 1 n0 e v' Φ →
      ∀ (hn : n0 ≤ Λ.nn) (y : ℕ), y + Λ.nn ≤ l - 1 →
        ‖LamOf ℂ_[l] l 1 n0
          (hRows n0 (Λ.hM χ g a 1 e (fun b => v' (Fin.castLE hn b)))) y‖ = 1

def htDet (g : Fin 2) (a : ZMod d) (bas : Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U g a))
    (t : Fin Λ.nn → Λ.Tt g) : ℂ_[l] :=
  (((Matrix.of fun k c : Fin Λ.nn => Λ.alHT g (t k) a (bas c : Fin (Λ.rk g a) → 𝓞_ℂ_[l])).det :
    𝓞_ℂ_[l]) : ℂ_[l])

def CHAt : Prop :=
  (Λ.Alternating → ∀ (g : Fin 2) (a : ZMod d), Λ.big g a →
    ∀ bas : Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U g a), ∃ t : Fin Λ.nn → Λ.Tt g,
      vLe (Λ.htDet g a bas t) ((Λ.nn : ℝ) * gam l + (Λ.mm : ℝ) / ((l : ℝ) - 1))) ∧
  (Λ.AllBig → ∀ a : ZMod d,
    ∀ bas : Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U 0 a), ∃ t : Fin Λ.nn → Λ.Tt 0,
      vLe (Λ.htDet 0 a bas t) ((Λ.mm : ℝ) / ((l : ℝ) - 1)))

abbrev LV (N : ℕ) := Fin N × Σ g : Fin 2, Σ a : ZMod d, Fin (Λ.rk g a)

abbrev CV (N : ℕ) := Fin N × Σ g : Fin 2, Λ.CoG g

def detBlock (N : ℕ) (a : ZMod d) (S : Fin Λ.nn ↪ Fin N)
    (bas : Fin Λ.nn → Fin (Λ.rk (Λ.bg a) a) → 𝓞_ℂ_[l]) : MvPolynomial (Λ.LV N) 𝓞_ℂ_[l] :=
  Matrix.det (Matrix.of fun k c : Fin Λ.nn =>
    ∑ κ : Fin (Λ.rk (Λ.bg a) a), MvPolynomial.C (bas c κ) * MvPolynomial.X (S k, ⟨Λ.bg a, a, κ⟩))

def DetProd (N : ℕ) (W : ZMod d → ℕ) : Set (MvPolynomial (Λ.LV N) 𝓞_ℂ_[l]) :=
  {P | ∃ (B : ℕ) (blk : Fin B → ZMod d) (S : Fin B → (Fin Λ.nn ↪ Fin N)) (ex : Fin B → ℕ)
      (bas : ∀ a, Module.Basis (Fin Λ.nn) 𝓞_ℂ_[l] (Λ.U (Λ.bg a) a)),
    (∀ a, ∑ β ∈ Finset.univ.filter (fun β => blk β = a), ex β = W a) ∧
    (∀ β β', β ≠ β' → blk β = blk β' → Disjoint (Set.range (S β)) (Set.range (S β'))) ∧
    P = ∏ β, (Λ.detBlock N (blk β) (S β)
      (fun c => (bas (blk β) c : Fin (Λ.rk (Λ.bg (blk β)) (blk β)) → 𝓞_ℂ_[l]))) ^ (ex β)}

end LocD

def thl (l k : ℕ) : ℝ :=
  ((l : ℝ) ^ sInf {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k : ℝ) ^ ((3 : ℝ) / 2) < (l : ℝ) ^ i})⁻¹

def addl (C : ℝ) (l k n d : ℕ) (l1 : ℝ) : ℝ :=
  if (l : ℝ) < (k : ℝ) ^ ((1 : ℝ) / 2) then C * d * (n : ℝ) ^ 3 * (k : ℝ) ^ 3 * Real.log k
  else if (l : ℝ) < l1 then C * d * (n : ℝ) ^ 3 * l * Real.log ((n : ℝ) * l) else 0

namespace LocD

variable {l d : ℕ} [Fact l.Prime] [NeZero d] (Λ : LocD l d)

def ContentAt (C : ℝ) : Prop :=
  Λ.Alternating → 0 < Λ.mm →
  ∀ (T Dp l1 : ℝ) (w : ZMod d → ℝ) (W : ZMod d → ℕ) (tha : ZMod d → ℝ),
    1 ≤ T → 1 ≤ Dp → Dp * ((Λ.nn : ℝ) + 1) / Λ.mm ≤ T → (Dp + 4) / T ≤ 1 / 2 →
    (∀ a, 0 < w a) → (∀ a, T * W a = w a * (1 - tha a)) →
    (∀ a, 0 ≤ tha a ∧ tha a ≤ (Dp + 4) / T) →
    ((Λ.nn : ℝ) + 1) ^ ((3 : ℝ) / 2) < l1 → 2 * (Λ.nn : ℝ) + 2 < l1 →
    ∃ N : ℕ, (N : ℝ) ≤ C * Λ.r * d * (1 + ((Finset.univ.sup W : ℕ) : ℝ) / l1 ^ 2) ∧
      ∃ P ∈ Λ.DetProd N W, ∃ (χ : Λ.Chart) (g : MvPowerSeries (Λ.CV N) 𝓞_ℂ_[l]),
        vLe (Λ.ev χ N P g)
          ((lpF l d (fun a => (Λ.nn : ℝ) * w a) +
            C * Real.log ((Λ.nn : ℝ) + 1) * Λ.mm * (∑ a, w a) / l +
            C * ((Λ.nn : ℝ) + 1) * thl l (Λ.nn + 1) * (∑ a, w a) +
            T * addl C l (Λ.nn + 1) Λ.nn d l1) / T)

def CartierFrobeniusFormLocal : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2), ∃ (c : ℕ → Λ.CoG g → Λ.CoG g → 𝓞_ℂ_[l])
      (c' : ℕ → Λ.CoG g → ∀ a : ZMod d, Fin (Λ.rk (1 - g) a) → 𝓞_ℂ_[l]),
    ∀ (x : Λ.CoG g) (i : ℕ) (a : ZMod d),
      (∀ k, (l : ℂ_[l]) * Λ.alC χ g x.1 x.2 (i + 1) a k =
        ∑ s ∈ Finset.range (i + 1), ∑ y : Λ.CoG g,
          ((c s x y : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (i - s)) * Λ.alC χ g y.1 y.2 (i - s) a k) ∧
      (∀ k, (l : ℂ_[l]) * Λ.beP χ g x.1 x.2 (i + 1) a k =
        (∑ s ∈ Finset.range (i + 1), ∑ y : Λ.CoG g,
          ((c s x y : 𝓞_ℂ_[l]) : ℂ_[l]) ^ (l ^ (i - s)) * Λ.beP χ g y.1 y.2 (i - s) a k) +
          ((c' i x a k : 𝓞_ℂ_[l]) : ℂ_[l]))

def LieLeafVanishingLocal : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) (i : ℕ), Odd i → i < d → Λ.big g a →
    Λ.big (1 - g) (a + (i : ZMod d)) →
    (∀ μ, (dL μ = 0 ∨ dR μ = 0) → MvPowerSeries.coeff μ (Λ.hL g a (a + (i : ZMod d))) = 0) ∧
    ∃ K' : Fin (Λ.rk (1 - g) (a + (i : ZMod d))) →
        MvPowerSeries (Λ.CoG g ⊕ Λ.CoG (1 - g)) 𝓞_ℂ_[l],
      ∀ b, (∑ k : Fin (Λ.rk (1 - g) (a + (i : ZMod d))),
          ((Λ.tan χ (1 - g) (a + (i : ZMod d)) b k : 𝓞_ℂ_[l]) : ℂ_[l]) •
            MvPowerSeries.pderiv ℂ_[l] (Sum.inr k) (Λ.hL g a (a + (i : ZMod d)))) =
        MvPowerSeries.subst
            (Sum.elim (fun x => embL (Λ.tL χ g a x))
              (fun x => embR (Λ.tL χ (1 - g) (a + (i : ZMod d)) x)))
            (MvPowerSeries.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) (K' b)) +
          embL (Λ.zeP χ g a (a + (i : ZMod d)) b)

def GoodC (χ : Λ.Chart) (g : Fin 2) (a : ZMod d) {N : ℕ} (e : Fin N ↪ Fin (Λ.rk g a)) : Prop :=
  ∀ c a'' k, Λ.alC χ g a (e c) 1 a'' k = 0

def RankOneLocalSpread : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2) (a : ZMod d), Λ.big g a → Λ.big g (a + 2) →
    ∀ (N : ℕ) (e : Fin N ↪ Fin (Λ.rk g a)), Λ.GoodC χ g a e →
      ∃ (N' : ℕ) (ρ : Fin N' ↪ Fin N) (κ : Fin N' ↪ Fin (Λ.rk g (a + 2))), N ≤ N' + Λ.j' ∧
        ‖(Matrix.of fun s t : Fin N' =>
          (l : ℂ_[l]) * Λ.alC χ g a (e (ρ s)) 2 (a + 2) (κ t)).det‖ = 1

def RankTwoLocalSpread : Prop :=
  ∀ (χ : Λ.Chart) (g : Fin 2) (a : ZMod d), Λ.big g a →
    ∀ (N : ℕ) (e : Fin N ↪ Fin (Λ.rk g a)), Λ.GoodC χ g a e →
      ∃ (N' : ℕ) (ρ : Fin N' ↪ Fin N) (κ : Fin N' ↪ Fin (Λ.rk (1 - g) (a + 1))), N ≤ N' + Λ.rh ∧
        ‖(Matrix.of fun s t : Fin N' =>
          (l : ℂ_[l]) * Λ.beP χ g a (e (ρ s)) 1 (a + 1) (κ t)).det‖ = 1

def FrobeniusNormedRingLocal : Prop :=
  ∀ g : Fin 2, ∃ (A : Type) (_ : CommRing A) (φ : A ≃+* A) (θ : A →+* 𝓞_ℂ_[l]) (μ ξ : A)
      (n1 nb : A → ℝ),
    IsDomain A ∧ Function.Surjective θ ∧ RingHom.ker θ = Ideal.span {ξ} ∧ μ = ξ * φ.symm μ ∧
    (∀ x y, n1 (x * y) = n1 x * n1 y) ∧ (∀ x y, nb (x * y) = nb x * nb y) ∧
    (∀ x, ‖((θ x : 𝓞_ℂ_[l]) : ℂ_[l])‖ ≤ n1 x) ∧ (∀ x, nb x ≤ n1 x) ∧ (∀ x, 0 ≤ nb x) ∧
    (∀ x, n1 x ≤ 1) ∧
    n1 (φ.symm μ) = (l : ℝ) ^ (-(1 / ((l : ℝ) - 1))) ∧
    nb (φ.symm μ) = (l : ℝ) ^ (-(1 / ((l : ℝ) - 1))) ∧
    ‖((θ (φ.symm μ) : 𝓞_ℂ_[l]) : ℂ_[l])‖ = (l : ℝ) ^ (-(1 / ((l : ℝ) - 1))) ∧
    nb ξ = (l : ℝ)⁻¹ ∧ (∀ x, nb (φ x) = nb x ^ l) ∧
    ∃ (M : ZMod d → Type) (_ : ∀ a, AddCommGroup (M a)) (_ : ∀ a, Module A (M a))
      (φM : ∀ a, M a →+ M (a + 1))
      (π : ∀ a, M a →+ ((Fin (Λ.rk g a) → 𝓞_ℂ_[l]) →ₗ[𝓞_ℂ_[l]] 𝓞_ℂ_[l]))
      (lam : ∀ a, M a →+ (Fin (Λ.r - Λ.rh - Λ.rk g a) → 𝓞_ℂ_[l]))
      (mT : Λ.Tt g → ∀ a, M a) (u : (𝓞_ℂ_[l])ˣ) (tb : Fin (Λ.r - Λ.rh) → Λ.Tt g),
      (∀ a, Module.Free A (M a) ∧ Module.Finite A (M a) ∧ Module.finrank A (M a) = Λ.r - Λ.rh) ∧
      (∀ a (c : A) (x : M a), φM a (c • x) = φ c • φM a x) ∧
      (∀ a, Function.Injective (φM a)) ∧
      (∀ a (x : M (a + 1)), φ ξ • x ∈ Submodule.span A (Set.range (φM a))) ∧
      (∀ a (x : M a), ∃ y, φM a (ξ • x) = φ ξ • y) ∧
      (∀ a (c : A) (x : M a), (∃ y, φM a x = φ ξ • y) → π a (c • x) = θ c • π a x) ∧
      (∀ a f, ∃ x : M a, (∃ y, φM a x = φ ξ • y) ∧ π a x = f) ∧
      (∀ a (x : M a), (∃ y, φM a x = φ ξ • y) → (π a x = 0 ↔ ∃ y, x = ξ • y)) ∧
      (∀ a (c : A) (x : M a), lam a (c • x) = θ c • lam a x) ∧
      (∀ a, Function.Surjective (lam a)) ∧
      (∀ a (x : M a), lam a x = 0 ↔ ∃ y, φM a x = φ ξ • y) ∧
      (∀ t t', mT (t + t') = mT t + mT t') ∧ Function.Injective mT ∧
      (∀ m : ∀ a, M a, (∀ a, φM a (m a) = φ ξ • m (a + 1)) ↔ ∃ t, mT t = m) ∧
      (∀ t a, π a (mT t a) = (u : 𝓞_ℂ_[l]) • Λ.alHT g t a) ∧
      (∀ a (x : M a), μ • x ∈ Submodule.span A (Set.range (fun t => mT t a))) ∧
      (∀ a, LinearIndependent A (fun i => mT (tb i) a) ∧
        ∀ t, mT t a ∈ Submodule.span A (Set.range (fun i => mT (tb i) a)))

abbrev LfV (N : ℕ) (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d) :=
  Σ ρ : Fin N, (Fin (Λ.rk (gρ ρ) (aρ ρ)) ⊕ Fin (Λ.rk (1 - gρ ρ) (a'ρ ρ)))

def OnLeaves {N : ℕ} (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d)
    (P : MvPolynomial (Λ.LV N) 𝓞_ℂ_[l]) : Prop :=
  ∀ μ ∈ P.support, ∀ x : Λ.LV N, μ x ≠ 0 →
    (x.2.1 = gρ x.1 ∧ x.2.2.1 = aρ x.1) ∨ (x.2.1 = 1 - gρ x.1 ∧ x.2.2.1 = a'ρ x.1)

def letterMap {N : ℕ} (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d) (x : Λ.LV N) :
    MvPolynomial (Λ.LfV N gρ aρ a'ρ) ℂ_[l] :=
  if h : x.2.1 = gρ x.1 ∧ x.2.2.1 = aρ x.1 then
    MvPolynomial.X ⟨x.1, Sum.inl (Fin.cast (by rw [← h.1, ← h.2]) x.2.2.2)⟩
  else if h' : x.2.1 = 1 - gρ x.1 ∧ x.2.2.1 = a'ρ x.1 then
    MvPolynomial.X ⟨x.1, Sum.inr (Fin.cast (by rw [← h'.1, ← h'.2]) x.2.2.2)⟩
  else 0

def coordMap (χ : Λ.Chart) {N : ℕ} (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d) (x : Λ.CV N) :
    MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l] :=
  if h : x.2.1 = gρ x.1 then
    MvPowerSeries.subst (fun k : Fin (Λ.rk x.2.1 (aρ x.1)) =>
        (MvPowerSeries.X ⟨x.1, Sum.inl (Fin.cast (by rw [h]) k)⟩ :
          MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l]))
      (Λ.tL χ x.2.1 (aρ x.1) x.2.2)
  else
    MvPowerSeries.subst (fun k : Fin (Λ.rk x.2.1 (a'ρ x.1)) =>
        (MvPowerSeries.X ⟨x.1, Sum.inr (Fin.cast (by rw [fin_two_eq_one_sub _ _ h]) k)⟩ :
          MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l]))
      (Λ.tL χ x.2.1 (a'ρ x.1) x.2.2)

def leafH {N : ℕ} (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d) :
    MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l] :=
  ∑ ρ : Fin N, MvPowerSeries.subst
    (Sum.elim (fun k => (MvPowerSeries.X ⟨ρ, Sum.inl k⟩ : MvPowerSeries (Λ.LfV N gρ aρ a'ρ) ℂ_[l]))
      (fun k => MvPowerSeries.X ⟨ρ, Sum.inr k⟩)) (Λ.hL (gρ ρ) (aρ ρ) (a'ρ ρ))

def LeafRuleLocal : Prop :=
  ∀ (χ : Λ.Chart) (N : ℕ) (gρ : Fin N → Fin 2) (aρ a'ρ : Fin N → ZMod d),
    (∀ ρ, Λ.big (gρ ρ) (aρ ρ) ∧ Λ.big (1 - gρ ρ) (a'ρ ρ) ∧ Odd (a'ρ ρ - aρ ρ).val) →
    ∀ (P : MvPolynomial (Λ.LV N) 𝓞_ℂ_[l]) (g : MvPowerSeries (Λ.CV N) 𝓞_ℂ_[l]),
      Λ.OnLeaves gρ aρ a'ρ P →
      Λ.ev χ N P g =
        jetAt0 (MvPolynomial.aeval (Λ.letterMap gρ aρ a'ρ)
            (MvPolynomial.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) P))
          (MvPowerSeries.subst (Λ.coordMap χ gρ aρ a'ρ)
              (MvPowerSeries.map (algebraMap 𝓞_ℂ_[l] ℂ_[l]) g) *
            mvExp (Λ.leafH gρ aρ a'ρ))

def AdmLoc : Prop := Λ.CartierFrobeniusFormLocal ∧ Λ.RankOneLocalSpread ∧ Λ.LieLeafVanishingLocal ∧ Λ.RankTwoLocalSpread ∧ Λ.FrobeniusNormedRingLocal ∧ Λ.LeafRuleLocal

end LocD

def RealisationStatementAll : Prop :=
  CayleyId → LPDual →
    ThmP ∧ ∃ C : ℝ, ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (Λ : LocD l d), Λ.AdmLoc →
      Λ.LemmaMAt ∧ Λ.UBAt ∧ Λ.CHAt ∧ Λ.ContentAt C

def PtCl (D : Formalism.BasicNotions.D7) (Y : ModuliIntegralCharts.Prov D) (w : Y.Dat) (l : ℕ) [Fact l.Prime] : Type :=
  Σ y : (Y.loc w l).Pt (Y.loc w l).YY,
    {e : ((Y.loc w l).fld y).C ≃+* ℂ_[l] // ∀ x, ‖e x‖ = ‖x‖}

structure Loc (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) where

  dat : ℕ → Y.Dat
  dat_rk : ∀ j, 1 ≤ j → j < D.R.m → Y.rk (dat j) = D.R.r
  dat_jj : ∀ j, 1 ≤ j → j < D.R.m → Y.jj (dat j) = D.R.k + j - 1

  Pt : D.jet.Sit → Type

  la : ∀ i, Pt i → X.PlP (D.jet.loc i).l

  ty : ∀ i, Pt i → ZMod (D.jet.loc i).d → DV.Emb D (D.jet.loc i).l
  ty_succ : ∀ i y a, ty i y (a + 1) = DV.phiPow D 1 (ty i y a)
  ty_inj : ∀ i y, Function.Injective (ty i y)

  ptE : ∀ i, D.jet.jOf i < D.R.m → Pt i ≃ PtCl D Y (dat (D.jet.jOf i)) (D.jet.loc i).l

  loc : ∀ i, Pt i → LocD (D.jet.loc i).l (D.jet.loc i).d

  loc_r : ∀ i y, (loc i y).r = D.R.r
  loc_j : ∀ i y, (loc i y).j = D.jet.jOf i
  loc_j' : ∀ i y, (loc i y).j' = D.R.m - D.jet.jOf i

  loc_big : ∀ i y a,
    ((loc i y).big 0 a ↔ ty i y a ∈ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y))) ∧
    ((loc i y).big 1 a ↔ ty i y a ∉ DV.PsiOf D (X.jC (D.jet.loc i).l (la i y)))

  loc_alt : ∀ i y, (loc i y).Alternating

  loc_rh : ∀ i (h : D.jet.jOf i < D.R.m) (y : Pt i),
    Module.finrank ℤ ((Y.loc (dat (D.jet.jOf i)) (D.jet.loc i).l).Ylat (ptE i h y).1) =
      2 * D.R.f * (loc i y).rh

variable (D : Formalism.BasicNotions.D7) (X : DivX D) (Y : ModuliIntegralCharts.Prov D) (Lc : Loc D X Y)

def adm1 : Prop := ∀ i y, (Lc.loc i y).CartierFrobeniusFormLocal ∧ (Lc.loc i y).RankOneLocalSpread

def adm2 : Prop := ∀ i y, (Lc.loc i y).LieLeafVanishingLocal

def adm3 : Prop := ∀ i y, (Lc.loc i y).RankTwoLocalSpread

def ArchimedeanSignatureMatching : Prop := CayleyId

def adm5 : Prop := ∀ i y, (Lc.loc i y).FrobeniusNormedRingLocal

def adm6 : Prop := ∀ i y, (Lc.loc i y).LeafRuleLocal

def adm7 : Prop := LPDual

def admitted : Prop :=
  adm1 D X Y Lc ∧ adm2 D X Y Lc ∧ adm3 D X Y Lc ∧ ArchimedeanSignatureMatching ∧ adm5 D X Y Lc ∧ adm6 D X Y Lc ∧ adm7

def Conclusion1 : Prop := ∀ i y, (Lc.loc i y).LemmaMAt

def Conclusion2 : Prop := ThmP

def PointsLemma : Prop := ∀ i y, (Lc.loc i y).UBAt

def Conclusion4 : Prop := ∀ i y, (Lc.loc i y).CHAt

def Conclusion5 (C : ℝ) : Prop := ∀ i y, (Lc.loc i y).ContentAt C

def Stmt (C : ℝ) : Prop :=
  admitted D X Y Lc → Conclusion1 D X Y Lc ∧ Conclusion2 ∧ PointsLemma D X Y Lc ∧ Conclusion4 D X Y Lc ∧ Conclusion5 D X Y Lc C

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
  (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
  (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (YF x hx i))

def AdmF : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i)

def Conclusion1Family : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion1 (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i)

def Conclusion3Family : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), PointsLemma (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i)

def SlopeLemmaFamily : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion4 (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i)

def SlopeLossFamily (C : ℝ) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion5 (Fm.D x i) (Fm.X x i) (YF x hx i) (LF x hx i) C

def ShareFamilyAtConstant (C : ℝ) : Prop :=
  AdmF Fm YF LF → Conclusion1Family Fm YF LF ∧ ThmP ∧ Conclusion3Family Fm YF LF ∧ SlopeLemmaFamily Fm YF LF ∧ SlopeLossFamily Fm YF LF C

def KudlaFamilyStatement (_CH : ℝ) : Prop :=
  AdmF Fm YF LF → Conclusion1Family Fm YF LF ∧ ThmP ∧ Conclusion3Family Fm YF LF ∧ SlopeLemmaFamily Fm YF LF ∧
    ∃ C : ℝ, SlopeLossFamily Fm YF LF C

end Family

def ClosedAbsoluteShare (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ C : ℝ, Formalism.MainNotions.Closed 𝒞 (fun Fm _ =>
    ∀ (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
      (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (YF x hx i)),
      ShareFamilyAtConstant Fm YF LF C)

theorem local_admissible_of_admissible {D : Formalism.BasicNotions.D7} {X : DivX D} {Y : ModuliIntegralCharts.Prov D} {Lc : Loc D X Y} (hA : admitted D X Y Lc)
    (s : D.jet.Sit) (y : Lc.Pt s) : (Lc.loc s y).AdmLoc :=
  ⟨(hA.1 s y).1, (hA.1 s y).2, hA.2.1 s y, hA.2.2.1 s y, hA.2.2.2.2.1 s y, hA.2.2.2.2.2.1 s y⟩

theorem family_statement_of_all_local (h : RealisationStatementAll) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (YF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ModuliIntegralCharts.Prov (Fm.D x i))
    (LF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Loc (Fm.D x i) (Fm.X x i) (YF x hx i)) (CH : ℝ) :
    KudlaFamilyStatement Fm YF LF CH := by
  intro hA
  obtain ⟨x0, -, hx1, -, ⟨i0⟩⟩ := Fm.toFamCore.exists_pt 0
  have hA0 := hA _ hx1 i0
  obtain ⟨hP, C, hC⟩ := h hA0.2.2.2.1 hA0.2.2.2.2.2.2
  exact ⟨fun x hx i s y => (hC _ _ _ (local_admissible_of_admissible (hA x hx i) s y)).1, hP,
    fun x hx i s y => (hC _ _ _ (local_admissible_of_admissible (hA x hx i) s y)).2.1,
    fun x hx i s y => (hC _ _ _ (local_admissible_of_admissible (hA x hx i) s y)).2.2.1, C,
    fun x hx i s y => (hC _ _ _ (local_admissible_of_admissible (hA x hx i) s y)).2.2.2⟩

theorem closed_statement_of_all_local (h : RealisationStatementAll) (h4 : CayleyId) (h7 : LPDual) (𝒞 : Formalism.MainNotions.FamClass) :
    ClosedAbsoluteShare 𝒞 := by
  obtain ⟨hP, C, hC⟩ := h h4 h7
  refine ⟨C, 1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ YF LF hA => ?_⟩⟩
  exact ⟨fun x hx i s y => (hC _ _ _ (local_admissible_of_admissible (hA x hx i) s y)).1, hP,
    fun x hx i s y => (hC _ _ _ (local_admissible_of_admissible (hA x hx i) s y)).2.1,
    fun x hx i s y => (hC _ _ _ (local_admissible_of_admissible (hA x hx i) s y)).2.2.1,
    fun x hx i s y => (hC _ _ _ (local_admissible_of_admissible (hA x hx i) s y)).2.2.2⟩

end Formalism.MainNotions.CartierLocalBounds
