import Mathlib

set_option autoImplicit false

noncomputable section

open PowerSeries

namespace JetMomFound

section FG

variable {R : Type*} [CommRing R]

def mulN (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => MvPowerSeries.subst (![mulN F n, PowerSeries.X] : Fin 2 → MvPowerSeries Unit R) F.toPowerSeries

def IsIsoGm (F : FormalGroup R) (f : PowerSeries R) : Prop :=
  constantCoeff f = 0 ∧ IsUnit (coeff 1 f) ∧
    PowerSeries.subst F.toPowerSeries f =
      (FormalGroup.𝔾ₘ : FormalGroup R).toPowerSeries.subst
        ![PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) f,
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) f]

end FG

section Padic

variable {p : ℕ} [Fact p.Prime]

def CoeffFinite (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ∃ L : IntermediateField ℚ_[p] ℂ_[p], FiniteDimensional ℚ_[p] L ∧
    ∀ m : Fin 2 →₀ ℕ, ((MvPowerSeries.coeff m F.toPowerSeries : 𝓞_ℂ_[p]) : ℂ_[p]) ∈ L

def HtOne (F : FormalGroup 𝓞_ℂ_[p]) : Prop :=
  ‖((coeff p (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = 1 ∧ ∀ k < p, ‖((coeff k (mulN F p) : 𝓞_ℂ_[p]) : ℂ_[p])‖ < 1

end Padic

def HtOneIsGm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : FormalGroup 𝓞_ℂ_[p]), CoeffFinite F → HtOne F → ∃ f : PowerSeries 𝓞_ℂ_[p], IsIsoGm F f

def RootUnique : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) (f g : MvPowerSeries σ K) (m : ℕ), 0 < m →
    MvPowerSeries.constantCoeff f = 1 → MvPowerSeries.constantCoeff g = 1 → f ^ m = g ^ m → f = g

def BimulTriv : Prop :=
  ∀ (A M : Type) [AddCommGroup A] [CommGroup M] (q : ℕ) (ze : A → A → M),
    (∀ a a' b, ze (a + a') b = ze a b * ze a' b) → (∀ a b b', ze a (b + b') = ze a b * ze a b') →
    (∀ a : A, ∃ n : ℕ, q ^ n • a = 0) → (∀ (a : A) (n : ℕ), ∃ b : A, q ^ n • b = a) → ∀ a b, ze a b = 1

def EvenHomTriv : Prop :=
  ∀ (A M : Type) [AddCommGroup A] [CommGroup M] (c : A → M), (∀ a b, c (a + b) = c a * c b) → (∀ a, c (-a) = c a) →
    (∀ a : A, ∃ b : A, (2 : ℕ) • b = a) → ∀ a, c a = 1

def substAll {σ : Type*} {p : ℕ} [Fact p.Prime] (e : PowerSeries ℂ_[p]) (G : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  MvPowerSeries.subst (fun i : σ => PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) e) G

def SolFE {σ : Type*} {p : ℕ} [Fact p.Prime] (e : PowerSeries ℂ_[p]) (ε : MvPowerSeries σ ℂ_[p]) (m : ℕ)
    (G : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff G = 1 ∧ substAll e G = G ^ m * ε

def FunEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (L : IntermediateField ℚ_[p] ℂ_[p]), FiniteDimensional ℚ_[p] L →
    ∀ (r : ℕ) (e : PowerSeries ℂ_[p]) (ε : MvPowerSeries (Fin r) ℂ_[p]) (m : ℕ),
      (∀ n, coeff n e ∈ L ∧ ‖coeff n e‖ ≤ 1) → constantCoeff e = 0 → ‖coeff 1 e‖ = 1 →
      (∀ ν, MvPowerSeries.coeff ν ε ∈ L ∧ ‖MvPowerSeries.coeff ν ε‖ ≤ 1) → MvPowerSeries.constantCoeff ε = 1 → p ∣ m →
      (∃ G, SolFE e ε m G ∧ ∀ ν, MvPowerSeries.coeff ν G ∈ L ∧ ‖MvPowerSeries.coeff ν G‖ ≤ 1) ∧ ∀ G₁ G₂, SolFE e ε m G₁ → SolFE e ε m G₂ → G₁ = G₂

def wCurve (L : PeriodPair) : WeierstrassCurve ℂ :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -(L.g₂ / 4), a₆ := -(L.g₃ / 4) }

def PAddThm : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice → z + w ∉ L.lattice →
    ∃ (h₁ : (wCurve L).toAffine.Nonsingular (L.weierstrassP z) (L.derivWeierstrassP z / 2))
      (h₂ : (wCurve L).toAffine.Nonsingular (L.weierstrassP w) (L.derivWeierstrassP w / 2))
      (h₃ : (wCurve L).toAffine.Nonsingular (L.weierstrassP (z + w)) (L.derivWeierstrassP (z + w) / 2)),
      WeierstrassCurve.Affine.Point.some _ _ h₁ + WeierstrassCurve.Affine.Point.some _ _ h₂ = WeierstrassCurve.Affine.Point.some _ _ h₃

def PParam : Prop :=
  ∀ L : PeriodPair, ∃ w : PowerSeries ℂ,
    PowerSeries.constantCoeff w = 0 ∧
    w = PowerSeries.X ^ 3 - PowerSeries.C (L.g₂ / 4) * PowerSeries.X * w ^ 2 - PowerSeries.C (L.g₃ / 4) * w ^ 3 ∧
    ∀ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ,
      let u := -(2 * L.weierstrassP z) / L.derivWeierstrassP z
      L.weierstrassP z ≠ 0 ∧ L.derivWeierstrassP z ≠ 0 ∧ HasSum (fun n => PowerSeries.coeff n w * u ^ n) (u / L.weierstrassP z)

abbrev Qb : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

def lamOf {p : ℕ} [Fact p.Prime] (lam : Qb →+* ℂ_[p]) (x : ℂ) : ℂ_[p] :=
  open Classical in if h : x ∈ Qb then lam ⟨x, h⟩ else 0

def uC (L : PeriodPair) (z : ℂ) : ℂ := -(2 * L.weierstrassP z) / L.derivWeierstrassP z

def offL (L : PeriodPair) (r : ℕ) : Set (Fin r → ℂ) := {z | ∀ i, z i ∉ L.lattice}

def IsUSer (L : PeriodPair) {r : ℕ} (f : (Fin r → ℂ) → ℂ) (S : MvPowerSeries (Fin r) ℂ) : Prop :=
  ∀ᶠ z in nhdsWithin (0 : Fin r → ℂ) (offL L r),
    HasSum (fun ν : Fin r →₀ ℕ => MvPowerSeries.coeff ν S * ∏ i, uC L (z i) ^ ν i) (f z)

def IsULaw (L : PeriodPair) (F : MvPowerSeries (Fin 2) ℂ) : Prop :=
  ∀ᶠ z in nhdsWithin (0 : Fin 2 → ℂ) {z | z 0 ∉ L.lattice ∧ z 1 ∉ L.lattice ∧ z 0 + z 1 ∉ L.lattice},
    HasSum (fun k : Fin 2 →₀ ℕ => MvPowerSeries.coeff k F * (uC L (z 0) ^ k 0 * uC L (z 1) ^ k 1)) (uC L (z 0 + z 1))

def ratC (L : PeriodPair) {r : ℕ} (A B : MvPolynomial (Fin r × Fin 2) Qb) (z : Fin r → ℂ) : ℂ :=
  MvPolynomial.eval₂ (algebraMap Qb ℂ) (fun k : Fin r × Fin 2 => if k.2 = 0 then L.weierstrassP (z k.1) else L.derivWeierstrassP (z k.1) / 2) A /
    MvPolynomial.eval₂ (algebraMap Qb ℂ) (fun k : Fin r × Fin 2 => if k.2 = 0 then L.weierstrassP (z k.1) else L.derivWeierstrassP (z k.1) / 2) B

def shiftSer {p : ℕ} [Fact p.Prime] {r : ℕ} (F : MvPowerSeries (Fin 2) ℂ_[p]) (y : Fin r → ℂ_[p]) (i : Fin r) :
    MvPowerSeries (Fin r) ℂ_[p] :=
  fun μ => open Classical in if μ = Finsupp.single i (μ i) then
    ∑' b : ℕ, MvPowerSeries.coeff (Finsupp.single 0 (μ i) + Finsupp.single 1 b) F * y i ^ b else 0

def yAt {p : ℕ} [Fact p.Prime] (lam : Qb →+* ℂ_[p]) (L : PeriodPair) {r : ℕ} (yt : Fin r → ℂ) (i : Fin r) : ℂ_[p] :=
  open Classical in if yt i ∈ L.lattice then 0 else lamOf lam (uC L (yt i))

def TransferTR : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (lam : Qb →+* ℂ_[p]) (L : PeriodPair), L.g₂ ∈ Qb → L.g₃ ∈ Qb →
    ‖lamOf lam (L.g₂ / 4)‖ ≤ 1 → ‖lamOf lam (L.g₃ / 4)‖ ≤ 1 → ‖lamOf lam (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)‖ = 1 →
    ∀ F : MvPowerSeries (Fin 2) ℂ, IsULaw L F →
    ∀ (r : ℕ) (A B : MvPolynomial (Fin r × Fin 2) Qb) (yt : Fin r → ℂ),
      (∃ N : ℕ, 0 < N ∧ ∀ i, (N : ℂ) * yt i ∈ L.lattice) →
      (∀ i, yt i ∈ L.lattice ∨ 1 < ‖lamOf lam (L.derivWeierstrassP (yt i) / 2)‖) →
    ∀ S Sy : MvPowerSeries (Fin r) ℂ, IsUSer L (ratC L A B) S → IsUSer L (fun z => ratC L A B (z + yt)) Sy →
      (∀ k, MvPowerSeries.coeff k F ∈ Qb) ∧ (∀ ν, MvPowerSeries.coeff ν S ∈ Qb) ∧ (∀ ν, MvPowerSeries.coeff ν Sy ∈ Qb) ∧
      ((∃ C : ℝ, ∀ ν, ‖lamOf lam (MvPowerSeries.coeff ν S)‖ ≤ C) →
        ∀ μ, HasSum (fun ν : Fin r →₀ ℕ => lamOf lam (MvPowerSeries.coeff ν S) *
            MvPowerSeries.coeff μ (∏ i, shiftSer ((fun k : Fin 2 →₀ ℕ => lamOf lam (MvPowerSeries.coeff k F)) : MvPowerSeries (Fin 2) ℂ_[p]) (yAt lam L yt) i ^ ν i))
          (lamOf lam (MvPowerSeries.coeff μ Sy)))

end JetMomFound
