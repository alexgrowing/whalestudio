import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric

noncomputable section

namespace Formalism.MainNotions.GL3Theta

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric

def Wp (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  (Subring.closure {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}).topologicalClosure

def InWf {p : ℕ} [Fact p.Prime] (x : ℂ_[p]) : Prop := ∃ k : ℕ, (p : ℂ_[p]) ^ k * x ∈ Wp p

def IntegralW {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, MvPowerSeries.coeff n F ∈ Wp p

def CoefWf {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : Prop :=
  ∀ n, InWf (MvPowerSeries.coeff n F)

def logMv {σ : Type*} {p : ℕ} [Fact p.Prime] (F : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    if n = 0 then 0 else (-1 : ℂ_[p]) ^ (n + 1) * MvPowerSeries.coeff α ((F - 1) ^ n) / (n : ℂ_[p])

def Simeq {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralMv (expMv (f - g))

def SimeqW {σ : Type*} {p : ℕ} [Fact p.Prime] (f g : MvPowerSeries σ ℂ_[p]) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ IntegralW (expMv (f - g))

def tauK (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.K) : ℂ_[p] :=
  lamC lam (D.host.φ₀ (a : D.host.E))

def tauKc (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (a : D.host.K) : ℂ_[p] :=
  lamC lam (D.host.φ₀ (D.host.conj (a : D.host.E)))

def OKp (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun a : 𝓞 D.host.K => (tauK D lam (a : D.host.K), tauKc D lam (a : D.host.K)))

def hP {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] (x y : ι → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

def IsModelU {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  let W := C • wModel lam Λ
  IsIntP W.a₁ ∧ IsIntP W.a₂ ∧ IsIntP W.a₃ ∧ IsIntP W.a₄ ∧ IsIntP W.a₆ ∧ ‖W.Δ‖ = 1

theorem IsModel.toU {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {Λ : AddSubgroup ℂ}
    {C : WeierstrassCurve.VariableChange ℂ_[p]} (h : IsModel lam Λ C) : IsModelU lam Λ C := by
  obtain ⟨h1, h2, h3, h4, h6, hd⟩ := h
  show IsIntP _ ∧ IsIntP _ ∧ IsIntP _ ∧ IsIntP _ ∧ IsIntP _ ∧ ‖_‖ = 1
  exact ⟨h1, h2, h3, h4, h6, by first | rw [hd, norm_one] | simp [hd]⟩

def ModelOverW {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
    (C : WeierstrassCurve.VariableChange ℂ_[p]) : Prop :=
  let W := C • wModel lam Λ
  W.a₁ ∈ Wp p ∧ W.a₂ ∈ Wp p ∧ W.a₃ ∈ Wp p ∧ W.a₄ ∈ Wp p ∧ W.a₆ ∈ Wp p

structure G1 (p : ℕ) [Fact p.Prime] where
  lam : Qbar →+* ℂ_[p]
  abelian₂ : AddSubgroup ℂ
  C : WeierstrassCurve.VariableChange ℂ_[p]
  wq : PowerSeries ℂ_[p]
  ex : PowerSeries ℂ_[p]

namespace G1

variable {p : ℕ} [Fact p.Prime] (g : G1 p)

def W : WeierstrassCurve ℂ_[p] := g.C • wModel g.lam g.abelian₂

def l : PowerSeries ℂ_[p] := flog g.W g.wq

def Ok : Prop :=
  IsModelU g.lam g.abelian₂ g.C ∧ IsWq g.W g.wq ∧
    PowerSeries.constantCoeff g.ex = 0 ∧ PowerSeries.subst g.ex g.l = PowerSeries.X

def ph : PowerSeries ℂ_[p] := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)

variable {σ : Type*}

def lg (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a g.l

def pt (x : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst x g.ex

def add (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := g.pt (g.lg a + g.lg b)

def sub (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := g.pt (g.lg a - g.lg b)

def mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  g.pt (MvPowerSeries.C c * g.lg a)

def lin {ι : Type*} [Fintype ι] (c : ι → ℂ_[p]) (a : ι → MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries σ ℂ_[p] :=
  g.pt (∑ j, MvPowerSeries.C (c j) * g.lg (a j))

def phAt (a : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] := PowerSeries.subst a g.ph

def be (a b : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  g.phAt (g.add a b) - g.phAt a - g.phAt b

end G1

def At (D : D7) {p : ℕ} [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p) : Prop :=
  IsCurveIdeal D cc ∧ Nat.Coprime (Ideal.absNorm cc) p ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧
    g.abelian₂ = lamOf D cc δ ∧ g.Ok

abbrev Xv {p : ℕ} [Fact p.Prime] {σ : Type*} (i : σ) : MvPowerSeries σ ℂ_[p] := MvPowerSeries.X i

def SplitK (D : D7) (p : ℕ) : Prop := jacobiSym (-(D.host.d : ℤ)) p = 1

def InertK (D : D7) (p : ℕ) : Prop := jacobiSym (-(D.host.d : ℤ)) p = -1

def modelEx (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ),
    IsCurveIdeal D cc → Nat.Coprime (Ideal.absNorm cc) p → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    (∃ C, IsModelU lam (lamOf D cc δ) C) ∧
    (5 ≤ p → InertK D p → ∃ C, IsModelU lam (lamOf D cc δ) C ∧ ModelOverW lam (lamOf D cc δ) C) ∧
    ∀ C, IsModelU lam (lamOf D cc δ) C → ‖((C.u : ℂ_[p]ˣ) : ℂ_[p])‖ = 1

def cube2 (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    Simeq (g.phAt (g.add (Xv 0) (Xv 1)) + g.phAt (g.sub (Xv 0) (Xv 1)) : MvPowerSeries (Fin 2) ℂ_[p])
      (2 * g.phAt (Xv 0) + 2 * g.phAt (Xv 1))

def cube3 (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) + g.phAt (g.sub (Xv 0) (Xv 1)) +
        g.phAt (g.sub (Xv 1) (Xv 2)) + g.phAt (g.sub (Xv 2) (Xv 0)) : MvPowerSeries (Fin 3) ℂ_[p])
      (3 * (g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2)))

def cube (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    Simeq (g.phAt (g.add (g.add (Xv 0) (Xv 1)) (Xv 2)) - g.phAt (g.add (Xv 0) (Xv 1)) -
        g.phAt (g.add (Xv 1) (Xv 2)) - g.phAt (g.add (Xv 2) (Xv 0)) +
        g.phAt (Xv 0) + g.phAt (Xv 1) + g.phAt (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p]) 0

def beBiadd (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    Simeq (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2))

def addInt (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    (ModelOverW g.lam g.abelian₂ g.C → IntegralW (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))

def endInt (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    ∀ α ∈ OKp D g.lam, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

def phNorm (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ α ∈ OKp D g.lam,
      Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ()))

def beConj (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ α ∈ OKp D g.lam,
      Simeq (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))

def splitZero (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    SplitK D p →
      Simeq (g.be (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) 0 ∧
      Simeq (g.phAt (Xv ()) : MvPowerSeries Unit ℂ_[p]) 0

def beDiag (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    (∀ γ ∈ OKp D g.lam,
      Simeq (2 * g.be (Xv ()) (g.mulBy γ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (γ.1 + γ.2) * g.be (Xv ()) (Xv ()))) ∧
    Simeq (g.be (Xv ()) (Xv ()) : MvPowerSeries Unit ℂ_[p]) (2 * g.phAt (Xv ()))

def ser1 {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (G : ℂ → ℂ) : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => lamC lam (iteratedDeriv n G 0 / (n.factorial : ℂ))

def G1.atU {p : ℕ} [Fact p.Prime] (g : G1 p) (G : ℂ → ℂ) : PowerSeries ℂ_[p] :=
  PowerSeries.subst (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * g.l)
    (ser1 g.lam G)

def Tors1 (p : ℕ) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  t ∉ Λ ∧ ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ (n : ℂ) * t ∈ Λ

def transl (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    ∀ t : ℂ, Tors1 p g.abelian₂ t →
      IntegralMv ((ePhi1 g.lam g.abelian₂ g.C g.wq)⁻¹ * g.atU (U1 g.abelian₂ t (sgStar g.abelian₂))) ∧
      ‖PowerSeries.constantCoeff (g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)))‖ = 1

def IsTwoTorsionPointUnkilled (D : D7) (Λ : AddSubgroup ℂ) (t : ℂ) : Prop :=
  2 * t ∈ Λ ∧ ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ ∧
    ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * t ∉ Λ

def th0 (Λ : AddSubgroup ℂ) (t0 : ℂ) : ℂ → ℂ :=
  fun z => U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0

def atTwo (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 2), At D cc δ g →
    ∀ t0 : ℂ, IsTwoTorsionPointUnkilled D g.abelian₂ t0 →
      Simeq (-logMv (g.atU (th0 g.abelian₂ t0)) : MvPowerSeries Unit ℂ_[2]) 0 ∧
      ∀ t : ℂ, Tors1 2 g.abelian₂ t → IntegralMv (g.atU (U1 g.abelian₂ t (th0 g.abelian₂ t0))) ∧
        ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ n, ‖PowerSeries.coeff n (g.atU (U1 g.abelian₂ t (th0 g.abelian₂ t0)))‖ ≤ ρ

def G1.jetPh {p : ℕ} [Fact p.Prime] (g : G1 p) (i : ℕ) : ℂ_[p] :=
  (i.factorial : ℂ_[p]) * PowerSeries.coeff i (PowerSeries.subst g.ex g.ph : PowerSeries ℂ_[p])

def jetsPh (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    (∀ i, i ≠ 2 → IsIntP (g.jetPh i)) ∧
    (∀ α ∈ OKp D g.lam, IsIntP ((α.1 - α.2) * g.jetPh 2)) ∧
    (p ≠ D.host.d → IsIntP (g.jetPh 2)) ∧
    (p = D.host.d → ‖g.jetPh 2‖ ≤ (p : ℝ) ^ ((1 : ℝ) / 2))

def InOKp (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {ι : Type*}
    (x : ι → ℂ_[p] × ℂ_[p]) : Prop := ∀ k, x k ∈ OKp D lam

def G1.PhOn {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) (fun e => Xv e))

def Primitive (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {n r : ℕ}
    (b : Fin r → Fin n → ℂ_[p] × ℂ_[p]) : Prop :=
  ∃ (M M' : Matrix (Fin n) (Fin n) (ℂ_[p] × ℂ_[p])) (f : Fin r → Fin n),
    (∀ i, InOKp D lam (M i)) ∧ (∀ i, InOKp D lam (M' i)) ∧ M * M' = 1 ∧ Function.Injective f ∧
    ∀ e k, M k (f e) = b e k

def PhUnitary (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ (n : ℕ) (de : Fin n → Fin n → ℂ_[p] × ℂ_[p]), (∀ j, InOKp D g.lam (de j)) →
      (∀ i j, hP (de i) (de j) = if i = j then 1 else 0) →
      Simeq (g.PhOn de) (∑ k, g.phAt (Xv k))

def PhIsotropic (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ (n r : ℕ) (b : Fin r → Fin n → ℂ_[p] × ℂ_[p]), (∀ e, InOKp D g.lam (b e)) →
      Primitive D g.lam b → (∀ e e', hP (b e) (b e') = 0) →
      Simeq (g.PhOn b) 0

def DualIso {p : ℕ} [Fact p.Prime] {κ ι : Type*} [Fintype κ] (b b' : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e e', hP (b e) (b e') = 0) ∧ (∀ e e', hP (b' e) (b' e') = 0) ∧
    ∀ e e', hP (b e) (b' e') = if e = e' then 1 else 0

def G1.beSum {p : ℕ} [Fact p.Prime] (g : G1 p) (ι : Type*) [Fintype ι] : MvPowerSeries (ι ⊕ ι) ℂ_[p] :=
  ∑ e : ι, g.be (Xv (Sum.inl e)) (Xv (Sum.inr e))

def PhDual (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g → p ≠ 2 →
    ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (b b' : ι → κ → ℂ_[p] × ℂ_[p]), (∀ e, InOKp D g.lam (b e)) →
      (∀ e, InOKp D g.lam (b' e)) → DualIso b b' →
      Simeq (g.PhOn (Sum.elim b b')) (g.beSum ι)

abbrev Idx (D : D7) (N N' : ℕ) : Type := D.what₂.Tau × Fin N' × Fin N

def embP (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (y : Matrix (Fin N') (Fin N) D.host.E) : Idx D N N' → ℂ_[p] × ℂ_[p] :=
  fun k => (lamC lam (embT D k.1 (y k.2.1 k.2.2)), lamC lam (embT D k.1 (D.host.conj (y k.2.1 k.2.2))))

def YYp (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    Set (Idx D N N' → ℂ_[p] × ℂ_[p]) :=
  closure (embP D lam '' (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)))

def BasisP (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {κ ι : Type*} [Fintype ι]
    (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e, b e ∈ Y) ∧ ∀ y ∈ Y, ∃! c : ι → ℂ_[p] × ℂ_[p], InOKp D lam c ∧ y = fun k => ∑ e, c e * b e k

def G1.atLogP {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι : Type*} [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) (F : MvPowerSeries κ ℂ_[p]) : MvPowerSeries ι ℂ_[p] :=
  MvPowerSeries.subst (fun k : κ => ∑ e, MvPowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (b e k).1) *
    g.lg (Xv e)) F

def G1.ePhI {p : ℕ} [Fact p.Prime] (g : G1 p) (ι : Type) [Fintype ι] : MvPowerSeries ι ℂ_[p] :=
  if p = 2 then 1 else
    ∏ i : ι, (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries ι ℂ_[p]) (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹

theorem G1.ePhI_fin {p : ℕ} [Fact p.Prime] (g : G1 p) (r : ℕ) :
    g.ePhI (Fin r) = ePh g.lam g.abelian₂ g.C g.wq r := rfl

def intOrtho (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), At D cc δ g → p ≠ D.host.d →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : MvPowerSeries (Idx D N N') ℂ_[p]),
      admitted D N N' L L' → IsComb D (tor0 D cc δ) e g.lam L L' F →
      ∀ (ι : Type) [Fintype ι] (b : ι → Idx D N N' → ℂ_[p] × ℂ_[p]), BasisP D g.lam (YYp D g.lam L L') b →
        (∀ i j, hP (b i) (b j) = if i = j then 1 else 0) →
        IntegralMv (g.atLogP b F * g.ePhI ι)

def intHyp (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), At D cc δ g → p ≠ D.host.d → p ≠ 2 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (F : MvPowerSeries (Idx D N N') ℂ_[p]),
      admitted D N N' L L' → IsComb D (tor0 D cc δ) e g.lam L L' F →
      ∀ (ι : Type) [Fintype ι] (b b' : ι → Idx D N N' → ℂ_[p] × ℂ_[p]),
        BasisP D g.lam (YYp D g.lam L L') (Sum.elim b b') → DualIso b b' →
        IntegralMv (g.atLogP (Sum.elim b b') F * expMv (g.beSum ι))

def prim (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (g : G1 p), At D cc δ g → p ≠ D.host.d →
    ∀ (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (t : VC D N N'), admitted D N N' L L' → admitted D N N' L₁ L₁' →
      EqAt D p L L₁ → EqAt D p L' L₁' → TorsPrime D p (La D (tor0 D cc δ) L L') t →
      ∀ (ι : Type) [Fintype ι] (b : ι → Idx D N N' → ℂ_[p] × ℂ_[p]), BasisP D g.lam (YYp D g.lam L L') b →
        (∀ i j, hP (b i) (b j) = if i = j then 1 else 0) →
        IntegralMv (g.atLogP b (pSer D g.lam (U D (tor0 D cc δ) t (e N N' L₁ L₁'))) * g.ePhI ι) ∧
        ¬ ∃ ρ : ℝ, ρ < 1 ∧ ∀ n, ‖MvPowerSeries.coeff n
          (g.atLogP b (pSer D g.lam (U D (tor0 D cc δ) t (e N N' L₁ L₁'))) * g.ePhI ι)‖ ≤ ρ

def orthoEx (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ D.host.d →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∃ (r : ℕ) (b : Fin r → Idx D N N' → ℂ_[p] × ℂ_[p]), BasisP D lam (YYp D lam L L') b ∧
        ∀ i j, hP (b i) (b j) = if i = j then 1 else 0

def phW (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C → CoefWf g.ph

def readW : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f : MvPowerSeries σ ℂ_[p]), CoefWf f → Simeq f 0 → SimeqW f 0

def logF (p : ℕ) [Fact p.Prime] : PowerSeries ℂ_[p] :=
  PowerSeries.mk fun n => ∑ j ∈ Finset.range (n + 1), if n = p ^ (2 * j) then ((p : ℂ_[p]) ^ j)⁻¹ else 0

def isoF (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∃ ep : ℂ_[p], ep ∈ Wp p ∧ ‖ep‖ = 1 ∧
      IntegralW (g.pt (MvPowerSeries.C (((g.C.u : ℂ_[p]ˣ) : ℂ_[p]) * ep) * logF p) :
        MvPowerSeries Unit ℂ_[p])

def G1.thF {p : ℕ} [Fact p.Prime] (g : G1 p) (ep : ℂ_[p]) {σ : Type*} (k : σ) : MvPowerSeries σ ℂ_[p] :=
  g.pt (MvPowerSeries.C (((g.C.u : ℂ_[p]ˣ) : ℂ_[p]) * ep) * PowerSeries.subst (Xv k) (logF p))

def endIntW (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∀ α ∈ OKp D g.lam, IntegralW (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])

def beW (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    CoefWf (g.be (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    SimeqW (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)) ∧
    SimeqW (g.be (Xv 0) (g.add (Xv 1) (Xv 2)) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 1) + g.be (Xv 0) (Xv 2)) ∧
    ∀ α ∈ OKp D g.lam,
      SimeqW (g.be (g.mulBy α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
        (g.be (Xv 0) (g.mulBy α.2 (Xv 1)))

def PhDualW (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∀ (κ ι : Type) [Fintype κ] [Fintype ι] (b b' : ι → κ → ℂ_[p] × ℂ_[p]), (∀ e, InOKp D g.lam (b e)) →
      (∀ e, InOKp D g.lam (b' e)) → DualIso b b' →
      CoefWf (g.PhOn (Sum.elim b b')) ∧ SimeqW (g.PhOn (Sum.elim b b')) (g.beSum ι)

def modelShort (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ),
    IsCurveIdeal D cc → Nat.Coprime (Ideal.absNorm cc) p → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → 5 ≤ p →
    (∃ C, IsModelU lam (lamOf D cc δ) C ∧ (C • wModel lam (lamOf D cc δ)).a₁ = 0 ∧
      (C • wModel lam (lamOf D cc δ)).a₂ = 0 ∧ (C • wModel lam (lamOf D cc δ)).a₃ = 0) ∧
    (InertK D p → ∃ C, IsModelU lam (lamOf D cc δ) C ∧ ModelOverW lam (lamOf D cc δ) C ∧
      (C • wModel lam (lamOf D cc δ)).a₁ = 0 ∧ (C • wModel lam (lamOf D cc δ)).a₂ = 0 ∧
      (C • wModel lam (lamOf D cc δ)).a₃ = 0)

def phEven (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    g.W.a₁ = 0 → g.W.a₃ = 0 →
    (g.mulBy (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = -Xv () ∧
    (g.phAt (-Xv ()) : MvPowerSeries Unit ℂ_[p]) = g.phAt (Xv ())

def serA (p : ℕ) [Fact p.Prime] : MvPowerSeries (Fin 2) ℂ_[p] :=
  fun n => ∑ i ∈ Finset.range (n 0 + 1), ∑ j ∈ Finset.range (n 1 + 1),
    if i ≤ j ∧ n 0 = p ^ (2 * i) ∧ n 1 = p * p ^ (2 * j) then ((p : ℂ_[p]) ^ (i + j + 1))⁻¹ else 0

def serB (p : ℕ) [Fact p.Prime] : MvPowerSeries (Fin 2) ℂ_[p] :=
  fun n => ∑ i ∈ Finset.range (n 1 + 1), ∑ j ∈ Finset.range (n 0 + 1),
    if i ≤ j ∧ n 1 = p ^ (2 * i) ∧ n 0 = p * p ^ (2 * j) then ((p : ℂ_[p]) ^ (i + j + 1))⁻¹ else 0

def beGc (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : G1 p), At D cc δ g →
    5 ≤ p → InertK D p → ModelOverW g.lam g.abelian₂ g.C →
    ∀ ep : ℂ_[p], ep ∈ Wp p → ‖ep‖ = 1 → IntegralW (g.thF ep () : MvPowerSeries Unit ℂ_[p]) →
      ∃ c : ℂ_[p], (c, -c) ∈ OKp D g.lam ∧
        SimeqW (g.be (g.thF ep 0) (g.thF ep 1) : MvPowerSeries (Fin 2) ℂ_[p])
          (MvPowerSeries.C c * (serA p + serB p))

def W2pair (p : ℕ) [Fact p.Prime] : Set (ℂ_[p] × ℂ_[p]) :=
  closure (Subring.closure {x : ℂ_[p] × ℂ_[p] | ∃ ζ : ℂ_[p], ζ ^ (p ^ 2 - 1) = 1 ∧ x = (ζ, ζ ^ p)} :
    Set (ℂ_[p] × ℂ_[p]))

def okpInert (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → InertK D p → OKp D lam = W2pair p

def supH (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ x ∈ La D (tor0 D cc δ) L L', x ≠ 0 → 2 / Real.sqrt D.host.d ≤ (Hf D (tor0 D cc δ) x x).re

def iopUnitary (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (N N' : ℕ) (L₁ L₂ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₁' L₂' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' →
      ∀ th ∈ Th D (tor0 D cc δ) L₁ L₁',
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) L₂ L₂') th ∈
          Th D (tor0 D cc δ) L₂ L₂' ∧
        normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L₂ L₂')
            (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) L₂ L₂') th) =
          normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') th ∧
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₂ L₂') (La D (tor0 D cc δ) L₁ L₁')
            (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) L₂ L₂') th) = th

def PUnit (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (z : D.host.E) : Prop :=
  ∀ s : D.R.GG, ‖lamC lam (D.host.emb s z)‖ = 1

def PowRat (D : D7) (t : D.Dt) (h : ℕ) (z : letI := D.host.cmStar; unitary D.host.E) : Prop :=
  0 < h ∧ ∃ k ∈ D.UO, t ^ h = D.e1Dt z * k

def chiMod1 (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (t : D.Dt) (h : ℕ) (z : unitary D.host.E), PowRat D t h z →
    ∃ hx : ((D.chiD t : ℂˣ) : ℂ) ∈ Qbar, ∀ ρ : Qbar →+* ℂ, ‖ρ ⟨((D.chiD t : ℂˣ) : ℂ), hx⟩‖ = 1

def chiUnitInert (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → InertK D p →
    ∀ (t : D.Dt) (h : ℕ) (z : unitary D.host.E), PowRat D t h z →
      ‖lamC lam ((D.chiD t : ℂˣ) : ℂ)‖ = 1

def chiVal (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (t : D.Dt) (h : ℕ) (z : unitary D.host.E), PowRat D t h z →
    ((D.chiD t : ℂˣ) : ℂ) ^ h = ∏ τ, (embT D τ (z : D.host.E))⁻¹ ∧
    ‖lamC lam ((D.chiD t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖⁻¹

def PowRatAll (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ t : D.Dt, ∃ (h : ℕ) (z : unitary D.host.E), PowRat D t h z

def NormOnePowerPrincipal (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ 𝔞 : IdE D, N1 D 𝔞 → ∃ (h : ℕ) (z : unitary D.host.E), 0 < h ∧
    𝔞 ^ h = Submodule.span (𝓞 D.host.E) {(z : D.host.E)}

theorem idl_pow {D : D7} {idl : D.Dt ⧸ D.UO → IdE D} (hm : ∀ x y, idl (x * y) = idl x * idl y)
    (x : D.Dt ⧸ D.UO) : ∀ n : ℕ, idl (x ^ (n + 1)) = idl x ^ (n + 1)
  | 0 => by simp
  | n + 1 => by rw [pow_succ, hm, idl_pow hm x n, ← pow_succ]

theorem powRatAll_of (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : RelDetPinned D idl) (hn : NormOnePowerPrincipal D) :
    PowRatAll D := by
  obtain ⟨hinj, hN1, hm, hz, -⟩ := h
  intro t
  obtain ⟨n, z, hn, hnz⟩ := hn (idl (QuotientGroup.mk t)) ((hN1 _).2 ⟨_, rfl⟩)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hq : (QuotientGroup.mk (D.e1Dt z) : D.Dt ⧸ D.UO) = QuotientGroup.mk (t ^ (m + 1)) := by
    apply hinj
    rw [hz, ← hnz, QuotientGroup.mk_pow, idl_pow hm]
  refine ⟨m + 1, z, ?_⟩
  unfold PowRat
  exact ⟨hn, (D.e1Dt z)⁻¹ * t ^ (m + 1), QuotientGroup.eq.mp hq, (mul_inv_cancel_left _ _).symm⟩

def rhoOf (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : D.Dt →* ℂˣ :=
  (mt (i + 1))⁻¹ * D.chiD ^ (-(((D.R.N (i + 1)) / 2 : ℕ) : ℤ))

def rhoOf' (D : D7) (mt : ℕ → D.Dt →* ℂˣ) (i : ℕ) : D.Dt →* ℂˣ :=
  mt (i + 1) * D.chiD ^ ((((D.R.N i) / 2 : ℕ) : ℤ))

def rhoCh (D : D7) (i : ℕ) : D.Dt →* ℂˣ := rhoOf D D.muTil i

def rhoCh' (D : D7) (i : ℕ) : D.Dt →* ℂˣ := rhoOf' D D.muTil i

def CarriesTupleCharacters (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (dt : ∀ i, C.cls i → D.Dt) : Prop :=
  ∀ i < D.R.m, (∀ c, C.rhoDet i c = ((rhoOf D mt i (dt i c) : ℂˣ) : ℂ)) ∧
    ∀ c, C.rhoDet' i c = ((rhoOf' D mt i (dt (i + 1) c) : ℂˣ) : ℂ)

theorem rhoDet_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (c : (D.mem u).C.cls i) :
    (D.mem u).C.rhoDet i c = ((rhoCh D i (D.detCls u i c) : ℂˣ) : ℂ) := by
  exact D.rhoDet_eq_inv_muTilde_chiD_pow u i c

theorem rhoDet'_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (c : (D.mem u).C.cls (i + 1)) :
    (D.mem u).C.rhoDet' i c = ((rhoCh' D i (D.detCls u (i + 1) c) : ℂˣ) : ℂ) := by
  exact D.rhoDetPrime_eq_muTilde_mul_chi_pow u i c

theorem member_chain_has_characters (D : D7) (u : D.what₂.Word) : CarriesTupleCharacters D (D.mem u).C D.muTil (D.detCls u) := by
  intro i _
  exact ⟨fun c => rhoDet_eq D u i c, fun c => rhoDet'_eq D u i c⟩

def Mod1E (x : ℂ) : Prop := ∃ hx : x ∈ Qbar, ∀ ρ : Qbar →+* ℂ, ‖ρ ⟨x, hx⟩‖ = 1

def rhoThreeOf (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ i < D.R.m,
    (∀ (t : D.Dt) (h : ℕ) (z : unitary D.host.E), PowRat D t h z →
      Mod1E ((rhoOf D mt i t : ℂˣ) : ℂ) ∧ Mod1E ((rhoOf' D mt i t : ℂˣ) : ℂ)) ∧
    (∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf D mt i k ^ n = 1 ∧ rhoOf' D mt i k ^ n = 1) ∧
    (∀ z : unitary D.host.E,
      ((rhoOf D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (-C.sSharp i τ) ∧
      ((rhoOf' D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (C.sDiv i τ))

def rhoThree (D : D7) : Prop := ∀ u : D.what₂.Word, rhoThreeOf D (D.mem u).C D.muTil

theorem lift_eqC (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ)
    (dt : ∀ i, C.cls i → D.Dt) (h : CarriesTupleCharacters D C mt dt) (i : ℕ) (hi : i < D.R.m) (φ : C.cls i → C.Y i → ℂ)
    (c' : C.cls (i + 1)) :
    C.K i φ c' = ∑ c, (((Nat.card (C.stab i c) : ℕ) : ℂ)⁻¹) •
      ((((rhoOf D mt i (dt i c) : ℂˣ) : ℂ) * ((rhoOf' D mt i (dt (i + 1) c') : ℂˣ) : ℂ)) •
        C.divDe i (C.unf i c c' (C.sharp i (φ c)))) := by
  obtain ⟨h1, h2⟩ := h i hi
  simp only [Formalism.BasicNotions.ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, Formalism.BasicNotions.ColumnChain.Kmap, Formalism.BasicNotions.ColumnChain.wt,
    LinearMap.smul_apply, LinearMap.comp_apply, h1, h2]

theorem lift_eq (D : D7) (u : D.what₂.Word) (i : ℕ) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)
    (c' : (D.mem u).C.cls (i + 1)) :
    (D.mem u).C.K i φ c' = ∑ c, (((Nat.card ((D.mem u).C.stab i c) : ℕ) : ℂ)⁻¹) •
      ((((rhoCh D i (D.detCls u i c) : ℂˣ) : ℂ) * ((rhoCh' D i (D.detCls u (i + 1) c') : ℂˣ) : ℂ)) •
        (D.mem u).C.divDe i ((D.mem u).C.unf i c c' ((D.mem u).C.sharp i (φ c)))) := by
  simp only [Formalism.BasicNotions.ColumnChain.K, Formalism.ThetaLiftIndependence.kerOpM, Formalism.BasicNotions.ColumnChain.Kmap, Formalism.BasicNotions.ColumnChain.wt,
    LinearMap.smul_apply, LinearMap.comp_apply, rhoDet_eq, rhoDet'_eq]

def applyAt0 (D : D7) {N N' : ℕ} (P : MvPolynomial (Idx D N N') ℂ) (G : VC D N N' → ℂ) : ℂ :=
  ∑ α ∈ P.support, MvPolynomial.coeff α P * (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α

abbrev FrV (D : D7) (N : ℕ) : Type := D.what₂.Tau × Fin N × Fin N

def evFr (D : D7) {N : ℕ} (Q : MvPolynomial (FrV D N) ℂ) (y : D.what₂.Tau → Matrix (Fin N) (Fin N) ℂ) : ℂ :=
  MvPolynomial.eval (fun k : FrV D N => y k.1 k.2.1 k.2.2) Q

def polD (D : D7) {N N' : ℕ} (s : D.what₂.Tau → ℂ) (Q : MvPolynomial (FrV D N) ℂ)
    (y' : D.what₂.Tau → Matrix (Fin N') (Fin N') ℂ) : MvPolynomial (Idx D N N') ℂ :=
  MvPolynomial.aeval (fun k : FrV D N => ∑ b : Fin N',
    MvPolynomial.C (s k.1 * (if h : (k.2.2 : ℕ) < N' then y' k.1 b ⟨k.2.2, h⟩ else 0)) *
      MvPolynomial.X ((k.1, b, k.2.1) : Idx D N N')) Q

def IsKer (D : D7) (T : Tor D) (e : FamE D) (S : Finset ℕ) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (Θ : VC D N N' → ℂ) : Prop :=
  ∃ (n : ℕ) (r : Fin n → ℂ) (t : Fin n → VC D N N'),
    (∀ k, r k ∈ Qbar) ∧
    (∀ k (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → ‖lamC lam (r k)‖ ≤ 1) ∧
    (∀ k, ∃ a : ℕ, 0 < a ∧ (∀ q : ℕ, q.Prime → q ∣ a → q ∈ S) ∧ a • t k ∈ La D T L L') ∧
    Θ = fun z => ∑ k, r k * U D T (t k) (e N N' L L') z

structure LiftObj (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) where
  mt : ℕ → D.Dt →* ℂˣ
  L0 : ∀ i, (letI := D.host.cmStar; SDLat D.host.E (D.R.N i))
  lattice_integral_coordinates : ∀ i (x : Fin (D.R.N i) → D.host.E), x ∈ (L0 i).1 ↔ ∀ k, IsIntegral ℤ (x k)
  lat : ∀ i, C.cls i → (letI := D.host.cmStar; SDLat D.host.E (D.R.N i))
  dt : ∀ i, C.cls i → D.Dt
  dt_lat : ∀ i c, (QuotientGroup.mk (dt i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) (L0 i) (lat i c)
  c13 : CarriesTupleCharacters D C mt dt
  frm : ∀ i, C.Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ
  frm_inj : ∀ i ≤ D.R.m, Function.Injective (frm i)
  frm_range : ∀ i ≤ D.R.m, ∀ f : D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ,
    (∃ y, frm i y = f) ↔ ∀ τ, (f τ).det ≠ 0
  frm_de : ∀ i ≤ D.R.m, ∀ y τ, C.de i y τ = (frm i y τ).det
  dgen : D.what₂.Tau → ℂ
  dgen_gen : ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M), (∀ τ x, embT D τ x ∈ M) ∧ ∀ τ, ∃ s : M, (s : ℂ) = dgen τ ∧
    ellT D M τ = Submodule.span (𝓞 M) {s}
  S : Finset ℕ
  Th : ∀ i, C.cls i → C.cls (i + 1) → VC D (D.R.N i) (D.R.N (i + 1)) → ℂ

def liftTie (D : D7) (T : Tor D) (e : FamE D) {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)}
    (O : LiftObj D C) (i : ℕ) : Prop :=
  (∀ c c', IsKer D T e O.S (O.lat i c).1 (O.lat (i + 1) c').1 (O.Th i c c')) ∧
  ∀ c c' (Q : MvPolynomial (FrV D (D.R.N i)) ℂ) (y' : C.Y (i + 1)),
    C.unf i c c' (fun y => evFr D Q (O.frm i y)) y' =
      applyAt0 D (polD D O.dgen Q (O.frm (i + 1) y')) (O.Th i c c')

theorem lift_formula (D : D7) (T : Tor D) (e : FamE D) {u : D.what₂.Word}
    {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} (O : LiftObj D C) (i : ℕ) (hi : i < D.R.m) (h : liftTie D T e O i)
    (φ : C.cls i → C.Y i → ℂ) (Q : C.cls i → MvPolynomial (FrV D (D.R.N i)) ℂ)
    (hQ : ∀ c, C.sharp i (φ c) = fun y => evFr D (Q c) (O.frm i y)) (c' : C.cls (i + 1)) (y' : C.Y (i + 1)) :
    C.K i φ c' y' = ∑ c, (((Nat.card (C.stab i c) : ℕ) : ℂ)⁻¹) *
      ((((rhoOf D O.mt i (O.dt i c) : ℂˣ) : ℂ) * ((rhoOf' D O.mt i (O.dt (i + 1) c') : ℂˣ) : ℂ)) *
        ((∏ τ, (C.de (i + 1) y' τ) ^ (C.sDiv i τ))⁻¹ *
          applyAt0 D (polD D O.dgen (Q c) (O.frm (i + 1) y')) (O.Th i c c'))) := by
  obtain ⟨-, h2⟩ := h
  rw [lift_eqC D C O.mt O.dt O.c13 i hi φ c', Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  have key := h2 c c' (Q c) y'
  rw [hQ c]
  simp only [Pi.smul_apply, smul_eq_mul, Formalism.BasicNotions.ColumnChain.divDe, Formalism.BasicNotions.mulFun, LinearMap.coe_mk,
    AddHom.coe_mk, key]

def LiftObj.IsMem {D : D7} {u : D.what₂.Word} (O : LiftObj D (D.mem u).C) : Prop :=
  letI := D.host.cmStar
  O.mt = D.muTil ∧ (∀ i c, O.dt i c = D.detCls u i c) ∧
  ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = ((D.mem u).A.T : D.host.E) ∧
    ∀ i, i ≤ D.R.m → ∃ co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E),
      (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
      (∀ y, co y ∈ (O.L0 i).1 ↔ y ∈ (D.sp.X i).L0) ∧
      ∀ (c : (D.mem u).C.cls i) y, co y ∈ (O.lat i c).1 ↔
        ∃ a ∈ D.clsLat u i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (D.clsLat u i c),
          y = a + D.host.conj (π : D.host.E) • b

def kjTie (D : D7) (T : Tor D) (e : FamE D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ O : LiftObj D (D.chTw u μ), ∀ i < D.R.m, liftTie D T e O i

def repEx (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (N : ℕ) (L L₀ : SDLat D.host.E N),
    ∃ γ : Matrix.unitaryGroup (Fin N) D.host.E,
      EqAt D p (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1) L₀.1

def repExS (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (n : ℕ), 0 < n → ∀ (N : ℕ) (L L₀ : SDLat D.host.E N),
    ∃ γ : Matrix.unitaryGroup (Fin N) D.host.E,
      EqAt D n (SDLat.smulLat (γ : Matrix (Fin N) (Fin N) D.host.E) L.1) L₀.1

def detIdP (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N : ℕ) (L L₀ : SDLat D.host.E N), EqAt D p L.1 L₀.1 →
    ∃ (h : ℕ) (z : unitary D.host.E), 0 < h ∧ PUnit D lam (z : D.host.E) ∧
      detId D L₀.1 L.1 ^ h = Submodule.span (𝓞 D.host.E) {(z : D.host.E)}

def relDetP (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N : ℕ) (L L₀ : SDLat D.host.E N), EqAt D p L.1 L₀.1 →
    ∃ (h : ℕ) (z : unitary D.host.E), 0 < h ∧ PUnit D lam (z : D.host.E) ∧
      D.relDet N L₀ L ^ h = QuotientGroup.mk (D.e1Dt z)

theorem relDetP_of_relDetPinned (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : RelDetPinned D idl) (hd : detIdP D) :
    relDetP D := by
  obtain ⟨hinj, -, hm, hz, hdet⟩ := h
  intro p _ lam N L L₀ hL
  obtain ⟨n, z, hn, hp, hnz⟩ := hd p lam N L L₀ hL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨m + 1, z, hn, hp, hinj ?_⟩
  rw [idl_pow hm, hdet, hnz, hz]

def repUnitsOf (D : D7) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (t : D.Dt) (h : ℕ) (z : unitary D.host.E),
    PowRat D t h z → PUnit D lam (z : D.host.E) →
      ‖lamC lam ((D.chiD t : ℂˣ) : ℂ)‖ = 1 ∧
      ∀ i < D.R.m, ‖lamC lam ((rhoOf D mt i t : ℂˣ) : ℂ)‖ = 1 ∧ ‖lamC lam ((rhoOf' D mt i t : ℂˣ) : ℂ)‖ = 1

def repUnits (D : D7) : Prop := repUnitsOf D D.muTil

def rhoValOf (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  letI := D.host.cmStar
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (t : D.Dt) (h : ℕ) (z : unitary D.host.E), PowRat D t h z →
    ∀ i < D.R.m,
      ‖lamC lam ((rhoOf D mt i t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖ ^ (-C.sSharp i τ) ∧
      ‖lamC lam ((rhoOf' D mt i t : ℂˣ) : ℂ)‖ ^ h = ∏ τ, ‖lamC lam (embT D τ (z : D.host.E))‖ ^ (C.sDiv i τ)

def nrmId (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (𝔞 : IdE D) : ℝ :=
  sSup ((fun x : D.host.E => ‖lamC lam (embT D τ x)‖) '' (𝔞 : Set D.host.E))

def brRhoOf (D : D7) {u : D.what₂.Word} (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ) : Prop :=
  ∀ idl : D.Dt ⧸ D.UO → IdE D, RelDetPinned D idl →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (t : D.Dt),
      ‖lamC lam ((D.chiD t : ℂˣ) : ℂ)‖ = ∏ τ, (nrmId D lam τ (idl (QuotientGroup.mk t)))⁻¹ ∧
      ∀ i < D.R.m,
        ‖lamC lam ((rhoOf D mt i t : ℂˣ) : ℂ)‖ = ∏ τ, nrmId D lam τ (idl (QuotientGroup.mk t)) ^ (-C.sSharp i τ) ∧
        ‖lamC lam ((rhoOf' D mt i t : ℂˣ) : ℂ)‖ = ∏ τ, nrmId D lam τ (idl (QuotientGroup.mk t)) ^ (C.sDiv i τ)

def rhoUse (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ), rhoThreeOf D C mt →
    repUnitsOf D mt ∧ rhoValOf D C mt ∧ brRhoOf D C mt

theorem chiUnitAll (D : D7) (h : chiUnitInert D) (ha : PowRatAll D) (p : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) (h2 : p ≠ 2) (hp : InertK D p) (t : D.Dt) :
    ‖lamC lam ((D.chiD t : ℂˣ) : ℂ)‖ = 1 := by
  obtain ⟨n, z, hz⟩ := ha t
  exact h p lam h2 hp t n z hz

theorem chiQ_move (D : D7) (idl : D.Dt ⧸ D.UO → IdE D) (h : RelDetPinned D idl) (N : ℕ)
    (L L'' : (letI := D.host.cmStar; SDLat D.host.E N)) (x : D.Dt ⧸ D.UO) (i : ℕ)
    (hi : detId D L.1 L''.1 = idl x ^ (i + 1)) : chiQ D (D.relDet N L L'') = chiQ D x ^ (i + 1) := by
  obtain ⟨hinj, -, hm, -, hdet⟩ := h
  have hx : D.relDet N L L'' = x ^ (i + 1) := hinj (by rw [hdet, hi, idl_pow hm])
  rw [hx, map_pow]

open IsDedekindDomain in

abbrev EP (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : Type := P.adicCompletion D.host.E

open IsDedekindDomain in

def SplitP (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) : Prop :=
  ∃ a b : 𝓞 D.host.E, (b : D.host.E) = D.host.conj (a : D.host.E) ∧ a ∈ P.asIdeal ∧ b ∉ P.asIdeal

open IsDedekindDomain in

def EqOff (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {N : ℕ}
    (L L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ m : ℕ, ∀ a b : 𝓞 D.host.E, (b : D.host.E) = D.host.conj (a : D.host.E) → a ∈ P.asIdeal ^ m →
    (∀ x ∈ L, (a * b) • x ∈ L₀) ∧ ∀ x ∈ L₀, (a * b) • x ∈ L

open IsDedekindDomain in

def EqOffSplit (D : D7) {N : ℕ} (L L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ a : 𝓞 D.host.E, a ≠ 0 ∧ (∀ Q : HeightOneSpectrum (𝓞 D.host.E), a ∈ Q.asIdeal → SplitP D Q) ∧
    (∀ x ∈ L, a • x ∈ L₀) ∧ ∀ x ∈ L₀, a • x ∈ L

open IsDedekindDomain in

def YP (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) {N N' : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    AddSubgroup (Matrix (Fin N') (Fin N) (EP D P)) :=
  ((YYl D L L').toAddSubgroup.map
    ((algebraMap D.host.E (EP D P)).toAddMonoidHom.mapMatrix)).topologicalClosure

open IsDedekindDomain in

def volP {D : D7} {P : HeightOneSpectrum (𝓞 D.host.E)} {N N' : ℕ}
    (Y₀ Y₁ : AddSubgroup (Matrix (Fin N') (Fin N) (EP D P))) : ℝ :=
  ((Y₀.addSubgroupOf Y₁).index : ℝ) / ((Y₁.addSubgroupOf Y₀).index : ℝ)

open IsDedekindDomain in

def modelXi (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (N N' : ℕ) (L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₀' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L₀ L₀' →
    ∀ P : HeightOneSpectrum (𝓞 D.host.E), SplitP D P →
    ∀ th ∈ Th D (tor0 D cc δ) L₀ L₀',
    ∃ Xi : (Matrix (Fin N') (Fin N) (EP D P) → ℂ) →ₗ[ℂ] (VC D N N' → ℂ),
      Xi (Set.indicator (YP D P L₀ L₀' : Set (Matrix (Fin N') (Fin N) (EP D P))) 1) = th ∧
      ∀ L L', admitted D N N' L L' → EqOff D P L L₀ → EqOff D P L' L₀' →
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₀ L₀') (La D (tor0 D cc δ) L L') th =
          fun z => (((Real.sqrt (volP (YP D P L₀ L₀') (YP D P L L')))⁻¹ : ℝ) : ℂ) *
            Xi (Set.indicator (YP D P L L' : Set (Matrix (Fin N') (Fin N) (EP D P))) 1) z

def movesCompose (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (N N' : ℕ) (L₁ L₂ L₃ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L₁' L₂' L₃' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)),
      admitted D N N' L₁ L₁' → admitted D N N' L₂ L₂' → admitted D N N' L₃ L₃' →
      EqOffSplit D L₁ L₂ → EqOffSplit D L₂ L₃ → EqOffSplit D L₁' L₂' → EqOffSplit D L₂' L₃' →
      ∀ th ∈ Th D (tor0 D cc δ) L₁ L₁',
        Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₂ L₂') (La D (tor0 D cc δ) L₃ L₃')
            (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) L₂ L₂') th) =
          Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) L₃ L₃') th

def InLaP (D : D7) (T : Tor D) (p : ℕ) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (x : VC D N N') : Prop :=
  ∃ k : ℕ, (p ^ k : ℕ) • x ∈ La D T L L'

def wPhase (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → p ≠ 2 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ x, InLaP D (tor0 D cc δ) p L L' x →
        ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D (tor0 D cc δ) x = (m : ℝ) ∧
          wPh D (tor0 D cc δ) p x = (-1 : ℂ) ^ m

def wOnLattice (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ x ∈ La D (tor0 D cc δ) L L', wPh D (tor0 D cc δ) p x = al D (tor0 D cc δ) x

def wCocycle (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → p ≠ 2 →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
      ∀ x y, InLaP D (tor0 D cc δ) p L L' x → InLaP D (tor0 D cc δ) p L L' y →
        ∃ (c : ℂ) (k : ℕ), c ^ (p ^ k) = 1 ∧ c ^ 2 = kap D (tor0 D cc δ) x y ∧
          ∀ G : VC D N N' → ℂ, Wop D (tor0 D cc δ) p x (Wop D (tor0 D cc δ) p y G) =
            fun z => c * Wop D (tor0 D cc δ) p (x + y) G z

def PhiHat (D : D7) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (p n : ℕ) [Fact p.Prime] (ε : 𝓞 D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ)
    (y : Fin r → Fin (p ^ n)) : ℂ :=
  ((p : ℂ) ^ (n * r))⁻¹ * ∑ a : Fin r → Fin (p ^ n), Φ (fun i => (((a i : ℕ) : ℤ_[p]))) *
    (kap D T (vecN D T δ p n b a) (liftY D T δ p n ε b y))⁻¹

theorem xi_formula (D : D7) (T : Tor D) (δ : ℂ) {N N' r : ℕ} (p n : ℕ) [Fact p.Prime] (ε : 𝓞 D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ)
    (G : VC D N N' → ℂ) (z : VC D N N') :
    XiF D T δ p n ε b Φ G z =
      ∑ y : Fin r → Fin (p ^ n), PhiHat D T δ p n ε b Φ y * Wop D T p (liftY D T δ p n ε b y) G z := by
  simp only [XiF, PhiHat, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

def xiOne (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → Nat.Coprime (Ideal.absNorm cc) p → (p = 2 ∨ SplitK D p) →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (b : Fin r → Matrix (Fin N') (Fin N) D.host.E),
      admitted D N N' L L' → NNBasis D (tor0 D cc δ) δ p L L' b →
      ∀ (n : ℕ) (ε : 𝓞 D.host.K), IsIdem D lam (2 * n + 2) ε →
        ∀ th ∈ Th D (tor0 D cc δ) L L', XiF D (tor0 D cc δ) δ p n ε b 1 th = th

def xiMove (D : D7) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → Nat.Coprime (Ideal.absNorm cc) p → (p = 2 ∨ SplitK D p) →
    ∀ (N N' : ℕ) (L L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
      (L' L₂ : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (r : ℕ)
      (b b₁ : Fin r → Matrix (Fin N') (Fin N) D.host.E) (c : Fin r → Fin r → D.host.K),
      admitted D N N' L L' → admitted D N N' L₁ L₂ → EqAway D p L L₁ → EqAway D p L' L₂ →
      NNBasis D (tor0 D cc δ) δ p L L' b → NNBasis D (tor0 D cc δ) δ p L₁ L₂ b₁ →
      (∀ j, b j = ∑ i, ((c i j : D.host.K) : D.host.E) • b₁ i) →
      (∀ i j, ‖tauKc D lam (c i j)‖ ≤ 1) →
      ∀ (n : ℕ) (ε : 𝓞 D.host.K) (Φ : LocallyConstant (Fin r → ℤ_[p]) ℂ),
        IsIdem D lam (2 * n + 2) ε → FactorsMod n Φ →
        (∀ a, Φ a = if ∃ x : Fin r → ℤ_[p], ∀ i, zc (a i) = ∑ j, tauKc D lam (c i j) * zc (x j)
          then 1 else 0) →
        ∀ th ∈ Th D (tor0 D cc δ) L₁ L₂,
          Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₂) (La D (tor0 D cc δ) L L') th =
            fun z => ((Real.sqrt (((La D (tor0 D cc δ) L₁ L₂).addSubgroupOf
              (La D (tor0 D cc δ) L L')).index : ℝ) : ℝ) : ℂ) * XiF D (tor0 D cc δ) δ p n ε b₁ Φ th z

def admJ (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    IsIntegral ℤ (1728 * g2 (lamOf D cc δ) ^ 3)

def InducedCMType (D : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (a : D.host.K), embT D τ (a : D.host.E) = D.host.φ₀ (a : D.host.E)

def HostFieldConditions (D : D7) : Prop := TaylorLogMetric.adm1 D

def Pinned (D : D7) : Prop := ∃ idl : D.Dt ⧸ D.UO → IdE D, RelDetPinned D idl

def StatementModelExists (D : D7) : Prop := admJ D → modelEx D
def StatementModelShort (D : D7) : Prop := modelEx D → modelShort D
def StatementAdditiveIntegral (D : D7) : Prop := addInt D
def StatementCubeSecond (D : D7) : Prop := cube2 D
def StatementCubeThird (D : D7) : Prop := cube3 D
def StatementCube (D : D7) : Prop := cube D
def StatementBilinearAdditive (D : D7) : Prop := beBiadd D
def StatementEndomorphismIntegral (D : D7) : Prop := endInt D
def StatementPhaseNorm (D : D7) : Prop := phNorm D
def StatementBilinearConjugate (D : D7) : Prop := beConj D
def StatementSplitZero (D : D7) : Prop := splitZero D
def StatementBilinearDiagonal (D : D7) : Prop := beDiag D
def StatementTranslation (D : D7) : Prop := transl D
def StatementAtTwo (D : D7) : Prop := atTwo D
def StatementJetsPhase (D : D7) : Prop := jetsPh D
def StatementPhaseUnitary (D : D7) : Prop := PhUnitary D
def StatementPhaseIsotropic (D : D7) : Prop := PhIsotropic D
def StatementPhaseDual (D : D7) : Prop := PhDual D
def StatementOrthonormalExists (D : D7) : Prop := InducedCMType D → HostFieldConditions D → orthoEx D
def StatementPhaseWitt (D : D7) : Prop := phW D
def StatementIsometryF (D : D7) : Prop := isoF D
def StatementEndomorphismIntegralWitt (D : D7) : Prop := endInt D → endIntW D
def StatementBilinearWitt (D : D7) : Prop := phW D → readW → addInt D → endIntW D → beBiadd D → beConj D → beW D
def StatementPhaseDualWitt (D : D7) : Prop := phW D → readW → addInt D → endIntW D → PhDual D → PhDualW D
def StatementPhaseEven (D : D7) : Prop := phEven D
def StatementBilinearGaloisConj (D : D7) : Prop := beW D → okpInert D → beGc D
def StatementInertIntegers (D : D7) : Prop := okpInert D
def StatementSupremumH (D : D7) : Prop := InducedCMType D → supH D
def StatementLocalIsometryUnitary (D : D7) : Prop := InducedCMType D → iopUnitary D
def StatementCharacterModOne (D : D7) : Prop := chiMod1 D
def StatementCharacterUnitInert (D : D7) : Prop := InducedCMType D → chiUnitInert D
def StatementCharacterValue (D : D7) : Prop := chiVal D
def StatementNormOnePower (D : D7) : Prop := NormOnePowerPrincipal D
def StatementRationalPowers (D : D7) : Prop := Pinned D → PowRatAll D
def StatementRepresentativesExist (D : D7) : Prop := HostFieldConditions D → repEx D
def StatementRepresentativesSplit (D : D7) : Prop := HostFieldConditions D → repExS D
def StatementDeterminantIdeal (D : D7) : Prop := HostFieldConditions D → detIdP D
def StatementRelativeDeterminant (D : D7) : Prop := Pinned D → relDetP D
def StatementRepresentativeUnits (D : D7) : Prop := rhoThree D → repUnits D
def StatementRhoUse (D : D7) : Prop := NormOnePowerPrincipal D → rhoUse D
def StatementModelXi (D : D7) : Prop := InducedCMType D → modelXi D
def StatementMovesCompose (D : D7) : Prop := InducedCMType D → movesCompose D
def StatementWeilPhase (D : D7) : Prop := InducedCMType D → wPhase D
def StatementWeilOnLattice (D : D7) : Prop := InducedCMType D → wOnLattice D
def StatementWeilCocycle (D : D7) : Prop := InducedCMType D → wCocycle D
def StatementXiOne (D : D7) : Prop := InducedCMType D → xiOne D
def StatementXiMove (D : D7) : Prop := InducedCMType D → xiMove D

def kerComb (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  ∀ (S : Finset ℕ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (Θ : VC D N N' → ℂ), admitted D N N' L L' →
    IsKer D (tor0 D cc δ) e S L L' Θ →
    ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ∉ S → IsComb D (tor0 D cc δ) e lam L L' (pSer D lam Θ)

def hf1 (Λ : AddSubgroup ℂ) (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w / (area Λ : ℂ)

def al1 (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : ℂ := (-1 : ℂ) ^ (round (Real.sqrt d / 2 * (hf1 Λ x x).re))

def IsTheta0 (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : Prop :=
  Differentiable ℂ G ∧ (∀ x ∈ Λ, ∀ z, al1 d Λ x * U1 Λ x G z = G z) ∧ G 0 = 1

def normSq1 (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : ℝ :=
  let Fd : Set ℂ := Classical.epsilon (fun Fd => MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume)
  ⨍ z in Fd, ‖G z‖ ^ 2 * Real.exp (-Real.pi * (hf1 Λ z z).re)

def thPow (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  (((∃ t0, IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) ∧ ∀ t0, IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → IsTheta0 D.host.d (lamOf D cc δ) (th0 (lamOf D cc δ) t0)) ∧
    ∀ G, IsTheta0 D.host.d (lamOf D cc δ) G → ∀ N N' L L', admitted D N N' L L' →
      normSq D (tor0 D cc δ) (La D (tor0 D cc δ) L L') (e N N' L L') = normSq1 (lamOf D cc δ) G ^ (fF D * N * N')) ∧
  ∀ (M : IntermediateField ℚ ℂ) [NumberField M], DataIn D (tor0 D cc δ) M → ∀ ρ : M →ₐ[ℚ] ℂ,
    ((∃ t0, IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0) ∧ ∀ t0, IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t0 →
      IsTheta0 D.host.d (lamConj M ρ (lamOf D cc δ)) (th0 (lamConj M ρ (lamOf D cc δ)) t0)) ∧
    ∀ G, IsTheta0 D.host.d (lamConj M ρ (lamOf D cc δ)) G → ∀ N N' L L', admitted D N N' L L' → CoefIn D (e N N' L L') M →
      normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L') (fnConj D M ρ (e N N' L L')) =
        normSq1 (lamConj M ρ (lamOf D cc δ)) G ^ (fF D * N * N')

def famItems (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  intOrtho D cc δ e ∧ intHyp D cc δ e ∧ prim D cc δ e ∧ kerComb D cc δ e ∧ thPow D cc δ e

def StatementIntegralityHypothesis (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (e : FamE D) : Prop :=
  intOrtho D cc δ e → orthoEx D → endInt D → addInt D → PhDual D → intHyp D cc δ e

def LatticeGrowthBound (D : D7) : Prop :=
  modelEx D ∧ addInt D ∧ cube2 D ∧ cube3 D ∧ cube D ∧ beBiadd D ∧ endInt D ∧ phNorm D ∧ beConj D ∧ splitZero D ∧
    beDiag D ∧ transl D ∧ atTwo D ∧ jetsPh D ∧ PhUnitary D ∧ PhIsotropic D ∧ PhDual D ∧ orthoEx D ∧
    phW D ∧ isoF D ∧ endIntW D ∧ beW D ∧ PhDualW D ∧ modelShort D ∧ phEven D ∧ beGc D ∧ okpInert D

def SplitModelProperties (D : D7) : Prop :=
  supH D ∧ iopUnitary D ∧ chiMod1 D ∧ chiUnitInert D ∧ chiVal D ∧ NormOnePowerPrincipal D ∧ repEx D ∧ detIdP D ∧ repExS D ∧ modelXi D ∧
    movesCompose D ∧ wPhase D ∧ wOnLattice D ∧ wCocycle D ∧ xiOne D ∧ xiMove D

def DeterminantCharacterProperties (D : D7) : Prop := rhoUse D ∧ (Pinned D → relDetP D ∧ PowRatAll D)

def aux₃ (D : D7) : Prop := LatticeGrowthBound D ∧ SplitModelProperties D ∧ DeterminantCharacterProperties D ∧ readW

def Adm3s (D : D7) : Prop := admJ D ∧ InducedCMType D ∧ HostFieldConditions D

def Stmt (D : D7) : Prop := Adm3s D → aux₃ D

theorem relative_determinant_of_split_model (D : D7) (h : SplitModelProperties D) : Pinned D → relDetP D ∧ PowRatAll D := by
  obtain ⟨-, -, -, -, -, hn, -, hd, -⟩ := h
  rintro ⟨idl, hi⟩
  exact ⟨relDetP_of_relDetPinned D idl hi hd, powRatAll_of D idl hi hn⟩

theorem repUnits_of (D : D7) (h : aux₃ D) (u : D.what₂.Word) (h3 : rhoThree D) : repUnits D := by
  obtain ⟨-, -, ⟨hu, -⟩, -⟩ := h
  exact (hu u (D.mem u).C D.muTil (h3 u)).1

def TwistedThetaTheorem (D : D7) (C : ℝ) (X : Ideal (𝓞 D.host.K) → ℂ → FamE D → Prop) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), IsCurveIdeal D cc → ∀ δ : ℂ, IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
    per22 D (tor0 D cc δ) ∧ (∃ χ, IsChi D χ) ∧
    ∀ χ, IsChi D χ →
    ∃ e : FamE D, (vec22 D (tor0 D cc δ) e ∧ th22 D (tor0 D cc δ) C e ∧ eq22 D (tor0 D cc δ) χ e ∧
      int22 D (tor0 D cc δ) e ∧ mom22 D cc δ e ∧ LargerSupportMomentCondition D cc δ e ∧ str22 D (tor0 D cc δ) e) ∧
      famItems D cc δ e ∧ X cc δ e

def ConclusionE (D : D7) (C : ℝ) : Prop := TwistedThetaTheorem D C fun _ _ _ => True

theorem TwistedThetaTheorem.mono {D : D7} {C : ℝ} {X X' : Ideal (𝓞 D.host.K) → ℂ → FamE D → Prop}
    (hX : ∀ cc δ e, X cc δ e → X' cc δ e) (h : TwistedThetaTheorem D C X) : TwistedThetaTheorem D C X' := by
  intro cc hcc δ hδ
  obtain ⟨h1, h2, h3⟩ := h cc hcc δ hδ
  refine ⟨h1, h2, fun χ hχ => ?_⟩
  obtain ⟨e, he, hf, hx⟩ := h3 χ hχ
  exact ⟨e, he, hf, hX _ _ _ hx⟩

theorem TwistedThetaTheorem.toTaylorLogMetric {D : D7} {C : ℝ} {X : Ideal (𝓞 D.host.K) → ℂ → FamE D → Prop} (h : TwistedThetaTheorem D C X) :
    TaylorLogMetric.aux₃ D C := by
  intro cc hcc δ hδ
  obtain ⟨h1, h2, h3⟩ := h cc hcc δ hδ
  refine ⟨h1, h2, fun χ hχ => ?_⟩
  obtain ⟨e, he, -⟩ := h3 χ hχ
  exact ⟨e, he⟩

theorem TwistedThetaTheorem.rec {D : D7} {C : ℝ} {X : Ideal (𝓞 D.host.K) → ℂ → FamE D → Prop} (h : TwistedThetaTheorem D C X)
    (idl : D.Dt ⧸ D.UO → IdE D) (hi : RelDetPinned D idl) (cc : Ideal (𝓞 D.host.K)) (hcc : IsCurveIdeal D cc) (δ : ℂ)
    (hδ : IsDiscriminantTwelfthRootOfIdealLattice D cc δ) :
    ∃ e : FamE D, vec22 D (tor0 D cc δ) e ∧ th22 D (tor0 D cc δ) C e ∧ RelativeDeterminantEquation D (tor0 D cc δ) e ∧
      int22 D (tor0 D cc δ) e ∧ mom22 D cc δ e ∧ LargerSupportMomentCondition D cc δ e ∧ str22 D (tor0 D cc δ) e ∧
      famItems D cc δ e ∧ X cc δ e := by
  obtain ⟨hinj, hN1, hm, hz, hdet⟩ := hi
  obtain ⟨χ, hχ⟩ : ∃ χ : IdE D → ℂ, ∀ x, χ (idl x) = ((chiQ D x : ℂˣ) : ℂ) :=
    ⟨fun 𝔞 => if h𝔞 : ∃ x, idl x = 𝔞 then ((chiQ D h𝔞.choose : ℂˣ) : ℂ) else 0, fun x => by
      have hex : ∃ y, idl y = idl x := ⟨x, rfl⟩
      dsimp only
      rw [dif_pos hex, hinj hex.choose_spec]⟩
  have hC : IsChi D χ := by
    simp only [IsChi]
    refine ⟨fun 𝔞 𝔟 ha hb => ?_, fun z => ?_⟩
    · obtain ⟨x, rfl⟩ := (hN1 𝔞).1 ha
      obtain ⟨y, rfl⟩ := (hN1 𝔟).1 hb
      rw [← hm]
      simp only [hχ, map_mul, Units.val_mul]
    · rw [← hz, hχ]
      simp only [chiQ, QuotientGroup.lift_mk]
      exact D.rest_detCharacter_on_unitary_eq z
  obtain ⟨-, -, h3⟩ := h cc hcc δ hδ
  obtain ⟨e, ⟨hv, ht, heq, hin, hmo, hmc, hs⟩, hf, hx⟩ := h3 χ hC
  obtain ⟨q1, q2, q3⟩ := heq
  have hR : RelativeDeterminantEquation D (tor0 D cc δ) e := by
    simp only [RelativeDeterminantEquation]
    refine ⟨q1, fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
    · rw [q2 N N' L L' L'' hN hN', ← hdet, hχ, Units.val_zpow_eq_zpow_val]
    · rw [q3 N N' L L₁ L' hN hN', ← hdet, hχ, Units.val_zpow_eq_zpow_val]
  exact ⟨e, hv, ht, hR, hin, hmo, hmc, hs, hf, hx⟩

def ClosedFormOfAdmitted (D : D7) (C : ℝ) : Prop := Adm3s D → aux₃ D ∧ ConclusionE D C

def Fam (P : D7 → Prop) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := ∀ x (i : Fm.Ix x), P (Fm.D x i)

def AdmF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := Fam Adm3s Fm
def ConclusionOnFamily {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := Fam aux₃ Fm
def KudlaFamilyStatement {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → ConclusionOnFamily Fm

def FamilyConclusionE {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop := Fam (fun D => ConclusionE D C) Fm
def StatementTwistedFamilyConstant {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C : ℝ) : Prop := AdmF Fm → ConclusionOnFamily Fm ∧ FamilyConclusionE Fm C
def FamilyClosedForm {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Prop := AdmF Fm → ConclusionOnFamily Fm ∧ ∃ C : ℝ, FamilyConclusionE Fm C

end Formalism.MainNotions.GL3Theta
