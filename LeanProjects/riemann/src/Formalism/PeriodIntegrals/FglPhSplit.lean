import Mathlib

noncomputable section

namespace PI.FglPhSplit

open Classical

def expMv {K : Type*} [Field K] {σ : Type*} (F : MvPowerSeries σ K) : MvPowerSeries σ K :=
  fun α => ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
    MvPowerSeries.coeff α (F ^ n) / (n.factorial : K)

def SimeqW {K : Type*} [Field K] (W : Subring K) {σ : Type*} (f g : MvPowerSeries σ K) : Prop :=
  MvPowerSeries.constantCoeff (f - g) = 0 ∧ ∀ n, MvPowerSeries.coeff n (expMv (f - g)) ∈ W

def hP {K : Type*} [Field K] {ι : Type*} [Fintype ι] (x y : ι → K × K) : K × K :=
  ∑ k, x k * (y k).swap

structure Dat (K : Type*) [Field K] where
  l : PowerSeries K
  ex : PowerSeries K
  ph : PowerSeries K

namespace Dat

variable {K : Type*} [Field K] (g : Dat K) {σ : Type*}

def lg (a : MvPowerSeries σ K) : MvPowerSeries σ K := PowerSeries.subst a g.l

def pt (x : MvPowerSeries σ K) : MvPowerSeries σ K := PowerSeries.subst x g.ex

def add (a b : MvPowerSeries σ K) : MvPowerSeries σ K := g.pt (g.lg a + g.lg b)

def mulBy (c : K) (a : MvPowerSeries σ K) : MvPowerSeries σ K :=
  g.pt (MvPowerSeries.C c * g.lg a)

def lin {ι : Type*} [Fintype ι] (c : ι → K) (a : ι → MvPowerSeries σ K) : MvPowerSeries σ K :=
  g.pt (∑ j, MvPowerSeries.C (c j) * g.lg (a j))

def phAt (a : MvPowerSeries σ K) : MvPowerSeries σ K := PowerSeries.subst a g.ph

def be (a b : MvPowerSeries σ K) : MvPowerSeries σ K :=
  g.phAt (g.add a b) - g.phAt a - g.phAt b

def PhV {κ ι : Type*} [Fintype κ] [Fintype ι] (b : ι → κ → K × K) (w : ι → MvPowerSeries σ K) :
    MvPowerSeries σ K :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) w)

def PhOn {κ ι : Type*} [Fintype κ] [Fintype ι] (b : ι → κ → K × K) : MvPowerSeries ι K :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) (fun e => MvPowerSeries.X e))

def beSum (ι : Type*) [Fintype ι] : MvPowerSeries (ι ⊕ ι) K :=
  ∑ e : ι, g.be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e))

def sdL {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → K × K) (a' : ι' → κ → K × K) : MvPowerSeries (ι ⊕ ι') K :=
  g.PhOn (Sum.elim a a') - g.PhV a (fun e => MvPowerSeries.X (Sum.inl e)) -
    g.PhV a' (fun e => MvPowerSeries.X (Sum.inr e))

def sdR {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → K × K) (a' : ι' → κ → K × K) : MvPowerSeries (ι ⊕ ι') K :=
  ∑ f, ∑ f', g.be (g.mulBy (hP (a f) (a' f')).1 (MvPowerSeries.X (Sum.inl f))) (MvPowerSeries.X (Sum.inr f'))

end Dat

def DualIso {K : Type*} [Field K] {κ ι : Type*} [Fintype κ] (b b' : ι → κ → K × K) : Prop :=
  (∀ e e', hP (b e) (b e') = 0) ∧ (∀ e e', hP (b' e) (b' e') = 0) ∧
    ∀ e e', hP (b e) (b' e') = if e = e' then 1 else 0

def Target : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : Subring K) (g : Dat K) (S : Set (K × K)),
    PowerSeries.constantCoeff g.ex = 0 → PowerSeries.subst g.ex g.l = PowerSeries.X →
    PowerSeries.constantCoeff g.ph = 0 →
    (∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → K × K)
        (a' : ι' → κ → K × K), (∀ e k, a e k ∈ S) → (∀ e k, a' e k ∈ S) →
        SimeqW W (g.sdL a a') (g.sdR a a')) →
    (∀ (κ ι : Type) [Fintype κ] [Fintype ι] (b b' : ι → κ → K × K), (∀ e k, b e k ∈ S) →
        (∀ e k, b' e k ∈ S) → DualIso b b' → SimeqW W (g.PhOn (Sum.elim b b')) (g.beSum ι)) →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (b b' : ι → κ → K × K)
      (b'' : ι' → κ → K × K), (∀ e k, b e k ∈ S) → (∀ e k, b' e k ∈ S) → (∀ e k, b'' e k ∈ S) →
      DualIso b b' → (∀ e f, hP (b e) (b'' f) = 0) → (∀ e f, hP (b' e) (b'' f) = 0) →
      SimeqW W (g.PhOn (Sum.elim (Sum.elim b b') b''))
        (∑ e : ι, g.be (MvPowerSeries.X (Sum.inl (Sum.inl e))) (MvPowerSeries.X (Sum.inl (Sum.inr e))) +
          g.PhV b'' (fun f => MvPowerSeries.X (Sum.inr f)))

end PI.FglPhSplit

end
