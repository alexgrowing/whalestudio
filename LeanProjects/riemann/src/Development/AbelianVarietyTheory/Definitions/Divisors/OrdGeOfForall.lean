import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLatticeQuadraticSumGeDiagonal

noncomputable section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.Poinc

def mono {s m : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] {V : Type} [CommRing V] (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (μ : Fin s → X) : V := ∏ i, t i ^ (qW W (δ i) μ).toNat

def lin {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) {X : Type} [AddCommGroup X] (a : Fin l × Fin s → X)
    (β : LinearMap.BilinForm ℤ X) : ℤ := ∑ i, qW W β fun u => a (i, u)

theorem qW_nonneg {s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} (hW : PosW W) {X : Type} [AddCommGroup X]
    {β : LinearMap.BilinForm ℤ X} (hs : ∀ a b, β a b = β b a) (hβ : ∀ y, 0 ≤ β y y) (y : Fin s → X) : 0 ≤ qW W β y := by
  obtain ⟨c, hc0, hc⟩ := QWDom.qW_ge s W hW
  have h2 : (0 : ℝ) ≤ ((∑ u, β (y u) (y u) : ℤ) : ℝ) := by
    exact_mod_cast Finset.sum_nonneg fun u _ => hβ _
  exact_mod_cast (mul_nonneg hc0.le h2).trans (hc X β hs hβ y)

theorem lin_nonneg {s l : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} (hW : PosW W) {X : Type} [AddCommGroup X]
    {β : LinearMap.BilinForm ℤ X} (hs : ∀ a b, β a b = β b a) (hβ : ∀ y, 0 ≤ β y y) (a : Fin l × Fin s → X) :
    0 ≤ lin W a β :=
  Finset.sum_nonneg fun _ _ => qW_nonneg hW hs hβ _

example {V : Type} [CommRing V] (t : V) :
    mono !![1] (fun _ : Fin 1 => t) (fun _ => LinearMap.mul ℤ ℤ) (fun _ => (2 : ℤ)) = t ^ 4 := by
  simp [mono, qW]

example : lin (l := 2) !![1] (fun p => ![(1 : ℤ), 2] p.1) (LinearMap.mul ℤ ℤ) = 5 := by
  simp [lin, qW, Fin.sum_univ_two]

example : PosW !![1] := by
  unfold PosW
  have : ((!![1] + (!![1] : Matrix (Fin 1) (Fin 1) ℤ).transpose).map (Int.cast : ℤ → ℝ)) = Matrix.diagonal fun _ => 2 := by
    ext i j
    fin_cases i; fin_cases j; simp
  rw [this, Matrix.posDef_diagonal_iff]
  intro _; norm_num

structure Dominant {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) (d N₁ : ℕ) {s l : ℕ} (W : Matrix (Fin s) (Fin s) ℤ)
    {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {r : ℕ} (γ : Fin r → LinearMap.BilinForm ℤ X)
    (a : Fin l × Fin s → X) : Prop where
  span : Submodule.span ℤ (Set.range a) = ⊤
  le : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → d * φ.evalZ β ≤ (lin W a β : ℤ)
  min : ∀ e : X ≃ₗ[O] X, (∀ x, CongMod N₁ (e x) x) → ∀ j, lin W a (γ j) ≤ lin W (fun i => e (a i)) (γ j)
  strict : ∀ e : X ≃ₗ[O] X, (∀ x, CongMod N₁ (e x) x) → (∃ x, e x ≠ x) → ∃ j, lin W a (γ j) < lin W (fun i => e (a i)) (γ j)

structure VSys {O : Type} [CommRing O] (bar : O → O) (q : ℕ) {s : ℕ} (W : Matrix (Fin s) (Fin s) ℤ) (N₁ : ℕ)
    (A : Type) [CommRing A] [IsLocalRing A] : Type 2 where
  posW : PosW W

  Y : Type 1

  V : Y → Type
  [ring : ∀ y, CommRing (V y)]
  [dom : ∀ y, IsDomain (V y)]
  [loc : ∀ y, IsLocalRing (V y)]
  cn : ∀ y, IsCN (V y)

  ev : ∀ y, A →+* V y
  ev_loc : ∀ y, IsLocalHom (ev y)

  X : Y → Type
  [add : ∀ y, AddCommGroup (X y)]
  [mod : ∀ y, Module O (X y)]
  [fin : ∀ y, Module.Finite O (X y)]
  [proj : ∀ y, Module.Projective O (X y)]
  [freeZ : ∀ y, Module.Free ℤ (X y)]
  [finZ : ∀ y, Module.Finite ℤ (X y)]
  rank_le : ∀ y, Module.finrank O (X y) ≤ q

  m : Y → ℕ

  t : ∀ y, Fin (m y) → V y
  t_mem : ∀ y i, t y i ∈ maximalIdeal (V y) ∧ t y i ≠ 0

  δ : ∀ y, Fin (m y) → LinearMap.BilinForm ℤ (X y)
  bal : ∀ y i, δ y i ∈ balForms bar (X y)
  nonneg : ∀ y i x, 0 ≤ δ y i x x
  pos : ∀ y x, x ≠ 0 → ∃ i, 0 < δ y i x x

  Q : Type

  u : ∀ y, (Fin s → X y) → Q → V y
  u_unit : ∀ y μ, ∃ c, IsUnit (u y μ c)
  lam : ∃ C : ℕ, ∀ y, m y = 1 → ∀ i x, x ≠ 0 → ∃ h ∈ maximalIdeal A, ev y h ∣ t y i ^ (C * (δ y i x x).toNat)
  four : ∀ (y₀ : Y) (N₀ : ℕ), ∃ N, N₀ ≤ N ∧ N₁ ∣ N ∧ ∃ k : ∀ y, X y₀ →ₗ[ℤ] X y, k y₀ = LinearMap.id ∧
    (∀ y, IsUnimodMod O N (k y)) ∧ ∀ (l : ℕ) (a : Fin l × Fin s → X y₀) (c : Fin l → Q) (e : ℕ), ∃ f : A, ∀ (y : Y) (j : ℕ),
      ∃ S : Finset (Fin l × Fin s → X y), (↑S : Set _) ⊆ orbit O N₁ N (k y) a ∧
        (∀ μ ∈ orbit O N₁ N (k y) a, μ ∉ S → (j : ℤ) ≤ ∑ i, lin W μ (δ y i)) ∧
        ev y f - ∑ μ ∈ S, ∏ i, u y (fun v => μ (i, v)) (c i) * mono W (t y) (δ y) (fun v => μ (i, v)) ∈
          maximalIdeal (V y) ^ j ⊔ (maximalIdeal A ^ e).map (ev y)

attribute [instance] VSys.ring VSys.dom VSys.loc VSys.add VSys.mod VSys.fin VSys.proj VSys.freeZ VSys.finZ

namespace VSys

variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {N₁ : ℕ} {A : Type} [CommRing A]
  [IsLocalRing A] (Φ : VSys bar q W N₁ A)

theorem qW_nonneg (y : Φ.Y) (i : Fin (Φ.m y)) (μ : Fin s → Φ.X y) : 0 ≤ qW W (Φ.δ y i) μ :=
  GlobalTheory.Poinc.qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) μ

theorem lin_nonneg (y : Φ.Y) (i : Fin (Φ.m y)) {l : ℕ} (a : Fin l × Fin s → Φ.X y) : 0 ≤ lin W a (Φ.δ y i) :=
  GlobalTheory.Poinc.lin_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) a

def monoT (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) : Φ.V y := ∏ i, mono W (Φ.t y) (Φ.δ y) fun v => a (i, v)

theorem monoT_eq (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) :
    Φ.monoT y a = ∏ j, Φ.t y j ^ (lin W a (Φ.δ y j)).toNat := by
  simp only [monoT, mono]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  apply Int.natCast_inj.1
  rw [Int.toNat_of_nonneg (Φ.lin_nonneg y j a), lin, Nat.cast_sum]
  exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (Φ.qW_nonneg y j _)

def coefT (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) (c : Fin l → Φ.Q) : Φ.V y := ∏ i, Φ.u y (fun v => a (i, v)) (c i)

def OrdGe (φ : InvFun O) (d e : ℕ) (f : A) : Prop :=
  ∀ y, IsPrincipalIdealRing (Φ.V y) → Φ.m y = 1 → ∀ i : Fin (Φ.m y),
    Φ.ev y f ∈ Ideal.span {Φ.t y i ^ ⌈(d : ℝ) * φ.evalZ (Φ.δ y i)⌉₊} ⊔ ((maximalIdeal A).map (Φ.ev y)) ^ e

variable {Φ} in

theorem OrdGe.mem {φ : InvFun O} {d e : ℕ} {f : A} (h : Φ.OrdGe φ d e f) (y : Φ.Y) (hP : IsPrincipalIdealRing (Φ.V y))
    (hm : Φ.m y = 1) (i : Fin (Φ.m y)) (b : ℕ) (hb : (b : ℝ) = d * φ.evalZ (Φ.δ y i)) :
    Φ.ev y f ∈ Ideal.span {Φ.t y i ^ b} ⊔ ((maximalIdeal A).map (Φ.ev y)) ^ e := by
  have := h y hP hm i
  rwa [← hb, Nat.ceil_natCast] at this

theorem ordGe_of_forall {φ : InvFun O} {d e : ℕ} {f : A}
    (h : ∀ y, IsPrincipalIdealRing (Φ.V y) → Φ.m y = 1 → ∀ (i : Fin (Φ.m y)) (b : ℕ),
      (∀ n : ℕ, d * φ.evalZ (Φ.δ y i) ≤ n → b ≤ n) →
      Φ.ev y f ∈ Ideal.span {Φ.t y i ^ b} ⊔ ((maximalIdeal A).map (Φ.ev y)) ^ e) : Φ.OrdGe φ d e f :=
  fun y hP hm i => h y hP hm i _ fun _ hn => Nat.ceil_le.2 hn

def Leads (y : Φ.Y) {l : ℕ} (a : Fin l × Fin s → Φ.X y) (c : Fin l → Φ.Q) (e : ℕ) (f : A) : Prop :=
  Φ.ev y f - Φ.coefT y a c * Φ.monoT y a ∈
    Ideal.span {Φ.monoT y a} * Ideal.span (Set.range (Φ.t y)) ⊔ maximalIdeal (Φ.V y) ^ e

end VSys

end GlobalTheory.Poinc
