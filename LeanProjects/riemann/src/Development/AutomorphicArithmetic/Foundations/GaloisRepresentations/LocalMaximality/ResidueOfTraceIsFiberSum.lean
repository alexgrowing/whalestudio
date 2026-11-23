import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm

set_option autoImplicit false

noncomputable section

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 GlobalTheory.W1.Lef
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

def locM {L V : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [Module L V] [Module ℂ V] [IsScalarTower ℂ L V]
    (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) (M : Submodule ℂ V) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ b : B, e b ≠ 0 ∧ (b : L) • v ∈ M}

def RedFib {F : Type} (L : Type) [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L] {d : ℕ}
    (x : Fin (d + 1) → Fˣ) : Prop :=
  IsReduced ((rB ℂ L (xv x) {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ L (xv x) j⟩ : rB ℂ L (xv x) {0}))))

section
variable {F K K' : Type} [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] {d : ℕ}
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')

structure Y0 : Prop where
  covZ : IsFinCover ℂ K (xv x)
  covY : IsFinCover ℂ K' (xv x)
  cov : ∀ (i : Fin (d + 1)) (e : rB ℂ K' (xv x) {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), R2 (xv x) j2 {j} ≤ loc (rB ℂ K' (xv x) {i}) e
  red : RedFib K' x

structure Y1 (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ) : Prop extends Y0 x j2 where
  off : ∀ i : Fin (d + 1), i ≠ 0 → ∀ e : rB ℂ K' (xv x) {i} →ₐ[ℂ] ℂ, ¬ IsFix (rB ℂ K' (xv x) {i}) e j2 (rB ℂ K (xv x) {i})
  orig : ∀ e : rB ℂ K' (xv x) {0} →ₐ[ℂ] ℂ, IsFix (rB ℂ K' (xv x) {0}) e j2 (rB ℂ K (xv x) {0}) →
    ∀ j : Fin d, e ⟨_, tco_mem ℂ K' (xv x) j⟩ = 0
  fx : ∀ e : fib ℂ K' (xv x), e ∈ Fx ↔ IsFix (rB ℂ K' (xv x) {0}) e.1 j2 (rB ℂ K (xv x) {0})
  tan : ∀ e ∈ Fx, ∀ m : Fin d, ∃ g : Fin d → K', (∀ l, Val (rB ℂ K' (xv x) {0}) e.1 (g l) (A e m l)) ∧
    j2 (tt K x m) = ∑ l, g l * tt K' x l
  det : ∀ e ∈ Fx, (1 - A e).det ≠ 0

def Over {I J : Finset (Fin (d + 1))} (e : RY (xv x) j2 I J →ₐ[ℂ] ℂ) (e0 : fib ℂ K' (xv x)) : Prop :=
  I = {0} ∧ loc (RY (xv x) j2 I J) e = loc (rB ℂ K' (xv x) {0}) e0.1 ∧
    ∀ v c, Val (RY (xv x) j2 I J) e v c ↔ Val (rB ℂ K' (xv x) {0}) e0.1 v c

abbrev gG {κ : Type} (z : κ → K ⊗[ℂ] K) : Mi d ⊕ₗ κ → K' := app (sysY x j2 d).mu fun l => gS j2 (z l)

abbrev gT : Fin d → K' := fun l => ((sysY x j2 d).X l.succ : K')

end

def n10 {κ : Type} : κ → ℕ × ℕ := fun _ => (1, 0)

def ValBasic : Prop := ∀ (L : Type) [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ), B ≤ loc B e ∧ (∃ ev : loc B e →ₐ[ℂ] ℂ, ∀ v c, Val B e v c ↔ ∃ h : v ∈ loc B e, ev ⟨v, h⟩ = c) ∧
  (∀ b : B, Val B e b (e b)) ∧ ∀ v c, Val B e v c → c ≠ 0 → v ≠ 0 ∧ v⁻¹ ∈ loc B e

def LG : Prop := ∀ (L : Type) [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) [Algebra.FiniteType ℂ B] (V σ : Type) [AddCommGroup V] [Module L V] [Module ℂ V] [IsScalarTower ℂ L V]
  [LinearOrder σ] [Fintype σ] (A : Finset σ → Submodule ℂ V) (w : σ → L), (∀ s, Stab (Algebra.lsmul ℂ ℂ V) B (A s)) →
  (∀ (n : ℤ) (c : Finset σ → V), (∀ e : B →ₐ[ℂ] ℂ, c ∈ (acx (fun s => locM B e (A s)) fun i => Algebra.lsmul ℂ ℂ V (w i)).B n) →
    c ∈ (acx A fun i => Algebra.lsmul ℂ ℂ V (w i)).B n) ∧
  ∀ m : V, (∀ e : B →ₐ[ℂ] ℂ, m ∈ sm (Algebra.lsmul ℂ ℂ V) (locM B e (A ∅)) (Set.range w)) →
    m ∈ sm (Algebra.lsmul ℂ ℂ V) (A ∅) (Set.range w)

def OmLoc : Prop := ∀ (L : Type) [Field L] [Algebra ℂ L] (B : Subalgebra ℂ L) (e : B →ₐ[ℂ] ℂ) (q : ℕ), locM B e (omB ℂ L B q) = omB ℂ L (loc B e) q ∧
  Stab (Algebra.lsmul ℂ ℂ (DR ℂ L)) B (omB ℂ L B q) ∧ ∀ B' : Subalgebra ℂ L, B ≤ B' → omB ℂ L B q ≤ omB ℂ L B' q

def LocMax : Prop := ∀ (F L : Type) [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ L (xv x) → RedFib L x → ∀ (e : fib ℂ L (xv x)) (v : L), Val (rB ℂ L (xv x) {0}) e.1 v 0 →
  InSp (loc (rB ℂ L (xv x) {0}) e.1) (tt L x) v

def LocOne : Prop := ∀ (F L : Type) [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ L (xv x) → RedFib L x → ∀ (e : fib ℂ L (xv x)), ∀ v ∈ loc (rB ℂ L (xv x) {0}) e.1,
  ∃ c : Fin d → L, (∀ l, c l ∈ loc (rB ℂ L (xv x) {0}) e.1) ∧ D ℂ L v = ∑ l, c l • D ℂ L (tt L x l)

def LocForms : Prop := ∀ (F L : Type) [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ L (xv x) → RedFib L x → ∀ (e : fib ℂ L (xv x)) (q : ℕ) (w : DR ℂ L), w ∈ omB ℂ L (loc (rB ℂ L (xv x) {0}) e.1) q ↔
  ∃ c : Finset (Fin d) → L, (∀ S, c S ∈ loc (rB ℂ L (xv x) {0}) e.1) ∧ w = ∑ S ∈ Finset.univ.powersetCard q, c S • dtS L x S

def LocReg : Prop := ∀ (F L : Type) [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ L (xv x) → RedFib L x → ∀ (e : fib ℂ L (xv x)),
  Reg (Algebra.lsmul ℂ ℂ (DR ℂ L)) (omB ℂ L (loc (rB ℂ L (xv x) {0}) e.1) d) (tt L x)

def DtBasic : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → LinearIndependent K (dtS K x) ∧ (∀ S, dtS K x S ∈ omB ℂ K (rB ℂ K (xv x) {0}) S.card) ∧
  dtS K x Finset.univ = algebraMap F K (omG x 0) • vol0 ℂ K (xv x) ∧ algebraMap F K (omG x 0) = ∏ l, tt K x l ∧
  ∃ ε : Finset (Fin d) → ℤˣ, ∀ U S : Finset (Fin d), U.card + S.card = d →
    dtS K x U * dtS K x S = if U = Sᶜ then ε S • dtS K x Finset.univ else 0

def CRT : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → Finite (fib ℂ K (xv x)) ∧ ∀ v : fib ℂ K (xv x) → ℂ, ∃ h : rB ℂ K (xv x) {0}, ∀ e, e.1 h = v e

def ResidueOfTraceIsFiberSum : Prop := ∀ (F L : Type) [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ L (xv x) → RedFib L x → ∀ ρ : F →ₗ[ℂ] ℂ, IsRes ℂ (xv x) ρ → ∀ h : rB ℂ L (xv x) {0},
  ρ (Algebra.trace F L h) = ∑ᶠ e : fib ℂ L (xv x), e.1 h

def TrVal : Prop := ∀ (F L : Type) [Field F] [Field L] [Algebra ℂ F] [Algebra ℂ L] [Algebra F L] [IsScalarTower ℂ F L] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ L (xv x) → RedFib L x → ∀ ρ : F →ₗ[ℂ] ℂ, IsRes ℂ (xv x) ρ → ∀ (g : L) (γ : fib ℂ L (xv x) → ℂ),
  (∀ e, Val (rB ℂ L (xv x) {0}) e.1 g (γ e)) → Algebra.trace F L g ∈ rA ℂ (xv x) {0} →
  ρ (Algebra.trace F L g) = ∑ᶠ e, γ e

def ResVal : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ ρ : F →ₗ[ℂ] ℂ, IsRes ℂ (xv x) ρ → ∀ (e : fib ℂ K (xv x)), ∀ f ∈ rA ℂ (xv x) {0},
  Val (rB ℂ K (xv x) {0}) e.1 (algebraMap F K f) (ρ f)

def RedK : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → RedFib K x

def RYBasic : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → (∀ I, RY (xv x) j2 I ∅ = rB ℂ K' (xv x) I) ∧ (∀ a, (sysY x j2 a).Good) ∧
  (∀ I I' J J', I ⊆ I' → J ⊆ J' → RY (xv x) j2 I J ≤ RY (xv x) j2 I' J') ∧
  (∀ I, ∀ b ∈ rB ℂ K (xv x) I, algebraMap K K' b ∈ rB ℂ K' (xv x) I ∧ j2 b ∈ R2 (xv x) j2 I) ∧
  ∀ J, ∀ j ∈ J, ∀ j', ∀ y ∈ R2 (xv x) j2 (insert j' J), ∃ N : ℕ, y * j2 (algebraMap F K ((x j' : F) / x j)) ^ N ∈ R2 (xv x) j2 J

def RYFT : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → ∀ I J, I.Nonempty → Algebra.FiniteType ℂ (RY (xv x) j2 I J)

def LocEq : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → ∀ I J, ∀ i ∈ I, ∀ (e : RY (xv x) j2 I J →ₐ[ℂ] ℂ), ∃ e0 : rB ℂ K' (xv x) {i} →ₐ[ℂ] ℂ,
  loc (RY (xv x) j2 I J) e = loc (rB ℂ K' (xv x) {i}) e0 ∧ ∀ v c, Val (RY (xv x) j2 I J) e v c ↔ Val (rB ℂ K' (xv x) {i}) e0 v c

def RowEx : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → ∀ (q : ℕ) (I : Finset (Fin (d + 1))), I.Nonempty → ∀ m : ℤ,
  (acx (fun J => omB ℂ K' (RY (xv x) j2 I J) q) fun _ => 1).Z m ≤ (acx (fun J => omB ℂ K' (RY (xv x) j2 I J) q) fun _ => 1).B m

def EdgeB : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → ∀ y ∈ (omCx (rB ℂ K' (xv x)) d).Z d, edge1 y ∈ (sysY x j2 d).mix.B (d + 2) →
  y ∈ (omCx (rB ℂ K' (xv x)) d).B d

def PtT : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → ∀ I J, ∀ i ∈ I, ∀ j ∈ J, ∀ (e : RY (xv x) j2 I J →ₐ[ℂ] ℂ),
  (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r n10 (gT x j2) i j l) 0) → ∃ e0, Over x j2 e e0

def PtG : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z → ∀ I J, ∀ i ∈ I, ∀ j ∈ J, ∀ (e : RY (xv x) j2 I J →ₐ[ℂ] ℂ),
  (∀ l, Val (RY (xv x) j2 I J) e ((sysY x j2 d).r (app n11 n) (gG x j2 z) i j l) 0) → J = {0} ∧ ∃ e0 ∈ Fx, Over x j2 e e0

def FixLoc : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ e ∈ Fx, ∃ N : Matrix (Fin d) (Fin d) K', (∀ a l, N a l ∈ loc (rB ℂ K' (xv x) {0}) e.1) ∧
  Val (rB ℂ K' (xv x) {0}) e.1 N.det (1 - A e).det ∧
  (∀ a, (sysY x j2 d).r n11 (sysY x j2 d).mu 0 0 (dj 0 a) = ∑ l, N a l * tt K' x l) ∧
  ∀ l, InSp (loc (rB ℂ K' (xv x) {0}) e.1) (fun a => (sysY x j2 d).r n11 (sysY x j2 d).mu 0 0 (dj 0 a)) (tt K' x l)

def YKE : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (r : κ → K') I J, I.Nonempty → (∀ l, r l ∈ RY (xv x) j2 I J) →
  ((∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, (∀ l, Val (RY (xv x) j2 I J) e (r l) 0) → ∃ e0, Over x j2 e e0 ∧
      ∀ l, InSp (loc (rB ℂ K' (xv x) {0}) e0.1) r (tt K' x l)) →
    KE (kos (sysY x j2 d).act ((sysY x j2 d).M I J) r) d) ∧
  (∀ (m : ℤ), ∀ c ∈ (kos (sysY x j2 d).act ((sysY x j2 d).M I J) r).Z m, (∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ,
      (∀ l, Val (RY (xv x) j2 I J) e (r l) 0) → c ∈ (kos (sysY x j2 d).act (omB ℂ K' (loc (RY (xv x) j2 I J) e) d) r).B m) →
    c ∈ (kos (sysY x j2 d).act ((sysY x j2 d).M I J) r).B m) ∧
  ∀ y ∈ (sysY x j2 d).M I J, (∀ e : RY (xv x) j2 I J →ₐ[ℂ] ℂ, (∀ l, Val (RY (xv x) j2 I J) e (r l) 0) →
      y ∈ sm (sysY x j2 d).act (omB ℂ K' (loc (RY (xv x) j2 I J) e) d) (Set.range r)) →
    y ∈ sm (sysY x j2 d).act ((sysY x j2 d).M I J) (Set.range r)

def YCols : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  (sysY x j2 d).admitted (app n11 n) (gG x j2 z) ∧ (sysY x j2 d).admitted n10 (gT x j2) ∧
  (sysY x j2 d).admitted (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) ∧ ∀ I J, I.Nonempty → J.Nonempty →
    KE ((sysY x j2 d).colCx (app n11 n) (gG x j2 z) I J) d ∧ KE ((sysY x j2 d).colCx n10 (gT x j2) I J) d ∧
    KE ((sysY x j2 d).colCx (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) I J) d ∧
    ((I ≠ {0} ∨ J ≠ {0}) → ∀ m, ((sysY x j2 d).colCx (app n11 n) (gG x j2 z) I J).Z m ≤ ((sysY x j2 d).colCx (app n11 n) (gG x j2 z) I J).B m ∧
      ((sysY x j2 d).colCx (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) I J).Z m ≤
        ((sysY x j2 d).colCx (app (app n11 n) n10) (app (gG x j2 z) (gT x j2)) I J).B m)

def YBig : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z → ∀ h : rB ℂ K' (xv x) {0}, (∀ e : fib ℂ K' (xv x), e ∉ Fx → e.1 h = 0) →
  ∃ c ∈ ((sysY x j2 d).cx (app (app n11 n) n10) (app (gG x j2 z) (gT x j2))).Z (d + 2),
    c (uni (uni {0} {0}) (img inrE)) = ((-1) ^ d * algebraMap F K' (x 0) ^ d * (h : K')) • dtS K' x Finset.univ ∧
    ∀ i j, (i ≠ 0 ∨ j ≠ 0) → col c (uni {i} {j}) = 0

def YXi : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → ∀ h : rB ℂ K' (xv x) {0}, ∃ c ∈ ((sysY x j2 d).cx n10 (gT x j2)).Z (d + 2),
  top c = edge1 (locCoch ℂ K' (xv x) h) ∧
  ∀ j, c (uni (uni {0} {j}) Finset.univ) = ((-1) ^ d * algebraMap F K' (x 0) ^ d * (h : K')) • dtS K' x Finset.univ

def YCmpT : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ h : rB ℂ K' (xv x) {0}, (∀ e : fib ℂ K' (xv x), e ∉ Fx → e.1 h = 0) →
  ∀ c ∈ ((sysY x j2 d).cx n10 (gT x j2)).Z (d + 2),
  c (uni (uni {0} {0}) Finset.univ) = ((-1) ^ d * algebraMap F K' (x 0) ^ d * (h : K')) • dtS K' x Finset.univ →
  (∀ i j, (i ≠ 0 ∨ j ≠ 0) → col c (uni {i} {j}) = 0) → top c - edge1 (locCoch ℂ K' (xv x) h) ∈ (sysY x j2 d).mix.B (d + 2)

def YCmpG : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z → ∀ (h : rB ℂ K' (xv x) {0}) (s : K'),
  (∀ e ∈ Fx, Val (rB ℂ K' (xv x) {0}) e.1 s (e.1 h * (1 - A e).det)) →
  ∀ c ∈ ((sysY x j2 d).cx (app (app n11 n) n10) (app (gG x j2 z) (gT x j2))).Z (d + 2),
  c (uni (uni {0} {0}) (img inrE)) = ((-1) ^ d * algebraMap F K' (x 0) ^ d * (h : K')) • dtS K' x Finset.univ →
  ∀ c' ∈ ((sysY x j2 d).cx (app n11 n) (gG x j2 z)).Z (d + 2),
  c' (uni (uni {0} {0}) (uni (img (dj 0)) ∅)) =
    ((-1) ^ d * (algebraMap F K' (x 0) * j2 (algebraMap F K (x 0))) ^ d * s) • dtS K' x Finset.univ →
  top c' - top c ∈ (sysY x j2 d).mix.B (d + 2)

def GMap : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → ∀ a, a ≤ d → (∀ l, gS j2 ((sysZ K x a).mu l) = (sysY x j2 d).mu l) ∧
  (∀ s m, gY j2 (actZ K s m) = gS j2 s • gY j2 m) ∧ (∀ I J, ∀ s ∈ (sysZ K x a).R I J, gS j2 s ∈ RY (xv x) j2 I J) ∧
  (∀ N, ∀ t ∈ (sysZ K x a).mix.B N, (fun s => gY j2 (t s)) ∈ (sysY x j2 d).mix.B N) ∧
  ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K) N, ∀ c ∈ ((sysZ K x a).cx n z).Z N,
    (fun s => gY j2 (c s)) ∈ ((sysY x j2 d).cx n fun l => gS j2 (z l)).Z N

def MinorSum : Prop := ∀ (d a : ℕ) (A : Matrix (Fin d) (Fin d) ℂ),
  (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • A.map Polynomial.C)).coeff a =
    ∑ S ∈ Finset.univ.powersetCard a, (A.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).det

def FixZ : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ e ∈ Fx, ∃ z : fib ℂ K (xv x), ∀ v c, Val (rB ℂ K (xv x) {0}) z.1 v c →
  Val (rB ℂ K' (xv x) {0}) e.1 (algebraMap K K' v) c ∧ Val (rB ℂ K' (xv x) {0}) e.1 (j2 v) c

def DtPull : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ e ∈ Fx, ∀ T : Finset (Fin d), mapDR ℂ K K' (dtS K x T) = dtS K' x T ∧
  ∃ c : Finset (Fin d) → K', pr2L j2 (dtS K x T) = ∑ S ∈ Finset.univ.powersetCard T.card, c S • dtS K' x S ∧
    ∀ S, ∀ hS : S.card = T.card,
      Val (rB ℂ K' (xv x) {0}) e.1 (c S) ((A e).submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin hS)).det

def IdVal : Prop := ∀ (F K : Type) [Field F] [Field K] [Algebra ℂ F] [Algebra ℂ K] [Algebra F K] [IsScalarTower ℂ F K] (d : ℕ)
  (x : Fin (d + 1) → Fˣ), IsFinCover ℂ K (xv x) → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → RedFib K x → ∀ a, a ≤ d → ∀ (m : ℕ) (w' w : Fin m → DR ℂ K),
  (∀ k, w' k ∈ omB ℂ K (rB ℂ K (xv x) {0}) (d - a) ∧ w k ∈ omB ℂ K (rB ℂ K (xv x) {0}) a) →
  Acts (F := F) K τ a (∑ k, w' k ⊗ₜ w k) (algebraMap F K (omG x 0)) → ∀ z : fib ℂ K (xv x),
  ∃ (g b : Fin m → Finset (Fin d) → K) (α β : Fin m → Finset (Fin d) → ℂ),
    (∀ k S, S.card = a → w' k * dtS K x S = g k S • dtS K x Finset.univ) ∧
    (∀ k, w k = ∑ T ∈ Finset.univ.powersetCard a, b k T • dtS K x T) ∧
    (∀ k S, S.card = a → Val (rB ℂ K (xv x) {0}) z.1 (g k S) (α k S) ∧ Val (rB ℂ K (xv x) {0}) z.1 (b k S) (β k S)) ∧
    ∀ S T, S.card = a → T.card = a → ∑ k, α k S * β k T = if S = T then 1 else 0

def ValG : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ m ∈ (sysZ K x a).M {0} {0},
  Acts (F := F) K τ a m (algebraMap F K (omG x 0)) → ∃ s : K', gY j2 m = s • dtS K' x Finset.univ ∧
    ∀ e ∈ Fx, Val (rB ℂ K' (xv x) {0}) e.1 s ((Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A e).map Polynomial.C)).coeff a)

def YMain : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ a, a ≤ d → ∀ (κ : Type) [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → K ⊗[ℂ] K), ZF K x n z →
  ∀ c ∈ ((sysZ K x a).cx (app n11 n) (app (sysZ K x a).mu z)).Z (d + 2), IsDiag K x τ a (resK inlE c) →
  ∃ h : rB ℂ K' (xv x) {0}, (fun s => gY j2 (top c s)) - edge1 (locCoch ℂ K' (xv x) h) ∈ (sysY x j2 d).mix.B (d + 2) ∧
    locCoch ℂ K' (xv x) h ∈ (omCx (rB ℂ K' (xv x)) d).Z d ∧ ∑ᶠ e : fib ℂ K' (xv x), e.1 h = ∑ e ∈ Fx, locTerm (A e) a

def TrTop : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K'), Y0 x j2 → ∀ (τ : DR ℂ K →ₗ[K] K), IsTop ℂ K (xv x) τ → ∀ (ρ : F →ₗ[ℂ] ℂ), IsRes ℂ (xv x) ρ →
  (∀ w y, trDR ℂ K K' (mapDR ℂ K K' w * y) = w * trDR ℂ K K' y) ∧
  (∀ h : K', trF ℂ τ ρ (trDR ℂ K K' (h • vol0 ℂ K' (xv x))) = ρ (Algebra.trace F K' h)) ∧
  ∀ y ∈ (omCx (rB ℂ K' (xv x)) d).B d, trF ℂ τ ρ (trDR ℂ K K' (y Finset.univ)) = 0

def FieldLe : Prop := ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K]
  [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (d : ℕ)
  (x : Fin (d + 1) → Fˣ) (j2 : K →ₐ[ℂ] K')
  (Fx : Finset (fib ℂ K' (xv x))) (A : fib ℂ K' (xv x) → Matrix (Fin d) (Fin d) ℂ), Y1 x j2 Fx A → ∀ a, a ≤ d →
  ∀ u : ∀ p : ℕ, (omCx (rB ℂ K (xv x)) a).H p →ₗ[ℂ] (omCx (rB ℂ K (xv x)) a).H p,
  (∀ (p : ℕ) (b : Finset (Fin (d + 1)) → DR ℂ K) (hb : b ∈ (omCx (rB ℂ K (xv x)) a).Z p),
    ∃ bt ∈ (cech fun s : Finset (Two d) => omB ℂ K' (RY (xv x) j2 (lft s) (rgt s)) a).Z p,
      (∀ J, bt (uni ∅ J) = pr2L j2 (b J)) ∧
      ∃ h : trC (k := ℂ) (K := K) (L := K') (fun I => bt (uni I ∅)) ∈ (omCx (rB ℂ K (xv x)) a).Z p,
        u p (Submodule.Quotient.mk ⟨b, hb⟩) = Submodule.Quotient.mk ⟨_, h⟩) →
  ∑ p ∈ Finset.range (d + 1), (-1 : ℂ) ^ p * LinearMap.trace ℂ _ (u p) = ∑ e ∈ Fx, locTerm (A e) a

def Field0 : Prop := ∀ (d a : ℕ) (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K'),
  IsFinCover ℂ K x → IsFinCover ℂ K' x →
  (∀ (i : Fin (d + 1)) (e : rB ℂ K' x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j}, ∃ (b : K') (hb : b ∈ rB ℂ K' x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ K' x {i}) →
  IsReduced ((rB ℂ K' x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K' x j⟩ : rB ℂ K' x {0})))) →
  (∀ (i : Fin (d + 1)), i ≠ 0 → ∀ e : rB ℂ K' x {i} →ₐ[ℂ] ℂ, ¬ IsFix (rB ℂ K' x {i}) e j2 (rB ℂ K x {i})) →
  (∀ e : rB ℂ K' x {0} →ₐ[ℂ] ℂ, IsFix (rB ℂ K' x {0}) e j2 (rB ℂ K x {0}) → ∀ j : Fin d, e ⟨_, tco_mem ℂ K' x j⟩ = 0) →
  ∀ (Fx : Finset (fib ℂ K' x)), (∀ e : fib ℂ K' x, e ∈ Fx ↔ IsFix (rB ℂ K' x {0}) e.1 j2 (rB ℂ K x {0})) →
  (∀ e ∈ Fx, ∀ (b : K) (hb1 : algebraMap K K' b ∈ rB ℂ K' x {0}), b ∈ rB ℂ K x {0} → e.1 ⟨_, hb1⟩ = 0 →
    ∃ (c : K) (hc1 : algebraMap K K' c ∈ rB ℂ K' x {0}), c ∈ rB ℂ K x {0} ∧ e.1 ⟨_, hc1⟩ ≠ 0 ∧
      ∃ g : Fin d → K, (∀ l, g l ∈ rB ℂ K x {0}) ∧ c * b = ∑ l, g l * algebraMap F K (x l.succ / x 0)) →
  ∀ A : fib ℂ K' x → Matrix (Fin d) (Fin d) ℂ,
  (∀ e ∈ Fx, ∀ m : Fin d, ∃ (c : K') (hc : c ∈ rB ℂ K' x {0}) (g : Fin d → K') (hg : ∀ l, g l ∈ rB ℂ K' x {0}), e.1 ⟨c, hc⟩ ≠ 0 ∧
    c * j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l * algebraMap F K' (x l.succ / x 0) ∧ ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * A e m l) →
  (∀ e ∈ Fx, (1 - A e).det ≠ 0) →
  ∀ u : ∀ p : ℕ, (cech fun I => omB ℂ K (rB ℂ K x I) a).H p →ₗ[ℂ] (cech fun I => omB ℂ K (rB ℂ K x I) a).H p,
  (∀ (p : ℕ) (b : Finset (Fin (d + 1)) → DR ℂ K) (hb : b ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p),
    ∃ bt ∈ (cech fun s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) => omB ℂ K' (RY x j2 (lft s) (rgt s)) a).Z p,
      (∀ J, bt (uni ∅ J) = pr2L j2 (b J)) ∧
      ∃ h : trC (k := ℂ) (K := K) (L := K') (fun I => bt (uni I ∅)) ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p,
        u p (Submodule.Quotient.mk ⟨b, hb⟩) = Submodule.Quotient.mk ⟨_, h⟩) →
  (∀ p : ℕ, FiniteDimensional ℂ ((cech fun I => omB ℂ K (rB ℂ K x I) a).H p)) →
  ∑ p ∈ Finset.range (d + 1), (-1 : ℂ) ^ p * LinearMap.trace ℂ _ (u p) =
    ∑ e ∈ Fx, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A e).map Polynomial.C)).coeff a / (1 - A e).det

end UpperTheory.Gal.productCup_of_system

end
