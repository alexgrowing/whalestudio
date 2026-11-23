import Development.AutomorphicArithmetic.QuadraticCharacters.ExceptionalCharacterCondition

open NumberField IntermediateField MeasureTheory

namespace HostParam

section Fields

variable (E : Type) [Field E] [NumberField E]

def inertiaB (p : ℕ) : Subgroup Gal(E/ℚ) :=
  ⨅ (P : Ideal (𝓞 E)) (_ : P.IsPrime) (_ : (p : 𝓞 E) ∈ P), P.inertia Gal(E/ℚ)

def decompB (p : ℕ) : Subgroup Gal(E/ℚ) :=
  open Pointwise in
  ⨅ (P : Ideal (𝓞 E)) (_ : P.IsPrime) (_ : (p : 𝓞 E) ∈ P), MulAction.stabilizer Gal(E/ℚ) P

def RamifiedB (p : ℕ) : Prop := inertiaB E p ≠ ⊥

def IsFrobB (p : ℕ) (σ : Gal(E/ℚ)) : Prop :=
  ∀ P : Ideal (𝓞 E), P.IsPrime → (p : 𝓞 E) ∈ P → ∀ x : 𝓞 E, σ • x - x ^ p ∈ P

noncomputable def conductorB : ℕ :=
  sInf {M : ℕ | 0 < M ∧ Nonempty (E →ₐ[ℚ] CyclotomicField M ℚ)}

def SplitsB (p : ℕ) : Prop := (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = 2

variable {E}

def IsConjB (c : Gal(E/ℚ)) : Prop := ∀ (φ : E →+* ℂ) (x : E), φ (c x) = starRingEnd ℂ (φ x)

def IsDirOf (χ : Gal(E/ℚ) →* ℂˣ) (ψ : PrimChar) : Prop :=
  0 < ψ.1 ∧ ψ.2.IsPrimitive ∧ ∃ M : ℕ, 0 < M ∧ ∀ p : ℕ, p.Prime → ¬ p ∣ M →
    ∀ σ : Gal(E/ℚ), IsFrobB E p σ → ψ.2 (p : ZMod ψ.1) = (χ σ : ℂ)

def dirSet (S : Set (Gal(E/ℚ) →* ℂˣ)) : Set PrimChar := {ψ | ∃ χ ∈ S, IsDirOf χ ψ}

end Fields

class PreHostB (T : HostType) (X x : ℝ) (E : Type) [Field E] [NumberField E]
    [IsAbelianGalois ℚ E] where
  one_le_X : 1 ≤ X
  x_ge : X ^ (1 / (T.J : ℝ)) ≤ x
  x_le : x ≤ X
  e : ℕ
  range_n : IsRangeN T x e

  cyc : ∃ N : ℕ, 0 < N ∧ Nonempty (E →ₐ[ℚ] CyclotomicField N ℚ)
  not_real : ¬ IsTotallyReal E
  c : Gal(E/ℚ)
  c_spec : IsConjB c

  d : ℕ
  d_prime : d.Prime
  d_mod : d % 16 = 7
  bE : E
  bE_sq : bE ^ 2 = -(d : E)
  ch : Gal(E/ℚ) →* ℂˣ
  ch_spec : ∀ σ : Gal(E/ℚ), (σ bE = bE → ch σ = 1) ∧ (σ bE ≠ bE → ch σ = -1)

  card_inertia_d : Nat.card (inertiaB E d) = 2

  ps : Gal(E/ℚ) →* ℂˣ
  ps_order : orderOf ps = 2
  ps_c : ps c = -1
  ps_inertia : ∀ σ ∈ inertiaB E d, ps σ = 1

  thE : E
  thE_spec : ∀ φ : E →+* ℂ, ∃ ζ : ℂ, IsPrimitiveRoot ζ (4 * 2 ^ e) ∧ φ thE = ζ + ζ⁻¹

  A0 : Subgroup Gal(E/ℚ)
  base_exponent_le_a : A0 ≤ ch.ker ⊓ ps.ker
  A0_inf_stabilizer_trivial : A0 ⊓ MulAction.stabilizer Gal(E/ℚ) thE = ⊥
  index_A0_eq_o : A0.relIndex (ch.ker ⊓ ps.ker) = T.o

  z_ge : 11 ≤ zR T X
  split_small : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ zR T X → SplitsB ℚ⟮bE⟯ p
  split_ram : ∀ l : ℕ, l.Prime → l ≠ d → RamifiedB E l → SplitsB ℚ⟮bE⟯ l

  small : Set ℕ
  large : Set ℕ
  ram_eq : {l : ℕ | l.Prime ∧ l ≠ d ∧ RamifiedB E l} = small ∪ large
  small_spec : ∀ l ∈ small, (l : ℝ) ≤ zR T X / 4 ∧ T.SM l
  large_spec : ∀ l ∈ large, zR T X / 2 < Real.log l ∧ Nat.card (inertiaB E l) = 2
  large_subsingleton : large.Subsingleton

  log_d_gt : zR' T X / 2 < Real.log d
  log_d_le : Real.log d ≤ zR' T X
  log_large_le : ∀ l ∈ large, Real.log l ≤ zR T X
  Nsharp : ℕ
  cond_dvd : conductorB E ∣ Nsharp
  log_Nsharp : Real.log Nsharp ≤ 3 * zR' T X

  qs : ℕ
  qs_prime : qs.Prime
  qs_ne : qs ≠ d
  qs_mod : qs % 8 = 3
  qs_split : SplitsB ℚ⟮bE⟯ qs
  log_qs_gt : zR T X / 2 < Real.log qs
  log_qs_le : Real.log qs ≤ zR T X
  large_eq_qs : ∀ l ∈ large, l = qs
  Nsharp_eq : Nsharp = Nat.lcm (conductorB E) qs

  rr : ℕ
  rr' : ℕ
  rr_prime : rr.Prime
  rr'_prime : rr'.Prime
  rr_odd : Odd rr
  rr'_odd : Odd rr'
  rr_lt : rr < rr'
  rr'_lt : rr' < 2 * rr
  rr_unram : ¬ RamifiedB E rr
  rr'_unram : ¬ RamifiedB E rr'
  rr'_le_alt : (rr' : ℝ) ≤ zR T X
  rr'_le : rr' ≤ T.rrBound

namespace PreHostB

variable {T : HostType} {X x : ℝ} {E : Type} [Field E] [NumberField E] [IsAbelianGalois ℚ E]
  (Q : PreHostB T X x E)

def Chat : Set (Gal(E/ℚ) →* ℂˣ) :=
  {ξ | (∀ g ∈ Q.A0, ξ g = 1) ∧ ξ Q.c = 1 ∧ ∀ g ∈ inertiaB E Q.d, ξ g = 1}

def Xplus : Set (Gal(E/ℚ) →* ℂˣ) := {χ | ∃ ξ ∈ Q.Chat, χ = ξ ∨ χ = ξ * Q.ps}

def Xminus : Set (Gal(E/ℚ) →* ℂˣ) := {χ | ∃ ξ ∈ Q.Xplus, χ = Q.ch * ξ}

def bounded : Set PrimChar := (dirSet Q.Xplus \ T.kept) ∪ dirSet Q.Xminus

def fixedA0Chars : Set PrimChar := dirSet {χ : Gal(E/ℚ) →* ℂˣ | ∀ g ∈ Q.A0, χ g = 1}

def BoundedCharsPointwise : Prop := ∀ ψ ∈ Q.bounded, ‖GP ψ x‖ ≤ x ^ (1 / 2 + T.eps)

def BoundedCharsMeanSquare : Prop :=
  ∑ᶠ (ψ : PrimChar) (_ : ψ ∈ Q.bounded),
      ∫ y in (X ^ (1 / (T.J : ℝ)))..X, ‖GP ψ y‖ ^ 2 * y ^ (-1 - 2 * T.eps) / y ≤ 1

structure HostConditions : Prop where
  kept_sub : T.kept ⊆ dirSet Q.Xplus
  a : ∀ ψ ∈ dirSet (Set.univ : Set (Gal(E/ℚ) →* ℂˣ)), ∀ y : ℝ, Xprime T x / 3 ≤ y →
    ‖GP ψ y‖ ≤ y * Real.exp (-(T.cA * x ^ (T.eps / 8)))
  b_ch : ∀ ψ, IsDirOf Q.ch ψ → ‖kappaP ψ‖ ≤ x ^ T.eps
  b_bdd : ∀ ψ ∈ Q.bounded, ‖kappaP ψ‖ ≤ T.CB * Real.log X
  c : Q.BoundedCharsPointwise ∨ Q.BoundedCharsMeanSquare
  e_some : ∀ κ, T.psK = some κ → IsDirOf Q.ps κ
  e_none : T.psK = none → ∀ ψ ∈ T.kept, ¬ IsDirOf Q.ps ψ

end PreHostB

structure VVField where
  VV : (E : Type) → [Field E] → [NumberField E] → ℕ → ENNReal
  mono : ∀ (E : Type) [Field E] [NumberField E], Monotone (VV E)
  iso : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'],
    Nonempty (E ≃ₐ[ℚ] E') → VV E = VV E'

class HostB (T : HostType) (V : VVField) (X x : ℝ) (E : Type) [Field E] [NumberField E]
    [IsAbelianGalois ℚ E] extends PreHostB T X x E where
  ha10 : toPreHostB.HostConditions
  ha11 : V.VV E (T.t x) ≤ ENNReal.ofReal (Real.exp (x ^ T.eps) ^ (1 / 2 : ℝ))

end HostParam
