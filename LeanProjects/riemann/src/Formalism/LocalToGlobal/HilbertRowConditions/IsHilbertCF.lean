import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.LocalToGlobal.Divisibility.LiftLat
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Rows

open Formalism.BasicNotions Formalism.L2.Host

def muFld (n : ℕ) : Fld := IntermediateField.adjoin ℚ {x : Qb | x ^ n = 1}

def valsOf {E : Type} [Field E] [NumberField E] (ι : Qb →+* ℂ) (s : ℝ) (χ : HChar E) : Set Qb :=
  {x | ∃ v, χ.UnrAt v ∧ ι x = χ.valTw s v}

def valsFld (D : D7) (T : HostTied D) (C : CharFrame D) : Fld :=
  IntermediateField.adjoin ℚ
    ((⋃ j, valsOf T.fr.ι 0 (C.mu0 j)) ∪ valsOf T.fr.ι (1 / 2) C.eta ∪
      valsOf T.fr.ι 0 C.del ∪ valsOf T.fr.ι 0 C.del')

def AbelOver (E' L : Fld) : Prop :=
  E' ≤ L ∧ (∀ σ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ E', σ x = x) → ∀ y ∈ L, σ y ∈ L) ∧
    ∀ σ τ : Qb ≃ₐ[ℚ] Qb, (∀ x ∈ E', σ x = x) → (∀ x ∈ E', τ x = x) → ∀ y ∈ L, σ (τ y) = τ (σ y)

local instance nfOfFin (L : Fld) [FiniteDimensional ℚ L] : NumberField L := {}

def UnramOverK (d : ℕ) (L : Fld) [FiniteDimensional ℚ L] : Prop :=
  (NumberField.discr L).natAbs = d ^ (Module.finrank ℚ L / 2)

def IsHilbertCF (d : ℕ) (H : Fld) [FiniteDimensional ℚ H] : Prop :=
  AbelOver (Formalism.L2.Host.KQ d) H ∧ UnramOverK d H ∧
    ∀ (H' : Fld) [FiniteDimensional ℚ H'], AbelOver (Formalism.L2.Host.KQ d) H' → UnramOverK d H' → H' ≤ H

structure KsPieces (D : D7) (T : HostTied D) where
  HK : Fld
  rcf : Fld
  M : Fld
  MDel : Fld
  KPs : Fld
  [HK_fin : FiniteDimensional ℚ HK]
  [rcf_fin : FiniteDimensional ℚ rcf]
  [M_fin : FiniteDimensional ℚ M]
  [MDel_fin : FiniteDimensional ℚ MDel]
  [KPs_fin : FiniteDimensional ℚ KPs]

  HK_hilb : IsHilbertCF D.host.d HK

  E_le_rcf : T.fr.j.fieldRange ≤ rcf

  rcf_abel : AbelOver T.fr.j.fieldRange rcf

  rcf_cond : (NumberField.discr rcf).natAbs ∣
    (NumberField.discr D.host.E).natAbs ^ (Module.finrank ℚ rcf / Module.finrank ℚ D.host.E) *
      (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') ^ Module.finrank ℚ rcf

  HK_le_M : HK ≤ M

  M_deg : Module.finrank ℚ M ≤ Module.finrank ℚ HK * Nat.card (GL (Fin 2) (ZMod 12))

  M_ram : ∀ p : ℕ, p.Prime → p ∣ (NumberField.discr M).natAbs → p ∣ 6 * D.host.d

  MDel_gen : ∃ (y : Qb) (h : y ^ 12 ∈ M), y ≠ 0 ∧
    (∃ I : FractionalIdeal (nonZeroDivisors (NumberField.RingOfIntegers M)) M,
      FractionalIdeal.spanSingleton (nonZeroDivisors (NumberField.RingOfIntegers M)) (⟨y ^ 12, h⟩ : M) = I ^ 12) ∧
    MDel = M ⊔ IntermediateField.adjoin ℚ {y}

  MDel_ram : ∀ p : ℕ, p.Prime → p ∣ (NumberField.discr MDel).natAbs → p ∣ 6 * D.host.d

  KPs_gen : ∃ S : Fin D.R.m → Finset Qb,
    (∀ j, (S j).card ≤ Nat.log 2 (NumberField.classNumber D.host.E)) ∧
    (∀ j, ∀ y ∈ S j, ∃ n : ℕ, 0 < n ∧ n ∣ NumberField.classNumber D.host.E ∧ y ^ n ∈ T.fr.j.fieldRange) ∧
    KPs = T.fr.j.fieldRange ⊔ muFld (NumberField.classNumber D.host.E) ⊔
      IntermediateField.adjoin ℚ (⋃ j, (S j : Set Qb))

  KPs_ram : ∀ p : ℕ, p.Prime → p ∣ (NumberField.discr KPs).natAbs →
    p ∣ NumberField.classNumber D.host.E * (NumberField.discr D.host.E).natAbs

  M_le_MDel : M ≤ MDel

  E_le_KPs : T.fr.j.fieldRange ≤ KPs

theorem KsPieces.K_le_M {D : D7} {T : HostTied D} (P : KsPieces D T) : Formalism.L2.Host.KQ D.host.d ≤ P.M :=
  le_trans (P.HK_hilb.1.1) P.HK_le_M

def rootOrders (D : D7) : List ℕ :=
  [Nat.card (G0g D.nd), D.host.g 0 * (D.host.g 0 - 1), D.host.g 1 * (D.host.g 1 - 1), 3 ^ 4, 5 ^ 4]

def KsQ (D : D7) (T : HostTied D) (C : CharFrame D) (P : KsPieces D T) : Fld :=
  T.fr.j.fieldRange ⊔ (⨆ n ∈ rootOrders D, muFld n) ⊔ valsFld D T C ⊔ P.rcf ⊔ P.M ⊔ P.MDel ⊔ P.KPs

def OsQ (K : Fld) : Set Qb := {x | x ∈ K ∧ IsIntegral ℤ x}

def getQ {n : ℕ} (f : Fin n → ℚ) (i : ℕ) : ℚ := if h : i < n then f ⟨i, h⟩ else 0

def vPar (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  if i < D.R.k - 1 then getQ (D.hc τ).v i else -getQ (D.hc τ).b (i - (D.R.k - 1))

def aPlus (D : D7) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ) : ℚ :=
  vPar D τ i + getQ (D.hc τ).e (j - 1) - ((D.R.nV : ℚ) + 1 - 2 * ((i : ℚ) + 1)) / 2 -
    (((D.R.sigW j).1 : ℚ) - (D.R.sigW j).2) / 2

def aMinusAt (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c₀ : ℕ) : ℚ :=
  (getQ (D.hc τ).b (j + c₀) - getQ (D.hc τ).e (j - 1)) - ((D.R.t : ℚ) - 1 + 2 * ((c₀ : ℚ) + 1)) / 2

def kaSmallOf (D : D7) (j : ℕ) (τ : D.what₂.Tau) (c₀ : ℕ) : ℚ := -aMinusAt D j τ c₀

end Formalism.L2.Rows
