import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField

section Point

variable {D : D7}

def FixedAt (L : SizeData₂ D) : Prop :=
  L.Ct = 401 ∧
  L.j0 = ⌈Real.logb 5 ((D.R.n : ℝ) * (D.R.N D.R.m : ℝ) / (D.R.m : ℝ))⌉₊ ∧
  D.host.Lw = 10 * ⌈(L.Ct + 4) * Real.log L.sc.x⌉₊ + 2 * ⌈30 / L.sc.eps⌉₊ + 22 ∧
  D.host.ccK = ⊤ ∧
  ∀ τ τ' : D.what₂.Tau, (D.hc τ).v = (D.hc τ').v

def RankWindowAt (L : SizeData₂ D) : Prop :=
  (L.sc.x ^ (2 + 8 * L.sc.eps) ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) ∧ 4 ≤ D.R.n) ∧
  ((L.sc.x * L.sc.delta1) ^ (1 / 2 : ℝ) ≤ (D.R.m : ℝ) ∧ (D.R.m : ℝ) ≤ 2 * (L.sc.x * L.sc.delta1) ^ (1 / 2 : ℝ)) ∧
  (L.sc.x ^ (9 / 2 + 10 * L.sc.eps) ≤ (D.R.k : ℝ) ∧ (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps))

def CoarseWindowAt (L : SizeData₂ D) : Prop :=
  L.sc.x ^ (1 / 2 - L.sc.eps / 8) ≤ (D.R.m : ℝ) ∧ (D.R.m : ℝ) ≤ L.sc.x ^ (1 / 2 : ℝ) ∧ 44 ≤ D.R.m ∧
  L.sc.x ^ (2 + 8 * L.sc.eps) / 2 ≤ (D.R.n : ℝ) ∧ (D.R.n : ℝ) ≤ 2 * L.sc.x ^ (2 + 8 * L.sc.eps) ∧
  (D.R.k : ℝ) ≤ 2 * L.sc.x ^ (9 / 2 + 10 * L.sc.eps)

def TypePrimeWindowAt (L : SizeData₂ D) (C : ℝ) : Prop :=
  ∃ Y : ℝ, ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ Y ∧
    (D.R.r : ℝ) ^ 4 * (LevelStarExponents.condE D : ℝ) ^ C ≤ Y ^ (1 / 4 : ℝ) ∧ 2 * Y ≤ L.sc.b ^ 9 ∧
    ∀ i : Fin 2, Y ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ 2 * Y

def BelowCutAt (L : SizeData₂ D) : Prop :=
  (D.host.q : ℝ) < L.sc.X' ∧ (D.host.d : ℝ) < L.sc.X' ∧ (D.host.pde : ℝ) < L.sc.X' ∧ (D.host.pde' : ℝ) < L.sc.X' ∧
  L.sc.X' ≤ L.sc.X'' D.R.n ∧ 2 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) + 1 < L.sc.X'

def WindowsAt (L : SizeData₂ D) (C : ℝ) : Prop :=
  RankWindowAt L ∧ CoarseWindowAt L ∧ TypePrimeWindowAt L C ∧ BelowCutAt L

def hWidth (L : SizeData₂ D) : ℝ := L.sc.b + L.Sc + L.etaSz + (D.R.t : ℝ) + 1

def lJ (L : SizeData₂ D) : ℝ :=
  (D.R.m : ℝ) * L.sc.b * L.sc.x ^ L.sc.eps / ((D.R.k : ℝ) * ((D.R.m : ℝ) + (D.R.t : ℝ)) * Real.log (3 * hWidth L))

def IsSmallPrime (L : SizeData₂ D) (q0 : ℕ) : Prop :=
  q0.Prime ∧ q0 ∈ D.host.levelPrimes ∧ q0 ≡ 1 [MOD LevelStarExponents.condE D] ∧
  (q0 ≠ D.host.pde ∧ q0 ≠ D.host.pde' ∧ ∀ i : Fin 2, q0 ≠ D.host.g i) ∧
  Real.log q0 ≤ L.sc.L ∧ (q0 : ℝ) ≤ lJ L ∧ (q0 : ℝ) < L.sc.X'

def SmallPrimeAt (L : SizeData₂ D) : Prop := ∃ q0 : ℕ, IsSmallPrime L q0

def SmallPrimeSharpAt (L : SizeData₂ D) (C8 : ℝ) : Prop :=
  ∃ q0 : ℕ, IsSmallPrime L q0 ∧ Real.log q0 ≤ C8 * Real.log (LevelStarExponents.condE D : ℝ) ∧
    C8 * Real.log (LevelStarExponents.condE D : ℝ) ≤ 2 * C8 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 ∧
    2 * C8 * L.sc.x ^ (L.sc.eps / 5) * Real.log L.sc.x ^ 2 ≤ L.sc.L

def tameList (D : D7) (k : Fin 2) (v : D.nd.PlG k) : Option (Fin D.R.m × Bool) → (ZMod (D.host.g k))ˣ
  | none => 1
  | some (j, true) => D.nd.chiT k v j
  | some (j, false) => (D.nd.chiT k v j)⁻¹

def TameDistinct (D : D7) : Prop := ∀ (k : Fin 2) (v : D.nd.PlG k), Function.Injective (tameList D k v)

def TameInjective (D : D7) : Prop := ∀ (k : Fin 2) (v : D.nd.PlG k), Function.Injective (D.nd.chiT k v)

def TameDistinctMod (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k) (l : ℕ), l.Prime → l ∉ Formalism.CyclotomicNorms.BB D.R.r (D.host.g k) →
    ∀ (a a' : Option (Fin D.R.m × Bool)) (e : ℕ), (tameList D k v a * (tameList D k v a')⁻¹) ^ l ^ e = 1 → a = a'

def TameEven (D : D7) : Prop := ∀ (k : Fin 2) (v : D.nd.PlG k) (j : Fin D.R.m), IsSquare (D.nd.chiT k v j)

def TameOfGenerator (D : D7) : Prop :=
  ∀ (k : Fin 2) (v : D.nd.PlG k), ∃ γ : (ZMod (D.host.g k))ˣ, Subgroup.zpowers γ = ⊤ ∧
    ∀ j : Fin D.R.m, D.nd.chiT k v j = γ ^ (2 * (j.1 + 1)) ∨ D.nd.chiT k v j = (γ ^ (2 * (j.1 + 1)))⁻¹

end Point

section Family

variable {eps : ℝ}

def AtLarge (Fm : FamP eps) (P : ∀ x : ℝ, Fm.Ix x → Prop) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, P x i

def FixedValues (Fm : FamP eps) : Prop := AtLarge Fm fun x i => FixedAt (Fm.L x i)

def Windows (Fm : FamP eps) : Prop := AtLarge Fm fun x i => WindowsAt (Fm.L x i) Fm.CY

def SmallPrime (Fm : FamP eps) : Prop := AtLarge Fm fun x i => SmallPrimeAt (Fm.L x i)

def DistinctTame (Fm : FamP eps) : Prop := AtLarge Fm fun x i => TameDistinct (Fm.D x i)

def WeightReq (Fm : FamP eps) : Prop :=
  AtLarge Fm fun x i => Formalism.MainNotions.AuxBlock8.WReq (Fm.Gx x i) Fm.GK (G.aL (Fm.L x i)) (G.bL (Fm.L x i))

def Duties (Fm : FamP eps) : Prop :=
  FixedValues Fm ∧ Windows Fm ∧ SmallPrime Fm ∧ DistinctTame Fm ∧ WeightReq Fm

def DutiesSharp (Fm : FamP eps) : Prop :=
  Duties Fm ∧ (Fm.CnW = 10 ∧ Fm.eP = 12 ∧ Fm.Cp = 1 ∧ Fm.cTO = 377) ∧
  (AtLarge Fm fun x i => SmallPrimeSharpAt (Fm.L x i) Fm.Cpde) ∧
  AtLarge Fm fun x i => TameDistinctMod (Fm.D x i) ∧ TameEven (Fm.D x i)

def HasConsts (Fm : FamP eps) (C : FC) : Prop :=
  Fm.Ct = C.Ct ∧ Fm.Cc = C.Cc ∧ Fm.CT2 = C.CT2 ∧ Fm.CGam = C.CGam ∧ Fm.Csz = C.Csz ∧ Fm.Cr = C.Cr ∧ Fm.CTu = C.CTu ∧
  Fm.GK = C.GK ∧ Fm.cX = C.cX ∧ Fm.PK = C.PK ∧ Fm.PT = C.PT

def IsPoint (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) {C : FC} (p : GlobalTheory.EX.Pt C) : Prop :=
  p.D = Fm.D x i ∧ HEq p.L (Fm.L x i) ∧ HEq p.gatT (Fm.gatT x i) ∧ HEq p.ta.Gx (Fm.Gx x i) ∧ HEq p.ta.Gy (Fm.Gy x i) ∧
  HEq p.xa.X (Fm.X x i) ∧ HEq p.xa.ex (Fm.ex x hx i)

end Family

def kitClass (Q : GlobalTheory.EX.PtProp) : FamClass := fun {eps} Fm =>
  ∃ (C : FC) (cD ch : ℝ), GlobalTheory.EX.Std C ∧ HasConsts Fm C ∧
    ∀ (x : ℝ) (hx : Fm.x1 < x), Nonempty (Fm.Ix x) → ∃ s : Scale, s.x = x ∧ s.eps = eps ∧ ∃ k : GlobalTheory.EX.Kit C cD ch s,
      (∀ j, (k.pt j).Has Q) ∧ ∀ i : Fm.Ix x, ∃ j, IsPoint Fm x hx i (k.pt j)

def ClassDuties (𝒞 : FamClass) : Prop := ∀ (eps : ℝ) (Fm : FamP eps), 𝒞 Fm → Duties Fm

def DutyClaim (Q : GlobalTheory.EX.PtProp) : Prop := ClassDuties (kitClass (GlobalTheory.EX.withDuty Q))

def CarriesTame (Q : GlobalTheory.EX.PtProp) : Prop :=
  ∀ D L gatT Gx Gy K X cX ex, Q D L gatT Gx Gy K X cX ex → TameOfGenerator D

def Claim : Prop := ∀ Q : GlobalTheory.EX.PtProp, CarriesTame Q → DutyClaim Q

theorem TameDistinct.injective {D : D7} (h : TameDistinct D) : TameInjective D := fun k v a b hab => by
  have := h k v (a₁ := some (a, true)) (a₂ := some (b, true)) hab
  simpa using this

theorem SmallPrimeSharpAt.weak {D : D7} {L : SizeData₂ D} {C8 : ℝ} (h : SmallPrimeSharpAt L C8) : SmallPrimeAt L :=
  h.imp fun _ h => h.1

theorem lJ_den_pos {D : D7} (L : SizeData₂ D) :
    0 < (D.R.k : ℝ) * ((D.R.m : ℝ) + (D.R.t : ℝ)) * Real.log (3 * hWidth L) := by
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have hk : ((D.R.m + 3 : ℕ) : ℝ) ≤ D.R.k := by exact_mod_cast D.R.m_add_three_le_k
  push_cast at hk
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hb : 0 < L.sc.b := Real.exp_pos _
  have h1 : 1 < 3 * hWidth L := by
    unfold hWidth
    have := L.Sc_pos
    have := L.etaSz_pos
    linarith
  exact mul_pos (mul_pos (by linarith) (by linarith)) (Real.log_pos h1)

end GlobalTheory.IndefiniteRowSideFullHecke.TameGeneratorWindow

end
