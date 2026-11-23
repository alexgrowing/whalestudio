import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.PrimePairSizeCondition

noncomputable section

namespace Formalism.HC

namespace An

abbrev abelian₂ (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n : ℝ)

def logDerivativeAtOne {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : ℂ :=
  deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1

def G (y : ℝ) : ℝ :=
  (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, abelian₂ n * max (y / n - 1) 0) -
    y * (Real.log y - 1 - Real.eulerMascheroniConstant)

def sumLamChi {N : ℕ} (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, (abelian₂ n : ℂ) * χ (n : ZMod N) * ((max (y / n - 1) 0 : ℝ) : ℂ)

open Classical in

def gChi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then ((G y : ℝ) : ℂ) else sumLamChi χ y + (y : ℂ) * logDerivativeAtOne χ

def Induces {N : ℕ} (χ : DirichletCharacter ℂ N) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  χ.IsPrimitive ∧ ∀ a : ℕ, a.Coprime M → χ (a : ZMod N) = f a

private theorem pchar_ext_of_N_eq_of_heq (ψ ψ' : PChar) (hN : ψ.N = ψ'.N) (hχ : HEq ψ.χ ψ'.χ) : ψ = ψ' := by
  cases ψ
  cases ψ'
  cases hN
  cases hχ
  rfl

private theorem heq_of_changeLevel_eq_of_level_eq {N N' L : ℕ} [NeZero L] (χ : DirichletCharacter ℂ N)
    (χ' : DirichletCharacter ℂ N') (d1 : N ∣ L) (d2 : N' ∣ L) (hNN : N = N')
    (heq : DirichletCharacter.changeLevel d1 χ = DirichletCharacter.changeLevel d2 χ') : HEq χ χ' := by
  subst hNN
  exact heq_of_eq (DirichletCharacter.changeLevel_injective d1 heq)

theorem Induces.unique {ψ ψ' : PChar} {f : ℕ → ℂ} {M : ℕ} (hM : M ≠ 0) (h : Induces ψ.χ f M) (h' : Induces ψ'.χ f M) :
    ψ = ψ' := by
  haveI := ψ.ne
  haveI := ψ'.ne
  have hN0 : ψ.N ≠ 0 := NeZero.ne _
  have hN0' : ψ'.N ≠ 0 := NeZero.ne _
  haveI : NeZero (ψ.N * ψ'.N * M) := ⟨mul_ne_zero (mul_ne_zero hN0 hN0') hM⟩
  have d1 : ψ.N ∣ ψ.N * ψ'.N * M := ⟨ψ'.N * M, by ring⟩
  have d2 : ψ'.N ∣ ψ.N * ψ'.N * M := ⟨ψ.N * M, by ring⟩
  have heq : DirichletCharacter.changeLevel d1 ψ.χ = DirichletCharacter.changeLevel d2 ψ'.χ := by
    apply MulChar.ext
    intro u
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd]
    have hcop : (u : ZMod (ψ.N * ψ'.N * M)).val.Coprime (ψ.N * ψ'.N * M) := ZMod.val_coe_unit_coprime u
    have hcM : (u : ZMod (ψ.N * ψ'.N * M)).val.Coprime M :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_left M (ψ.N * ψ'.N)) hcop
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, h.2 _ hcM, h'.2 _ hcM]
  have hc : ψ.N = ψ'.N := by
    have e1 := DirichletCharacter.conductor_changeLevel ψ.χ d1
    have e2 := DirichletCharacter.conductor_changeLevel ψ'.χ d2
    rw [heq, e2] at e1
    calc ψ.N = ψ.χ.conductor := ((DirichletCharacter.isPrimitive_def ψ.χ).mp ψ.prim).symm
      _ = ψ'.χ.conductor := e1.symm
      _ = ψ'.N := (DirichletCharacter.isPrimitive_def ψ'.χ).mp ψ'.prim
  exact pchar_ext_of_N_eq_of_heq ψ ψ' hc (heq_of_changeLevel_eq_of_level_eq ψ.χ ψ'.χ d1 d2 hc heq)

theorem induces_of {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    Induces (PChar.of χ).χ (fun a => χ (a : ZMod N)) N := by
  refine ⟨DirichletCharacter.primitiveCharacter_isPrimitive χ, fun a ha => ?_⟩
  show χ.primitiveCharacter (a : ZMod χ.conductor) = χ (a : ZMod N)
  have hu : ((ZMod.unitOfCoprime a ha : (ZMod N)ˣ) : ZMod N) = (a : ZMod N) :=
    ZMod.coe_unitOfCoprime a ha
  conv_rhs => rw [← DirichletCharacter.changeLevel_primitiveCharacter χ, ← hu,
    DirichletCharacter.changeLevel_eq_cast_of_dvd, hu,
    ZMod.cast_natCast (DirichletCharacter.conductor_dvd_level χ)]

end An

namespace Frame

variable (φ : Frame)

abbrev Char : Type := φ.GG →* ℂˣ

def psC : φ.Char := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp φ.chQ

def TrivialOnFirstFactor {φ : Frame} (θ : φ.Char) : Prop := ∀ s ∈ φ.A0, θ (φ.tau1 s) = 1

def Chat : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = 1 ∧ θ φ.cc = 1}

def Xp : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = 1}

def Xm : Set φ.Char := {θ | TrivialOnFirstFactor θ ∧ θ φ.iod = -1}

end Frame

namespace HostRaw

variable {φ : Frame} (H : HostRaw φ)

def dir (θ : φ.Char) : DirichletCharacter ℂ H.condN := MulChar.ofUnitHom (θ.comp H.art)

def dirAt (θ : φ.Char) (a : ℕ) : ℂ := H.dir θ (a : ZMod H.condN)

def IsPrimOf (θ : φ.Char) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := An.Induces χ (H.dirAt θ) H.condN

def prim (θ : φ.Char) : PChar := PChar.of (H.dir θ)

theorem isPrimOf_prim (θ : φ.Char) : H.IsPrimOf θ (H.prim θ).χ :=
  An.induces_of (H.dir θ)

theorem isPrimOf_iff (θ : φ.Char) (ψ : PChar) : H.IsPrimOf θ ψ.χ ↔ ψ = H.prim θ := by
  constructor
  · intro h
    have hN : H.condN ≠ 0 := NeZero.ne _
    exact An.Induces.unique hN h (H.isPrimOf_prim θ)
  · rintro rfl
    exact H.isPrimOf_prim θ

theorem dir_unit (θ : φ.Char) (u : (ZMod H.condN)ˣ) : H.dir θ u = θ (H.art u) := by
  rw [dir, MulChar.ofUnitHom_coe]
  rfl

def IsCharE {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop := ∃ θ : φ.Char, H.IsPrimOf θ χ

def Kept (S : Finset PChar) (θ : φ.Char) : Prop := ∃ ψ ∈ S, H.IsPrimOf θ ψ.χ

theorem kept_iff (S : Finset PChar) (θ : φ.Char) : H.Kept S θ ↔ H.prim θ ∈ S := by
  constructor
  · rintro ⟨ψ, hψ, h⟩
    rwa [(H.isPrimOf_iff θ ψ).mp h] at hψ
  · intro h
    exact ⟨H.prim θ, h, H.isPrimOf_prim θ⟩

def Bounded (S : Finset PChar) : Set φ.Char := {θ | (θ ∈ φ.Xp ∧ ¬ H.Kept S θ) ∨ θ ∈ φ.Xm}

def KeptInXp (S : Finset PChar) : Prop := ∀ ψ ∈ S, ∃ θ ∈ φ.Xp, H.IsPrimOf θ ψ.χ

def KeptEqChat (S : Finset PChar) : Prop :=
  (∀ ψ ∈ S, ∃ θ ∈ φ.Chat, H.IsPrimOf θ ψ.χ) ∧ ∀ θ ∈ φ.Chat, H.Kept S θ

def KeptEqXp (S : Finset PChar) : Prop := H.KeptInXp S ∧ ∀ θ ∈ φ.Xp, H.Kept S θ

def ChebyshevCharacterBound (x eps c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsCharE χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖An.gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

def LogDerivativeBound (S : Finset PChar) (X x eps C : ℝ) : Prop :=
  (∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf φ.chC χ → ‖An.logDerivativeAtOne χ‖ ≤ x ^ eps) ∧
  ∀ θ ∈ H.Bounded S, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.logDerivativeAtOne χ‖ ≤ C * Real.log X

def BoundedCharsPointwise (S : Finset PChar) (x eps : ℝ) : Prop :=
  ∀ θ ∈ H.Bounded S, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), H.IsPrimOf θ χ →
    ‖An.gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps)

def ExceptionalCharacterKept (S : Finset PChar) (psK : Option PChar) : Prop :=
  (∀ ψ, psK = some ψ → H.IsPrimOf φ.psC ψ.χ) ∧ (psK = none → ¬ H.Kept S φ.psC)

end HostRaw

structure HostConditions (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostRaw φ) : Prop where
  kept : H.KeptInXp T.KEPT
  a : H.ChebyshevCharacterBound x T.eps κ.c
  b : H.LogDerivativeBound T.KEPT X x T.eps κ.C
  c1 : H.BoundedCharsPointwise T.KEPT x T.eps
  e : H.ExceptionalCharacterKept T.KEPT T.psK

structure PreHostAn (T : HType) (κ : HConst) (X x : ℝ) {φ : Frame} (H : HostAx φ) (rr rr' : ℕ) : Prop
    extends PreHost T κ X x H rr rr' where
  ha10 : HostConditions T κ X x H.toHostRaw

end Formalism.HC

end
