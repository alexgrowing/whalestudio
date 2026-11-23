import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.HolCuspLevDeltaNeBot

noncomputable section

open GlobalTheory.SmGL GlobalTheory.TfJl ValuativeRel Matrix

namespace GlobalTheory.IwFn

section Lin

variable {G : Type} [Group G] {U : Subgroup G}

def hLin {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → HeckeFn U) : HeckeFn U where
  toFun g := ∑ i ∈ s, c i * (f i).toFun g
  left u hu g := by simp only [(f _).left u hu]
  right u hu g := by simp only [(f _).right u hu]
  fin := by
    refine (s.finite_toSet.biUnion fun i _ => (f i).fin).subset fun q hq => ?_
    obtain ⟨i, hi, h⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    exact Set.mem_iUnion₂.2 ⟨i, hi, right_ne_zero_of_mul h⟩

theorem hLin_apply {ι : Type} (s : Finset ι) (c : ι → ℂ) (f : ι → HeckeFn U) (g : G) :
    (hLin s c f).toFun g = ∑ i ∈ s, c i * (f i).toFun g := rfl

end Lin

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {a : ℕ}

def sList (S : Finset (Fin a)) : List (Fin a) := (List.finRange a).filter (· ∈ S)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem nodup_sList (S : Finset (Fin a)) : (sList S).Nodup := (List.nodup_finRange a).filter _

theorem mem_sList {S : Finset (Fin a)} {c : Fin a} : c ∈ sList S ↔ c ∈ S := by
  simp [sList]

def cyc (S : Finset (Fin a)) : Equiv.Perm (Fin a) := (sList S).formPerm

def dEnt (ϖ : kˣ) (S : Finset (Fin a)) (c : Fin a) : kˣ := if (sList S).head? = some c then ϖ else 1

def wS (ϖ : kˣ) (S : Finset (Fin a)) : GL (Fin a) k :=
  GeneralLinearGroup.mkOfDetNeZero ((cyc S).permMatrix k * diagonal fun c => (dEnt k ϖ S c : k)) (by
    rw [det_mul, det_permutation, det_diagonal]
    refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.2 fun c _ => Units.ne_zero _)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (cyc S)) with h | h <;> simp [h])

theorem val_wS (ϖ : kˣ) (S : Finset (Fin a)) :
    (wS k ϖ S : Matrix (Fin a) (Fin a) k) = (cyc S).permMatrix k * diagonal fun c => (dEnt k ϖ S c : k) := rfl

def phiS (ϖ : kˣ) (S : Finset (Fin a)) : HeckeFn (iwahori k (Fin a)) :=
  HeckeFn.dc (IwahoriOnto.isOpen_iwahori k (Fin a)) (IwahoriOnto.isCompact_iwahori k (Fin a)) (wS k ϖ S)

theorem phiS_toFun (ϖ : kˣ) (S : Finset (Fin a)) : (phiS k ϖ S).toFun = dcFn (iwahori k (Fin a)) (wS k ϖ S) := rfl

theorem phiS_self (ϖ : kˣ) (S : Finset (Fin a)) : (phiS k ϖ S).toFun (wS k ϖ S) = 1 := dcFn_self _ _

def phiClosed (ϖ : kˣ) (T : Finset (Fin a)) : HeckeFn (iwahori k (Fin a)) :=
  hLin (Finset.univ.filter fun S : Finset (Fin a) => S.Nonempty ∧ T ⊆ S) (fun _ => 1) (phiS k ϖ)

def kotQ (ϖ : kˣ) (Q : ℂ) : HeckeFn (iwahori k (Fin a)) :=
  hLin (Finset.univ.filter fun S : Finset (Fin a) => S.Nonempty) (fun S => (1 - Q) ^ (S.card - 1)) (phiS k ϖ)

def kot (ϖ : kˣ) : HeckeFn (iwahori k (Fin a)) := kotQ k ϖ (Nat.card 𝓀[k] : ℂ)

theorem kot_apply (ϖ : kˣ) (g : GL (Fin a) k) :
    (kot (a := a) k ϖ).toFun g = ∑ S ∈ Finset.univ.filter fun S : Finset (Fin a) => S.Nonempty,
      (1 - (Nat.card 𝓀[k] : ℂ)) ^ (S.card - 1) * (phiS k ϖ S).toFun g := rfl

def IsCentralBC (r : ℕ) (f : HeckeFn (iwahori k (Fin a))) : Prop :=
  ∀ α : Fin a → ℂˣ, heckeFix (prinSeries fun i => unrChar k (α i)) f =
    ((((Nat.card 𝓀[k] : ℝ) ^ ((r : ℝ) * ((a : ℝ) - 1) / 2) : ℝ) : ℂ) * ∑ i, (α i : ℂ) ^ r) • LinearMap.id

def chainLat (ϖ : kˣ) (c : ℕ) : Set (Fin a → k) :=
  {v | ∀ i : Fin a, valuation k (v i) ≤ if (i : ℕ) < c then 1 else valuation k (ϖ : k)}

def iwahoriAdmissibleSet (ϖ : kˣ) : Set (GL (Fin a) k) :=
  {g | ord k (GeneralLinearGroup.det g) = 1 ∧
    ∀ c ≤ a, ∀ v ∈ chainLat (a := a) k ϖ c, (g : Matrix (Fin a) (Fin a) k) *ᵥ v ∈ chainLat k ϖ c}

def stratOf (ϖ : kˣ) (g : GL (Fin a) k) : Set (Fin a) :=
  {c | ∀ v ∈ chainLat (a := a) k ϖ ((c : ℕ) + 1), (g : Matrix (Fin a) (Fin a) k) *ᵥ v ∈ chainLat k ϖ c}

example (ϖ : kˣ) : (wS k ϖ ({0} : Finset (Fin 1)) : Matrix (Fin 1) (Fin 1) k) = !![(ϖ : k)] := by
  ext i j
  fin_cases i; fin_cases j
  simp [val_wS, cyc, sList, dEnt, Equiv.Perm.permMatrix, List.finRange, PEquiv.toMatrix]

example (ϖ : kˣ) : (wS k ϖ ({0, 1} : Finset (Fin 2)) : Matrix (Fin 2) (Fin 2) k) = !![0, 1; (ϖ : k), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [val_wS, cyc, sList, dEnt, Equiv.Perm.permMatrix, List.finRange, PEquiv.toMatrix, List.formPerm_pair]

example (ϖ : kˣ) : (phiS k ϖ ({1} : Finset (Fin 2))).toFun (wS k ϖ {1}) = 1 := phiS_self k ϖ _

example (ϖ : kˣ) : (kot (a := 1) k ϖ).toFun = (phiS k ϖ {0}).toFun := by
  funext g
  rw [kot_apply, show (Finset.univ.filter fun S : Finset (Fin 1) => S.Nonempty) = {{0}} from by decide]
  simp

example (ϖ : kˣ) (g : GL (Fin 2) k) : (kot (a := 2) k ϖ).toFun g = (phiS k ϖ {0}).toFun g + (phiS k ϖ {1}).toFun g +
    (1 - (Nat.card 𝓀[k] : ℂ)) * (phiS k ϖ {0, 1}).toFun g := by
  rw [kot_apply, show (Finset.univ.filter fun S : Finset (Fin 2) => S.Nonempty) = {{0}, {1}, {0, 1}} from by decide]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [add_assoc]

end GlobalTheory.IwFn
