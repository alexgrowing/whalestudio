import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
import Formalism.LocalToGlobal.Divisibility.DefGroup

noncomputable section

open NumberField Matrix Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped TensorProduct

namespace GlobalTheory.FlagBasis

def dualIdx (ρ k i : ℕ) : ℕ :=
  if i < ρ then 2 * ρ + k - i else if i < ρ + k then 2 * ρ + k - 1 - i else if i = ρ + k then i else 2 * ρ + k - i

def flagGram (A : Type) [CommRing A] (n ρ k : ℕ) : Matrix (Fin n) (Fin n) A :=
  fun i j => if j.val = dualIdx ρ k i.val then (if i.val = ρ + k then -1 else 1) else 0

def FlagCond {A : Type} [CommRing A] {n : ℕ} (P : A → Prop) (ρ k : ℕ) (ε : A) (m : Matrix (Fin n) (Fin n) A) : Prop :=
  (∀ i j : Fin n, j.val < ρ → j.val ≤ i.val → P ((m - 1) i j)) ∧
  (∀ i j : Fin n, j.val = ρ + k → ρ ≤ i.val → P ((m - 1) i j)) ∧
  ∀ i j : Fin n, ρ ≤ j.val → j.val < ρ + k → j.val ≤ i.val → P (ε * (m - 1) i j)

def rootSum {A : Type} [CommRing A] {n : ℕ} (ρ k : ℕ) (ε : A) (m : Matrix (Fin n) (Fin n) A) : A :=
  ∑ i : Fin n, ∑ j : Fin n,
    if (i.val + 1 < ρ ∧ j.val = i.val + 1) ∨ (i.val + 1 = ρ ∧ j.val = ρ + k) then m i j
    else if ρ ≤ i.val ∧ j.val = i.val + 1 ∧ j.val < ρ + k then ε * m i j else 0

def flagVec {V : Type} [AddCommGroup V] {ρ k : ℕ} (e0 f0 : Fin ρ → V) (z0 : V) (bw bwd : Fin k → V) (j : ℕ) : V :=
  if h : j < ρ then e0 ⟨j, h⟩
  else if h : j - ρ < k then bw ⟨j - ρ, h⟩ + bwd (Fin.rev ⟨j - ρ, h⟩)
  else if j = ρ + k then z0
  else if h : 2 * ρ + k - j < ρ then f0 ⟨2 * ρ + k - j, h⟩ else 0

def IsRefFrame (I : AutInst) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I)
    (ew : I.E ⊗[I.F] Af I.F) : Prop :=
  ((∀ a, e0 a ∈ I.Lf ∧ f0 a ∈ I.Lf) ∧ z0 ∈ I.Lf ∧ ∀ i, bw i ∈ I.Lf ∧ bwd i ∈ I.Lf) ∧
  (∀ a b, ZMod' I g (hA I (e0 a) (e0 b)) ∧ ZMod' I g (hA I (f0 a) (f0 b)) ∧
    ZMod' I g (hA I (e0 a) (f0 b) - if a = b then 1 else 0)) ∧
  (ZMod' I g (hA I z0 z0 + 1) ∧ ∀ a, ZMod' I g (hA I (e0 a) z0) ∧ ZMod' I g (hA I (f0 a) z0)) ∧
  (∀ i, ZMod' I g (hA I z0 (bw i)) ∧ ZMod' I g (hA I z0 (bwd i)) ∧
    ∀ a, ZMod' I g (hA I (e0 a) (bw i)) ∧ ZMod' I g (hA I (f0 a) (bw i)) ∧
      ZMod' I g (hA I (e0 a) (bwd i)) ∧ ZMod' I g (hA I (f0 a) (bwd i))) ∧
  (ew * ew = ew ∧ ew * sigA I ew = 0 ∧ ew ∈ IntAf I.F I.E ∧ ∀ y ∈ I.Lf, (1 - ew - sigA I ew) • y ∈ mL I g) ∧
  ((∀ i, bw i = ew • bw i) ∧ ∀ i, bwd i = sigA I ew • bwd i) ∧
  (∀ i j, ZMod' I g (hA I (bwd i) (bw j) - if i = j then ew else 0)) ∧
  ∀ y ∈ I.Lf, InMod I g (Set.range e0 ∪ Set.range f0 ∪ {z0} ∪ Set.range bw ∪ Set.range bwd) y

theorem isRefFrame_setting {D : Formalism.BasicNotions.D7} (X : HidaSetting D) :
    IsRefFrame X.B.I X.B.g X.e0 X.f0 X.z0 X.bw X.bwd X.ew :=
  ⟨X.vectorsInLattice, X.gramIntegral, X.formsAtZero, X.weightVectorsIntegral, ⟨X.ew_idem, X.ew_orth, X.ew_int, X.ew_full⟩, ⟨X.bw_w, X.bwd_w⟩,
    fun i j => by convert X.bw_dual i j, X.latticeSpan⟩

def IsLiftFrame (I : AutInst) (g : ℕ) (b : ℕ → VA I) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Prop :=
  Formalism.L2.DIV.IsFrame β I.L ∧
    ∀ j : Fin I.n, (fun i => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j) - b j.val ∈ mL I g

def matIn (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) (x : I.Gf) :
    Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  ((β⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _)

def gramIn (I : AutInst) (β : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
  fun i j => hA I (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) l i)
    (fun l => (β : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) l j)

def sigInt (I : AutInst) : Formalism.L2.Herm.intAf I.F I.E →+* Formalism.L2.Herm.intAf I.F I.E :=
  ((sigA I).comp (Formalism.L2.Herm.intAf I.F I.E).subtype).codRestrict _ fun s => Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem I s.2

theorem sigInt_coe (I : AutInst) (s : Formalism.L2.Herm.intAf I.F I.E) :
    ((sigInt I s : Formalism.L2.Herm.intAf I.F I.E) : I.E ⊗[I.F] Af I.F) = sigA I s := rfl

def chiArg (I : AutInst) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I) (bw bwd : Fin k → VA I) (x : I.Gf) :
    I.E ⊗[I.F] Af I.F :=
  (∑ a, hA I (f0 a) (I.fmat x *ᵥ nxt e0 z0 a)) +
    ∑ i : Fin k, if h : i.1 + 1 < k then hA I (bwd i) (I.fmat x *ᵥ bw ⟨i.1 + 1, h⟩) else 0

theorem flagLevelCharacter_eq_psi_divN (I : AutInst) (psiEf : I.E ⊗[I.F] Af I.F → ℂ) (g : ℕ) {ρ k : ℕ} (e0 f0 : Fin ρ → VA I) (z0 : VA I)
    (bw bwd : Fin k → VA I) (x : I.Gf) :
    chi2f I psiEf g e0 f0 z0 bw bwd x = psiEf (divN I g (chiArg I e0 f0 z0 bw bwd x)) := rfl

end GlobalTheory.FlagBasis

end
