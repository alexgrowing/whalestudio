import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.StmtPhi
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.Pb

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def AW (_ : Res l K) : Type := Acris l

instance (r : Res l K) : CommRing (AW r) := inferInstanceAs (CommRing (Acris l))

instance (r : Res l K) : Algebra (WittVector l r.k) (AW r) := r.w.toAlgebra

instance (r : Res l K) : Module (per l K).A (AW r) := inferInstanceAs (Module (Acris l) (Acris l))

instance (r : Res l K) : SMulCommClass (WittVector l r.k) (per l K).A (AW r) :=
  ⟨fun w a x => mul_left_comm (r.w w) (show Acris l from a) (show Acris l from x)⟩

def ofA (r : Res l K) (a : (per l K).A) : AW r := a

abbrev LW (r : Res l K) (M : Model l K) (j : ℕ) : Type 1 := (Wc.HS l (B.schFn M.p) r.ρ j).lim

abbrev HL (M : Model l K) (j : ℕ) : Type 1 := (M.HA true).N j

def phiL (M : Model l K) (j : ℕ) : HL M j →+ HL M j := (M.phiH j).lim.toAddMonoidHom

def galL (M : Model l K) (j : ℕ) (g : K.fixingSubgroup) : HL M j →+ HL M j := (M.HA true).act j g

def pullL {M M' : Model l K} (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p) (j : ℕ) : HL M' j →+ HL M j :=
  (Model.pullH u hu true j).lim.toAddMonoidHom

abbrev AL (r : Res l K) (M : Model l K) (j : ℕ) : Type 1 := AW r ⊗[WittVector l r.k] LW r M j

structure Fac (r : Res l K) (N : ℕ) where
  e : Model l K → ℕ → ℕ
  α : ∀ M j, HL M j →+ AL r M j
  β : ∀ M j, AL r M j →ₗ[(per l K).A] HL M j
  phiT : ∀ M j, AL r M j →+ AL r M j
  galT : ∀ M j, K.fixingSubgroup → AL r M j →+ AL r M j
  phiT_tmul : ∀ M, M.Sm → ∀ j (a : (per l K).A) (y : LW r M j),
    phiT M j (ofA r a ⊗ₜ y) = ofA r ((per l K).φ a) ⊗ₜ (Wc.phiS l (B.schFn M.p) r.ρ j).lim y
  galT_tmul : ∀ M, M.Sm → ∀ j g (a : (per l K).A) (y : LW r M j), galT M j g (ofA r a ⊗ₜ y) = ofA r ((per l K).σA g a) ⊗ₜ y
  lin : ∀ M, M.Sm → ∀ j (a : (per l K).A) (x : HL M j), α M j (a • x) = ((per l K).φ^[N] a) • α M j x
  fac : ∀ M, M.Sm → ∀ j (x : HL M j), β M j (α M j x) = ((l : (per l K).A) ^ e M j) • (phiL M j)^[N] x
  phi : ∀ M, M.Sm → ∀ j (x : HL M j), α M j (phiL M j x) = phiT M j (α M j x)
  gal : ∀ M, M.Sm → ∀ j g (x : HL M j), α M j (galL M j g x) = galT M j g (α M j x)
  galβ : ∀ M, M.Sm → ∀ j g (y : LW r M j), galL M j g (β M j ((1 : AW r) ⊗ₜ y)) = β M j ((1 : AW r) ⊗ₜ y)
  nat : ∀ (M M' : Model l K) (u : M.X ⟶ M'.X) (hu : u ≫ M'.p = M.p), M.Sm → M'.Sm → ∀ j (x : HL M' j), ∃ m : ℕ,
    ((l : (per l K).A) ^ m) • (((l : (per l K).A) ^ e M' j) • α M j (pullL u hu j x) -
      ((l : (per l K).A) ^ e M j) • (LinearMap.lTensor (AW r) (Wc.pullS l r.ρ (B.schMap u hu) j).lim) (α M' j x)) = 0

def perCOf (r : Res l K) (C₀ : Type) [CommRing C₀] (c : Acris l →+* C₀) (ι : C₀ →+* (per l K).B) (φ : C₀ →+* C₀)
    (σ : K.fixingSubgroup → C₀ →+* C₀) (q : ℚ_[l] →+* C₀) (k : Wc.K₀ l r.k →+* C₀) : PerC (per l K) where
  C := C₀
  K₀ := Wc.K₀ l r.k
  c := c
  ι := ι
  φ := φ
  σ := σ
  q := q
  k := k

end CrystallineSemistableComparison.Pb
