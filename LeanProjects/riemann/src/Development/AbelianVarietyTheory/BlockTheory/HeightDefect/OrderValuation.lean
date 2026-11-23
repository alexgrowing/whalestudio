import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PtFree
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36

open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivialClassCondition (T : CDVR) (ι : c.F →+* T.Fr) (_y : IntFr Xo c T ι) : Prop := True

abbrev algVal (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) := valSet Xo c (algCls Xo c) la

abbrev allVal (la : HeightOneSpectrum (𝓞 c.F)) : Set (Rul Xo c → EReal) := valSet Xo c (trivialClassCondition Xo c) la

def TrivOn (T : CDVR) (ι : c.F →+* T.Fr) : Prop := ∀ a : c.F, a ≠ 0 → vV T.V (ι a) = 0

def ordVal : Set (Rul Xo c → EReal) :=
  {o | ∃ (T : CDVR) (ι : c.F →+* T.Fr) (_ : TrivOn c T ι) (y : IntFr Xo c T ι),
    o = fun f => nval T.V 1 (evI y f)}

variable {Xo c}

def NoCommonZero {κ : Type} (w : κ → Rul Xo c) : Prop :=
  ∀ (L : Type) [Field L] [Algebra c.F L] (y : FrPt Xo c L),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y → ∃ k, evR Xo c (w k) y ≠ 0

def NoCommonZeroAt (la : HeightOneSpectrum (𝓞 c.F)) {κ : Type} (w : κ → Rul Xo c) : Prop :=
  ∀ v ∈ algVal Xo c la, ∃ k, v (w k) ≠ ⊤

def LeastLe {R κ : Type} (w : κ → R) (ν : ℝ) (v : R → EReal) : Prop := ∃ k, v (w k) ≤ (ν : EReal)

def Comb {R κ : Type} (w : κ → R) (η : R) (ν c' : ℝ) (v : R → EReal) : Prop :=
  0 ≤ v η ∧ (v η ≠ ⊤ → ∃ k, v (w k) ≤ (ν : EReal) + (c' : EReal) * v η)

variable (Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def TransferInt : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → ∀ F ∈ cusp Xo c U a n,
    (∀ v ∈ algVal Xo c la, 0 ≤ v F) → (∀ v ∈ allVal Xo c la, 0 ≤ v F) ∧ ∀ o ∈ ordVal Xo c, 0 ≤ o F

def TransferComb (nz : HeightOneSpectrum (𝓞 c.F) → ∀ {m : ℕ}, (Fin m → Rul Xo c) → Prop) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ) (aE : (E →+* ℂ) × ℕ → ℕ) (nE : ℕ),
    Dom aL nL → Dom aE nE → ∀ (m : ℕ) (w : Fin m → Rul Xo c), (∀ k, w k ∈ cusp Xo c U aL nL) → nz la w →
    ∀ η ∈ cusp Xo c U aE nE, ∀ ν c' : ℝ, 0 ≤ c' →
      (∀ v ∈ algVal Xo c la, Comb w η ν c' v) →
        (∀ v ∈ allVal Xo c la, Comb w η ν c' v) ∧ ∀ o ∈ ordVal Xo c, Comb w η 0 c' o

def TransferLeast (nz : HeightOneSpectrum (𝓞 c.F) → ∀ {m : ℕ}, (Fin m → Rul Xo c) → Prop) : Prop :=
  ∀ (la : HeightOneSpectrum (𝓞 c.F)) (aL : (E →+* ℂ) × ℕ → ℕ) (nL : ℕ), Dom aL nL →
    ∀ (m : ℕ) (w : Fin m → Rul Xo c), (∀ k, w k ∈ cusp Xo c U aL nL) → nz la w → ∀ ν : ℝ,
      (∀ v ∈ algVal Xo c la, LeastLe w ν v) →
        (∀ v ∈ allVal Xo c la, LeastLe w ν v) ∧ ∀ o ∈ ordVal Xo c, LeastLe w 0 o

def Transfer : Prop :=
  TransferInt Xo c U ∧ TransferComb Xo c U (fun _ _ w => NoCommonZero w) ∧
    TransferLeast Xo c U (fun _ _ w => NoCommonZero w)

def TransferAt : Prop :=
  TransferInt Xo c U ∧ TransferComb Xo c U (fun la _ w => NoCommonZeroAt la w) ∧
    TransferLeast Xo c U (fun la _ w => NoCommonZeroAt la w)

variable {Xo c U}

theorem NoCommonZero.at {κ : Type} {w : κ → Rul Xo c} (h : NoCommonZero w) (la : HeightOneSpectrum (𝓞 c.F)) :
    NoCommonZeroAt la w := by
  rintro _ ⟨⟨q, T, ι, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
  letI := ι.toAlgebra
  obtain ⟨k, hk⟩ := h T.Fr y.1 y.2.1
  refine ⟨k, ?_⟩
  show nval T.V e (evI y (w k)) ≠ ⊤
  have hk' : evI y (w k) ≠ 0 := hk
  rw [nval_of_ne hk']
  exact EReal.coe_ne_top _

theorem TransferAt.transfer (h : TransferAt Xo c U) : Transfer Xo c U :=
  ⟨h.1, fun la aL nL aE nE hL hE m w hw hz => h.2.1 la aL nL aE nE hL hE m w hw (hz.at la),
    fun la aL nL hL m w hw hz => h.2.2 la aL nL hL m w hw (hz.at la)⟩

theorem ordVal_smul {o : Rul Xo c → EReal} (ho : o ∈ ordVal Xo c) {a : c.F} (ha : a ≠ 0) (f : Rul Xo c) :
    o (a • f) = o f := by
  obtain ⟨T, ι, ht, y, rfl⟩ := ho
  show nval T.V 1 (evI y (a • f)) = nval T.V 1 (evI y f)
  rw [evI_smul]
  exact nval_mul_unit 1 ((map_ne_zero ι).2 ha) (ht a ha) _

end GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot36
