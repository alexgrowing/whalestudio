import Formalism.LocalToGlobal.ProjectiveLattices.RecPJThAllNeBot

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j) (i : ℕ)
  (η : (recB h.toLawsCore).Cusp j (wEt D j i))

def EtCusp : Prop := η ≠ 0 ∧ (recPJ h j hj).NonZeroComp _ η

def EtVal : Prop :=
  ∀ la (y : (recPJ h j hj).Pt la),
    ((2 * i * (recPJ h j hj).phiC la y : ℝ) : EReal) ≤ (recPJ h j hj).vAt la y ((recPJ h j hj).inc _ η)

def EtSup (P : ℝ) : Prop := ∀ σ, Real.log ((recB h.toLawsCore).supN j _ σ η) / i ≤ P

variable (P : ℝ) (Arch : ∀ j i, (recB h.toLawsCore).Cusp j (wEt D j i) → Prop)

def ETEx : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j < D.R.m), ∃ i : ℕ, 0 < i ∧ ∃ η : (recB h.toLawsCore).Cusp j (wEt D j i),
    EtCusp h j ⟨h1, h2.le⟩ i η ∧ EtVal h j ⟨h1, h2.le⟩ i η ∧ EtSup h j i η P ∧ Arch j i η

variable {h P Arch}

def etI (e : ETEx h P Arch) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) : ℕ := (e j h1 h2).choose

def etF (e : ETEx h P Arch) (j : ℕ) (h1 : 1 ≤ j) (h2 : j < D.R.m) :
    (recB h.toLawsCore).Cusp j (wEt D j (etI e j h1 h2)) :=
  (e j h1 h2).choose_spec.2.choose

end Formalism.L2.Pj
