import Formalism.SharpRestriction.InertJacobiLevels.EtaSz
import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldSatisfiesConditions

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits NumberField

abbrev Core : Type 1 := Σ R : Ranks, Host R × (↥(R.Psi) → HCParam R)

def coreOf (D : D7) : Core := ⟨D.R, D.host, fun g => D.hc (D.eTau.symm g)⟩

def plPsi (φ : Formalism.HC.Frame) (c : Bool) (t : φ.A) : ↥φ.Psi :=
  ⟨if c then φ.tau2 t else φ.tau1 t, by
    rw [(factPlaces φ).1]
    cases c
    · exact Or.inl ⟨t, by simp⟩
    · exact Or.inr ⟨t, by simp⟩⟩

def wjv (R : Ranks) (hc : ↥(R.Psi) → HCParam R) (j : ℕ) (c : Bool) (v : ℕ) : ℝ :=
  if h : j - 1 < R.m then (((hc (plPsi R.toFrame c (R.ofNat v))).e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0

def Core.rh (X : Core) : Σ R : Ranks, Host R := ⟨X.1, X.2.1⟩

def Core.wjv (X : Core) : ℕ → Bool → ℕ → ℝ := Inhab.wjv X.1 X.2.2

theorem wj_core (D : D7) (j : ℕ) (c : Bool) (t : G.HH D) : wj D j (tauOf D (c, t)) = (coreOf D).wjv j c t.val := by
  show wj D j (tauOf D (c, t)) =
    if h : j - 1 < D.R.m then
      (((D.hc (D.eTau.symm (plPsi D.R.toFrame c (D.R.ofNat t.val)))).e ⟨j - 1, h⟩ : ℚ) : ℝ) else 0
  rw [Formalism.HC.Frame.ofNat_val]
  rfl

def OkT {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT) (Ts : ℝ) (T : ℕ) : Prop :=
  T.Prime ∧ Ts ≤ (T : ℝ) ∧ (T : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * Ts ∧ TNorm (host2 B 0 ∅) T ∧ T ≠ B.pde ∧ T ≠ B.pde'

def GeneratorPrimeEtaBound (Ts : ℝ) (T : ℕ) (Y : Σ R : Ranks, Host R) : Prop :=
  T.Prime ∧ Ts ≤ (T : ℝ) ∧ (T : ℝ) ≤ (1 + 1 / ((Y.1.f : ℝ) * Y.1.k)) * Ts ∧ TNorm Y.2 T ∧ T ≠ Y.2.pde ∧ T ≠ Y.2.pde'

def inertBaseShadowData {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT) (etaSz Sc : ℝ) (offS : ℕ → ℕ → ℝ) (kapI : KapI)
    (ep : ℕ → ℕ) : Shd0 where
  R := R
  TTn := B.TT.image Formalism.HC.Frame.A.val
  T2 := B.T2
  q := B.q
  d := B.d
  g := ![B.g0, B.g1]
  pde := B.pde
  pde' := B.pde'
  bits := fun _ => false
  etaSz := etaSz
  Sc := Sc
  hP := (fieldDataH ⟨R, host2 B 0 ∅⟩).hval
  offS := offS
  kapI := kapI
  ep := ep

end Formalism.MainNotions.Inhab

end
