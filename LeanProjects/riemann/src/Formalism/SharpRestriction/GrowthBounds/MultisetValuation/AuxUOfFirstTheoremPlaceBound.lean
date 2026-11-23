import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RamifiedLatticeOfChainEstimates

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def PIvS (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ) :=
  ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat,
    (p : MvPolynomial (X.ZA j) (MvPolynomial (X.FrI j) ℤ)) ^ (X.colExp j I i0 v s c) * X.colFac j I v s c

theorem PI_eq_prod (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) : X.PI j I i0 = ∏ v, PIvS X j I i0 v := rfl

theorem PIvS_congr (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    PIvS X j I i0 v = PIvS X j I (fun _ => i0 v) v := rfl

theorem colExp_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) (s : Fin (X.G.P.n' v)) (c : ℕ) :
    X.colExp j I (fun _ => 0) v s c = 0 := by
  unfold Sys.colExp
  split_ifs <;> simp

theorem PIvS_zero (j : ℕ) (I : X.ColCh j) (v : X.Pl) : PIvS X j I (fun _ => 0) v = X.PIv j I v := by
  unfold PIvS Sys.PIv
  simp only [colExp_zero, pow_zero, one_mul]

def LowAtI (j : ℕ) (v : X.Pl) (i : ℕ) (g : ℝ) : Prop :=
  ∀ U : MvPowerSeries (X.EA j ⊕ X.EA j) Y.Kc, IntR Y.Oc (inParamK p Y.Kc U) →
    ∀ (I : X.ColCh j) (n : X.FrI j →₀ ℕ),
      Y.geC (MvPolynomial.coeff n (applyD (PIvS X j I (fun _ => i) v)
        (X.ThZA Y.Kc j (MvPowerSeries.map (algebraMap (K0 p) Y.Kc) (expS p (-Y.PhAt j v)) * U)))) g

variable {X Y}

theorem lowAtI_zero {j : ℕ} {v : X.Pl} {g : ℝ} : LowAtI X Y j v 0 g ↔ Y.LowAt j v g := by
  unfold LowAtI Pend.LowAt
  simp only [PIvS_zero]

theorem LowAtI.mono {j : ℕ} {v : X.Pl} {i : ℕ} {g g' : ℝ} (h : g' ≤ g) (hg : LowAtI X Y j v i g) :
    LowAtI X Y j v i g' :=
  fun U hU I n => Y.geC_mono h (hg U hU I n)

variable (X Y)

def PlacewiseLowerBoundEvenShift (D : Formalism.BasicNotions.D7) : Prop :=
  admitted D X Y → ∀ v, ∀ j < X.mm, Y.LowAt j v (X.gv v (j + 1) - X.alEven v)

def RestBU (D : Formalism.BasicNotions.D7) : Prop :=
  admitted D X Y → ∀ v, ∀ j < X.mm, ∀ i ∈ Icc 1 X.G.P.r, LowAtI X Y j v i (X.gv v (j + 1))

def EntryBoundOfHypotheses (D : Formalism.BasicNotions.D7) : Prop := admitted D X Y → VolumeRatio₂ D X Y

def RestPlaces (D : Formalism.BasicNotions.D7) : Prop :=
  admitted D X Y → ∀ j < X.mm, ∀ (i0 : X.Pl → ℕ) (gP : X.Pl → ℚ), (∀ v, LowAtI X Y j v (i0 v) (gP v)) →
    EntB X Y j i0 (∑ v, (gP v : ℝ))

variable {X Y}

theorem auxU_of_firstTheoremPlaceBound (D : Formalism.BasicNotions.D7) (h : EntryBoundOfHypotheses X Y D) (hA : admitted D X Y) : VolumeRatio₂ D X Y := h hA

theorem restEnt_of_rest (D : Formalism.BasicNotions.D7) (hP : RestPlaces X Y D) (h2 : PlacewiseLowerBoundEvenShift X Y D) (hB : RestBU X Y D)
    (hA : admitted D X Y) : EntCondition X Y := by
  intro j hj i0 gP hPl
  refine hP hA j hj i0 gP fun v => ?_
  rcases hPl v with ⟨h0, h1 | h1⟩ | ⟨h0, h1, h3⟩
  · rw [h0]; exact lowAtI_zero.2 h1
  · rw [h0]; exact lowAtI_zero.2 (Pend.LowAt.mono Y h1 (h2 hA v j hj))
  · exact LowAtI.mono h3 (hB hA v j hj (i0 v) (Finset.mem_Icc.2 ⟨h0, h1⟩))

end Formalism.MainNotions.FormalGroupSystem.Pf
