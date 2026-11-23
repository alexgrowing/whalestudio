import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Cval
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormNatCastLe
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaPar.Chord

theorem chord_change {K : Type*} [Field K] [CharZero K] (e r s t a b c d : K) (he : e ≠ 0)
    (hac : a - c ≠ 0) :
    e ^ 2 * ((((b - d) / (a - c)) ^ 2 / 4 - a - c) - r) =
      ((e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
          (e ^ 2 * (a - r) - e ^ 2 * (c - r))) ^ 2 +
        (e * (2 * s)) * ((e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
          (e ^ 2 * (a - r) - e ^ 2 * (c - r))) - e ^ 2 * (3 * r - s ^ 2) -
        e ^ 2 * (a - r) - e ^ 2 * (c - r) := by
  have hm : (e ^ 3 * (b / 2 - s * (a - r) - t) - e ^ 3 * (d / 2 - s * (c - r) - t)) /
      (e ^ 2 * (a - r) - e ^ 2 * (c - r)) = e * ((b - d) / (a - c) / 2 - s) := by
    rw [show e ^ 2 * (a - r) - e ^ 2 * (c - r) = e ^ 2 * (a - c) by ring]
    field_simp
    ring
  rw [hm]
  ring

variable {p : ℕ} [Fact p.Prime]

theorem lamC_coe' (lam : Qbar →+* ℂ_[p]) (x : Qbar) : lamC lam (x : ℂ) = lam x := by
  unfold lamC
  rw [dif_pos x.2]

theorem W_a₁ (g : GL3Theta.G1 p) : g.W.a₁ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * (2 * g.C.s) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₁]

theorem W_a₂ (g : GL3Theta.G1 p) :
    g.W.a₂ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (3 * g.C.r - g.C.s ^ 2) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₂]

theorem W_a₃ (g : GL3Theta.G1 p) :
    g.W.a₃ = ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3 * (2 * g.C.t) := by
  simp [GL3Theta.G1.W, wModel, WeierstrassCurve.variableChange_a₃]

theorem xAt_add (g : GL3Theta.G1 p) (P Q : ℂ) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (hP : P ∉ g.abelian₂)
    (hQ : Q ∉ g.abelian₂) (h1 : P + Q ∉ g.abelian₂) (h2 : P - Q ∉ g.abelian₂) (a1 : wpF g.abelian₂ P ∈ Qbar)
    (a2 : wpD g.abelian₂ P ∈ Qbar) (a3 : wpF g.abelian₂ Q ∈ Qbar) (a4 : wpD g.abelian₂ Q ∈ Qbar) :
    GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) =
      ((yAt g P - yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 +
        g.W.a₁ * ((yAt g P - yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) -
        g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  have hne : wpF g.abelian₂ P ≠ wpF g.abelian₂ Q := fun e => by
    rcases (h.wp_eq_iff hP hQ).1 e.symm with h' | h'
    exacts [h1 h', h2 h']
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair g.abelian₂ h
  have hadd : wpF g.abelian₂ (P + Q) =
      ((wpD g.abelian₂ P - wpD g.abelian₂ Q) / (wpF g.abelian₂ P - wpF g.abelian₂ Q)) ^ 2 / 4 -
        wpF g.abelian₂ P - wpF g.abelian₂ Q := by
    simp only [GlobalTheory.LatticeInvariants.wpF_eq hL, GlobalTheory.LatticeInvariants.wpD_eq hL] at hne ⊢
    exact (GlobalTheory.weierstrassP_add L ((hL P).not.1 hP) ((hL Q).not.1 hQ) hne).1
  set A : Qbar := ⟨_, a1⟩
  set B : Qbar := ⟨_, a2⟩
  set C : Qbar := ⟨_, a3⟩
  set D : Qbar := ⟨_, a4⟩
  have eA : lamC g.lam (wpF g.abelian₂ P) = g.lam A := lamC_coe' g.lam A
  have eB : lamC g.lam (wpD g.abelian₂ P) = g.lam B := lamC_coe' g.lam B
  have eC : lamC g.lam (wpF g.abelian₂ Q) = g.lam C := lamC_coe' g.lam C
  have eD : lamC g.lam (wpD g.abelian₂ Q) = g.lam D := lamC_coe' g.lam D
  have eS : lamC g.lam (wpF g.abelian₂ (P + Q)) =
      ((g.lam B - g.lam D) / (g.lam A - g.lam C)) ^ 2 / 4 - g.lam A - g.lam C := by
    have : wpF g.abelian₂ (P + Q) = ((((B - D) / (A - C)) ^ 2 / 4 - A - C : Qbar) : ℂ) := by
      rw [hadd]; push_cast; rfl
    rw [this, lamC_coe']
    simp only [map_sub, map_div₀, map_pow, map_ofNat]
  have hAC : g.lam A - g.lam C ≠ 0 := fun e =>
    hne (congrArg Subtype.val (g.lam.injective (sub_eq_zero.1 e)))
  have he : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  rw [W_a₁, W_a₂]
  simp only [GlobalTheory.EvenTheta.xAt, yAt, eA, eB, eC, eD, eS]
  refine ⟨fun e => hAC ?_, chord_change _ _ _ _ _ _ _ _ he hAC⟩
  have := mul_left_cancel₀ (pow_ne_zero 2 he) e
  linear_combination this

theorem wpF_neg' {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) (z : ℂ) :
    wpF Λ (-z) = wpF Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  simp only [GlobalTheory.LatticeInvariants.wpF_eq hL, PeriodPair.weierstrassP_neg]

theorem wpD_neg' {Λ : AddSubgroup ℂ} (h : GlobalTheory.EvenTheta.IsLat Λ) (z : ℂ) :
    wpD Λ (-z) = -wpD Λ z := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  simp only [GlobalTheory.LatticeInvariants.wpD_eq hL, PeriodPair.derivWeierstrassP_neg]

theorem xAt_neg (g : GL3Theta.G1 p) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (Q : ℂ) :
    GlobalTheory.EvenTheta.xAt g (-Q) = GlobalTheory.EvenTheta.xAt g Q := by
  simp only [GlobalTheory.EvenTheta.xAt, wpF_neg' h]

theorem yAt_neg (g : GL3Theta.G1 p) (h : GlobalTheory.EvenTheta.IsLat g.abelian₂) (Q : ℂ)
    (a4 : wpD g.abelian₂ Q ∈ Qbar) :
    yAt g (-Q) = g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (yAt g Q) := by
  have e : lamC g.lam (-wpD g.abelian₂ Q) = -lamC g.lam (wpD g.abelian₂ Q) := by
    have e1 := lamC_coe' g.lam (-(⟨_, a4⟩ : Qbar))
    have e2 := lamC_coe' g.lam (⟨_, a4⟩ : Qbar)
    rw [map_neg, ← e2] at e1
    exact e1
  have e1 : g.W.toAffine.a₁ = _ := W_a₁ g
  have e3 : g.W.toAffine.a₃ = _ := W_a₃ g
  rw [WeierstrassCurve.Affine.negY, e1, e3]
  simp only [GlobalTheory.EvenTheta.xAt, yAt, wpF_neg' h, wpD_neg' h, e]
  ring

theorem model_chord : ∀ {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (P Q : ℂ), GlobalTheory.EvenTheta.IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → P ∉ g.abelian₂ → Q ∉ g.abelian₂ → P + Q ∉ g.abelian₂ → P - Q ∉ g.abelian₂ → wpF g.abelian₂ P ∈ Qbar → wpD g.abelian₂ P ∈ Qbar → wpF g.abelian₂ Q ∈ Qbar → wpD g.abelian₂ Q ∈ Qbar → GlobalTheory.EvenTheta.xAt g P ≠ GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P + Q) = ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - GlobalTheory.ThetaPar.yAt g Q) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q ∧ GlobalTheory.EvenTheta.xAt g (P - Q) = ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) ^ 2 + g.W.a₁ * ((GlobalTheory.ThetaPar.yAt g P - g.W.toAffine.negY (GlobalTheory.EvenTheta.xAt g Q) (GlobalTheory.ThetaPar.yAt g Q)) / (GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q)) - g.W.a₂ - GlobalTheory.EvenTheta.xAt g P - GlobalTheory.EvenTheta.xAt g Q := by
  intro p _ g P Q h _ _ hP hQ h1 h2 a1 a2 a3 a4
  obtain ⟨n, e⟩ := xAt_add g P Q h hP hQ h1 h2 a1 a2 a3 a4
  refine ⟨n, e, ?_⟩
  have := (xAt_add g P (-Q) h hP (by simpa using hQ) (by rwa [← sub_eq_add_neg])
    (by rwa [sub_neg_eq_add]) a1 a2 (by rwa [wpF_neg' h])
    (by rw [wpD_neg' h]; exact neg_mem a4)).2
  rwa [← sub_eq_add_neg, xAt_neg g h, yAt_neg g h Q a4] at this

end GlobalTheory.ThetaPar.Chord
