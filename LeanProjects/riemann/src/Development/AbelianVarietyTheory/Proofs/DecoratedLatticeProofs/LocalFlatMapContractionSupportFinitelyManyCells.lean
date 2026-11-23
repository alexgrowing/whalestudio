import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalDoublingIntegralOddCase
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatSelfAverageHeisenberg
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalZetaIntegralOpenSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

noncomputable section
namespace GlobalTheory.LocFlat.CellsContr

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem opE_const_mul {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (C : ℂ)
    (F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun z => C * F z) x₀ = C * opE ψ ν p F x₀ := by
  simp only [opE]
  rw [← integral_const_mul]
  congr 1; funext e; ring

theorem opEFJ_const_mul {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ₀ : (n' → k) → ℂ) (C : ℂ)
    (F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν p Φ₀ (fun z => C * F z) x₀ = C * GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν p Φ₀ F x₀ := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ, opE_const_mul]
  rw [← integral_const_mul]
  congr 1; funext u; ring

theorem om_eq_const_mul {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ' : kˣ →* ℂˣ)
    (x : GL a k) (y : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ' x y Φ = fun z => ((μ' (Matrix.GeneralLinearGroup.det x) : ℂ) * ((μ' (Matrix.GeneralLinearGroup.det y))⁻¹ : ℂˣ)) *
      om 1 1 y (om 1 x 1 Φ) z := by
  funext z
  simp [om, nabs]
  ring
end
end GlobalTheory.LocFlat.CellsContr

open GlobalTheory.LocFlat.CellsContr in

theorem GlobalTheory.LocFlat.contr_support_finite_cells :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k),
    IsSelfDual ψ ν → ∀ (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] (c ρ : ℕ), c + 1 = 2 * ρ → ∀ (μ μ' : kˣ →* ℂˣ) (J : Subgroup (GL (n₂ ⊕ Fin c) k)),
    IsOpen (J : Set (GL (n₂ ⊕ Fin c) k)) → ∀ (Φ₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k))
    (Φ₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (a : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (x : GL (n₁ ⊕ Fin (c + 1)) k),
    ∃ T : Finset (GL (n₂ ⊕ Fin c) k), ∀ y : GL (n₂ ⊕ Fin c) k,
      GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) (om μ a x Φ₁.1)) (GlobalTheory.LocFlat.flRow ψ ν ρ (om μ' x y Φ₂.1)) ≠ 0 →
      ∃ r ∈ R k n₂ c ρ, ∃ t ∈ T, ∃ j ∈ J, y = r * t * j := by
  intro k _ _ _ _ _ _ ψ hψc hψ1 ν hsd n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ μ μ' J hJ Φ₁ Φ₂ a x
  classical
  haveI : ν.IsAddHaarMeasure := hsd.1
  have hρ1 : 1 ≤ ρ := by omega
  have hρc : ρ ≤ c := by omega
  have hker : IsOpen (((1 : kˣ →* ℂˣ).ker : Subgroup kˣ) : Set kˣ) := by
    rw [MonoidHom.ker_one]; exact isOpen_univ
  let Φ₁' : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) := ⟨om μ a x Φ₁.1, om_mem_SB μ a x Φ₁.2⟩

  obtain ⟨m, Ψ, Φ₀, hdec⟩ := (GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum k ψ hψc hψ1 ν hsd n₀ n₁ n₂ c ρ hcρ μ Φ₁' Φ₂).2.2.2.1

  let Φ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := ⟨om 1 x 1 Φ₂.1, om_mem_SB 1 x 1 Φ₂.2⟩
  have hav := fun i => (GlobalTheory.PosOne.avg_self_and_props k n₂ n₁ c ρ hρ1 hρc ψ hψc hψ1 ν hsd 1 hker Φ).2 (Φ₀ i)

  have hcov : ∀ i, ∃ T : Finset (GL (n₂ ⊕ Fin c) k), GlobalTheory.PosOne.Covers ρ J T fun h =>
      opE ψ ν ρ (om 1 1 h (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν 1 ρ (Φ₀ i).1 Φ.1)) := fun i =>
    GlobalTheory.PosOne.covers_opE_finite k n₂ n₁ c ρ hρ1 hρc ψ hψc hψ1 ν 1 hker J hJ ⟨_, (hav i).1⟩
  choose Ti hTi using hcov
  refine ⟨Finset.univ.biUnion Ti, fun y hy => ?_⟩
  obtain ⟨X, hX⟩ : ∃ X, GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁'.1)
      (GlobalTheory.LocFlat.flRow ψ ν ρ (om μ' x y Φ₂.1)) X ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (funext h)
  let Φ₂' : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k) := ⟨om μ' x y Φ₂.1, om_mem_SB μ' x y Φ₂.2⟩
  have hid := (GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum k ψ hψc hψ1 ν hsd n₀ n₁ n₂ c ρ hcρ μ Φ₁' Φ₂').2.2.2.2
    m Ψ Φ₀ hdec X
  have hX' := hX
  change GlobalTheory.LocFlat.contr ψ ν (GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ₁'.1) (GlobalTheory.LocFlat.flRow ψ ν ρ Φ₂'.1) X ≠ 0 at hX'
  rw [hid] at hX'
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hX'
  have hi2 : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν ρ (Φ₀ i).1 (om μ' x y Φ₂.1) X.2 ≠ 0 := right_ne_zero_of_mul hi
  rw [om_eq_const_mul, opEFJ_const_mul] at hi2
  have hi3 : GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.opEFJ ψ ν ρ (Φ₀ i).1 (om 1 1 y Φ.1) X.2 ≠ 0 := right_ne_zero_of_mul hi2
  have hne : opE ψ ν ρ (om 1 1 y (GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.avg ψ ν 1 ρ (Φ₀ i).1 Φ.1)) ≠ 0 := by
    rw [(hav i).2.1 y]
    intro h0
    exact hi3 (congrFun h0 X.2)
  obtain ⟨t, ht, hmk⟩ := (hTi i).2 y hne
  obtain ⟨r, hr, j, hj, hy'⟩ := (DoubleCoset.eq _ _ t y).1 hmk.symm
  exact ⟨r, hr, t, Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, ht⟩, j, hj, hy'⟩
