import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnMapEqRootExchangeOperatorTranslate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalZetaIntegralOpenSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.LocFlat.CellSupport

theorem det_colE {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] (c p : ℕ) (β : n → k) :
    Matrix.GeneralLinearGroup.det (colE c p β) = 1 := by
  ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, colE, upU, Matrix.det_fromBlocks_zero₂₁]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem om_inv_of_det_one {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g : GL b k) (hg : Matrix.GeneralLinearGroup.det g = 1) (Ψ : Matrix b a k → ℂ) :
    om μ (1 : GL a k) g⁻¹ Ψ = fun z => Ψ (g.val * z) := by
  funext z
  simp only [om, map_inv, hg, inv_one, map_one, nabs_one, inv_inv, Real.one_rpow, Units.val_one, Complex.ofReal_one,
    one_mul, Matrix.mul_one]

theorem om_eq_mul_om_triv {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (h : GL b k) (Ψ : Matrix b a k → ℂ) :
    om μ (1 : GL a k) h Ψ = fun z => (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) * om 1 (1 : GL a k) h Ψ z := by
  funext z
  simp only [om, map_one, MonoidHom.one_apply, inv_one, Units.val_one]
  ring

theorem opE_const_mul [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n']
    [DecidableEq n'] {c : ℕ} (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (s : ℂ)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) :
    opE ψ ν p (fun z => s * Ψ z) x₀ = s * opE ψ ν p Ψ x₀ := by
  unfold opE
  rw [← integral_const_mul]
  simp only [mul_assoc]

end GlobalTheory.LocFlat.CellSupport

namespace GlobalTheory.LocFlat
open GlobalTheory.LocFlat.CellSupport

theorem flCol_support_finite_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (ν : Measure k),
    ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c p : ℕ), 1 ≤ p →
    p ≤ c → ∀ (μ : kˣ →* ℂˣ) (J : Subgroup (GL (n ⊕ Fin c) k)), IsOpen (J : Set (GL (n ⊕ Fin c) k)) →
    ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (a : GL (n' ⊕ Fin (c + 1)) k),
    ∃ T : Finset (GL (n ⊕ Fin c) k), ∀ x : GL (n ⊕ Fin c) k, GlobalTheory.LocFlat.flCol ψ ν p (om μ a x Φ.1) ≠ 0 →
      ∃ β : n → k, ∃ r ∈ R k n c p, ∃ t ∈ T, ∃ j ∈ J, x = colE c p β * r * t * j := by
  intro k _ _ _ _ _ _ ψ hψc hψ ν hν n n' _ _ _ _ c p hp1 hpc μ J hJ Φ a
  obtain ⟨T, -, hT⟩ := GlobalTheory.PosOne.covers_opE_finite k n n' c p hp1 hpc ψ hψc hψ ν 1
    (by rw [MonoidHom.ker_one]; exact isOpen_univ) J hJ ⟨om μ a 1 Φ.1, om_mem_SB μ a 1 Φ.2⟩
  refine ⟨T, fun x hx => ?_⟩
  obtain ⟨X, hX⟩ := Function.ne_iff.1 hx
  rw [flCol_eq_opE_colE k ψ ν hψc hν n n' c p hp1 hpc _ (om_mem_SB μ a x Φ.2) X] at hX
  set β : n → k := fun r => X r (Sum.inr ()) with hβ
  replace hX : opE ψ ν p (om μ 1 (colE c p β)⁻¹ (om μ a x Φ.1)) X.toCols₁ ≠ 0 := by
    rw [om_inv_of_det_one μ _ (det_colE c p β)]
    exact hX
  rw [← om_mul] at hX
  have e : om μ (1 * a) ((colE c p β)⁻¹ * x) Φ.1 = om μ 1 ((colE c p β)⁻¹ * x) (om μ a 1 Φ.1) := by
    rw [← om_mul, mul_one]
  rw [e, om_eq_mul_om_triv, opE_const_mul] at hX
  obtain ⟨t, ht, hd⟩ := hT ((colE c p β)⁻¹ * x) (Function.ne_iff.2 ⟨X.toCols₁, right_ne_zero_of_mul hX⟩)
  obtain ⟨r, hr, j, hj, hx'⟩ := (DoubleCoset.eq _ _ _ _).1 hd.symm
  refine ⟨β, r, hr, t, ht, j, hj, ?_⟩
  rw [mul_assoc, mul_assoc, ← mul_assoc r, ← hx', mul_inv_cancel_left]

end GlobalTheory.LocFlat
