import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFgA

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section Curve

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

def ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (t : ℝ) : Matrix (Fin N) (Fin N) (Cinf E) :=
  NormedSpace.exp (t • Z)

theorem hasDerivAt_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : HasDerivAt (ecurve Z) Z 0 := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

theorem ecurve_zero {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) : ecurve Z 0 = 1 := by
  simp [ecurve]

theorem ecurve_mem {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) :
    ecurve Z t ∈ Matrix.unitaryGroup (Fin N) (Cinf E) := by
  have hc : (t • Z)ᴴ = -(t • Z) := by
    rw [conjTranspose_smul, hZ]; simp
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, ecurve, ← Matrix.exp_conjTranspose, hc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl (t • Z)).neg_right]
  simp

def toLclm (N : ℕ) : Matrix (Fin N) (Fin N) (Cinf E) →L[ℝ] Lie E N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => toL A, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

theorem hasDerivAt_toL_ecurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) :
    HasDerivAt (fun t => (toL (ecurve Z t) : Lie E N)) (toL Z) 0 := by
  have h := ((toLclm (E := E) N).hasFDerivAt (x := ecurve Z 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_ecurve Z)
  exact h

end Curve

def kcurve {N : ℕ} (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) (t : ℝ) : Kinf E N :=
  ⟨ecurve Z t, ecurve_mem Z hZ t⟩

theorem lie_mem_orbSpan {N : ℕ} (φ : Sm E N) [FiniteDimensional ℂ (GlobalTheory.CuspRep.LocEx.orbSpan φ)]
    (Z : Matrix (Fin N) (Fin N) (Cinf E)) (hZ : Zᴴ = -Z) :
    lie E N (toL Z) φ ∈ GlobalTheory.CuspRep.LocEx.orbSpan φ := by
  set A : Submodule ℂ (GA E N → ℂ) := (GlobalTheory.CuspRep.LocEx.orbSpan φ).map (Sm E N).subtype with hA
  have : FiniteDimensional ℂ A := inferInstance
  obtain ⟨S, a, ha⟩ := SliceTensor.interp A
  let c : ℝ → GL (Fin N) (Cinf E) := fun t => Unitary.toUnits (kcurve Z hZ t)
  have h0 : c 0 = 1 := Units.ext (ecurve_zero Z)
  have hc : HasDerivAt (fun t => toL (c t).val) (toL Z) 0 := hasDerivAt_toL_ecurve Z
  have hmem : ∀ t, (cptRep E N (kcurve Z hZ t) φ).1 ∈ A := fun t =>
    ⟨_, Submodule.subset_span ⟨kcurve Z hZ t, rfl⟩, rfl⟩
  have hval : ∀ t g, (cptRep E N (kcurve Z hZ t) φ).1 g = φ.1 (g * infGL E N (c t)) := fun _ _ => rfl
  have key : ∀ g, lieD (toL Z) φ.1 g = ∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g := by
    intro g
    have e : ∀ t, φ.1 (g * infGL E N (c t)) = ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g := by
      intro t
      have := congrFun (ha _ (hmem t)) g
      rw [hval, Finset.sum_apply] at this
      rw [this]
      refine Finset.sum_congr rfl fun κ _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, hval]
    have d1 := hasDerivAt_curve φ g c (toL Z) h0 hc
    have d2 : HasDerivAt (fun t => ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g)
        (∑ κ : S, lieD (toL Z) φ.1 κ.1 * (a κ : GA E N → ℂ) g) 0 :=
      HasDerivAt.fun_sum fun κ _ => (hasDerivAt_curve φ κ.1 c (toL Z) h0 hc).mul_const _
    rw [show (fun t => φ.1 (g * infGL E N (c t))) = fun t =>
      ∑ κ : S, φ.1 (κ.1 * infGL E N (c t)) * (a κ : GA E N → ℂ) g from funext e] at d1
    exact d1.unique d2
  have hL : (lie E N (toL Z) φ).1 ∈ A := by
    have e : (lie E N (toL Z) φ).1 = ∑ κ : S, lieD (toL Z) φ.1 κ.1 • (a κ : GA E N → ℂ) := by
      funext g
      rw [GlobalTheory.CuspRep.lie_apply, key g, Finset.sum_apply]
      rfl
    rw [e]
    exact A.sum_mem fun κ _ => A.smul_mem _ (a κ).2
  obtain ⟨y, hy, e⟩ := hL
  have : y = lie E N (toL Z) φ := Subtype.ext e
  rw [← this]
  exact hy

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
