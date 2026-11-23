import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

private theorem isLocallyConstant_weighted_sum {X : Type*} [TopologicalSpace X] (T : Finset ℤ) (f : ℤ → X → ℤ)
    (hf : ∀ c, IsLocallyConstant (f c)) : IsLocallyConstant (fun y => ∑ c ∈ T, c * f c y) := by
  have h : ∀ c, Continuous (f c) := fun c => (IsLocallyConstant.iff_continuous _).1 (hf c)
  exact (IsLocallyConstant.iff_continuous _).2
    (continuous_finset_sum _ fun c _ => continuous_const.mul (h c))

theorem UpperTheory.Gal.TranscendenceTraces.wtClopen_of :
    WtCrit → FibFin → WtClopen := by
  intro hcrit hfin Z S p _ w hcl
  apply hcrit p w
  intro A φ hφ u
  have hφc : Continuous φ := (IsLocallyConstant.iff_continuous φ).1 hφ
  haveI := A.finite
  obtain ⟨U0, hU0, hu, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 A.U.isBasis_affineOpens)
    (show u ∈ (⊤ : A.U.Opens) from trivial)
  have hK : IsCompact (A.r ⁻¹' (U0 : Set A.U)) :=
    QuasiCompact.isCompact_preimage _ U0.isOpen (IsAffineOpen.isCompact hU0)
  let T : Finset ℤ := ((hK.image hφc).finite_of_discrete).toFinset
  choose ψ hψ hψs using fun c : ℤ => hcl A (φ ⁻¹' {c}) (hφ.isClopen_fiber c)
  let Ψ : A.U → ℤ := fun y => ∑ c ∈ T, c * ψ c y
  have hΨ : IsLocallyConstant Ψ := isLocallyConstant_weighted_sum T ψ hψ
  refine ⟨(U0 : Set A.U) ∩ {y | Ψ y = Ψ u}, Ψ u, U0.isOpen.inter (hΨ.isOpen_fiber _),
    ⟨hu, rfl⟩, ?_⟩
  rintro Ω _ _ x ⟨hx0, hxΨ⟩
  rw [← show Ψ (pt x) = Ψ u from hxΨ]
  have hF := hfin A.r Ω x
  classical
  have key : ∀ c, ψ c (pt x) =
      ∑ z ∈ hF.toFinset, if φ (pt z) = c then w Ω (z ≫ A.v) else 0 := by
    intro c
    rw [hψs c Ω x, finsum_mem_eq_finite_toFinset_sum _ (hF.inter_of_left _), ← Finset.sum_filter]
    congr 1
    ext z
    simp
  simp only [Ψ, key, Finset.mul_sum]
  rw [finsum_mem_eq_finite_toFinset_sum _ hF, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  have hzf : z ≫ A.r = x := (Set.Finite.mem_toFinset hF).1 hz
  have hmem : φ (pt z) ∈ T := by
    rw [Set.Finite.mem_toFinset]
    refine ⟨pt z, ?_, rfl⟩
    show A.r (pt z) ∈ (U0 : Set A.U)
    rw [← pt_comp, hzf]
    exact hx0
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq, if_pos hmem, mul_comm]
