import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RationalSymplecticPointsSelfAnnihilatorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HomSymplecticHalfFormAlgebraicLawsContinuous

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexOrder

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeisTotal

theorem star_char {R : Type} [CommRing R] (ψ : AddChar R ℂ) (h : ∀ x, ‖ψ x‖ = 1) (x : R) :
    star (ψ (-x)) = ψ x := by
  have h1 : ψ (-x) * ψ x = 1 := by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have h2 : star (ψ (-x)) * ψ (-x) = 1 := by
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; simp
  calc star (ψ (-x)) = star (ψ (-x)) * (ψ (-x) * ψ x) := by rw [h1, mul_one]
    _ = ψ x := by rw [← mul_assoc, h2, one_mul]

theorem eq_zero_abstract {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G)
    [DiscreteTopology Γ] (K : Set G) (hK : IsCompact K) (hcov : ∀ x, ∃ γ ∈ Γ, γ + x ∈ K)
    {R : Type} [CommRing R] [TopologicalSpace R] [ContinuousAdd R] (ψ : AddChar R ℂ) (hψc : Continuous ψ)
    (hψn : ∀ x, ‖ψ x‖ = 1) (H : G → G → R)
    (hl : ∀ x y z, H (x + y) z = H x z + H y z) (hr : ∀ x y z, H x (y + z) = H x y + H x z)
    (halt : ∀ x, H x x = 0) (hcont : Continuous fun q : G × G => H q.1 q.2)
    (hann : ∀ x, (∀ γ ∈ Γ, ψ (H x γ + H x γ) = 1) ↔ x ∈ Γ)
    (f₀ f : G → ℂ) (c₀ : Continuous f₀) (c : Continuous f)
    (q₀ : ∀ γ ∈ Γ, ∀ w, f₀ (γ + w) = ψ (-(H γ w)) * f₀ w) (q : ∀ γ ∈ Γ, ∀ w, f (γ + w) = ψ (-(H γ w)) * f w)
    (hne : f₀ ≠ 0) (μ : Measure G) (𝓕 : Set G) (hμ : μ.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain Γ 𝓕 μ)
    (horth : ∀ w, ∫ x in 𝓕, ψ (H x w) * f₀ (x + w) * star (f x) ∂μ = 0) : f = 0 := by
  have hskew : ∀ x y : G, H y x = -H x y := by
    intro x y
    have h := halt (x + y)
    rw [hl, hr, hr, halt x, halt y] at h
    linear_combination h
  have hz : ∀ x : G, H x 0 = 0 := by
    intro x
    have h := hr x 0 0
    rw [add_zero] at h
    linear_combination -h
  have hcy : ∀ y : G, Continuous fun x : G => H x y := fun y =>
    hcont.comp (continuous_id.prodMk continuous_const)
  have key : ∀ a : G, (fun x => ψ (H x a) * f₀ (x + a) * star (f x)) = 0 := by
    intro a
    refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov
      Γ (fun γ x => ψ (H x γ + H x γ)) ?_ ?_ ?_ ?_ ?_ ?_ μ 𝓕 hμ h𝓕 _ ?_ ?_ ?_
    · intro γ
      exact hψc.comp ((hcy _).add (hcy _))
    · intro γ x y
      rw [← AddChar.map_add_eq_mul, hl]
      congr 1; ring
    · intro γ γ' x
      rw [← AddChar.map_add_eq_mul, AddSubgroup.coe_add, hr]
      congr 1; ring
    · intro x
      rw [AddSubgroup.coe_zero, hz, add_zero, AddChar.map_zero_eq_one]
    · intro γ x
      exact hψn _
    · intro x
      rw [← hann x]
      exact ⟨fun h γ hγ => h ⟨γ, hγ⟩, fun h γ => h γ γ.2⟩
    · exact ((hψc.comp (hcy a)).mul (c₀.comp (continuous_id.add continuous_const))).mul c.star
    · intro γ hγ x
      rw [add_assoc, q₀ γ hγ, q γ hγ, star_mul', star_char ψ hψn]
      have e : ψ (H (γ + x) a) * ψ (-(H γ (x + a))) * ψ (H γ x) = ψ (H x a) := by
        rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hl, hr]
        congr 1; ring
      linear_combination (f₀ (x + a) * star (f x)) * e
    · intro γ
      have h := horth ((γ : G) + a)
      have e : ∀ x : G, ψ (H x γ + H x γ) * (ψ (H x a) * f₀ (x + a) * star (f x))
          = ψ (H γ a) * (ψ (H x (γ + a)) * f₀ (x + (γ + a)) * star (f x)) := by
        intro x
        rw [add_left_comm x, q₀ γ γ.2]
        have e' : ψ (H x γ + H x γ) * ψ (H x a) =
            ψ (H γ a) * ψ (H x (γ + a)) * ψ (-(H γ (x + a))) := by
          rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, hr, hr, hskew x γ]
          congr 1; ring
        linear_combination (f₀ (x + a) * star (f x)) * e'
      simp only [e]
      rw [integral_const_mul, h, mul_zero]
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hne
  funext x
  have h := congrFun (key (y - x)) x
  simp only [add_sub_cancel, Pi.zero_apply, mul_eq_zero, star_eq_zero] at h
  rcases h with (h | h) | h
  · have := hψn (H x (y - x))
    rw [h] at this
    simp at this
  · exact absurd h hy
  · exact h

theorem quasi_of_mem {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g)
    (γ : WO S T) (hγ : γ ∈ ratL T S) (w : WO S T) : g (γ + w) = ψ (-(symplOH S T γ w)) * g w := by
  obtain ⟨γ', rfl⟩ := hγ
  exact hg.quasi γ' w

theorem eq_zero_of_orthogonal_translates (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (S T : HSp D) (f₀ f : WO S T → ℂ) (h₀ : IsThetaFunO ψ S T f₀) (hne : f₀ ≠ 0) (hf : IsThetaFunO ψ S T f)
    (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) (hμ : μ.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ)
    (horth : ∀ w, ∫ x in 𝓕, heisO ψ S T w f₀ x * star (f x) ∂μ = 0) : f = 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨hl, hr, halt, hdbl, hcont, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D S T
  obtain ⟨hψc, hψn, -, -⟩ := hψ.1
  have hann : ∀ x : WO S T, (∀ γ ∈ ratL T S, ψ (symplOH S T x γ + symplOH S T x γ) = 1) ↔ x ∈ ratL T S := by
    intro x
    simp only [hdbl]
    exact GlobalTheory.T.rationalSymplecticPoints_self_annihilator D ψ hψ S T x
  exact eq_zero_abstract (G := WO S T) (ratL T S) K hK hcov ψ hψc hψn (symplOH S T) hl hr halt hcont hann f₀ f
    h₀.cont hf.cont (quasi_of_mem h₀) (quasi_of_mem hf) hne μ 𝓕 hμ h𝓕 horth

end GlobalTheory.HeisTotal

end
