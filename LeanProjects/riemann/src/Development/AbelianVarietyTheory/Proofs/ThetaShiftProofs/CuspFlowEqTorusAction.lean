import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfB
import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ

set_option autoImplicit false

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt
open scoped ComplexConjugate

namespace GlobalTheory.CuspFlow

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}

theorem herm_comb_eq_zero (X : Data E r) (cu : CuspFD X ρ) (η : Fin ρ → E) :
    herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) = 0 := by
  have h : herm X.Gm (∑ a, η a • cu.e a) (∑ a, η a • cu.e a) =
      ∑ a, ∑ b, η a * cc (η b) * herm X.Gm (cu.e a) (cu.e b) := by
    simp only [herm, maxCuspsA_vec_apply, cc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
    calc ∑ k, ∑ l, ∑ b, ∑ a, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l))
        = ∑ k, ∑ b, ∑ a, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ b, ∑ a, ∑ k, ∑ l, η a * cu.e a k * X.Gm k l *
            (IsCMField.complexConj E (η b) * IsCMField.complexConj E (cu.e b l)) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.sum_comm]
      _ = _ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
            Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
          ring
  rw [h]
  simp [cu.iso]

theorem exists_int_coords (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) (a : E) (ha : cc a = a)
    (hai : IsIntegral ℤ a) :
    ∃ c : Fin (nZ X ρ) → ℤ, ∑ k, c k • zBas X cu k = ((X.m : E) * a * X.κ0) • mcMη η := by
  obtain ⟨γ, hγ, hγe⟩ := X.transv _ hη (herm_comb_eq_zero X cu η) a ha hai
  have hmem : ((X.m : E) * a * X.κ0) • mcMη η ∈ zGam X cu := by
    refine ⟨fun i j => ?_, γ, hγ, by rw [hγe, maxCuspsA_transv]⟩
    have hk := maxCuspsA_kappa_cc X
    simp only [cc] at hk ha
    simp only [mcMη, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, cc, map_mul, map_natCast,
      hk, ha, IsCMField.complexConj_apply_apply]
    ring
  exact (Submodule.mem_span_range_iff_exists_fun ℤ).mp ((hb.2 _).mp hmem)

theorem exists_linear (X : Data E r) (cu : CuspFD X ρ) (hb : IsZBasis X cu (zBas X cu))
    (η : Fin ρ → E) (hη : (∑ a, η a • cu.e a) ∈ X.Λ) :
    ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ),
      (∀ (s : X.Ψ → ℝ) (τ : X.Ψ) (a b : Fin ρ), ∑ k, (L s k : ℂ) * τ.1 (zBas X cu k a b) =
        τ.1 X.κ0 * (s τ : ℂ) * (τ.1 (η a) * conj (τ.1 (η b)))) ∧
      ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  obtain ⟨ω, hω⟩ := FlowMeanContinuity.exists_basis X 0
  have hωp : ∀ j, ω j ∈ X.periods 0 := fun j => by
    have : ω j ∈ RealEmbeddingCharacters.perL X 0 := hω ▸ Submodule.subset_span ⟨j, rfl⟩
    exact this
  choose a ha hai hae using fun j => (RealEmbeddingCharacters.mem_periods_iff X 0 _).mp (hωp j)
  choose c hc using fun j => exists_int_coords X cu hb η hη (a j) (ha j) (hai j)
  set n0 : ℕ := X.chiOrd 0 with hn0
  have hn0pos : (n0 : ℝ) ≠ 0 := by
    have := RealEmbeddingCharacters.chiOrd_pos X 0
    positivity
  let L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ) := ω.constr ℝ fun j k => (n0 : ℝ) * (c j k : ℝ)
  have hL : ∀ j k, L (ω j) k = (n0 : ℝ) * (c j k : ℝ) := fun j k => by
    simp only [L, Module.Basis.constr_basis]
  refine ⟨L, fun s τ i i' => ?_, fun la p hp k => ?_⟩
  · have hj : ∀ j, ∑ k, (L (ω j) k : ℂ) * τ.1 (zBas X cu k i i') =
        τ.1 X.κ0 * (ω j τ : ℂ) * (τ.1 (η i) * conj (τ.1 (η i'))) := by
      intro j
      have h1 := congrArg (fun M : Matrix (Fin ρ) (Fin ρ) E => τ.1 (M i i')) (hc j)
      simp only [Matrix.sum_apply, Matrix.smul_apply] at h1
      simp only [map_sum, mcMη, Matrix.of_apply,
        smul_eq_mul, zsmul_eq_mul, map_mul, map_intCast, map_natCast,
        Formalism.L2.Pj.FJ.emb_cc'] at h1
      have h2 : (ω j τ : ℂ) = (X.m : ℂ) * (n0 : ℂ) * τ.1 (a j) := by
        rw [hae j, RealEmbeddingCharacters.emb_real (ha j)]
        simp only [RealEmbeddingCharacters.per]
        push_cast
        rfl
      simp only [hL]
      push_cast
      simp only [mul_assoc (n0 : ℂ)]
      rw [← Finset.mul_sum, h1, h2]
      ring
    have hs : s = ∑ j, ω.repr s j • ω j := (ω.sum_repr s).symm
    generalize ω.repr s = t at hs
    subst hs
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [mul_assoc ((t j : ℝ) : ℂ)]
    rw [← Finset.mul_sum, hj]
    ring
  · obtain ⟨b, hb1, hb2, rfl⟩ := (RealEmbeddingCharacters.mem_periods_iff X la p).mp hp
    have h0 : RealEmbeddingCharacters.per X 0 b ∈ Submodule.span ℤ (Set.range ω) := by
      rw [hω]
      exact (RealEmbeddingCharacters.mem_periods_iff X 0 _).mpr ⟨b, hb1, hb2, rfl⟩
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h0
    have h1 : RealEmbeddingCharacters.per X la b =
        ((X.chiOrd la : ℝ) / (n0 : ℝ)) • RealEmbeddingCharacters.per X 0 b := by
      funext τ
      simp only [RealEmbeddingCharacters.per, Pi.smul_apply, smul_eq_mul, ← hn0]
      push_cast
      field_simp
    refine ⟨X.chiOrd la * ∑ j, d j * c j k, ?_⟩
    rw [h1, ← hd]
    simp only [map_smul, map_sum, map_zsmul, Pi.smul_apply, Finset.sum_apply, hL]
    simp only [smul_eq_mul, zsmul_eq_mul]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    field_simp

theorem flow_eq_zAct : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r ρ : ℕ) (X : Data E r) (cu : CuspFD X ρ), IsZBasis X cu (zBas X cu) → ∀ η : Fin ρ → E, (∑ a, η a • cu.e a) ∈ X.Λ → ∃ L : (X.Ψ → ℝ) →ₗ[ℝ] (Fin (nZ X ρ) → ℝ), (∀ s x, X.flow (∑ a, η a • cu.e a) (fun τ => (s τ : ℂ)) x = zAct X cu (L s) x) ∧ (∀ χ : Matrix (Fin ρ) (Fin ρ) E, IsHermE χ → ∀ s, ∑ k, phZ X cu χ k * L s k = 2 * ∑ τ : X.Ψ, (τ.1 (hq χ η)).re * s τ) ∧ ∀ (la : Wt X.Ψ r), ∀ p ∈ X.periods la, ∀ k, ∃ z : ℤ, L p k = z := by
  intro E _ _ _ r ρ X cu hb η hη
  obtain ⟨L, hL, hZ⟩ := exists_linear X cu hb η hη
  refine ⟨L, fun s x => ?_, fun χ _ s => ?_, hZ⟩
  · funext τ
    show X.flowMat (∑ a, η a • cu.e a) τ (s τ : ℂ) * mat x τ =
      zMatC X cu.e τ.1 (∑ k, (L s k : ℂ) • (zBas X cu k).map τ.1) * mat x τ
    rw [maxCuspsA_flowMat, ← TransvectionPeriodicity.emb_kappa]
    congr 2
    ext a b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mcMηc,
      Matrix.of_apply]
    exact (hL s τ a b).symm
  · simp only [phZ, prE, Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hκ : τ.1 X.κ0 ≠ 0 := fun h => by
      have := X.κ0_sign τ
      rw [h] at this
      simp at this
    have key : ∑ k, τ.1 (Matrix.trace (χ.transpose * zBas X cu k) / (X.κ0 / 2)) * (L s k : ℂ) =
        2 * (τ.1 (hq χ η) * (s τ : ℂ)) := by
      have e1 : ∀ k, τ.1 (Matrix.trace (χ.transpose * zBas X cu k) / (X.κ0 / 2)) * (L s k : ℂ) =
          ∑ b, ∑ a, 2 / τ.1 X.κ0 * τ.1 (χ a b) * ((L s k : ℂ) * τ.1 (zBas X cu k a b)) := by
        intro k
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply,
          map_div₀, map_sum, map_mul, map_ofNat, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
        field_simp
      simp only [e1]
      rw [Finset.sum_comm]
      simp only [hq, map_sum, map_mul, Formalism.L2.Pj.FJ.emb_cc', Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm (f := fun a b => 2 * (τ.1 (η a) * τ.1 (χ a b) * conj (τ.1 (η b)) * (s τ : ℂ)))]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.mul_sum, hL]
      field_simp
    have h := congrArg Complex.re key
    simpa [Complex.re_sum] using h

end GlobalTheory.CuspFlow
