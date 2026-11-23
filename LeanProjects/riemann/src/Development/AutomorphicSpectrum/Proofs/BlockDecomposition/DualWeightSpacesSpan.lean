import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCliff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CPoly
import GroundTheory.GlobalFields.TateThesis.ArchCharsUnitary

noncomputable section

open Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RealCount.TorusSpan

open PositivityTheory.RgBcC Module.End

variable {n : ℕ}

theorem diag_mem (t : Fin n → Circle) :
    diagonal (fun a => (t a : ℂ)) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  simp [Complex.mul_conj]

def torus : (Fin n → Circle) →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun t := ⟨diagonal fun a => (t a : ℂ), diag_mem t⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp [diagonal_mul_diagonal])

theorem continuous_torus : Continuous (torus (n := n)) := by
  apply Continuous.subtype_mk
  apply Continuous.matrix_diagonal
  exact continuous_pi fun a => continuous_subtype_val.comp (continuous_apply a)

variable (E : KMod n)

theorem inner_rho (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : E.V) : ⟪E.ρ k x, E.ρ k y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(E.ρ k : E.V →ₗ[ℂ] E.V), E.iso k⟩ : E.V →ₗᵢ[ℂ] E.V).inner_map_map x y

theorem rho_inv_apply (k : Matrix.unitaryGroup (Fin n) ℂ) (y : E.V) : E.ρ k (E.ρ k⁻¹ y) = y := by
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]

theorem inner_rho_left (k : Matrix.unitaryGroup (Fin n) ℂ) (x y : E.V) :
    ⟪E.ρ k x, y⟫_ℂ = ⟪x, E.ρ k⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← rho_inv_apply E k y]
  exact inner_rho E k x _

end GlobalTheory.CompanionTheory.RealCount.TorusSpan

namespace GlobalTheory.CompanionTheory.RealCount.TorusSpan

open PositivityTheory.RgBcC Module.End

theorem jointEig_top {V I : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (T : I → V →ₗ[ℂ] V) (hc : ∀ i k, Commute (T i) (T k))
    (hadj : ∀ i, ∃ k, ∀ x y, ⟪T i x, y⟫_ℂ = ⟪x, T k y⟫_ℂ) :
    ⨆ χ : I → ℂ, ⨅ i, eigenspace (T i) (χ i) = ⊤ := by
  choose s hs using hadj
  have hs' : ∀ i x y, ⟪T (s i) x, y⟫_ℂ = ⟪x, T i y⟫_ℂ := fun i x y => by
    rw [← inner_conj_symm, ← hs, inner_conj_symm]
  let H : I ⊕ I → V →ₗ[ℂ] V := Sum.elim (fun i => T i + T (s i)) (fun i => Complex.I • (T i - T (s i)))
  have hH : ∀ i, (H i).IsSymmetric := by
    rintro (i | i) x y
    · simp only [H, Sum.elim_inl, LinearMap.add_apply, inner_add_left, inner_add_right, hs i, hs' i]
      ring
    · simp only [H, Sum.elim_inr, LinearMap.smul_apply, LinearMap.sub_apply, inner_smul_left, inner_smul_right,
        inner_sub_left, inner_sub_right, hs i, hs' i, Complex.conj_I]
      ring
  have hT : ∀ i k, Commute (H i) (T k) := by
    rintro (i | i) k
    · exact (hc _ _).add_left (hc _ _)
    · exact ((hc _ _).sub_left (hc _ _)).smul_left _
  have hHc : ∀ i k, Commute (H i) (H k) := by
    rintro i (k | k)
    · exact (hT _ _).add_right (hT _ _)
    · exact ((hT _ _).sub_right (hT _ _)).smul_right _
  have h := LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hH (fun i k _ => hHc i k)
  rw [eq_top_iff, ← h]
  refine iSup_le fun χ => le_iSup_of_le (fun i => (χ (.inl i) - Complex.I * χ (.inr i)) / 2) fun x hx => ?_
  simp only [Submodule.mem_iInf, mem_eigenspace_iff] at hx ⊢
  intro i
  have h1 : T i x + T (s i) x = χ (.inl i) • x := hx (.inl i)
  have h2 : Complex.I • (T i x - T (s i) x) = χ (.inr i) • x := hx (.inr i)
  have h3 : T i x - T (s i) x = -(Complex.I * χ (.inr i)) • x := by
    rw [neg_smul, mul_smul, ← h2, smul_smul, Complex.I_mul_I]; simp
  have h4 : (2 : ℂ) • T i x = (χ (.inl i) - Complex.I * χ (.inr i)) • x := by
    rw [sub_eq_add_neg, add_smul, ← h1, ← h3, two_smul]; abel
  rw [div_eq_inv_mul, mul_smul, ← h4, smul_smul]; simp

variable {n : ℕ} (E : KMod n)

def rhoT (t : Fin n → Circle) : E.V →ₗ[ℂ] E.V := ((E.ρ (torus t) : E.V →L[ℂ] E.V) : E.V →ₗ[ℂ] E.V)

theorem span_V : ⨆ χ : (Fin n → Circle) → ℂ, ⨅ t, eigenspace (rhoT E t) (χ t) = ⊤ := by
  apply jointEig_top
  · intro s t
    have h : torus s * torus t = torus t * torus s := by rw [← map_mul, ← map_mul, mul_comm]
    refine LinearMap.ext fun x => ?_
    simp only [rhoT, Module.End.mul_apply, ContinuousLinearMap.coe_coe]
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, h, map_mul, ContinuousLinearMap.mul_apply]
  · intro t
    refine ⟨t⁻¹, fun x y => ?_⟩
    simp only [rhoT, ContinuousLinearMap.coe_coe]
    rw [inner_rho_left, map_inv torus t]

theorem exists_weight {χ : (Fin n → Circle) → ℂ} {v : E.V}
    (hv : v ∈ ⨅ t, eigenspace (rhoT E t) (χ t)) (hv0 : v ≠ 0) :
    ∃ μ : Fin n → ℤ, ∀ t, E.ρ (torus t) v = (∏ a, (t a : ℂ) ^ μ a) • v := by
  have hχ : ∀ t, E.ρ (torus t) v = χ t • v := fun t =>
    mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv t)
  have hmul : ∀ s t, χ (s * t) = χ s * χ t := by
    intro s t
    have h := hχ (s * t)
    rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, hχ t, map_smul, hχ s, smul_smul] at h
    rw [← smul_left_injective ℂ hv0 h, mul_comm]
  have hone : χ 1 = 1 := by
    have h := hχ 1
    rw [map_one, map_one, ContinuousLinearMap.one_apply] at h
    exact (smul_left_injective ℂ hv0 (h.symm.trans (one_smul ℂ v).symm))
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hv0
  have hform : ∀ t, χ t = ⟪v, E.ρ (torus t) v⟫_ℂ / ⟪v, v⟫_ℂ := by
    intro t
    rw [hχ, inner_smul_right, mul_div_assoc, div_self hvv, mul_one]
  have hcont : Continuous χ := by
    have : χ = fun t => ⟪v, E.ρ (torus t) v⟫_ℂ / ⟪v, v⟫_ℂ := funext hform
    rw [this]
    exact (continuous_const.inner ((E.cont.comp continuous_torus).clm_apply continuous_const)).div_const _
  let χM : (Fin n → Circle) →* ℂ := ⟨⟨χ, hone⟩, hmul⟩
  have hc : ∀ a, ∃ m : ℤ, ∀ z : Circle, χ (Pi.mulSingle a z) = (z : ℂ) ^ m := by
    intro a
    let f : Circle →* ℂˣ := (χM.comp (MonoidHom.mulSingle _ a)).toHomUnits
    have hf : Continuous f := by
      have hs : Continuous fun z : Circle => (Pi.mulSingle a z : Fin n → Circle) := by
        refine continuous_pi fun j => ?_
        rcases eq_or_ne j a with rfl | h
        · simp only [Pi.mulSingle_eq_same]; exact continuous_id'
        · simpa [Pi.mulSingle_eq_of_ne h] using continuous_const
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · show Continuous fun z => χ (Pi.mulSingle a z)
        exact hcont.comp hs
      have : (fun z => (((f z)⁻¹ : ℂˣ) : ℂ)) = fun z => χ (Pi.mulSingle a z⁻¹) := by
        funext z; rw [← map_inv]; rfl
      rw [this]; exact hcont.comp (hs.comp continuous_inv)
    obtain ⟨m, hm, -⟩ := GroundTheory.Global.existsUnique_circle_zpow ⟨f, hf⟩
    exact ⟨m, hm⟩
  choose μ hμ using hc
  refine ⟨μ, fun t => ?_⟩
  rw [hχ]
  congr 1
  conv_lhs => rw [← Finset.univ_prod_mulSingle t]
  change χM (∏ a, Pi.mulSingle a (t a)) = _
  rw [map_prod]
  exact Finset.prod_congr rfl fun a _ => hμ a (t a)

end GlobalTheory.CompanionTheory.RealCount.TorusSpan

namespace GlobalTheory.CompanionTheory.RealCount.TorusSpan

open PositivityTheory.RgBcC Module.End

variable {n : ℕ}

theorem exists_torus (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ) (hk : k.1 = diagonal z) :
    ∃ t : Fin n → Circle, torus t = k ∧ ∀ a, (t a : ℂ) = z a := by
  have hn : ∀ a, ‖z a‖ = 1 := by
    intro a
    have h1 := congrFun (congrFun (Matrix.mem_unitaryGroup_iff'.1 k.2) a) a
    rw [hk, Matrix.star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal] at h1
    simp only [diagonal_apply_eq, one_apply_eq, Pi.star_apply, Complex.star_def] at h1
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at h1
    have h2 : ‖z a‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  refine ⟨fun a => ⟨z a, mem_sphere_zero_iff_norm.2 (hn a)⟩, Subtype.ext ?_, fun a => rfl⟩
  rw [hk]
  rfl

end GlobalTheory.CompanionTheory.RealCount.TorusSpan

namespace GlobalTheory.CompanionTheory.RealCount.Tope

open PositivityTheory.RgBcC Module.End GlobalTheory.CompanionTheory.RealCount.TorusSpan

theorem iSup_wtDual_eq_top {n : ℕ} (E : KMod n) : (⨆ μ, wtDual E μ) = ⊤ := by
  haveI := FiniteDimensional.complete ℂ E.V
  rw [eq_top_iff]
  intro ξ _
  obtain ⟨v, rfl⟩ := (InnerProductSpace.toDual ℂ E.V).surjective ξ
  have hv : v ∈ (⊤ : Submodule ℂ E.V) := trivial
  rw [← span_V E] at hv
  refine Submodule.iSup_induction _ (motive := fun v => InnerProductSpace.toDual ℂ E.V v ∈ ⨆ μ, wtDual E μ) hv
    ?_ ?_ ?_
  · intro χ v hv
    by_cases hv0 : v = 0
    · subst hv0; simp
    obtain ⟨μ, hμ⟩ := exists_weight E hv hv0
    refine Submodule.mem_iSup_of_mem (-μ) ?_
    intro k z hk
    obtain ⟨t, rfl, htz⟩ := exists_torus k z hk
    ext w
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply_apply,
      InnerProductSpace.toDual_apply_apply, ← inner_rho_left, hμ, inner_smul_left, smul_eq_mul]
    congr 1
    rw [map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← htz, map_zpow₀, ← Circle.coe_inv_eq_conj, ← Circle.coe_zpow, ← Circle.coe_zpow, _root_.inv_zpow', Pi.neg_apply]
  · simp
  · intro x y hx hy
    rw [map_add]
    exact add_mem hx hy

end GlobalTheory.CompanionTheory.RealCount.Tope
