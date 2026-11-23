import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral

noncomputable section

namespace GlobalTheory.LieDisc

open NumberField Matrix Polynomial GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD

theorem isIntegral_trace_of_isIntegral_matrix {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (M : Matrix n n K) (hM : IsIntegral ℤ M) : IsIntegral ℤ M.trace := by
  let L := AlgebraicClosure K
  let φ : Matrix n n K →ₐ[ℤ] Matrix n n L := ((algebraMap K L).mapMatrix).toIntAlgHom
  have hM' : IsIntegral ℤ (φ M) := hM.map φ
  have htr : algebraMap K L M.trace = (φ M).trace := by
    simp only [Matrix.trace, Matrix.diag, map_sum]
    rfl
  rw [← isIntegral_algebraMap_iff (A := K) (B := L) (algebraMap K L).injective, htr,
    Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : IsRoot (φ M).charpoly μ := (mem_roots'.1 hμ).2
  have hspec : μ ∈ spectrum L (φ M) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 hroot
  obtain ⟨p, hp, hp0⟩ := hM'
  refine ⟨p, hp, ?_⟩
  have h1 := spectrum.subset_polynomial_aeval (φ M) (p.map (algebraMap ℤ L)) ⟨μ, hspec, rfl⟩
  have h2 : aeval (φ M) (p.map (algebraMap ℤ L)) = 0 := by
    rw [aeval_map_algebraMap]; simpa [aeval_def] using hp0
  have : Nontrivial (Matrix n n L) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [spectrum.of_subsingleton] at hspec
    exact hspec
  rw [h2, spectrum.zero_eq, Set.mem_singleton_iff] at h1
  simpa [eval_map] using h1

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem isIntegral_of_mapsTo_lattice (Λ : Submodule (𝓞 E) (Fin r → E)) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) (Y : Matrix (Fin r) (Fin r) E)
    (hY : ∀ x ∈ Λ, Y *ᵥ x ∈ Λ) : IsIntegral (𝓞 E) Y := by
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  let f : Module.End (𝓞 E) Λ :=
    { toFun := fun x => ⟨Y *ᵥ (x : Fin r → E), hY _ x.2⟩
      map_add' := fun x y => by ext1; simp [mulVec_add]
      map_smul' := fun c x => by ext1; simp [mulVec_smul] }
  obtain ⟨p, hp, hp0⟩ := LinearMap.exists_monic_and_aeval_eq_zero (𝓞 E) f
  have key : ∀ q : (𝓞 E)[X], ∀ x (hx : x ∈ Λ), aeval Y q *ᵥ x = ((aeval f q ⟨x, hx⟩ : Λ) : Fin r → E) := by
    intro q
    induction q using Polynomial.induction_on with
    | C a =>
      intro x hx
      simp only [aeval_C]
      rw [show (algebraMap (𝓞 E) (Matrix (Fin r) (Fin r) E)) a = Matrix.diagonal (fun _ => (a : E)) from rfl]
      ext i
      rw [mulVec_diagonal, Module.algebraMap_end_apply]
      rfl
    | add p q hp hq =>
      intro x hx
      rw [map_add, add_mulVec, hp x hx, hq x hx, map_add]
      rfl
    | monomial n a ih =>
      intro x hx
      have e1 : aeval Y (C a * X ^ (n + 1)) = aeval Y (C a * X ^ n) * Y := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      have e2 : aeval f (C a * X ^ (n + 1)) = aeval f (C a * X ^ n) * f := by
        rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      rw [e1, e2, ← mulVec_mulVec, ih _ (hY x hx)]
      rfl
  have hker : ∀ v, aeval Y p *ᵥ v = 0 := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => rw [key p x hx, hp0]; rfl
    | zero => simp
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [mulVec_smul, hx, smul_zero]
  have hA : aeval Y p = 0 := by
    apply Matrix.toLin'.injective
    ext v i
    simp [Matrix.toLin'_apply, hker]
  exact ⟨p, hp, by rw [← aeval_def]; exact hA⟩

theorem isIntegral_trace_of_mem_endLat [IsCMField E] (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E) (hS : SelfDualLat G Λ)
    (hY : Y ∈ endLat Λ) : IsIntegral ℤ Y.trace :=
  isIntegral_trace_of_isIntegral_matrix Y
    (@isIntegral_trans ℤ (𝓞 E) _ _ _ _ _ _ _ AddCommGroup.intIsScalarTower _ Y
      (isIntegral_of_mapsTo_lattice Λ hS.2.2.1 hS.2.2.2.1 Y (mem_endLat.mp hY)))

theorem trace_integral_main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Y : Matrix (Fin r) (Fin r) E),
    SelfDualLat G Λ → Y ∈ endLat Λ → IsIntegral ℤ Y.trace :=
  fun _ _ _ _ _ G Λ Y hS hY => isIntegral_trace_of_mem_endLat G Λ Y hS hY

end GlobalTheory.LieDisc
