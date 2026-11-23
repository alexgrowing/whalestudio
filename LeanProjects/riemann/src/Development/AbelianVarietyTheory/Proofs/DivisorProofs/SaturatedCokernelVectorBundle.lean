import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleOfFreeStalks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrincipalIdealRingStalk

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB
open GlobalTheory.Twist (resM germ_resM)
open GlobalTheory.QCoh (stalkLinear)

namespace GlobalTheory.VB

theorem projective_of_retraction_of_smul_mem {R M N Q : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    [Module.Projective R M] [Module.IsTorsionFree R M] (f : N →ₗ[R] M) (ρ : M →ₗ[R] N)
    (hρ : ρ ∘ₗ f = LinearMap.id) (π : M →ₗ[R] Q) (hπ : Function.Surjective π)
    (h0 : ∀ n, π (f n) = 0) (hk : ∀ m, π m = 0 → ∃ a : R, a ≠ 0 ∧ ∃ n, f n = a • m) :
    Module.Projective R Q := by
  have hle : LinearMap.ker π ≤ LinearMap.ker (LinearMap.id - f ∘ₗ ρ) := by
    intro m hm
    obtain ⟨a, ha, n, hn⟩ := hk m hm
    have h1 : ρ (f n) = n := LinearMap.congr_fun hρ n
    have h2 : a • (m - f (ρ m)) = 0 := by
      rw [smul_sub, ← map_smul, ← map_smul, ← hn, h1, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left ha
  refine Module.Projective.of_split (R := R) (M := M)
    (((LinearMap.ker π).liftQ _ hle) ∘ₗ (π.quotKerEquivOfSurjective hπ).symm.toLinearMap) π ?_
  ext q
  obtain ⟨m, rfl⟩ := hπ q
  have e : (π.quotKerEquivOfSurjective hπ).symm (π m) = Submodule.Quotient.mk m :=
    (LinearEquiv.symm_apply_eq _).2 rfl
  simp [e, h0]

variable {X : Scheme.{0}} [IsIntegral X] {F G : X.Modules}

theorem exists_smul_mem_of_mem_range_satι (i : G ⟶ F) [F.IsQuasicoherent] [G.IsQuasicoherent]
    (x : X) {m : (F.presheaf.stalk x :)} (hm : m ∈ Set.range (stalkLinear (satι i) x)) :
    ∃ a : X.presheaf.stalk x, a ≠ 0 ∧ ∃ n, stalkLinear i x n = a • m := by
  obtain ⟨t, rfl⟩ := hm
  obtain ⟨V, hV, s, rfl⟩ := (sat i).presheaf.exists_germ_eq t
  obtain ⟨U, hU, hxU, hle⟩ := QCoh.exists_affine_mem_le x hV
  rw [← germ_resM hle hxU, QCoh.stalkLinear_germ]
  obtain ⟨a, ha, u, hu⟩ := (mem_satSub_iff i hU (genericPoint_mem hxU)).1
    ((satSub i).incl_app_mem (resM (sat i) hle s))
  refine ⟨X.presheaf.germ U x hxU a, fun h => ha (germ_injective_of_isIntegral X x hxU
    (h.trans (map_zero _).symm)), G.presheaf.germ U x hxU u, ?_⟩
  rw [QCoh.stalkLinear_germ, hu, QCoh.germ_smul]
  rfl

theorem isVB_cokernel_satι_of_split : ∀ (C : Scheme.{0}) [IsIntegral C] [IsLocallyNoetherian C] (F G : C.Modules) (r : ℕ) (φ : G ⟶ F), IsVB F (r + 1) → IsVB G 1 → Mono φ → (∀ x : C, IsPrincipalIdealRing (C.presheaf.stalk x) ∨ ∃ ρ : (F.presheaf.stalk x :) →ₗ[C.presheaf.stalk x] (G.presheaf.stalk x :), ρ ∘ₗ GlobalTheory.QCoh.stalkLinear φ x = LinearMap.id) → IsVB (Limits.cokernel (satι φ)) r := by
  intro C _ _ F G r φ hF hG _ H
  have := hF.isFiniteQC
  have := hG.isFiniteQC
  have hr : genRank (Limits.cokernel (satι φ)) = r := by
    have := genRank_cokernel (satι φ)
    rw [genRank_sat, hF.genRank_eq, hG.genRank_eq] at this
    omega
  refine isVB_of_basis_stalk C _ r fun x => ?_
  suffices Module.Free (C.presheaf.stalk x) ((Limits.cokernel (satι φ)).presheaf.stalk x :) from
    ⟨Module.finBasisOfFinrankEq _ _ ((finrank_stalk_eq_genRank x).trans hr)⟩
  rcases H x with h | ⟨ρ, hρ⟩
  · have := IsTorsionFree.isTorsionFree_stalk (isSaturated_satι φ) x
    infer_instance
  · obtain ⟨U, e, -, hxU, -, he⟩ := hF.exists_affine (V := ⊤) (x := x) trivial
    have := Module.Free.of_basis (he.stalkBasis x hxU)
    have := hF.isTorsionFree.isTorsionFree_stalk x
    have ex := (QCoh.exact_iff_stalkLinear _).1 (ShortComplex.exact_cokernel (satι φ)) x
    have := projective_of_retraction_of_smul_mem (stalkLinear φ x) ρ hρ
      (stalkLinear (Limits.cokernel.π (satι φ)) x) (QCoh.stalkLinear_surjective _ x)
      (fun n => (ex _).2 ⟨stalkLinear (toSat φ) x n, by
        rw [← LinearMap.comp_apply, ← QCoh.stalkLinear_comp, toSat_ι]⟩)
      (fun m hm => exists_smul_mem_of_mem_range_satι φ x ((ex _).1 hm))
    exact Module.free_of_flat_of_isLocalRing

end GlobalTheory.VB
