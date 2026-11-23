import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemEigSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LieBridgeC
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieType

noncomputable section
namespace GlobalTheory.UPel.HT.LieType

open Polynomial in

theorem toLin'_map_aeval_int {F : Type} [Field F] [NumberField F] {g : ℕ}
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (x : 𝓞 F) (p : ℤ[X]) :
    Matrix.toLin' (φ (aeval x p)) = aeval (Matrix.toLin' (φ x)) (p.map (algebraMap ℤ ℂ)) := by
  have h1 : φ (aeval x p) = aeval (φ x) p := (Polynomial.aeval_algHom_apply φ.toIntAlgHom x p).symm
  rw [h1, ← Polynomial.aeval_map_algebraMap ℂ (φ x) p]
  exact (Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin g)) (φ x) _).symm

open Polynomial in

theorem trace_eq_sum_finrank_eigSp : ∀ (F : Type) [Field F] [NumberField F] (g : ℕ)
    (φ : 𝓞 F →+* Matrix (Fin g) (Fin g) ℂ) (c : 𝓞 F),
    (φ c).trace = ∑ τ : F →+* ℂ, (Module.finrank ℂ (eigSp φ τ) : ℂ) * τ (c : F) := by
  intro F _ _ g φ c
  classical
  obtain ⟨α, hinj, ⟨f, hf0, hfmap⟩, hmul⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.exists_sepElt (E := F) (F := ℂ)
    (RingHom.id ℂ) (fun τ => τ.comp (algebraMap (𝓞 F) F)) (fun _ _ => rfl)
  simp only [RingHom.comp_apply] at hinj hfmap
  set L : Module.End ℂ (Fin g → ℂ) := Matrix.toLin' (φ α) with hL

  have hLf : aeval L (∏ τ : F →+* ℂ, (X - C (τ ((α : 𝓞 F) : F)))) = 0 := by
    rw [← hfmap, ← algebraMap_int_eq, hL, ← toLin'_map_aeval_int, hf0, map_zero, map_zero]
  have hss : L.IsSemisimple := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero ?_ hLf
    exact (Polynomial.separable_prod_X_sub_C_iff'.2 fun x _ y _ h => hinj h).squarefree

  have hW : ∀ τ : F →+* ℂ, eigSp φ τ = L.eigenspace (τ ((α : 𝓞 F) : F)) := by
    intro τ
    ext u
    rw [Module.End.mem_eigenspace_iff, mem_eigSp, hL, Matrix.toLin'_apply]
    refine ⟨fun h => h α, fun h c' => ?_⟩
    obtain ⟨N, p, hN, hp⟩ := hmul c'
    have hNC : (N : ℂ) ≠ 0 := Int.cast_ne_zero.2 hN
    have key : φ ((N : 𝓞 F) * c') *ᵥ u = τ (((N : 𝓞 F) * c' : 𝓞 F) : F) • u := by
      rw [hp, ← Matrix.toLin'_apply, toLin'_map_aeval_int]
      by_cases hu : u = 0
      · simp [hu]
      have hev : L.HasEigenvector (τ ((α : 𝓞 F) : F)) u :=
        ⟨Module.End.mem_eigenspace_iff.2 (by rw [hL, Matrix.toLin'_apply]; exact h), hu⟩
      rw [← hL, Module.End.aeval_apply_of_hasEigenvector hev]
      congr 1
      have h2 : (τ.comp (algebraMap (𝓞 F) F)) (aeval α p) = aeval ((τ.comp (algebraMap (𝓞 F) F)) α) p :=
        (Polynomial.aeval_algHom_apply (τ.comp (algebraMap (𝓞 F) F)).toIntAlgHom α p).symm
      simp only [RingHom.comp_apply] at h2
      rw [RingOfIntegers.coe_eq_algebraMap, h2, Polynomial.eval_map_algebraMap]
    have e1 : φ ((N : 𝓞 F) * c') = (N : ℂ) • φ c' := by
      rw [map_mul, map_intCast, Int.cast_smul_eq_zsmul, zsmul_eq_mul]
    have e2 : τ (((N : 𝓞 F) * c' : 𝓞 F) : F) = (N : ℂ) * τ (c' : F) := by
      simp
    rw [e1, e2, Matrix.smul_mulVec, mul_smul] at key
    exact smul_right_injective _ hNC key

  have hind : iSupIndep (eigSp φ) := by
    have := iSupIndep.comp (Module.End.eigenspaces_iSupIndep L) hinj
    convert this using 1
    funext τ
    exact hW τ
  have htop : ⨆ τ, eigSp φ τ = ⊤ := by
    rw [eq_top_iff, ← hss.iSup_eigenspace_eq_top, iSup_le_iff]
    intro m
    by_cases hm : L.eigenspace m = ⊥
    · rw [hm]; exact bot_le
    · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
      have hev : L.HasEigenvector m u := ⟨hu, hu0⟩
      have h0 := Module.End.aeval_apply_of_hasEigenvector hev
        (p := ∏ τ : F →+* ℂ, (X - C (τ ((α : 𝓞 F) : F))))
      rw [hLf, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h0
      have hroot := h0.resolve_right hu0
      rw [eval_prod, Finset.prod_eq_zero_iff] at hroot
      obtain ⟨τ, -, hτ⟩ := hroot
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hτ
      rw [hτ, ← hW τ]
      exact le_iSup (eigSp φ) τ
  have hint : DirectSum.IsInternal (eigSp φ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have hmaps : ∀ τ, Set.MapsTo (Matrix.toLin' (φ c)) (eigSp φ τ) (eigSp φ τ) := by
    intro τ u hu
    have hu' := (mem_eigSp φ τ u).1 hu
    show Matrix.toLin' (φ c) u ∈ eigSp φ τ
    rw [Matrix.toLin'_apply, hu' c]
    exact (eigSp φ τ).smul_mem _ hu
  rw [← Matrix.trace_toLin'_eq, LinearMap.trace_eq_sum_trace_restrict hint hmaps]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hres : (Matrix.toLin' (φ c)).restrict (hmaps τ) = τ (c : F) • LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext ?_
    have hv := (mem_eigSp φ τ v).1 v.2
    show Matrix.toLin' (φ c) (v : Fin g → ℂ) = τ (c : F) • (v : Fin g → ℂ)
    rw [Matrix.toLin'_apply, hv c]
  rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]

end GlobalTheory.UPel.HT.LieType
