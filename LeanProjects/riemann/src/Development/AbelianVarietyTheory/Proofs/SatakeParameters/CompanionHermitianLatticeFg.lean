import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImportsRest
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory.CompanFG

theorem fg_of_le_fg {R M : Type*} [CommRing R] [IsNoetherianRing R] [AddCommGroup M] [Module R M]
    {P Q : Submodule R M} (hQ : Q.FG) (hPQ : P ≤ Q) : P.FG := by
  haveI := isNoetherian_of_fg_of_noetherian Q hQ
  have h1 : (P.comap Q.subtype).FG := IsNoetherian.noetherian _
  have h2 := h1.map Q.subtype
  rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hPQ] at h2

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {N : ℕ} (Lb : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) (v : Fin N → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • v ∈ Lb := by
  first
  | exact @_root_.GlobalTheory.ExistsSmulMem.exists_smul_mem
  | exact _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem
  | (apply _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExistsSmulMem.exists_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExistsSmulMem.exists_smul_mem ..)

theorem hform_single {E : Type} [Field E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E)
    (c : E) (i : Fin N) (y : Fin N → E) :
    hform σ J (c • Pi.single i 1) y = σ c * (J *ᵥ y) i := by
  simp [hform, Pi.single_apply, mulVec, dotProduct, Finset.mul_sum, mul_assoc, apply_ite σ, ite_mul]

theorem dualSet_le_fg {E : Type} [Field E] [NumberField E] {N : ℕ} (σ : E →+* E)
    (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (Lb : Submodule (𝓞 E) (Fin N → E))
    (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    ∃ M : Submodule (𝓞 E) (Fin N → E), M.FG ∧ dualSet σ J Lb ⊆ M := by
  choose c hc0 hcm using fun i : Fin N => exists_smul_mem Lb hsp (Pi.single i 1)
  refine ⟨Submodule.span (𝓞 E) (Set.range fun i => (σ (c i : E))⁻¹ • (J⁻¹ *ᵥ Pi.single i 1)),
    Submodule.fg_span (Set.finite_range _), ?_⟩
  intro y hy
  have hint : ∀ i, ∃ w : 𝓞 E, (w : E) = σ (c i : E) * (J *ᵥ y) i := by
    intro i
    have h := hy _ (hcm i)
    rw [← algebraMap_smul E (c i), hform_single] at h
    obtain ⟨w, hw⟩ := h
    exact ⟨w, hw⟩
  choose w hw using hint
  have hσ : ∀ i, σ (c i : E) ≠ 0 := fun i => by
    rw [map_ne_zero]
    exact_mod_cast hc0 i
  have hy' : y = ∑ i, w i • ((σ (c i : E))⁻¹ • (J⁻¹ *ᵥ Pi.single i 1)) := by
    have e1 : y = J⁻¹ *ᵥ (J *ᵥ y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul J hJ, Matrix.one_mulVec]
    conv_lhs => rw [e1, ← Finset.univ_sum_single (J *ᵥ y)]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul E (w i), smul_smul, ← Matrix.mulVec_smul]
    congr 1
    ext k
    simp only [Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    split_ifs
    · subst_vars
      show (J *ᵥ y) k = (algebraMap (𝓞 E) E (w k)) * (σ (c k : E))⁻¹ * 1
      rw [show algebraMap (𝓞 E) E (w k) = (w k : E) from rfl, hw k]
      field_simp [hσ k]
    · simp
  rw [hy']
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.CompanFG

namespace GlobalTheory

open GlobalTheory.CompanFG in

theorem compan_fg {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (a : 𝓞 E)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfg : Lb.FG) (hsp : Submodule.span E (Lb : Set (Fin N → E)) = ⊤) :
    (compan (sp := sp) J a Lb).FG := by
  obtain ⟨M, hM, hle⟩ := dualSet_le_fg (sp.cm.sig : E →+* E) J hJ Lb hsp
  have h1 : (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)).FG :=
    fg_of_le_fg hM (Submodule.span_le.mpr hle)
  exact hfg.sup (fg_of_le_fg h1 Submodule.smul_le_right)

end GlobalTheory
