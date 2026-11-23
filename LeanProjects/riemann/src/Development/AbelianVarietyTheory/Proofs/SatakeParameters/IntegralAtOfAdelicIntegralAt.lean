import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
open Matrix

namespace GlobalTheory.RatInt

theorem mem_range_of_iA_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (a : E) (ha : iA F E a ∈ Formalism.L2.Herm.intAf F E) : a ∈ (algebraMap (𝓞 E) E).range := by
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have h1 : (fun _ => 1 : Fin 1 → E) ∈ Λ := Submodule.subset_span rfl
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • (fun _ => 1 : Fin 1 → E) := by
      funext i
      rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hmem : (fun _ => a : Fin 1 → E) ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin 1) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 1) (Fin 1) _) *ᵥ
      (fun _ => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
    have h2 : (fun _ => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (1 : E)) ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ :=
      Submodule.subset_span ⟨_, h1, rfl⟩
    have h3 := Submodule.smul_mem _ (⟨_, ha⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) h2
    convert h3 using 1
    funext i
    show _ = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (1 : E)
    rw [map_one, mul_one]
  rw [Formalism.UG.P.global_lattice_one_holds F E (Fin 1) Λ hfin hspan] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨c, ?_⟩
  have := congrFun hc 0
  simpa [Algebra.smul_def] using this

theorem intAt_of_intAtA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (x : E), IntAtA (F := F) P (iA F E x) → IntAt P x := by
  intro F E _ _ _ _ _ P x ⟨s, hs, hm⟩
  rw [← map_mul] at hm
  obtain ⟨r, hr⟩ := mem_range_of_iA_mem (F := F) _ hm
  exact ⟨r, s, hs, hr.symm⟩

end GlobalTheory.RatInt
