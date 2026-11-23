import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.T2SpaceScalarTensorExt

noncomputable section

namespace MassDataIdxK

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain Topology
open scoped Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : ℕ} (v : HeightOneSpectrum (𝓞 F))

theorem latImage (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (hfg : L.FG) :
    ∃ (m : ℕ) (b : Fin m → (Fin n → Fv F v ⊗[F] E)),
      (∀ i, b i ∈ latLoc (E := E) v (L : Set (Fin n → E))) ∧
      Submodule.span (Fv F v) (Set.range b) = ⊤ ∧
      (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
        (fun c : Fin m → Fv F v => ∑ i, c i • b i) ''
          Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := by
  obtain ⟨m, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (hfg.restrictScalars (R := ℤ))
  have hsL : ∀ i, s i ∈ L := fun i => by
    have : s i ∈ Submodule.span ℤ (Set.range s) := Submodule.subset_span ⟨i, rfl⟩
    rw [hs] at this; exact this
  set b : Fin m → (Fin n → Fv F v ⊗[F] E) := fun i => ratV (F := F) (Fv F v) (s i) with hb
  have hlat : latLoc (E := E) v (L : Set (Fin n → E)) =
      Submodule.span (v.adicCompletionIntegers F) (Set.range b) := by
    apply le_antisymm
    · unfold latLoc
      rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : x ∈ Submodule.span ℤ (Set.range s) := by rw [hs]; exact hx
      clear hx
      induction hx' using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
      | zero => rw [ratV_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [ratV_add]; exact add_mem hx hy
      | smul k x _ hx => rw [ratV_zsmul]; exact zsmul_mem hx k
    · unfold latLoc
      apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨s i, hsL i, rfl⟩
  have hbΛ : ∀ i, b i ∈ latLoc (E := E) v (L : Set (Fin n → E)) := fun i => by
    rw [hlat]; exact Submodule.subset_span ⟨i, rfl⟩
  refine ⟨m, b, hbΛ, ?_, ?_⟩
  · rw [eq_top_iff, ← spanTop v L hL, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    have : ratV (F := F) (Fv F v) x ∈ latLoc (E := E) v (L : Set (Fin n → E)) :=
      Submodule.subset_span ⟨x, hx, rfl⟩
    rw [hlat] at this
    exact Submodule.span_le_restrictScalars (v.adicCompletionIntegers F) (Fv F v) _ this
  · ext x
    rw [SetLike.mem_coe, hlat, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun i => (c i : Fv F v), fun i _ => (c i).2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨fun i => ⟨d i, hd i (Set.mem_univ _)⟩, rfl⟩

theorem latOpenCompact (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (hfg : L.FG) :
    IsOpen (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) ∧
      IsCompact (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) := by
  have := fdFE (F := F) (E := E)
  have := MassDataIdxSteps.tens_topRing (F := F) (E := E) v
  obtain ⟨m, b, -, hsp, heq⟩ := latImage v L hL hfg
  let Φ : (Fin m → Fv F v) →ₗ[Fv F v] (Fin n → Fv F v ⊗[F] E) :=
    { toFun := fun c => ∑ i, c i • b i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r c => by simp [Finset.smul_sum, smul_smul] }
  have hsurj : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i 1, ?_⟩
    simp [Φ, Pi.single_apply]
  have himg : (latLoc (E := E) v (L : Set (Fin n → E)) : Set (Fin n → Fv F v ⊗[F] E)) =
      Φ '' Set.pi Set.univ (fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) := heq
  rw [himg]
  refine ⟨IsModuleTopology.isOpenMap_of_surjective hsurj _
    (isOpen_set_pi Set.finite_univ fun i _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v), ?_⟩
  exact (isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v).image
    (IsModuleTopology.continuous_of_linearMap Φ)

end MassDataIdxK
