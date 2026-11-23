import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraAlt

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound

namespace GlobalTheory.OnRankAlg

section Gen

variable {K : Type} [Field K] [NumberField K]
variable {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z]

theorem exists_smul_mem_of_mem_span {A : Submodule (𝓞 K) Z} {x : Z} (hx : x ∈ Submodule.span K (A : Set Z)) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.TargetLemmaCollection.target
  | exact _root_.GlobalTheory.TargetLemmaCollection.target
  | (apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply _root_.GlobalTheory.TargetLemmaCollection.target <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TargetLemmaCollection.target <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TargetLemmaCollection.target ..)

theorem span_cut {A : Submodule (𝓞 K) Z} (hA : Submodule.span K (A : Set Z) = ⊤) (W : Submodule K Z) :
    Submodule.span K (Formalism.EigenvalueLevelCeiling.cut W A : Set Z) = W := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro x hx
    exact (Submodule.mem_inf.1 hx).2
  · intro w hw
    obtain ⟨d, hd, hm⟩ := exists_smul_mem_of_mem_span (A := A) (x := w) (by rw [hA]; trivial)
    have hd' : algebraMap (𝓞 K) K d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hd
    have hmem : d • w ∈ Formalism.EigenvalueLevelCeiling.cut W A := by
      refine Submodule.mem_inf.2 ⟨hm, ?_⟩
      show d • w ∈ W
      rw [← algebraMap_smul K d w]
      exact W.smul_mem _ hw
    have hw' : w = (algebraMap (𝓞 K) K d)⁻¹ • (d • w) := by
      rw [← algebraMap_smul K d w, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [hw']
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)

theorem span_le_span_sc {a : K} (ha : a ≠ 0) (A : Submodule (𝓞 K) Z) :
    Submodule.span K (A : Set Z) ≤ Submodule.span K (Formalism.EigenvalueLevelCeiling.sc a A : Set Z) := by
  rw [Submodule.span_le]
  intro y hy
  have hm : a • y ∈ Formalism.EigenvalueLevelCeiling.sc a A := Submodule.mem_map.2 ⟨y, hy, rfl⟩
  have hy' : y = a⁻¹ • (a • y) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  rw [hy']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem locP_subset_span (v : HeightOneSpectrum (𝓞 K)) (L : Submodule (𝓞 K) Z) :
    (Formalism.HermitianLatticesTheory.localization₂ v.asIdeal L : Set Z) ⊆ Submodule.span K (L : Set Z) := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := hx
  have hs0 : s ≠ 0 := fun h => hs (h ▸ v.asIdeal.zero_mem)
  have hs' : algebraMap (𝓞 K) K s ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 hs0
  have hx' : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
    rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs', one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsx)

variable {P : Type} [Group P]

theorem mem_eig_iff (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (x : Z) :
    x ∈ Formalism.EigenvalueLevelCeiling.eig ρ U ψ ↔ ∀ u : U, ρ u x = ((ψ u : 𝓞 K) : K) • x := by
  unfold Formalism.EigenvalueLevelCeiling.eig
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem map_eig (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) :
    (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).map e = Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine Submodule.mem_inf.2 ⟨(mem_eig_iff ρ U ψ _).2 fun u => ?_, by rw [← hp.2]; exact LinearMap.mem_range_self e x⟩
    have h := congrArg (fun f : Z →ₗ[K] Z => f x) (hc u)
    simp only [LinearMap.comp_apply] at h
    rw [← h, (mem_eig_iff ρ U ψ x).1 hx u, map_smul]
  · intro x hx
    obtain ⟨hx, hv⟩ := Submodule.mem_inf.1 hx
    rw [← hp.2] at hv
    obtain ⟨y, rfl⟩ := hv
    exact ⟨e y, hx, congrArg (fun f : Z →ₗ[K] Z => f y) hp.1⟩

theorem isLatIn_map (ρ : Representation K P Z) (U : Subgroup P) (ψ : P → 𝓞 K) (e : Z →ₗ[K] Z) (V₀ : Submodule K Z)
    (hp : e ∘ₗ e = e ∧ LinearMap.range e = V₀) (hc : ∀ g : P, e ∘ₗ ρ g = ρ g ∘ₗ e) {A : Submodule (𝓞 K) Z}
    (hfg : A.FG) (hle : A ≤ (Formalism.EigenvalueLevelCeiling.eig ρ U ψ).restrictScalars (𝓞 K))
    (hge : (Formalism.EigenvalueLevelCeiling.eig ρ U ψ : Set Z) ⊆ Submodule.span K (A : Set Z)) :
    Formalism.EigenvalueLevelCeiling.IsLatIn (Formalism.EigenvalueLevelCeiling.eig ρ U ψ ⊓ V₀) (A.map (e.restrictScalars (𝓞 K))) := by
  refine ⟨hfg.map _, ?_⟩
  have hs : Submodule.span K (A : Set Z) = Formalism.EigenvalueLevelCeiling.eig ρ U ψ :=
    le_antisymm (Submodule.span_le.2 fun x hx => hle hx) hge
  rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image, hs, map_eig ρ U ψ e V₀ hp hc]

end Gen

theorem rankAtPlaces_alg : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Bs : DefBase K) (Df : DefSide Bs) (S : IndefData Df) (P : Type) [Group P] [Finite P] (c : OnConst) (O : OnObj S P c), LeafSpan O → LeafData O → LeafProj O → (∀ j (g : P), O.e j ∘ₗ O.ρ j g = O.ρ j g ∘ₗ O.e j) → (AtPair S fun v => ∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) → RankAtPlaces O := by
  intro K _ _ _ Bs Df S P _ _ c O hSp hD hPr hc hJ w hw
  have one : ∀ v : HeightOneSpectrum (𝓞 K),
      (∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.Th v j) ∧ Formalism.EigenvalueLevelCeiling.IsLatIn ⊤ (O.ThK v j)) →
      (∀ j, (O.Th0 v j).FG ∧ O.Th0 v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.EigenvalueLevelCeiling.sc ((Nat.card O.U : ℕ) : K) (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j)) ≤ O.Th0 v j) →
      (∀ j, (O.ThJ v j).FG ∧ O.ThJ v j ≤ (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).restrictScalars (𝓞 K) ∧
        Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j)) →
      ∀ j, Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) ((O.Th0 v j).map ((O.e j).restrictScalars (𝓞 K))) ∧
        Formalism.EigenvalueLevelCeiling.IsLatIn (O.Zg j) (O.eJ v j) ∧ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.Th0 v j) ≤ Formalism.HermitianLatticesTheory.localization₂ v.asIdeal (O.ThJ v j) := by
    intro v hs hd hj j
    have hU : ((Nat.card O.U : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    have h0 : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.Th0 v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      have h1 : x ∈ Submodule.span K (Formalism.EigenvalueLevelCeiling.cut (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ) (O.ThK v j) : Set (Fin (O.nZ j) → K)) := by
        rw [span_cut (hs j).2.2]; exact hx
      exact Submodule.span_mono (fun y hy => (hd j).2.2 hy) (span_le_span_sc hU _ h1)
    have hJs : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ : Set (Fin (O.nZ j) → K)) ⊆ (Submodule.span K (O.ThJ v j : Set (Fin (O.nZ j) → K)) : Set (Fin (O.nZ j) → K)) := by
      intro x hx
      exact Submodule.span_le.2 (fun y hy => locP_subset_span v _ ((hj j).2.2 (Formalism.HermitianLatticesTheory.locBasic_le_locS _ _ hy))) (h0 hx)
    exact ⟨isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hd j).1 (hd j).2.1 h0,
      isLatIn_map (O.ρ j) O.U O.ψ (O.e j) (O.V₀ j) (hPr j) (hc j) (hj j).1 (hj j).2.1 hJs, (hj j).2.2⟩
  exact ⟨one w (hSp w hw).1 (hD w hw).1 (hJ w hw).1, one _ (hSp w hw).2 (hD w hw).2 (hJ w hw).2⟩

end GlobalTheory.OnRankAlg

end
