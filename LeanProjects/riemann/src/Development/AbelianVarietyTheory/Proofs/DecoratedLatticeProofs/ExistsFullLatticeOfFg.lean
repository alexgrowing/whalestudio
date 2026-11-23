import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

namespace GlobalTheory.SpanLattice

open Formalism.L2.GlobalTheoryTheory.HLatOps

theorem exists_fullLattice_of_fg :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)
      (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ), (∀ v, IsUnit (X v).det) →
      ∀ N : Submodule (𝓞 K) (Fin n → K), N.FG →
      ∃ (j : ℕ) (e : Fin j → Fin n → K) (Y : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ)
        (L : Submodule (𝓞 K) (Fin j → K)), LinearIndependent K e ∧ (∀ v, IsUnit (Y v).det) ∧
        Submodule.IsLattice K L ∧ (∀ x : Fin j → K, x ∈ L ↔ ∑ i, x i • e i ∈ N) ∧
        (∀ v, gram Y v (fun i => (Pi.single i 1 : Fin j → K)) = gram X v e) ∧
        lcv Y L = lcv X N := by
  intro K _ _ _ n X hX N hN
  set U : Submodule K (Fin n → K) := Submodule.span K (N : Set (Fin n → K)) with hU
  let c := Module.finBasis K U
  let e : Fin (finrank K U) → Fin n → K := fun i => (c i : Fin n → K)
  let ψ : (Fin (finrank K U) → K) →ₗ[K] (Fin n → K) := U.subtype ∘ₗ c.equivFun.symm.toLinearMap
  have hψ : ∀ x, ψ x = ∑ i, x i • e i := by
    intro x
    simp [ψ, e, Basis.equivFun_symm_apply]
  have hinj : Function.Injective ψ :=
    (Submodule.injective_subtype U).comp c.equivFun.symm.injective
  have hrange : ∀ y ∈ U, ∃ x, ψ x = y := fun y hy =>
    ⟨c.equivFun ⟨y, hy⟩, by simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, Submodule.subtype_apply]⟩
  have hmemU : ∀ x, ψ x ∈ U := fun x => (c.equivFun.symm x).2
  have hsingle : ∀ i, ψ (Pi.single i 1) = e i := by
    intro i
    rw [hψ, Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  let L : Submodule (𝓞 K) (Fin (finrank K U) → K) := N.comap (ψ.restrictScalars (𝓞 K))
  have hmap : L.map (ψ.restrictScalars (𝓞 K)) = N := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := hrange y (Submodule.subset_span hy)
      exact ⟨x, hy, rfl⟩
  have hfg : L.FG :=
    Submodule.fg_of_fg_map_injective (ψ.restrictScalars (𝓞 K)) hinj (by rw [hmap]; exact hN)
  have hS := isSesq_comp (isSesq_maj (Pi.basisFun K (Fin n)) X) ψ
  have hP := posAt_comp (Pi.basisFun K (Fin n)) (Pi.basisFun K (Fin (finrank K U)))
    (isSesq_maj (Pi.basisFun K (Fin n)) X) (posAt_maj (Pi.basisFun K (Fin n)) X hX) ψ hinj
  obtain ⟨h1, h2, h3⟩ := of_form_spec K _ _ (Pi.basisFun K (Fin (finrank K U))) L _ hS hP
  let Y : InfinitePlace K → Matrix (Fin (finrank K U)) (Fin (finrank K U)) ℂ := fun v =>
    frameOf (gramOf (Pi.basisFun K (Fin (finrank K U)))
      (fun x y => Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y)))
  have hY : ∀ v, IsUnit (Y v).det := h1
  have hm : ∀ v x y, Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin (finrank K U))) Y v x y =
      Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin n)) X v (ψ x) (ψ y) := h2
  have hn : ∀ v x, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X v (ψ x) =
      Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin (finrank K U))) Y v x := fun v x => by
    rw [normAt_eq_sqrt (Pi.basisFun K (Fin n)) X v (ψ x)]
    exact (h3 v x).symm
  refine ⟨finrank K U, e, Y, L, ?_, hY, ⟨hfg, ?_⟩, fun x => ?_, fun v => ?_, ?_⟩
  · exact c.linearIndependent.map' U.subtype (Submodule.ker_subtype U)
  · rw [eq_top_iff]
    intro x _
    have hsp : Submodule.span K (N : Set (Fin n → K)) =
        (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ := by
      rw [Submodule.map_span, ← hmap]
      rfl
    have hx : ψ x ∈ (Submodule.span K (L : Set (Fin (finrank K U) → K))).map ψ := by
      rw [← hsp]
      exact hmemU x
    obtain ⟨y, hy, hxy⟩ := hx
    exact hinj hxy ▸ hy
  · rw [← hψ]
    rfl
  · ext a b
    simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, hm, hsingle]
  · have h := (Formalism.HN.rerealize K _ _ _ _ (Pi.basisFun K (Fin (finrank K U))) Y
      (Pi.basisFun K (Fin n)) X ψ hY hX hinj hn L hfg).1
    rw [hmap] at h
    unfold lcv
    rw [h]

end GlobalTheory.SpanLattice
