import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPointsLieOverDistinctPlacesStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

namespace GlobalTheory.SplitStab

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_latS_iff (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R))
    (hS : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) R (c : E) ∈ S)
    (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E))
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r))
    (y : Fin m → E ⊗[F] R) :
    y ∈ Formalism.UG.latS (F := F) R S Λ ↔ (∀ j, y j ∈ S) ∧
      ∀ j : Fin m, j.1 + 1 = m → ∃ s ∈ S, y j = Formalism.UG.inclE (F := F) R (t : E) * s := by
  constructor
  · intro hy
    unfold Formalism.UG.latS at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      rw [SetLike.mem_coe, hΛ] at hx
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · obtain ⟨r, hr, -⟩ := hx j
        simp only [hr]; exact hS r
      · obtain ⟨r, hr, hd⟩ := hx j
        obtain ⟨c, rfl⟩ := hd hj
        refine ⟨_, hS c, ?_⟩
        simp only [hr]; push_cast; rw [map_mul]
    | zero => exact ⟨fun j => zero_mem _, fun j _ => ⟨0, zero_mem _, by simp⟩⟩
    | add a b _ _ ha hb =>
      refine ⟨fun j => add_mem (ha.1 j) (hb.1 j), fun j hj => ?_⟩
      obtain ⟨s1, hs1, e1⟩ := ha.2 j hj
      obtain ⟨s2, hs2, e2⟩ := hb.2 j hj
      exact ⟨s1 + s2, add_mem hs1 hs2, by simp [Pi.add_apply, e1, e2, mul_add]⟩
    | smul a b _ hb =>
      refine ⟨fun j => ?_, fun j hj => ?_⟩
      · simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]
        exact mul_mem a.2 (hb.1 j)
      · obtain ⟨s, hs, e⟩ := hb.2 j hj
        refine ⟨(a : E ⊗[F] R) * s, mul_mem a.2 hs, ?_⟩
        simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, e]
        ring
  · rintro ⟨h1, h2⟩
    have key : ∀ (j : Fin m) (r : 𝓞 E), (j.1 + 1 = m → t ∣ r) → ∀ s ∈ S,
        Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) ∈ Formalism.UG.latS (F := F) R S Λ := by
      intro j r hr s hs
      have hx : (Pi.single j (r : E) : Fin m → E) ∈ Λ := by
        rw [hΛ]; intro i
        by_cases hij : i = j
        · subst hij; exact ⟨r, by simp, hr⟩
        · exact ⟨0, by simp [hij], fun _ => dvd_zero _⟩
      have : (Pi.single j (s * Formalism.UG.inclE (F := F) R (r : E)) : Fin m → E ⊗[F] R) =
          (⟨s, hs⟩ : S) • (fun i => Formalism.UG.inclE (F := F) R ((Pi.single j (r : E) : Fin m → E) i)) := by
        ext i; by_cases hij : i = j
        · subst hij; simp [Subring.smul_def]
        · simp [hij, Subring.smul_def]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hx, rfl⟩)
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : j.1 + 1 = m
    · obtain ⟨s, hs, e⟩ := h2 j hj
      rw [e, mul_comm]; exact key j t (fun _ => dvd_refl _) s hs
    · simpa using key j 1 (fun h => absurd h hj) (y j) (h1 j)

end GlobalTheory.SplitStab

theorem GlobalTheory.SplitStab.stab_of_split_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (φ : E ⊗[F] v.adicCompletion F →+* k),
    (∀ z, z ∈ Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring ↔
      φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR σ (v.adicCompletion F) z) ∈ 𝒪[k]) →
    ∀ (m : ℕ) (t : 𝓞 E) (Λ : Submodule (𝓞 E) (Fin m → E)),
    (∀ x, x ∈ Λ ↔ ∀ j : Fin m, ∃ r : 𝓞 E, x j = (r : E) ∧ (j.1 + 1 = m → t ∣ r)) →
    ∀ q : Unif k, valuation k (φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E))) = valuation k ((q.1 : 𝒪[k]) : k) →
    valuation k (φ (Formalism.UG.sigR σ (v.adicCompletion F) (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)))) = 1 →
    ∀ M : GL (Fin m) (E ⊗[F] v.adicCompletion F), M ∈ Formalism.UG.UJ (Formalism.UG.sigR σ (v.adicCompletion F)) 1 →
    ∀ h h' : Matrix (Fin m) (Fin m) k, M.val.map φ = h → h * h' = 1 →
    (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], u r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s) ↔
      ((∀ r, (h *ᵥ u) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (h *ᵥ u) r0 = φ (Formalism.UG.inclE (F := F) (v.adicCompletion F) (t : E)) * s)) →
    (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔ ∀ r, (h'ᵀ *ᵥ u) r ∈ 𝒪[k]) →
    M ∈ Formalism.UG.stabGL (Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ) := by
  intro F E _ _ _ _ _ σ v k _ _ _ _ φ hS m t Λ hΛ q hq hq' M hM h h' hh hhh' hA hB
  have hSO : ∀ c : 𝓞 E, Formalism.UG.inclE (F := F) (v.adicCompletion F) (c : E) ∈
      Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring :=
    fun c => Subring.subset_closure (Or.inl ⟨⟨(c : E), c, rfl⟩, rfl⟩)
  have ht : (t : E) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero, map_zero] at hq
    have h1 : ((q.1 : 𝒪[k]) : k) = 0 := (valuation k).zero_iff.mp hq.symm
    exact q.2.ne_zero (by simpa using h1)
  have hint : ∀ x : k, x ∈ 𝒪[k] ↔ valuation k x ≤ 1 := fun x => Valuation.mem_integer_iff (valuation k) x
  set σ' := Formalism.UG.sigR σ (v.adicCompletion F) with hσ'
  set ι := Formalism.UG.inclE (F := F) (E := E) (v.adicCompletion F) with hι

  have hchar : ∀ y : Fin m → E ⊗[F] v.adicCompletion F,
      y ∈ Formalism.UG.latS (F := F) (v.adicCompletion F)
          (Formalism.UG.tensInt (F := F) (v.adicCompletion F) (Formalism.UG.intOE E) (v.adicCompletionIntegers F).toSubring) Λ ↔
      (((∀ r, (fun j => φ (y j)) r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m →
        ∃ s ∈ 𝒪[k], (fun j => φ (y j)) r0 = φ (ι (t : E)) * s) ∧
        ∀ r, (fun j => φ (σ' (y j))) r ∈ 𝒪[k]) := by
    intro y
    rw [GlobalTheory.SplitStab.mem_latS_iff (F := F) (v.adicCompletion F) _ hSO m t Λ hΛ y]
    simp only [hS]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨fun r => (h1 r).1, fun r0 hr0 => ?_⟩, fun r => (h1 r).2⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      exact ⟨φ s, hs.1, by rw [e, map_mul]⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨fun r => ⟨h1 r, h3 r⟩, fun r0 hr0 => ?_⟩
      obtain ⟨s, hs, e⟩ := h2 r0 hr0
      have hu : ι (t : E) * ι ((t : E)⁻¹) = 1 := by rw [← map_mul, mul_inv_cancel₀ ht, map_one]
      refine ⟨ι ((t : E)⁻¹) * y r0, ?_, ?_⟩
      · constructor
        · have hu' : φ (ι ((t : E)⁻¹)) * φ (ι (t : E)) = 1 := by rw [← map_mul, mul_comm, hu, map_one]
          rw [map_mul, show φ (y r0) = φ (ι (t : E)) * s from e, ← mul_assoc, hu', one_mul]
          exact hs
        · have hu' : φ (σ' (ι ((t : E)⁻¹))) * φ (σ' (ι (t : E))) = 1 := by
            rw [← map_mul, ← map_mul, mul_comm, hu, map_one, map_one]
          have hv : valuation k (φ (σ' (ι ((t : E)⁻¹)))) = 1 := by
            have := congrArg (valuation k) hu'
            rw [map_mul, hq', mul_one, map_one] at this
            exact this
          rw [map_mul, map_mul]
          exact mul_mem ((hint _).2 hv.le) (h3 r0)
      · rw [← mul_assoc, hu, one_mul]

  have hU : (M.val.map (φ.comp σ'))ᵀ * h = 1 := by
    have h0 : Formalism.UG.cT σ' (M : Matrix (Fin m) (Fin m) _) * 1 * (M : Matrix (Fin m) (Fin m) _) = 1 := hM
    rw [Matrix.mul_one] at h0
    have := congrArg (fun X => X.map φ) h0
    simp only [Formalism.UG.cT] at this
    rw [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, Matrix.map_one _ (map_zero φ) (map_one φ)] at this
    rw [← hh]
    simpa [Matrix.transpose_map] using this
  have hh'h : h' * h = 1 := mul_eq_one_comm.mp hhh'
  have hσM : M.val.map (φ.comp σ') = h'ᵀ := by
    have : (M.val.map (φ.comp σ'))ᵀ = h' := by
      calc (M.val.map (φ.comp σ'))ᵀ = (M.val.map (φ.comp σ'))ᵀ * (h * h') := by rw [hhh', Matrix.mul_one]
        _ = h' := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
    rw [← this, Matrix.transpose_transpose]
  intro y
  rw [hchar y, hchar]
  have e1 : (fun j => φ (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j)) = h *ᵥ (fun j => φ (y j)) := by
    funext j; rw [RingHom.map_mulVec, hh]; rfl
  have e2 : (fun j => φ (σ' (((M : Matrix (Fin m) (Fin m) _) *ᵥ y) j))) = h'ᵀ *ᵥ (fun j => φ (σ' (y j))) := by
    funext j
    have := RingHom.map_mulVec (φ.comp σ') (M : Matrix (Fin m) (Fin m) _) y j
    rw [← hσM]
    exact this
  rw [e1, e2]
  exact and_congr (hA _) (hB _)
