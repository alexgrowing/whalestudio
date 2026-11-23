import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsSatFlagOne

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.FlagMeas

private theorem finrank_span_map_ringHom_eq_finrank {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ)
    (U : Submodule K (Fin n → K)) :
    Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U : Set (Fin n → K)))) =
      Module.finrank K U := by

  have hle : ∀ V : Submodule K (Fin n → K),
      Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K)))) ≤
        Module.finrank K V := by
    intro V
    let b := Module.finBasis K V
    have hsub : (fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K)) ⊆
        Submodule.span ℂ (Set.range fun k => fun l => φ ((b k : Fin n → K) l)) := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [SetLike.mem_coe]
      have hu' : u = ∑ k, b.repr ⟨u, hu⟩ k • (b k : Fin n → K) := by
        have h := congrArg Subtype.val (b.sum_repr ⟨u, hu⟩)
        simp only [Submodule.coe_sum, SetLike.val_smul] at h
        exact h.symm
      have hφ : (fun l => φ (u l)) = ∑ k, φ (b.repr ⟨u, hu⟩ k) • fun l => φ ((b k : Fin n → K) l) := by
        conv_lhs => rw [hu']
        ext l
        simp [Finset.sum_apply, map_sum, map_mul]
      rw [hφ]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    calc Module.finrank ℂ (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K))))
        ≤ Module.finrank ℂ (Submodule.span ℂ (Set.range fun k => fun l => φ ((b k : Fin n → K) l))) :=
          Submodule.finrank_mono (Submodule.span_le.2 hsub)
      _ ≤ Fintype.card (Fin (Module.finrank K V)) := finrank_range_le_card _
      _ = Module.finrank K V := Fintype.card_fin _
  have hsup : ∀ V V' : Submodule K (Fin n → K), V ⊔ V' = ⊤ →
      Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V : Set (Fin n → K))) ⊔
        Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (V' : Set (Fin n → K))) = ⊤ := by
    intro V V' h
    rw [eq_top_iff]
    intro z _
    have hz : z = ∑ i, z i • (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
      ext l
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hz]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have hsingle : (fun l => φ ((Pi.single i (1 : K) : Fin n → K) l)) = (Pi.single i (1 : ℂ) : Fin n → ℂ) := by
      ext l
      by_cases hl : l = i
      · subst hl; simp
      · simp [Pi.single_eq_of_ne hl]
    rw [← hsingle]
    have hmem : (Pi.single i (1 : K) : Fin n → K) ∈ V ⊔ V' := by rw [h]; exact Submodule.mem_top
    obtain ⟨u, hu, u', hu', hsum⟩ := Submodule.mem_sup.1 hmem
    rw [← hsum]
    have hadd : (fun l => φ ((u + u') l)) = (fun l => φ (u l)) + fun l => φ (u' l) := by
      ext l; simp
    rw [hadd]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨u, hu, rfl⟩) (Submodule.subset_span ⟨u', hu', rfl⟩)
  obtain ⟨U', hU'⟩ := Submodule.exists_isCompl U
  have h1 := hle U
  have h2 := hle U'
  have h3 : Module.finrank K U + Module.finrank K U' = n := by
    have := Submodule.finrank_add_eq_of_isCompl hU'
    simpa using this
  have h4 := Submodule.finrank_add_le_finrank_add_finrank
    (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U : Set (Fin n → K))))
    (Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (U' : Set (Fin n → K))))
  rw [hsup U U' hU'.sup_eq_top, finrank_top, Module.finrank_fin_fun] at h4
  omega

private theorem span_map_ringHom_span_eq_span_map {K : Type*} [Field K] {n : ℕ} (φ : K →+* ℂ) (X : Set (Fin n → K)) :
    Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' (Submodule.span K X : Set (Fin n → K))) =
      Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have h0 : (fun l => φ ((0 : Fin n → K) l)) = 0 := by ext; simp
      change (fun l => φ ((0 : Fin n → K) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h0]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have h : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext; simp
      change (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hx
      change (fun l => φ (y l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hy
      change (fun l => φ ((x + y) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      have h : (fun l => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext; simp
      change (fun l => φ (x l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X) at hx
      change (fun l => φ ((c • x) l)) ∈ Submodule.span ℂ ((fun y : Fin n → K => fun l => φ (y l)) '' X)
      rw [h]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem isIsoFlag_flagAt_of_isSatFlag :
    ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (a : ℕ) (j : Fin a → ℕ)
      (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)),
      IsSatFlag I Λ j S → ∀ v, IsIsoFlag (I.ε v) j (flagAt I S v) := by
  intro I Λ a j S hS v
  obtain ⟨h0, hmono, hrk, -, hiso⟩ := hS
  have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  have hPQ : I.P v * (I.P v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hinj : Function.Injective (Matrix.mulVecLin (I.P v)⁻¹) := by
    intro x y hxy
    have h := congrArg (fun z => I.P v *ᵥ z) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hPQ] using h

  have hspan : ∀ i, flagAt I S v i =
      (Submodule.span ℂ ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S i : Set _))).map
        (Matrix.mulVecLin (I.P v)⁻¹) := by
    intro i
    rw [Submodule.map_span, Set.image_image]
    rfl
  have hfr : ∀ i, Module.finrank ℂ (flagAt I S v i) = Formalism.HN.rkK (S i) := by
    intro i
    rw [hspan i, ← (Submodule.equivMapOfInjective _ hinj _).finrank_eq]
    show _ = Module.finrank I.E (Submodule.span I.E (S i : Set (Fin I.n → I.E)))
    rw [← span_map_ringHom_span_eq_span_map, finrank_span_map_ringHom_eq_finrank]

  have hstar : ∀ x : I.E, I.φ v (starRingEnd I.E x) = starRingEnd ℂ (I.φ v x) := fun x =>
    I.cm.cmUnram.2.1 (I.φ v) x
  have hJ : ((I.P v)⁻¹)ᴴ * (Formalism.REAL.Jm (I.ε v) * (I.P v)⁻¹) = I.J.map (I.φ v) := by
    rw [← I.P_spec v]
    calc ((I.P v)⁻¹)ᴴ * ((I.P v)ᴴ * I.J.map (I.φ v) * I.P v * (I.P v)⁻¹)
        = (I.P v * (I.P v)⁻¹)ᴴ * I.J.map (I.φ v) * (I.P v * (I.P v)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = I.J.map (I.φ v) := by rw [hPQ]; simp
  have hgen : ∀ x y : Fin I.n → ℂ, star ((I.P v)⁻¹ *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm (I.ε v) *ᵥ ((I.P v)⁻¹ *ᵥ y)) =
      star x ⬝ᵥ (I.J.map (I.φ v) *ᵥ y) := by
    intro x y
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec]
    simp only [Matrix.mulVec_mulVec, hJ]
  have hpair : ∀ s ∈ S (Fin.last a), ∀ t ∈ S (Fin.last a),
      star (fun l => I.φ v (s l)) ⬝ᵥ (I.J.map (I.φ v) *ᵥ fun l => I.φ v (t l)) = 0 := by
    intro s hs t ht
    have h := hiso s hs t ht
    have h' := congrArg (I.φ v) h
    rw [map_zero] at h'
    rw [← h']
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, map_sum, map_mul, hstar, Finset.mul_sum, mul_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Submodule.span ℂ _ = ⊥
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, hy, rfl⟩
    rw [h0] at hy
    have hy0 : y = 0 := by simpa using hy
    subst hy0
    ext l
    simp [Matrix.mulVec, dotProduct]
  · intro i k hik
    exact Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 (hmono hik)))
  · intro i
    rw [hfr, hfr]
    exact hrk i
  · intro x hx y hy
    rw [hspan] at hx hy
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨w', hw', rfl⟩ := Submodule.mem_map.1 hy
    rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, hgen]
    clear hx hy

    have hgen1 : ∀ g ∈ (fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S (Fin.last a) : Set (Fin I.n → I.E)),
        ∀ z ∈ Submodule.span ℂ
          ((fun y : Fin I.n → I.E => fun l => I.φ v (y l)) '' (S (Fin.last a) : Set (Fin I.n → I.E))),
          star g ⬝ᵥ (I.J.map (I.φ v) *ᵥ z) = 0 := by
      rintro _ ⟨s, hs, rfl⟩ z hz
      induction hz using Submodule.span_induction with
      | mem u hu =>
        obtain ⟨t, ht, rfl⟩ := hu
        exact hpair s hs t ht
      | zero => simp
      | add u u' _ _ hu hu' => rw [Matrix.mulVec_add, dotProduct_add, hu, hu', add_zero]
      | smul c u _ hu => rw [Matrix.mulVec_smul, dotProduct_smul, hu, smul_zero]
    induction hw using Submodule.span_induction with
    | mem u hu => exact hgen1 u hu w' hw'
    | zero => simp
    | add u u' _ _ hu hu' => rw [star_add, add_dotProduct, hu, hu', add_zero]
    | smul c u _ hu => rw [star_smul, smul_dotProduct, hu, smul_zero]

end GlobalTheory.FlagMeas
