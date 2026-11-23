import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowestKTypeMultiplicityOneLargeGaps
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIsoStatement

open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KFinDual

theorem decomp : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (Kset ε) ρ → (∀ S : Submodule ℂ H, FiniteDimensional ℂ S → S ≠ ⊥ → IsKStableOn ε ρ S → (∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S) → ∃ Λ, IsKTypeOf ε ρ Λ S) → ∀ v : H, IsKFin ε ρ v → v ∈ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
  classical
  intro n ε H _ _ ρ hU hirr
  have key : ∀ (d : ℕ) (F : Submodule ℂ H), FiniteDimensional ℂ F → Module.finrank ℂ F ≤ d →
      IsKStableOn ε ρ F → F ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} := by
    intro d
    induction d with
    | zero =>
      intro F hF hd _
      rw [Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hd)]
      exact bot_le
    | succ d ih =>
      intro F hF hd hFK
      by_cases hF0 : F = ⊥
      · rw [hF0]; exact bot_le
      have hex : ∃ m, ∃ S : Submodule ℂ H, S ≤ F ∧ S ≠ ⊥ ∧ IsKStableOn ε ρ S ∧ Module.finrank ℂ S = m :=
        ⟨_, F, le_rfl, hF0, hFK, rfl⟩
      obtain ⟨S, hSF, hS0, hSK, hSm⟩ := Nat.find_spec hex
      haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSF
      have hirrS : ∀ S' : Submodule ℂ H, S' ≤ S → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = S := by
        intro S' hS' hS'K
        by_cases h0 : S' = ⊥
        · exact Or.inl h0
        right
        haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
        have h1 := Nat.find_min' hex ⟨S', hS'.trans hSF, h0, hS'K, rfl⟩
        exact Submodule.eq_of_le_of_finrank_le hS' (hSm ▸ h1)
      obtain ⟨Λ, hΛ⟩ := hirr S inferInstance hS0 hSK hirrS
      have hSle : S ≤ ⨆ Λ : Fin n → ℝ, sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S} :=
        (le_sSup (s := {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) hΛ).trans (le_iSup (fun Λ => sSup {S : Submodule ℂ H | IsKTypeOf ε ρ Λ S}) Λ)
      have hF'K : IsKStableOn ε ρ (Sᗮ ⊓ F) := by
        intro k hk v hv
        refine ⟨?_, hFK k hk v hv.2⟩
        show (ρ k) v ∈ Sᗮ
        rw [Submodule.mem_orthogonal]
        intro u hu
        have h1 := GlobalTheory.Dec.FormF.inner_rep_K hU (Formalism.REAL.Kset_star ε hk) u v
        rw [star_star] at h1
        rw [← h1]
        exact (Submodule.mem_orthogonal S v).1 hv.1 _ (hSK _ (Formalism.REAL.Kset_star ε hk) u hu)
      haveI : FiniteDimensional ℂ (Sᗮ ⊓ F : Submodule ℂ H) := Submodule.finiteDimensional_of_le inf_le_right
      have hsup : S ⊔ Sᗮ ⊓ F = F := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hSF
      have hinf : S ⊓ (Sᗮ ⊓ F) = ⊥ :=
        eq_bot_iff.2 ((inf_le_inf_left S inf_le_left).trans (Submodule.inf_orthogonal_eq_bot S).le)
      have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (Sᗮ ⊓ F)
      rw [hsup, hinf, finrank_bot, add_zero] at hdim
      have hpos : 0 < Module.finrank ℂ S := Nat.pos_of_ne_zero fun h => hS0 (Submodule.finrank_eq_zero.1 h)
      have hle : F ≤ _ := hsup ▸ sup_le hSle (ih _ inferInstance (by omega) hF'K)
      exact hle
  intro v ⟨F, hF, hvF, hFK⟩
  exact key _ F hF le_rfl hFK hvF

variable {n : ℕ} {ε : Fin n → Bool}

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

def kIso (ε : Fin n → Bool) (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Λ : Fin n → ℝ) : Submodule ℂ H :=
  sSup {S | IsKTypeOf ε ρ Λ S}

theorem isURepOn_K (h : IsAdmRep ε ρ) : IsURepOn (Kset ε) ρ :=
  ⟨⟨h.1.1, fun a ha b hb => h.1.2 a (mem_UJset_of_mem_Kset ha) b (mem_UJset_of_mem_Kset hb)⟩, h.2.2.1,
    fun v => (h.2.1 v).mono fun _ hk => mem_UJset_of_mem_Kset hk⟩

theorem finiteDimensional_kIso (h : IsAdmRep ε ρ) (Λ : Fin n → ℝ) : FiniteDimensional ℂ (kIso ε ρ Λ) := by
  have e : {S : Submodule ℂ H | S ≤ ⊤ ∧ IsKTypeOf ε ρ Λ S} = {S | IsKTypeOf ε ρ Λ S} := by
    ext S; simp
  unfold kIso
  rw [← e]
  exact h.2.2.2 Λ

theorem kIso_le (Λ : Fin n → ℝ) : kIso ε ρ Λ ≤ kFinVec ε ρ :=
  sSup_le fun S hS v hv => ⟨S, hS.1, hv, hS.2.1⟩

theorem kIso_orth (hU : IsURepOn (Kset ε) ρ) {Λ μ : Fin n → ℝ} (hne : μ ≠ Λ) :
    ∀ x ∈ kIso ε ρ Λ, ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq]
  refine Submodule.isOrtho_sSup_left.2 fun S hS => Submodule.isOrtho_sSup_right.2 fun T hT => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (GlobalTheory.Jet.MultGap.orth_of_ne hU hS hT hne)

theorem finset_orth (hU : IsURepOn (Kset ε) ρ) (s : Finset (Fin n → ℝ)) {μ : Fin n → ℝ} (hμ : μ ∉ s) :
    ∀ x ∈ s.sup (kIso ε ρ), ∀ y ∈ kIso ε ρ μ, ⟪x, y⟫_ℂ = 0 := by
  rw [← Submodule.isOrtho_iff_inner_eq, Finset.sup_eq_iSup]
  refine Submodule.isOrtho_iSup_left.2 fun Λ => Submodule.isOrtho_iSup_left.2 fun hΛ => ?_
  exact (Submodule.isOrtho_iff_inner_eq).2 (kIso_orth hU (fun e => hμ (e ▸ hΛ)))

theorem exists_finset (hd : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ) (v : H) (hv : IsKFin ε ρ v) :
    ∃ s : Finset (Fin n → ℝ), v ∈ s.sup (kIso ε ρ) := by
  obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hd v hv)
  exact ⟨s, by rwa [Finset.sup_eq_iSup]⟩

theorem finset_sup_le (s : Finset (Fin n → ℝ)) : s.sup (kIso ε ρ) ≤ kFinVec ε ρ :=
  Finset.sup_le fun Λ _ => kIso_le Λ

end

section
variable {H V : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup V]
  [InnerProductSpace ℂ V] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)}

theorem map_kIso_le {T : H →ₗ[ℂ] V} (hT : ∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y))
    (Λ : Fin n → ℝ) : (kIso ε ρ Λ).map T ≤ kIso ε π Λ := by
  rw [Submodule.map_le_iff_le_comap]
  refine sSup_le fun S hS => ?_
  rw [← Submodule.map_le_iff_le_comap]
  haveI := hS.1
  set Q : S →L[ℂ] V := LinearMap.toContinuousLinearMap (T ∘ₗ S.subtype) with hQdef
  have hR : S.map T = LinearMap.range (Q : S →ₗ[ℂ] V) := by
    rw [hQdef, LinearMap.coe_toContinuousLinearMap, LinearMap.range_comp, Submodule.range_subtype]
  by_cases hQ : Q = 0
  · rw [hR, hQ]; simp
  · rw [hR]
    refine le_sSup (GlobalTheory.Dec.FormF.rangeType n ε Λ H ρ S V π Q hS (fun k hk x y hxy => ?_) hQ)
    change T y = π k (T x)
    rw [hxy]
    exact hT k hk x ⟨S, hS.1, x.2, hS.2.1⟩

theorem ext_types (hUρ : IsURepOn (Kset ε) ρ) (hUπ : IsURepOn (Kset ε) π)
    (hd : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ) {T : H →ₗ[ℂ] V}
    (hT : ∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y)) (s : Finset (Fin n → ℝ)) {a : H} {w : V}
    (ha : a ∈ s.sup (kIso ε ρ)) (hw : w ∈ s.sup (kIso ε π))
    (hs : ∀ Λ ∈ s, ∀ y ∈ kIso ε ρ Λ, ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) :
    ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ := by
  intro y hy
  refine Submodule.iSup_induction (kIso ε ρ) (motive := fun y => ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) (hd y hy)
    (fun Λ y hyΛ => ?_) (by simp) (fun y₁ y₂ h₁ h₂ => by simp [inner_add_right, h₁, h₂])
  by_cases hΛ : Λ ∈ s
  · exact hs Λ hΛ y hyΛ
  · rw [finset_orth hUρ s hΛ a ha y hyΛ,
      finset_orth hUπ s hΛ w hw (T y) (map_kIso_le hT Λ (Submodule.mem_map_of_mem hyΛ))]

end

theorem kFinite_riesz : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsAdmRep ε ρ → IsAdmRep ε π → ∀ T : H →ₗ[ℂ] V, (kFinVec ε ρ).map T = kFinVec ε π → (∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y)) → (∀ a : H, IsKFin ε ρ a → (∀ y, IsKFin ε ρ y → T y = 0 → ⟪a, y⟫_ℂ = 0) → ∃ w, IsKFin ε π w ∧ ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) ∧ ∀ w : V, IsKFin ε π w → ∃ a, IsKFin ε ρ a ∧ ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ := by
  intro n ε H _ _ _ ρ V _ _ _ π hρ hπ T hmap hT
  have hUρ := isURepOn_K hρ
  have hUπ := isURepOn_K hπ
  have hdρ : ∀ v, IsKFin ε ρ v → v ∈ ⨆ Λ, kIso ε ρ Λ :=
    decomp n ε H ρ hUρ (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H ρ hρ.1 hρ.2.1 hρ.2.2.1).1
  have hdπ : ∀ v, IsKFin ε π v → v ∈ ⨆ Λ, kIso ε π Λ :=
    decomp n ε V π hUπ (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε V π hπ.1 hπ.2.1 hπ.2.2.1).1
  haveI : ∀ Λ, FiniteDimensional ℂ (kIso ε ρ Λ) := finiteDimensional_kIso hρ
  haveI : ∀ Λ, FiniteDimensional ℂ (kIso ε π Λ) := finiteDimensional_kIso hπ
  refine ⟨fun a ha hker => ?_, fun w hw => ?_⟩
  · obtain ⟨s, hs⟩ := exists_finset hdρ a ha
    set U := s.sup (kIso ε π) with hUdef
    let Y : Submodule ℂ H := U.comap T ⊓ kFinVec ε ρ
    let T' : Y →ₗ[ℂ] U := (T ∘ₗ Y.subtype).codRestrict U (fun y => y.2.1)
    have hsurj : LinearMap.range T' = ⊤ := by
      rw [eq_top_iff]
      rintro u -
      have hu : (u : V) ∈ kFinVec ε π := finset_sup_le s u.2
      rw [← hmap] at hu
      obtain ⟨y, hy, hyu⟩ := hu
      exact ⟨⟨y, ⟨show T y ∈ U from hyu ▸ u.2, hy⟩⟩, Subtype.ext hyu⟩
    obtain ⟨r, hr⟩ := LinearMap.exists_rightInverse_of_surjective T' hsurj
    let φ : Y →ₗ[ℂ] ℂ := (innerₛₗ ℂ a) ∘ₗ Y.subtype
    let g : U →ₗ[ℂ] ℂ := φ ∘ₗ r
    have hg : ∀ y : Y, g (T' y) = φ y := by
      intro y
      have h1 : T' (r (T' y)) = T' y := by rw [← LinearMap.comp_apply, hr, LinearMap.id_apply]
      have h2 : T ((r (T' y) : H) - y) = 0 := by
        have := congrArg Subtype.val h1
        rw [map_sub, sub_eq_zero]
        exact this
      have h3 := hker ((r (T' y) : H) - y) ((kFinVec ε ρ).sub_mem (r (T' y)).2.2 y.2.2) h2
      simp only [g, φ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply]
      rw [inner_sub_right, sub_eq_zero] at h3
      exact h3
    let w : U := (InnerProductSpace.toDual ℂ U).symm (LinearMap.toContinuousLinearMap g)
    refine ⟨w, finset_sup_le s w.2, ext_types hUρ hUπ hdρ hT s hs w.2 ?_⟩
    intro Λ hΛ y hy
    have hyK : IsKFin ε ρ y := kIso_le Λ hy
    have hTy : T y ∈ U := Finset.le_sup (f := kIso ε π) hΛ (map_kIso_le hT Λ (Submodule.mem_map_of_mem hy))
    have h6 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := U) (x := ⟨T y, hTy⟩)
      (y := LinearMap.toContinuousLinearMap g)
    rw [Submodule.coe_inner] at h6
    have h4 := hg ⟨y, hTy, hyK⟩
    have h5 : T' ⟨y, hTy, hyK⟩ = ⟨T y, hTy⟩ := rfl
    rw [h5] at h4
    simp only [φ, LinearMap.comp_apply, Submodule.subtype_apply, innerₛₗ_apply_apply] at h4
    rw [h6, LinearMap.coe_toContinuousLinearMap', h4]
  · obtain ⟨s, hs⟩ := exists_finset hdπ w hw
    set A := s.sup (kIso ε ρ) with hAdef
    let g : A →ₗ[ℂ] ℂ := (innerₛₗ ℂ w) ∘ₗ T ∘ₗ A.subtype
    let a : A := (InnerProductSpace.toDual ℂ A).symm (LinearMap.toContinuousLinearMap g)
    refine ⟨a, finset_sup_le s a.2, ext_types hUρ hUπ hdρ hT s a.2 hs ?_⟩
    intro Λ hΛ y hy
    have hyA : y ∈ A := Finset.le_sup (f := kIso ε ρ) hΛ hy
    have h6 := InnerProductSpace.toDual_symm_apply (𝕜 := ℂ) (E := A) (x := ⟨y, hyA⟩)
      (y := LinearMap.toContinuousLinearMap g)
    rw [Submodule.coe_inner] at h6
    rw [h6]
    simp [g]

end GlobalTheory.KFinDual
