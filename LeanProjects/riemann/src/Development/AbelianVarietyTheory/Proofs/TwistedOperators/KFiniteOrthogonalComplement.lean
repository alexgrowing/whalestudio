import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MaxCompactIrreducibleHasHighestWeightAndIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqLowKOfLeLowKSub
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.KPerp

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem inner_map_map_of_norm {A : H →L[ℂ] H} (hA : ∀ v, ‖A v‖ = ‖v‖) (u v : H) :
    ⟪A u, A v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (A : H →ₗ[ℂ] H), norm_map' := hA }
  exact L.inner_map_map u v

theorem isKStableOn_orthogonal (hK : ∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) {T : Submodule ℂ H}
    [FiniteDimensional ℂ T] (hT : IsKStableOn ε ρ T) : IsKStableOn ε ρ Tᗮ := by
  intro k hk x hx
  rw [Submodule.mem_orthogonal]
  intro t ht
  let f : T →ₗ[ℂ] T := ((ρ k : H →ₗ[ℂ] H).restrict fun v hv => hT k hk v hv)
  have hinj : Function.Injective f := by
    intro a b hab
    have : ρ k ((a : H) - b) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 (congrArg Subtype.val hab)
    have h0 : ‖((a : H) - b)‖ = 0 := by rw [← hK k hk, this, norm_zero]
    exact Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h0))
  obtain ⟨t', ht'⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨t, ht⟩
  have ht'' : ρ k (t' : H) = t := congrArg Subtype.val ht'
  rw [← ht'', inner_map_map_of_norm (hK k hk)]
  exact (Submodule.mem_orthogonal _ _).1 hx t' t'.2

theorem le_of_forall_irred (hK : ∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) (M : Submodule ℂ H) :
    ∀ (d : ℕ) (F : Submodule ℂ H), FiniteDimensional ℂ F → Module.finrank ℂ F = d → IsKStableOn ε ρ F →
      (∀ T : Submodule ℂ H, T ≤ F → T ≠ ⊥ → FiniteDimensional ℂ T → IsKStableOn ε ρ T →
        (∀ S' : Submodule ℂ H, S' ≤ T → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = T) → T ≤ M) → F ≤ M := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro F hF hd hFK hM
  by_cases hF0 : F = ⊥
  · rw [hF0]; exact bot_le

  have hex : ∃ m, ∃ T : Submodule ℂ H, T ≤ F ∧ T ≠ ⊥ ∧ IsKStableOn ε ρ T ∧ Module.finrank ℂ T = m :=
    ⟨_, F, le_rfl, hF0, hFK, rfl⟩
  classical
  obtain ⟨T, hTF, hT0, hTK, hTm⟩ := Nat.find_spec hex
  haveI : FiniteDimensional ℂ T := Submodule.finiteDimensional_of_le hTF
  have hTirr : ∀ S' : Submodule ℂ H, S' ≤ T → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = T := by
    intro S' hS' hS'K
    by_cases h0 : S' = ⊥
    · exact Or.inl h0
    right
    haveI : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'
    have hle : Module.finrank ℂ T ≤ Module.finrank ℂ S' := by
      rw [hTm]; exact Nat.find_min' hex ⟨S', hS'.trans hTF, h0, hS'K, rfl⟩
    exact Submodule.eq_of_le_of_finrank_le hS' hle
  have hTM : T ≤ M := hM T hTF hT0 inferInstance hTK hTirr

  set F' := Tᗮ ⊓ F with hF'
  have hF'K : IsKStableOn ε ρ F' := fun k hk v hv =>
    ⟨isKStableOn_orthogonal hK hTK k hk v hv.1, hFK k hk v hv.2⟩
  haveI : FiniteDimensional ℂ F' := Submodule.finiteDimensional_of_le inf_le_right
  have hlt : F' < F := by
    refine lt_of_le_of_ne inf_le_right fun h => hT0 ?_
    rw [eq_bot_iff]
    intro x hx
    have hxF' : x ∈ F' := h ▸ hTF hx
    have := Submodule.inner_right_of_mem_orthogonal hx hxF'.1
    rw [Submodule.mem_bot]
    exact inner_self_eq_zero.1 this
  have hF'M : F' ≤ M :=
    ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hlt) F' inferInstance rfl hF'K
      fun T' hT' => hM T' (hT'.trans inf_le_right)
  have hsup : T ⊔ F' = F := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hTF
  rw [← hsup]
  exact sup_le hTM hF'M

theorem starProjection_mem (W : Submodule ℂ H) [W.HasOrthogonalProjection] (x : H) : W.starProjection x ∈ W := by
  rw [Submodule.starProjection_apply]; exact (W.orthogonalProjection x).2

theorem cdom_of_not_le_orthogonal (hK : ∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) {Λ μ : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε ρ Λ S) (hTK : IsKStableOn ε ρ T)
    (hTirr : ∀ S' : Submodule ℂ H, S' ≤ T → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = T) {v : H} (hvT : v ∈ T)
    (hv0 : v ≠ 0) (hvw : IsWtOn (Kset ε) ρ μ v) (hTS : ¬ T ≤ Sᗮ) : CDom ε μ Λ := by
  haveI : FiniteDimensional ℂ S := hS.1
  have hSo : IsKStableOn ε ρ Sᗮ := isKStableOn_orthogonal hK hS.2.1
  have hmeet : T ⊓ Sᗮ = ⊥ :=
    (hTirr _ inf_le_left fun k hk x hx => ⟨hTK k hk x hx.1, hSo k hk x hx.2⟩).resolve_right
      fun h => hTS (inf_eq_left.1 h)
  have hPv : S.starProjection v ≠ 0 := by
    intro h
    have hv : v ∈ T ⊓ Sᗮ := ⟨hvT, (Submodule.starProjection_apply_eq_zero_iff S).1 h⟩
    rw [hmeet, Submodule.mem_bot] at hv
    exact hv0 hv
  have comm : ∀ k ∈ Kset ε, ∀ x, S.starProjection (ρ k x) = ρ k (S.starProjection x) := by
    intro k hk x
    have hx : ρ k x = ρ k (S.starProjection x) + ρ k (x - S.starProjection x) := by
      rw [← map_add, add_sub_cancel]
    rw [hx, map_add, Submodule.starProjection_eq_self_iff.2 (hS.2.1 k hk _ (starProjection_mem S x)),
      (Submodule.starProjection_apply_eq_zero_iff S).2 (hSo k hk _ (Submodule.sub_starProjection_mem_orthogonal x)),
      add_zero]
  refine hS.2.2.2.2 μ _ (starProjection_mem S v) hPv ?_
  intro θ hθ
  rw [← comm _ hθ, hvw θ hθ, map_smul]

theorem inner_eq_zero_of_ne (hK : ∀ k ∈ Kset ε, ∀ v, ‖ρ k v‖ = ‖v‖) {Λ Λ' : Fin n → ℝ} {S T : Submodule ℂ H}
    (hS : IsKTypeOf ε ρ Λ S) (hT : IsKTypeOf ε ρ Λ' T) (hne : Λ ≠ Λ') :
    ∀ s ∈ S, ∀ t ∈ T, ⟪s, t⟫_ℂ = 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨s, hs, t, ht, hst⟩ := hcon
  have hTS : ¬ T ≤ Sᗮ := fun h => hst (Submodule.inner_right_of_mem_orthogonal hs (h ht))
  have hST : ¬ S ≤ Tᗮ := fun h => hst (Submodule.inner_left_of_mem_orthogonal ht (h hs))
  obtain ⟨w, hwT, hw0, hww⟩ := hT.2.2.2.1
  obtain ⟨u, huS, hu0, huw⟩ := hS.2.2.2.1
  have h1 : CDom ε Λ' Λ := cdom_of_not_le_orthogonal hK hS hT.2.1 hT.2.2.1 hwT hw0 hww hTS
  have h2 : CDom ε Λ Λ' := cdom_of_not_le_orthogonal hK hT hS.2.1 hS.2.2.1 huS hu0 huw hST
  exact hne (GlobalTheory.LowHW.cdom_antisymm h2 h1)

end GlobalTheory.KPerp

open GlobalTheory.KPerp in

theorem GlobalTheory.exists_kFin_orthogonal_of_ne_kFinVec :
    ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmRep ε ρ → ∀ Z : Submodule ℂ H, Z ≤ kFinVec ε ρ →
        IsKStableOn ε ρ Z → Z ≠ kFinVec ε ρ → ∃ a : H, a ≠ 0 ∧ IsKFin ε ρ a ∧ ∀ z ∈ Z, ⟪a, z⟫_ℂ = 0 := by
  intro n ε H _ _ _ ρ hρ Z hZ hZK hne
  obtain ⟨hC, hcont, hK, hadm⟩ := hρ
  have hirr := (GlobalTheory.T.maxCompact_irreducible_has_highest_weight_and_iso n ε H ρ hC hcont hK).1
  obtain ⟨y, hy, hyZ⟩ := SetLike.not_le_iff_exists.1 fun h : kFinVec ε ρ ≤ Z => hne (le_antisymm hZ h)
  obtain ⟨F, hF, hyF, hFK⟩ := hy
  have hex : ∃ T : Submodule ℂ H, T ≤ F ∧ T ≠ ⊥ ∧ FiniteDimensional ℂ T ∧ IsKStableOn ε ρ T ∧
      (∀ S' : Submodule ℂ H, S' ≤ T → IsKStableOn ε ρ S' → S' = ⊥ ∨ S' = T) ∧ ¬ T ≤ Z := by
    by_contra hcon
    push_neg at hcon
    exact hyZ (le_of_forall_irred hK Z _ F hF rfl hFK (fun T a b c d e => hcon T a b c d e) hyF)
  obtain ⟨S, -, hS0, hSfd, hSK, hSirr, hSZ⟩ := hex
  obtain ⟨Λ, hΛ⟩ := hirr S hSfd hS0 hSK hSirr
  set U : Submodule ℂ H := sSup {S | S ≤ ⊤ ∧ IsKTypeOf ε ρ Λ S} with hUdef
  haveI hUfd : FiniteDimensional ℂ U := hadm Λ
  have hSU : S ≤ U := le_sSup ⟨le_top, hΛ⟩
  have hUK : IsKStableOn ε ρ U := by
    intro k hk v hv
    have : U ≤ U.comap (ρ k : H →ₗ[ℂ] H) :=
      sSup_le fun S' hS' x hx => show ρ k x ∈ U from le_sSup hS' (hS'.2.2.1 k hk x hx)
    exact this hv
  obtain ⟨x, hxS, hxZ⟩ := SetLike.not_le_iff_exists.1 hSZ
  set W : Submodule ℂ H := Z ⊓ U with hWdef
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le inf_le_right
  have haW : x - W.starProjection x ∈ Wᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have haU : x - W.starProjection x ∈ U := U.sub_mem (hSU hxS) (starProjection_mem W x).2
  refine ⟨x - W.starProjection x, ?_, ⟨U, hUfd, haU, hUK⟩, ?_⟩
  · intro h
    have hx : x = W.starProjection x := sub_eq_zero.1 h
    exact hxZ (hx ▸ (starProjection_mem W x).1)
  · intro z hz
    obtain ⟨F', hF', hzF', hF'K⟩ := hZ hz
    have hGK : IsKStableOn ε ρ (F' ⊓ Z) := fun k hk v hv => ⟨hF'K k hk v hv.1, hZK k hk v hv.2⟩
    haveI : FiniteDimensional ℂ ↥(F' ⊓ Z) := Submodule.finiteDimensional_of_le inf_le_left
    have hle : F' ⊓ Z ≤ (ℂ ∙ (x - W.starProjection x))ᗮ := by
      refine le_of_forall_irred hK _ _ _ inferInstance rfl hGK ?_
      intro T hTG hT0 hTfd hTK hTirr t ht
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      obtain ⟨Λ', hΛ'⟩ := hirr T hTfd hT0 hTK hTirr
      by_cases hL : Λ' = Λ
      · subst hL
        have hTU : T ≤ U := le_sSup ⟨le_top, hΛ'⟩
        have htW : t ∈ W := ⟨(hTG ht).2, hTU ht⟩
        exact Submodule.inner_left_of_mem_orthogonal htW haW
      · have hUT : U ≤ Tᗮ := sSup_le fun S' hS' s hs =>
          (Submodule.mem_orthogonal T s).2 fun t' ht' => inner_eq_zero_of_ne hK hΛ' hS'.2 hL t' ht' s hs
        exact Submodule.inner_left_of_mem_orthogonal ht (hUT haU)
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle ⟨hzF', hz⟩)
