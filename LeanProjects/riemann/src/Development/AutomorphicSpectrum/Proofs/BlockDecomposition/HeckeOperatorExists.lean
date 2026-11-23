import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.StandardFunctorsFiniteLength
import GroundTheory.AutomorphicForms.SmoothRep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.HeckeKm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mem_span_unif_pow_iff (m : ℕ) (a : 𝒪[k]) :
    a ∈ Ideal.span {Zls.unif k ^ m} ↔ (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (a : k) ∈ 𝒪[k] := by
  have hc : (((Zls.unifU k ^ m : kˣ)) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k) := by
    simp [Zls.unifU]
    rfl
  have hne : ((Zls.unif k ^ m : 𝒪[k]) : k) ≠ 0 := by
    rw [← hc]; exact Units.ne_zero _
  have hinv : (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) = ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, hc]
  rw [Ideal.mem_span_singleton', hinv]
  constructor
  · rintro ⟨b, rfl⟩
    have : ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * ((b * Zls.unif k ^ m : 𝒪[k]) : k) = (b : k) := by
      rw [MulMemClass.coe_mul]
      field_simp
    rw [this]
    exact b.2
  · intro h
    refine ⟨⟨_, h⟩, Subtype.ext ?_⟩
    rw [MulMemClass.coe_mul]
    change ((Zls.unif k ^ m : 𝒪[k]) : k)⁻¹ * (a : k) * _ = _
    field_simp

theorem mem_Km_iff {N m : ℕ} (g : GL (Fin N) k) :
    g ∈ Zls.Km k N m ↔ g ∈ KO k (Fin N) ∧
      ∀ i j, (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j ∈ 𝒪[k] := by
  have key : ∀ (u : GL (Fin N) 𝒪[k]) (i j : Fin N),
      ((Matrix.GeneralLinearGroup.map (n := Fin N) (algebraMap 𝒪[k] k) u).val - 1) i j =
        ((u.val i j - (1 : Matrix (Fin N) (Fin N) 𝒪[k]) i j : 𝒪[k]) : k) := by
    intro u i j
    by_cases h : i = j
    · subst h
      simp [Matrix.GeneralLinearGroup.map_apply]
      rfl
    · simp [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply_ne h]
      rfl
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨⟨u, rfl⟩, fun i j => ?_⟩
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq]
    have h := congrArg (fun x : GL (Fin N) (𝒪[k] ⧸ Ideal.span {Zls.unif k ^ m}) => x.val i j)
      (MonoidHom.mem_ker.1 hu)
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h
  · rintro ⟨⟨u, rfl⟩, h⟩
    refine ⟨u, MonoidHom.mem_ker.2 (Units.ext (Matrix.ext fun i j => ?_)), rfl⟩
    have h' := h i j
    rw [key, ← mem_span_unif_pow_iff, ← Ideal.Quotient.eq] at h'
    simpa [Matrix.GeneralLinearGroup.map_apply, Matrix.one_apply, apply_ite] using h'

theorem continuous_entry_Km (N : ℕ) (c : k) (i j : Fin N) :
    Continuous fun g : GL (Fin N) k => c * (g.val - 1) i j :=
  continuous_const.mul
    (((Units.continuous_val (M := Matrix (Fin N) (Fin N) k)).sub continuous_const).matrix_elem i j)

theorem coe_Km_eq (N m : ℕ) :
    (Zls.Km k N m : Set (GL (Fin N) k)) = (KO k (Fin N) : Set (GL (Fin N) k)) ∩
      ⋂ i, ⋂ j, (fun g : GL (Fin N) k => (((Zls.unifU k ^ m)⁻¹ : kˣ) : k) * (g.val - 1) i j) ⁻¹'
        (𝒪[k] : Set k) := by
  ext g
  simp only [SetLike.mem_coe, mem_Km_iff, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]

theorem isOpen_Km (N m : ℕ) : IsOpen (Zls.Km k N m : Set (GL (Fin N) k)) := by
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isOpen_KO.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
    (show IsOpen (𝒪[k] : Set k) from Valuation.isOpen_integer).preimage (continuous_entry_Km N _ i j))

theorem isCompact_Km (N m : ℕ) : IsCompact (Zls.Km k N m : Set (GL (Fin N) k)) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  rw [coe_Km_eq]
  exact GlobalTheory.SplitFlip.isCompact_KO.inter_right (isClosed_iInter fun i => isClosed_iInter fun j =>
    (show IsCompact (𝒪[k] : Set k) from IsNonarchimedeanLocalField.isCompact_closedBall k 1).isClosed.preimage
      (continuous_entry_Km N _ i j))

theorem totallyDisconnected_GL (N : ℕ) : TotallyDisconnectedSpace (GL (Fin N) k) := by
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin N) (Fin N) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin N → Fin N → k))
  exact ⟨(GlobalTheory.SplitFlip.isEmbedding_val_GL (k := k) (n := Fin N)).isTotallyDisconnected
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

theorem exists_isHeckeOp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π →
    ∀ (m : ℕ) (g : GL (Fin N) k), ∃ T : Module.End ℂ (fixed π (Zls.Km k N m)), Zls.IsHeckeOp π m g T := by
  intro k _ _ _ _ N V _ _ π hπ m g
  obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  haveI := totallyDisconnected_GL (k := k) N
  have hKc := isCompact_Km (k := k) N m
  have hKo := isOpen_Km (k := k) N m
  have hπ' : GroundTheory.Automorphic.IsSmooth π := fun v => hπ v
  have hfix : ∀ w : GroundTheory.Automorphic.fixedVectors π (Zls.Km k N m),
      (w : V) ∈ fixed π (Zls.Km k N m) := fun w h => by
    simpa using w.2 h h.2
  refine ⟨LinearMap.codRestrict (fixed π (Zls.Km k N m))
    ((Submodule.subtype _) ∘ₗ GroundTheory.Automorphic.fixedProj π hπ' hKc hKo ∘ₗ π g ∘ₗ
      (fixed π (Zls.Km k N m)).subtype) fun v => hfix _, ?_⟩
  intro v l hl
  have hs := GroundTheory.Automorphic.sub_fixedProj_mem hπ' hKc hKo (π g (v : V))
  have h0 := GroundTheory.Automorphic.coinvariantsKer_le_ker_of_invariant (ρ := π) (K := Zls.Km k N m) (f := l)
    (fun x hx w => LinearMap.congr_fun (hl x hx) w) hs
  rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.CompanionTheory.HeckeKm

end
