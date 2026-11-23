import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.CentralResidueGroups.Across
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Z.Bc
open scoped Matrix
private theorem across_cc (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] : ∃ c : G ℚ Ω, IsConjEl c := by
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
  haveI : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  let τ : ℂ ≃ₐ[ℚ] ℂ := AlgEquiv.ofRingEquiv (f := starRingAut) fun x => by simp
  exact ⟨τ.restrictNormal Ω, algebraMap Ω ℂ, fun x => AlgEquiv.restrictNormal_commutes τ Ω x⟩
private theorem across_pair {F₀ F Ω k : Type} [Field F₀] [Field F] [Field Ω] [Algebra F₀ F] [Algebra F₀ Ω] [Algebra F Ω]
    [IsScalarTower F₀ F Ω] [Field k] {n : ℕ} (r : G F₀ Ω →* GL (Fin n) k) (θ : G F₀ Ω →* kˣ) (h : DualTw r θ)
    (c : G F₀ Ω) : ∃ P, IsPairing c (r.comp (resG F₀ F Ω)) (θ.comp (resG F₀ F Ω)) P := by
  obtain ⟨J, hJ⟩ := h
  refine ⟨J * r c⁻¹, fun s s' h => ?_⟩
  have h' : resG F₀ F Ω s' = c * resG F₀ F Ω s * c⁻¹ := h
  have e : r c⁻¹ * r (resG F₀ F Ω s') = r (resG F₀ F Ω s) * r c⁻¹ := by
    rw [h', ← map_mul, ← map_mul]; congr 1; group
  have e' : (r c⁻¹).val * (r (resG F₀ F Ω s')).val = (r (resG F₀ F Ω s)).val * (r c⁻¹).val := congrArg Units.val e
  have hp := hJ (resG F₀ F Ω s)
  simp only [MonoidHom.comp_apply]
  rw [Units.val_mul, ← Matrix.smul_mul, ← hp]
  simp only [Matrix.mul_assoc, e']
private theorem across_tf (L Ω : Type) [Field L] [Field Ω] [Algebra L Ω] : Module.IsTorsionFree L Ω :=
  DivisionSemiring.to_moduleIsTorsionFree
attribute [local instance] across_tf
private theorem across_up (L Ω : Type) [Field L] [CharZero L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω :=
  ⟨IsAlgClosure.isAlgClosed ℚ, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩
private theorem across_irr {Γ Δ Δ' k : Type} [Group Γ] [Group Δ] [Group Δ'] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k)
    (f : Δ →* Γ) (f' : Δ' →* Γ) (h : ∀ s, ∃ t, f' t = f s) (H : IsIrr (r.comp f)) : IsIrr (r.comp f') := by
  refine ⟨H.1, fun _ _ _ => trivial, fun W hW hI => H.2.2 W hW fun s v hv => ?_⟩
  obtain ⟨t, ht⟩ := h s
  have := hI t v hv
  rw [MonoidHom.comp_apply, ht] at this
  exact this
theorem UpperTheory.V.Z.Bc.across_alt :
    _root_.UpperTheory.V.Af.HypothesesH' → SolC → BiQuad → Across := by
  intro _ hS hB K K' Ω _ _ _ _ _ _ _ iA _ _ iT iT' iC hK hK' l _ ι n hn r θ hr hθ hd hirr haut
  haveI : CharZero Ω := algebraRat.charZero Ω
  obtain rfl : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨M, _, _, iM, _, _, _, _, _, _, _, hs, hs', hM, -⟩ := hB K K' Ω hK hK'
  haveI := across_up K Ω
  haveI := across_up K' Ω
  haveI := across_up M Ω
  obtain ⟨c, hc⟩ := across_cc Ω
  have he : (r.comp (resG ℚ K Ω)).comp (resG K M Ω) = (r.comp (resG ℚ K' Ω)).comp (resG K' M Ω) :=
    MonoidHom.ext fun s => rfl
  have hi : IsIrr ((r.comp (resG ℚ K Ω)).comp (resG K M Ω)) := by
    refine across_irr r _ ((resG ℚ K Ω).comp (resG K M Ω)) ?_ hirr
    rintro ⟨s, ⟨t, rfl⟩, h2⟩
    obtain ⟨u, rfl⟩ := (hM t).2 h2
    exact ⟨u, rfl⟩
  obtain ⟨P, hP⟩ := across_pair (F := K) r θ hd c
  obtain ⟨P', hP'⟩ := across_pair (F := K') r θ hd c
  have h1 := (hS ℚ K M Ω hs ⟨inferInstance, Or.inr ⟨hK, inferInstance⟩⟩ inferInstance iM l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K Ω)) hi hθ (UpperTheory.V.Ws.auSign θ) ⟨c, P, hc, hP⟩).1 haut
  rw [he] at h1 hi
  exact (hS ℚ K' M Ω hs' ⟨inferInstance, Or.inr ⟨hK', inferInstance⟩⟩ inferInstance iM l ι n hn _ θ
    (hr.comp (continuous_restrictScalarsHom ℚ K' Ω)) hi hθ (UpperTheory.V.Ws.auSign θ) ⟨c, P', hc, hP'⟩).2 h1
end
