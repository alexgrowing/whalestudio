import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientExistence
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixConclIffOfIsDS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactFiniteApproxIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteApproximateIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section
namespace GlobalTheory.KAvgFinite

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Kt : Type}

def FinMult (s : Kt → (H →L[ℂ] H)) : Prop :=
  ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → (∀ k, ∀ w ∈ S, s k w ∈ S) →
    (∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', s k w ∈ S') → S' = ⊥ ∨ S' = S) →
    FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k, ∀ w ∈ S, T (s k w) = s k (T w)} :
      Submodule ℂ H)

theorem orth_stable {s : Kt → (H →L[ℂ] H)} (hs : ∀ k v, ‖s k v‖ = ‖v‖) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (hW : ∀ k, ∀ w ∈ W, s k w ∈ W) (k : Kt) : ∀ y ∈ Wᗮ, s k y ∈ Wᗮ := by
  intro y hy
  let L : W →ₗ[ℂ] W := (s k : H →ₗ[ℂ] H).restrict (hW k)
  have hinj : Function.Injective L := by
    intro a b hab
    have h1 : s k ((a : H) - b) = 0 := by
      have := congrArg Subtype.val hab
      simp only [L, LinearMap.restrict_apply] at this
      rw [map_sub]
      exact sub_eq_zero.2 this
    have h2 : ‖(a : H) - b‖ = 0 := by rw [← hs k, h1, norm_zero]
    exact Subtype.ext (sub_eq_zero.1 (norm_eq_zero.1 h2))
  have hsurj : Function.Surjective L := LinearMap.injective_iff_surjective.1 hinj
  let I : H →ₗᵢ[ℂ] H := ⟨(s k : H →ₗ[ℂ] H), fun v => hs k v⟩
  rw [Submodule.mem_orthogonal]
  intro w hw
  obtain ⟨w', hw'⟩ := hsurj ⟨w, hw⟩
  have e : w = s k w' := (congrArg Subtype.val hw').symm
  rw [e]
  have := I.inner_map_map (w' : H) y
  simp only [I, LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe] at this
  rw [this]
  exact (Submodule.mem_orthogonal _ _).1 hy _ w'.2

theorem starProjection_comm {s : Kt → (H →L[ℂ] H)} (hs : ∀ k v, ‖s k v‖ = ‖v‖) (W : Submodule ℂ H)
    [FiniteDimensional ℂ W] (hW : ∀ k, ∀ w ∈ W, s k w ∈ W) (k : Kt) (y : H) :
    W.starProjection (s k y) = s k (W.starProjection y) := by
  apply Submodule.eq_starProjection_of_mem_orthogonal (hW k _ (W.starProjection_apply_mem y))
  rw [← map_sub]
  exact orth_stable hs W hW k _ (W.sub_starProjection_mem_orthogonal y)

theorem finiteDimensional_iSup_range {s : Kt → (H →L[ℂ] H)} (hs : ∀ k v, ‖s k v‖ = ‖v‖) (hA : FinMult s) :
    ∀ (d : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E], Module.finrank ℂ E ≤ d →
    ∀ (ρ : Kt → Module.End ℂ E) (ι : Type) (T : ι → E →ₗ[ℂ] H), (∀ i k x, T i (ρ k x) = s k (T i x)) →
    FiniteDimensional ℂ (⨆ i, LinearMap.range (T i) : Submodule ℂ H) := by
  intro d
  induction d with
  | zero =>
    intro E _ _ _ hd ρ ι T hT
    have hsub : Subsingleton E := (Module.finrank_zero_iff (R := ℂ) (M := E)).1 (by omega)
    have : (⨆ i, LinearMap.range (T i)) = ⊥ := by
      refine iSup_eq_bot.2 fun i => ?_
      rw [LinearMap.range_eq_bot]
      ext x
      rw [Subsingleton.elim x 0]
      simp
    rw [this]
    infer_instance
  | succ d ih =>
    intro E _ _ _ hd ρ ι T hT
    by_cases hirr : ∀ E' : Submodule ℂ E, (∀ k, ∀ x ∈ E', ρ k x ∈ E') → E' = ⊥ ∨ E' = ⊤
    · by_cases h0 : ∀ i, T i = 0
      · have : (⨆ i, LinearMap.range (T i)) = ⊥ := by
          refine iSup_eq_bot.2 fun i => ?_
          rw [h0 i, LinearMap.range_zero]
        rw [this]
        infer_instance
      push_neg at h0
      obtain ⟨i0, hi0⟩ := h0
      have hker : LinearMap.ker (T i0) = ⊥ := by
        rcases hirr (LinearMap.ker (T i0)) (fun k x hx => by
          rw [LinearMap.mem_ker] at hx ⊢
          rw [hT, hx, map_zero]) with h | h
        · exact h
        · exact absurd (LinearMap.ker_eq_top.1 h) hi0
      set S := LinearMap.range (T i0) with hSdef
      have hSst : ∀ k, ∀ w ∈ S, s k w ∈ S := by
        rintro k _ ⟨x, rfl⟩
        exact ⟨ρ k x, hT i0 k x⟩
      have hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → (∀ k, ∀ w ∈ S', s k w ∈ S') → S' = ⊥ ∨ S' = S := by
        intro S' hle hst
        rcases hirr (S'.comap (T i0)) (fun k x hx => by
          show T i0 (ρ k x) ∈ S'
          rw [hT]
          exact hst k _ hx) with h | h
        · left
          rw [eq_bot_iff]
          intro y hy
          obtain ⟨x, rfl⟩ := hle hy
          have : x ∈ S'.comap (T i0) := hy
          rw [h, Submodule.mem_bot] at this
          rw [this, map_zero]
          exact Submodule.zero_mem _
        · right
          apply le_antisymm hle
          rintro _ ⟨x, rfl⟩
          have : x ∈ S'.comap (T i0) := by rw [h]; trivial
          exact this
      haveI hfin := hA S inferInstance hSst hSirr
      refine Submodule.finiteDimensional_of_le
        (S₂ := sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧ ∀ k, ∀ w ∈ S, T (s k w) = s k (T w)})
        (iSup_le fun i => ?_)
      let e := LinearEquiv.ofInjective (T i0) (LinearMap.ker_eq_bot.1 hker)
      obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
      let P : H →ₗ[ℂ] S := Submodule.linearProjOfIsCompl S C hC
      let B : H →ₗ[ℂ] H := T i ∘ₗ e.symm.toLinearMap ∘ₗ P
      have hB : ∀ x, B (T i0 x) = T i x := by
        intro x
        have h1 : (e x : H) = T i0 x := LinearEquiv.ofInjective_apply _ _
        have h2 : P (T i0 x) = e x := by
          rw [← h1]
          exact Submodule.linearProjOfIsCompl_apply_left hC (e x)
        simp only [B, LinearMap.comp_apply, LinearEquiv.coe_coe, h2, LinearEquiv.symm_apply_apply]
      have hR : LinearMap.range (T i) = S.map B := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          exact ⟨T i0 x, ⟨x, rfl⟩, hB x⟩
        · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
          exact ⟨x, (hB x).symm⟩
      apply le_sSup
      refine ⟨B, hR, ?_⟩
      rintro k _ ⟨x, rfl⟩
      rw [← hT i0 k x, hB, hB, hT]
    · push_neg at hirr
      obtain ⟨E', hE'st, hbot, htop⟩ := hirr
      have h1 : Module.finrank ℂ E' < Module.finrank ℂ E := Submodule.finrank_lt htop
      let ρ' : Kt → Module.End ℂ E' := fun k => (ρ k).restrict (hE'st k)
      let T' : ι → E' →ₗ[ℂ] H := fun i => T i ∘ₗ E'.subtype
      have hT' : ∀ i k x, T' i (ρ' k x) = s k (T' i x) := fun i k x => hT i k x
      haveI hW' := ih E' (by omega) ρ' ι T' hT'
      set W' := ⨆ i, LinearMap.range (T' i) with hW'def
      have hW'st : ∀ k, ∀ w ∈ W', s k w ∈ W' := by
        intro k w hw
        refine Submodule.iSup_induction _ (motive := fun w => s k w ∈ W') hw ?_ ?_ ?_
        · rintro i _ ⟨x, rfl⟩
          exact Submodule.mem_iSup_of_mem i ⟨ρ' k x, hT' i k x⟩
        · rw [map_zero]; exact Submodule.zero_mem _
        · intro a b ha hb
          rw [map_add]
          exact Submodule.add_mem _ ha hb
      let Q : H →ₗ[ℂ] H := LinearMap.id - (W'.starProjection : H →ₗ[ℂ] H)
      have hQ : ∀ y, Q y = y - W'.starProjection y := fun y => rfl
      have hQK : ∀ k y, Q (s k y) = s k (Q y) := by
        intro k y
        rw [hQ, hQ, map_sub, starProjection_comm hs W' hW'st]
      have hQW : ∀ w ∈ W', Q w = 0 := by
        intro w hw
        rw [hQ, Submodule.starProjection_eq_self_iff.2 hw, sub_self]
      have hle : ∀ i, E' ≤ LinearMap.ker (Q ∘ₗ T i) := by
        intro i x hx
        rw [LinearMap.mem_ker, LinearMap.comp_apply]
        exact hQW _ (Submodule.mem_iSup_of_mem i ⟨⟨x, hx⟩, rfl⟩)
      let ρ'' : Kt → Module.End ℂ (E ⧸ E') := fun k => E'.mapQ E' (ρ k) (fun x hx => hE'st k x hx)
      let T'' : ι → (E ⧸ E') →ₗ[ℂ] H := fun i => E'.liftQ (Q ∘ₗ T i) (hle i)
      have hT'' : ∀ i k x, T'' i (ρ'' k x) = s k (T'' i x) := by
        intro i k x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          simp only [ρ'', T'', Submodule.mapQ_apply, Submodule.liftQ_apply, LinearMap.comp_apply]
          rw [hT, hQK]
      have h2 : Module.finrank ℂ (E ⧸ E') < Module.finrank ℂ E := by
        have := Submodule.finrank_quotient_add_finrank E'
        have h3 : Module.finrank ℂ E' ≠ 0 := fun h => hbot (Submodule.finrank_eq_zero.1 h)
        omega
      haveI hW'' := ih (E ⧸ E') (by omega) ρ'' ι T'' hT''
      refine Submodule.finiteDimensional_of_le (S₂ := W' ⊔ ⨆ i, LinearMap.range (T'' i)) (iSup_le fun i => ?_)
      rintro _ ⟨x, rfl⟩
      have e : T i x = W'.starProjection (T i x) + Q (T i x) := by rw [hQ]; abel
      rw [e]
      refine Submodule.add_mem_sup (W'.starProjection_apply_mem _) ?_
      exact Submodule.mem_iSup_of_mem i ⟨Submodule.Quotient.mk x, by simp [T'']⟩

end GlobalTheory.KAvgFinite

namespace GlobalTheory.KAvgFinite

open GlobalTheory.SchurProjCompare (onMatrices onMatrices_umat isURepOn_iff)

variable {n : ℕ} {ε : Fin n → Bool} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem onMatrices_kg (π : UJ ε →* (U →L[ℂ] U)) (k : KG ε) : onMatrices (⇑π) (toMK k) = π k :=
  onMatrices_umat _ _

theorem isURepOn_onMatrices {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π) :
    IsURepOn (UJset ε) (onMatrices ⇑π) := by
  rw [isURepOn_iff]
  have e : (fun g : UJ ε => onMatrices (⇑π) (umat g)) = ⇑π := funext (onMatrices_umat _)
  rw [e]
  exact ⟨π.map_one, π.map_mul, hπ.norm_apply, hπ.continuous_apply⟩

theorem isIrredOn_onMatrices {π : UJ ε →* (U →L[ℂ] U)} (hI : IsTopIrreducible π) :
    IsIrredOn (UJset ε) (onMatrices ⇑π) := by
  intro S hS hst
  exact hI.2 S ⟨hS, fun g v hv => by
    have := hst (umat g) g.2 v hv
    rwa [onMatrices_umat] at this⟩

theorem finMult_of_isAdmOn {π : UJ ε →* (U →L[ℂ] U)} (h : GlobalTheory.LinRed.IsAdmOn (UJset ε) (onMatrices ⇑π)) :
    FinMult (fun k : KG ε => π (k : UJ ε)) := by
  intro S hS hst hirr
  have hK : ∀ S' : Submodule ℂ U, GlobalTheory.LinRed.IsKStable (UJset ε) (onMatrices ⇑π) S' ↔
      ∀ k : KG ε, ∀ w ∈ S', π k w ∈ S' := by
    intro S'
    unfold GlobalTheory.LinRed.IsKStable
    rw [GlobalTheory.HCUnitary.maxCpt_UJset, ← range_toMK]
    constructor
    · intro h k w hw
      rw [← onMatrices_kg]
      exact h _ ⟨k, rfl⟩ w hw
    · rintro h _ ⟨k, rfl⟩ w hw
      rw [onMatrices_kg]
      exact h k w hw
  haveI := h.2.2.2 S hS ((hK S).2 hst) (fun S' hle h' => hirr S' hle ((hK S').1 h'))
  refine Submodule.finiteDimensional_of_le (S₂ := sSup {S' | ∃ T : U →ₗ[ℂ] U, S' = S.map T ∧
    ∀ k ∈ GlobalTheory.LinRed.maxCpt (UJset ε), ∀ w ∈ S, T (onMatrices (⇑π) k w) = onMatrices (⇑π) k (T w)})
    (sSup_le_sSup ?_)
  rintro _ ⟨T, rfl, hT⟩
  refine ⟨T, rfl, ?_⟩
  rw [GlobalTheory.HCUnitary.maxCpt_UJset, ← range_toMK]
  rintro _ ⟨k, rfl⟩ w hw
  rw [onMatrices_kg]
  exact hT k w hw

end GlobalTheory.KAvgFinite

namespace GlobalTheory.KAvgFinite

open GlobalTheory.SchurProjCompare (onMatrices)

variable {n : ℕ} {ε : Fin n → Bool} {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem integrable_avg {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π) {ψ : KG ε → ℂ} (hψ : Continuous ψ)
    (u : U) : Integrable (fun k : KG ε => ψ k • π k u) (muK ε) :=
  (hψ.smul ((hπ.continuous_apply u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

variable [CompleteSpace U]

theorem exists_fix {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π) (S : Submodule ℂ U) [FiniteDimensional ℂ S]
    (hS : ∀ k ∈ KG ε, ∀ u ∈ S, π k u ∈ S) :
    ∃ e : KG ε → ℂ, GlobalTheory.TypeSum.KFinFun ε e ∧ ∀ s ∈ S, ∫ k, e k • π k s ∂(muK ε) = s := by
  let b := Module.finBasis ℂ S
  let m := Module.finrank ℂ S
  let w : Fin m → KG ε → S := fun i k => ⟨π k (b i), hS k k.2 _ (b i).2⟩
  have hwc : ∀ i, Continuous (w i) := fun i =>
    ((hπ.continuous_apply (b i : U)).comp continuous_subtype_val).subtype_mk _
  let F : Fin m × Fin m → KG ε → ℂ := fun p k => b.coord p.2 (w p.1 k)
  have hFc : ∀ p, Continuous (F p) := fun p =>
    (LinearMap.continuous_of_finiteDimensional (b.coord p.2)).comp (hwc p.1)
  have hV : (fun p => F p 1) ∈ GlobalTheory.KFinReproduce.intSpace F hFc := by
    have hcl : IsClosed ((GlobalTheory.KFinReproduce.intSpace F hFc : Submodule ℂ _) : Set (Fin m × Fin m → ℂ)) :=
      Submodule.closed_of_finiteDimensional _
    refine hcl.closure_subset (Metric.mem_closure_iff.2 fun δ hδ => ?_)
    obtain ⟨e, he, hb⟩ := GlobalTheory.KFinApprox.approx_identity n ε (Fin m × Fin m) F
      (continuous_prod_of_discrete_left.2 fun p => hFc p) Set.univ isCompact_univ δ hδ
    refine ⟨fun p => ∫ k, e k * F p k ∂(muK ε), ⟨e, he, fun p => rfl⟩, ?_⟩
    rw [dist_pi_lt_iff hδ]
    intro p
    rw [dist_eq_norm]
    exact hb p trivial
  obtain ⟨e, he, hej⟩ := hV
  have hec := GlobalTheory.KFinReproduce.continuous_of_kFinFun he
  refine ⟨e, he, ?_⟩
  have hexp : ∀ i (k : KG ε), π k (b i : U) = ∑ j, F (i, j) k • (b j : U) := by
    intro i k
    have h := b.sum_repr (w i k)
    have h2 : π k (b i : U) = ((w i k : S) : U) := rfl
    conv_lhs => rw [h2, ← h]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_smul]
    rfl
  have hbasis : ∀ i, ∫ k, e k • π k (b i : U) ∂(muK ε) = b i := by
    intro i
    calc ∫ k, e k • π k (b i : U) ∂(muK ε) = ∫ k, ∑ j, (e k * F (i, j) k) • (b j : U) ∂(muK ε) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only [hexp, Finset.smul_sum, smul_smul]
      _ = ∑ j, (∫ k, e k * F (i, j) k ∂(muK ε)) • (b j : U) := by
          rw [integral_finset_sum _ fun j _ =>
            ((GlobalTheory.KFinReproduce.integrable_mul hec (hFc (i, j))).smul_const _)]
          simp only [integral_smul_const]
      _ = ∑ j, F (i, j) 1 • (b j : U) := by simp only [hej]
      _ = b i := by
          rw [← hexp i 1]
          simp
  let A : U →ₗ[ℂ] U :=
    { toFun := fun v => ∫ k, e k • π k v ∂(muK ε)
      map_add' := fun x y => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_avg hπ hec x) (integrable_avg hπ hec y)
      map_smul' := fun c x => by
        simp only [map_smul, smul_comm (e _) c, RingHom.id_apply]
        exact integral_smul c _ }
  have hext : A ∘ₗ S.subtype = S.subtype := b.ext fun i => hbasis i
  intro s hs
  exact LinearMap.congr_fun hext ⟨s, hs⟩

theorem finiteDimensional_range {π : UJ ε →* (U →L[ℂ] U)} (hπ : IsUnitaryRep π)
    (hA : FinMult (fun k : KG ε => π (k : UJ ε))) {e : KG ε → ℂ} (he : GlobalTheory.TypeSum.KFinFun ε e) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => ∫ k, e k • π k u ∂(muK ε))) := by
  obtain ⟨F, hFf, heF, hFc, hFt⟩ := he
  let ρ : KG ε → Module.End ℂ F := fun k₀ =>
    { toFun := fun ψ => ⟨fun k => (ψ : KG ε → ℂ) (k₀⁻¹ * k), (hFt ψ ψ.2 k₀⁻¹).1⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let T : U → F →ₗ[ℂ] U := fun u =>
    { toFun := fun ψ => ∫ k, (ψ : KG ε → ℂ) k • π k u ∂(muK ε)
      map_add' := fun ψ χ => by
        simp only [Submodule.coe_add, Pi.add_apply, add_smul]
        exact integral_add (integrable_avg hπ (hFc ψ ψ.2) u) (integrable_avg hπ (hFc χ χ.2) u)
      map_smul' := fun c ψ => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  have hT : ∀ u k₀ ψ, T u (ρ k₀ ψ) = π k₀ (T u ψ) := by
    intro u k₀ ψ
    show ∫ k, (ψ : KG ε → ℂ) (k₀⁻¹ * k) • π k u ∂(muK ε) = π k₀ (∫ k, (ψ : KG ε → ℂ) k • π k u ∂(muK ε))
    rw [← ContinuousLinearMap.integral_comp_comm _ (integrable_avg hπ (hFc ψ ψ.2) u)]
    rw [← integral_mul_left_eq_self (fun k => (ψ : KG ε → ℂ) (k₀⁻¹ * k) • π k u) k₀]
    congr 1
    funext k
    simp only [inv_mul_cancel_left, map_smul, Subgroup.coe_mul, map_mul, ContinuousLinearMap.mul_apply]
  haveI := finiteDimensional_iSup_range (s := fun k : KG ε => π (k : UJ ε)) (fun k v => hπ.norm_apply k v) hA
    (Module.finrank ℂ F) F le_rfl ρ U T (fun u k ψ => hT u k ψ)
  refine Submodule.finiteDimensional_of_le (S₂ := ⨆ u, LinearMap.range (T u)) (Submodule.span_le.2 ?_)
  rintro _ ⟨u, rfl⟩
  exact Submodule.mem_iSup_of_mem u ⟨⟨e, heF⟩, rfl⟩

end GlobalTheory.KAvgFinite

open GlobalTheory.SchurProjCompare (onMatrices) in

theorem GlobalTheory.KAvgFinite.fix_and_finite_range : GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → ∀ S : Submodule ℂ U, FiniteDimensional ℂ S → (∀ k ∈ KG ε, ∀ u ∈ S, π k u ∈ S) → ∃ φ : KG ε → ℂ, Continuous φ ∧ (∀ s ∈ S, ∫ k, φ k • π k s ∂(muK ε) = s) ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun u : U => ∫ k, φ k • π k u ∂(muK ε))) := by
  intro hadm n ε U _ _ _ π hπ hI S hS hst
  have hA := GlobalTheory.KAvgFinite.finMult_of_isAdmOn (hadm n (UJset ε) (GlobalTheory.HCUnitary.isLinRed_UJset ε) U
    (onMatrices ⇑π) (GlobalTheory.KAvgFinite.isURepOn_onMatrices hπ) (GlobalTheory.KAvgFinite.isIrredOn_onMatrices hI))
  obtain ⟨e, he, hfix⟩ := GlobalTheory.KAvgFinite.exists_fix hπ S hst
  exact ⟨e, GlobalTheory.KFinReproduce.continuous_of_kFinFun he, hfix, GlobalTheory.KAvgFinite.finiteDimensional_range hπ hA he⟩
