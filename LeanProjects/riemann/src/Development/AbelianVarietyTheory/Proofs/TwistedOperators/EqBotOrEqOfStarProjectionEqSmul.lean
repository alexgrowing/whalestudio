import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ExponentSeparation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfinitePartActDiscreteSeriesHomFactorwise
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.TrCopy

theorem eq_bot_or_eq_of_starProjection_eq_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {U U' : Submodule ℂ H} [U'.HasOrthogonalProjection] (hle : U' ≤ U) (a : ℂ)
    (hPU : ∀ v ∈ U, U'.starProjection v = a • v) {u0 : H} (hu0 : u0 ∈ U) (hne : u0 ≠ 0) : U' = ⊥ ∨ U' = U := by
  have haa : a * a = a := by
    have h1 : U'.starProjection (U'.starProjection u0) = U'.starProjection u0 :=
      (Submodule.starProjection_eq_self_iff (K := U')).2 (U'.starProjection_apply_mem _)
    rw [hPU _ hu0, map_smul, hPU _ hu0, smul_smul] at h1
    exact smul_left_injective ℂ hne h1
  rcases mul_eq_zero.1 (show a * (a - 1) = 0 by rw [mul_sub, haa, mul_one, sub_self]) with h0 | h1
  · left
    refine (Submodule.eq_bot_iff U').2 fun v hv => ?_
    rw [← (Submodule.starProjection_eq_self_iff (K := U')).2 hv, hPU v (hle hv), h0, zero_smul]
  · right
    refine le_antisymm hle fun v hv => ?_
    have hv' : U'.starProjection v = v := by rw [hPU v hv, sub_eq_zero.1 h1, one_smul]
    exact hv' ▸ U'.starProjection_apply_mem v

theorem eq_smul_on_closure_span {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : Set H) (P : H →L[ℂ] H) (a : ℂ)
    (hP : ∀ v ∈ (Submodule.span ℂ s).topologicalClosure, P v ∈ (Submodule.span ℂ s).topologicalClosure)
    (h : ∀ u ∈ s, ∀ u' ∈ s, ⟪u', P u - a • u⟫_ℂ = 0) :
    ∀ v ∈ (Submodule.span ℂ s).topologicalClosure, P v = a • v := by
  set A := Submodule.span ℂ s with hA
  let Q : H →L[ℂ] H := P - a • ContinuousLinearMap.id ℂ H
  have hQ : ∀ v, Q v = P v - a • v := fun v => rfl
  have hQA : ∀ v ∈ A, Q v ∈ Aᗮ := by
    intro v hv
    refine (Submodule.span_le (p := Aᗮ.comap (Q : H →ₗ[ℂ] H))).2 ?_ hv
    intro u hu
    show Q u ∈ Aᗮ
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hle : A ≤ (ℂ ∙ Q u)ᗮ := Submodule.span_le.2 (by
      intro u' hu'
      rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_symm, hQ]
      exact h u hu u' hu')
    exact inner_eq_zero_symm.1 ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 (hle hx))
  have hQcl : ∀ v ∈ A.topologicalClosure, Q v ∈ Aᗮ := fun v hv =>
    (Submodule.topologicalClosure_minimal (s := A) (t := Aᗮ.comap (Q : H →ₗ[ℂ] H)) (fun u hu => hQA u hu)
      ((Submodule.isClosed_orthogonal A).preimage Q.continuous)) hv
  have hcl : A.topologicalClosure ≤ Aᗮᗮ :=
    Submodule.topologicalClosure_minimal _ A.le_orthogonal_orthogonal (Submodule.isClosed_orthogonal _)
  intro v hv
  have h1 : Q v ∈ A.topologicalClosure := by
    rw [hQ]
    exact sub_mem (hP v hv) (Submodule.smul_mem _ _ hv)
  have h2 : ⟪Q v, Q v⟫_ℂ = 0 := Submodule.inner_right_of_mem_orthogonal (hQcl v hv) (hcl h1)
  rw [inner_self_eq_zero, hQ, sub_eq_zero] at h2
  exact h2

theorem isIrredSubrep_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : Type)
    [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : GA D V →* (H →L[ℂ] H)),
    IsUnitaryRep ρ → ∀ U : Submodule ℂ H, IsCopyFinDS σ M ρ U → IsIrredSubrep ρ U := by
  intro D V S M W _ _ σ hirr hadm H _ _ _ ρ hρ U hU
  classical
  obtain ⟨T, hT, hinj, rfl⟩ := hU
  have hTm := mem_homTensorPi.1 hT
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M

  have hgen : ∀ g w y, ρ g (T w y) ∈ Submodule.span ℂ {v | ∃ w y, v = T w y} := by
    intro g w y
    have e1 := GlobalTheory.TrAct.toInf_apply_homDS D V S M H ρ ⊤ (T (σ (toFin V g) w)) (hT.1 _) g y
    rw [hTm.2.1] at e1
    have e2 : ρ g (T w y) = ρ (toInf V g : GA D V) (ρ ((GfC V).subtype (toFin V g)) (T w y)) := by
      conv_lhs => rw [← toInf_mul_toFin g]
      rw [map_mul]
      rfl
    rw [e2, e1]
    exact Submodule.subset_span ⟨_, _, rfl⟩
  have hsub : IsSubrep ρ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
    isSubrep_topologicalClosure fun g v hv => Submodule.mem_comap.1
      ((Submodule.span_le (p := Submodule.comap (ρ g : H →ₗ[ℂ] H) _)).2
        (by rintro _ ⟨w, y, rfl⟩; exact hgen g w y) hv)

  obtain ⟨w0, hw0⟩ : ∃ w : W, w ≠ 0 := by
    by_contra h
    push Not at h
    have hne : (⊥ : Subrepresentation σ) ≠ ⊤ := bot_ne_top
    exact hne (by ext v; simp [h v])
  have hTw0 : T w0 ≠ 0 := fun h => hw0 (hinj (h.trans (map_zero T).symm))
  obtain ⟨y0, hy0⟩ : ∃ y, T w0 y ≠ 0 := by
    by_contra h
    push Not at h
    exact hTw0 (ContinuousMultilinearMap.ext h)
  have hu0 : T w0 y0 ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w0, y0, rfl⟩)
  refine ⟨hsub, fun h => hy0 ((Submodule.mem_bot ℂ).1 (h ▸ hu0)), fun U' hU'le hU' => ?_⟩
  haveI : CompleteSpace U' := hU'.1.completeSpace_coe

  have hPc : ∀ g v, U'.starProjection (ρ g v) = ρ g (U'.starProjection v) := by
    intro g v
    have h1 : ρ g (U'.starProjection v) ∈ U' := hU'.2 g _ (U'.starProjection_apply_mem v)
    have h2 : ρ g (v - U'.starProjection v) ∈ U'ᗮ :=
      (hU'.orthogonal hρ).2 g _ (Submodule.sub_starProjection_mem_orthogonal (K := U') v)
    have e : ρ g v = ρ g (U'.starProjection v) + ρ g (v - U'.starProjection v) := by
      rw [← map_add, add_sub_cancel]
    rw [e, map_add, (Submodule.starProjection_eq_self_iff (K := U')).2 h1,
      (Submodule.starProjection_apply_eq_zero_iff U').2 h2, add_zero]

  obtain ⟨T', hT'a⟩ : ∃ T' : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H, ∀ w y, T' w y = U'.starProjection (T w y) :=
    ⟨(ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H H U'.starProjection).toLinearMap ∘ₗ T,
      fun _ _ => rfl⟩
  have hΦ' : ∀ w, T' w ∈ homDS M ρ ⊤ := fun w => mem_homPi.2 ⟨fun _ => trivial, fun τ g y => by
    rw [hT'a, hT'a, (hT.1 w).2 τ g y, hPc]⟩

  let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  let C : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => bePi (T' v) (T w))
    (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
    (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
  have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
    bePi_self_pos hδ hρ (hT.1 x) ((map_ne_zero_iff T hinj).2 hx)
  have hBinv : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g v w => by
    change ⟪T (σ g w) _, T (σ g v) _⟫_ℂ = _
    rw [hTm.2.1, hTm.2.1, inner_map_map hρ]
    rfl
  have hCinv : ∀ g x y, C (σ g x) (σ g y) = C x y := fun g v w => by
    change ⟪T (σ g w) _, T' (σ g v) _⟫_ℂ = _
    rw [hT'a, hTm.2.1, hTm.2.1, hPc, inner_map_map hρ, ← hT'a]
    rfl
  obtain ⟨K, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨φ, hφ, hC⟩ := GlobalTheory.InvPairing.exists_intertwiner (GfC V) K hKo hKc W W σ σ hadm hadm.1 B C hBpos hBinv hCinv
  obtain ⟨c, hc⟩ := GlobalTheory.SchurAdm.schur_admissible (GfC V) K hKo hKc W σ hirr hadm φ hφ
  have key : ∀ x y, bePi (T' x) (T y) = conj c * bePi (T x) (T y) := fun x y => by
    have := hC x y
    rw [hc, LinearMap.smul_apply, LinearMap.id_apply, map_smulₛₗ, smul_eq_mul] at this
    exact this
  have hgen2 : ∀ u ∈ {v | ∃ w y, v = T w y}, ∀ u' ∈ {v | ∃ w y, v = T w y},
      ⟪u', U'.starProjection u - conj c • u⟫_ℂ = 0 := by
    rintro _ ⟨w, z, rfl⟩ _ ⟨w', z', rfl⟩
    rw [inner_sub_right, inner_smul_right, ← hT'a, inner_eq_bePi hδ hρ (hΦ' w) (hT.1 w'),
      inner_eq_bePi hδ hρ (hT.1 w) (hT.1 w'), key, mul_assoc, sub_self]
  exact eq_bot_or_eq_of_starProjection_eq_smul hU'le (conj c)
    (eq_smul_on_closure_span _ U'.starProjection (conj c) (fun v _ => hU'le (U'.starProjection_apply_mem v)) hgen2)
    hu0 hy0

end GlobalTheory.TrCopy
