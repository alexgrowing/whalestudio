import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapGermEqGenMapGerm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeEigenVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagBasisChangeIntegralStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MinorRatioRegularOfInvertibleStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameChangeByUnitMatrixStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagChartGenericFieldStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameCoeffsRegularInChartStatement
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagBun

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun.Flags

theorem isExtOver_mk (Ω K E : Type) [Field Ω] [Field K] [Algebra Ω K] [AddCommGroup E] [Module Ω E] :
    IsExtOver (algebraMap Ω K) (TensorProduct.mk Ω K E 1).toAddMonoidHom := by
  refine ⟨fun a e => ?_, fun n b hb => ?_⟩
  · show (1 : K) ⊗ₜ[Ω] (a • e) = algebraMap Ω K a • ((1 : K) ⊗ₜ[Ω] e)
    rw [TensorProduct.tmul_smul, algebraMap_smul]
  · exact Module.Flat.linearIndependent_one_tmul hb

theorem pull_isFlagVB_genB : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (κ : Type) [Finite κ] (x : κ → Ω) (S : Type) [Fintype S] (r : S → ℕ) (V : S → Submodule Ω E) (L : S → Lat ξ E) (m n : S → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω r)) ⟶ X') (f : X' ⟶ X), CoordTie ℤ ξ x → (∀ q : X, genPt ξ ⤳ q) → (∀ s, (L s).IsVB (r s) (V s)) → (∀ s, IsTwistGen ξ x (L s) (m s) (φ s)) → (∀ s, LinearIndependent Ω (c s) ∧ Submodule.span Ω (Set.range (c s)) = V s) → CoordTie ℤ ξ' (flagCoord κ x φ c) → (∀ q : X', genPt ξ' ⤳ q) → Dominates ξ' ξ f (algebraMap Ω (GenField Ω r)) → (∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => algebraMap Ω (GenField Ω r) (x k)) c₁ p') → ∀ s, ((L s).pull ξ' f (TensorProduct.mk Ω (GenField Ω r) E 1).toAddMonoidHom).IsFlagVBOn Set.univ (genB c s) := by
  intro X Ω _ ξ E _ _ κ _ x S _ r V L m n φ c X' ξ' f hx hgen hVB hTw hc hx' hgen' hd hch s p' _
  classical
  obtain ⟨⟨c₁, J⟩, hcJ⟩ := hx'.cover p'
  obtain ⟨hx0, hchart, hmin⟩ := GlobalTheory.T.flag_chart_generic_field Ω E κ x S r n φ c X' ξ' p' c₁ J hcJ
  obtain ⟨hfp, hreg, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' _ ξ' f _ hd p'
  have hInC : InChart ξ x c₁ ⟨f p'.1, hfp⟩ := (hch p' c₁ hfp).2 hchart
  obtain ⟨U, hU, β₀, hspan, hfr⟩ := hVB s ⟨f p'.1, hfp⟩ trivial
  have hfr0 := hfr ⟨f p'.1, hfp⟩ trivial hU
  obtain ⟨B₀, hBreg, hAreg, hBA⟩ := GlobalTheory.T.frame_coeffs_regular_in_chart X Ω ξ E κ x (L s) (m s) (n s) (r s) (φ s) (hTw s) _ c₁ hInC β₀ hfr0
  have hxΩ : x c₁ ≠ 0 := hInC.1
  have hCex : ∀ l, ∃ C : Fin (r s) → Ω, c s l = ∑ a, C a • β₀ a := by
    intro l
    have : c s l ∈ Submodule.span Ω (Set.range β₀) := by
      rw [hspan, ← (hc s).2]
      exact Submodule.subset_span ⟨l, rfl⟩
    obtain ⟨C, hC⟩ := (Submodule.mem_span_range_iff_exists_fun Ω).1 this
    exact ⟨C, hC.symm⟩
  choose C hC using hCex
  set ι := algebraMap Ω (GenField Ω r) with hι
  let A₀ : Matrix (Fin (n s)) (Fin (r s)) Ω := Matrix.of (fun j a => φ s j (β₀ a) / x c₁ ^ m s)
  let A : Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) := A₀.map ι
  let B : Matrix (Fin (r s)) (Fin (n s)) (GenField Ω r) := B₀.map ι
  let Cm : Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := Matrix.of (fun a l => ι (C l a))
  let G : Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := Cm * genU Ω r s
  let a : GenField Ω r := ι (x c₁ ^ m s)
  have ha : a ≠ 0 := by
    simpa [a] using pow_ne_zero (m s) hx0
  have hF : flagMat φ c s = a • (A * G) := by
    have h1 : (Matrix.of (fun j l => ι (φ s j (c s l))) : Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r))
        = a • (A * Cm) := by
      ext j l
      simp only [Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, A, Cm, A₀, Matrix.map_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [hC l, map_sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [map_smul, smul_eq_mul, a, ← map_mul]
      congr 1
      field_simp
    rw [flagMat, h1, Matrix.smul_mul, Matrix.mul_assoc]
  have hBA' : B * A = 1 := by
    have := congrArg (fun M : Matrix (Fin (r s)) (Fin (r s)) Ω => M.map ι) hBA
    simpa [B, A, A₀, Matrix.map_mul] using this
  haveI : IsLocalRing (regAt ξ' p') := EigSplit.isLocalRing_regAt p'
  obtain ⟨P, hPreg, hP0, hPinv, hPflag⟩ := GlobalTheory.T.flag_basis_change_integral (GenField Ω r) (regAt ξ' p') (r s) (fun c i => G i c) (fun k =>
    GlobalTheory.T.minor_ratio_regular_of_invertible (GenField Ω r) (regAt ξ' p') (n s) (r s) A B G a k (J ⟨s, k⟩)
      (fun j l => hreg _ (hAreg j l)) (fun l j => hreg _ (hBreg l j)) hBA' ha
      (by have := (hmin ⟨s, k⟩).1; rwa [show flagMat φ c (⟨s, k⟩ : Σ s, Fin (r s)).1 = a • (A * G) from hF] at this)
      (by have := (hmin ⟨s, k⟩).2; rwa [show flagMat φ c (⟨s, k⟩ : Σ s, Fin (r s)).1 = a • (A * G) from hF] at this))
  have hext := isExtOver_mk Ω (GenField Ω r) E
  let β : Fin (r s) → TensorProduct Ω (GenField Ω r) E := fun a => TensorProduct.mk Ω (GenField Ω r) E 1 (β₀ a)
  let T : (Fin (r s) → GenField Ω r) →ₗ[GenField Ω r] TensorProduct Ω (GenField Ω r) E :=
    Fintype.linearCombination (GenField Ω r) β
  have hTapp : ∀ v, T v = ∑ a, v a • β a := fun v => by simp [T, Fintype.linearCombination_apply]
  have hmap : ∀ (w : Fin (r s) → Fin (r s) → GenField Ω r) (i : ℕ),
      flagStep (GenField Ω r) (fun k => T (w k)) i = (flagStep (GenField Ω r) w i).map T := by
    intro w i
    simp only [flagStep, Submodule.map_span, Set.image_image]
  have hgenB : genB c s = fun k => T (fun a => G a k) := by
    funext k
    rw [hTapp]
    simp only [genB, G, Matrix.mul_apply, Cm, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hC l, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    have h1 : TensorProduct.mk Ω (GenField Ω r) E 1 (C l b • β₀ b) = ι (C l b) • β b := hext.1 (C l b) (β₀ b)
    rw [h1, smul_smul, mul_comm]
  have hPfun : (fun k => ∑ a, P a k • β a) = fun k => T (fun a => P a k) := by
    funext k
    rw [hTapp]
  obtain ⟨U₁, hU₁, hq₁⟩ := EigSplit.exists_open_forall_mem_regAt p'
    (fun ab : Fin (r s) × Fin (r s) => P ab.1 ab.2) (fun ab => hPreg _ _)
  have hdetreg : P.det ∈ regAt ξ' p' := by
    rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hPreg _ _)
  obtain ⟨U₂, hU₂, hq₂⟩ := (regAt_unitAt_open X' _ ξ' p' P.det).2 ⟨hP0, hdetreg, hPinv⟩
  refine ⟨(f ⁻¹ᵁ U) ⊓ U₁ ⊓ U₂, ⟨⟨hU, hU₁⟩, hU₂⟩, fun k => ∑ a, P a k • β a, ?_, ?_⟩
  · intro i
    rw [hgenB, hPfun, hmap, hmap, hPflag]
  · rintro q - ⟨⟨hqU, hq1⟩, hq2⟩
    obtain ⟨hqf, -, -⟩ := RegAtDom.regAt_dominates X Ω ξ X' _ ξ' f _ hd q
    have hfq := hfr ⟨f q.1, hqf⟩ trivial hqU
    have hpull := FlagPull.pull_isFrameAt hd hext q hqf hfq
    exact GlobalTheory.T.frame_change_by_unit_matrix X' _ ξ' _ _ _ β q P hpull (fun a b => hq₁ q hq1 (a, b)) (hq₂ q hq2)

end GlobalTheory.CompanionTheory.Ar.FlagBun.Flags
