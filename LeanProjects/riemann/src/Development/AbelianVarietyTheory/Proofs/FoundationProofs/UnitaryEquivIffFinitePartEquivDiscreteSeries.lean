import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ApplyEqOfMemHomFinDS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntertwinerOfInvariantPairingAdmissible
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.AutMult

theorem isUnitEquiv_iff_nonempty_equiv_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (π' : GA D V →* (H' →L[ℂ] H')), IsIrrUnitary π' → ∀ (W' : Type) [AddCommGroup W'] [Module ℂ W'] (σ' : Representation ℂ (GfC V) W'), σ'.IsIrreducible → IsAdmissible σ' → IsCopyFinDS σ' M π' ⊤ → (IsUnitEquiv π π' ↔ Nonempty (σ.Equiv σ')) := by
  classical
  intro D V S M H _ _ π hπ W _ _ σ hσ hσa hc H' _ _ π' hπ' W' _ _ σ' hσ' hσa' hc'
  have := hπ.complete
  have := hπ'.complete
  obtain ⟨T, hT, hTi, hTd⟩ := hc
  obtain ⟨T', hT', hTi', hTd'⟩ := hc'
  have hTf : T ∈ homFinDS σ M π ⊤ := hT
  have hTf' : T' ∈ homFinDS σ' M π' ⊤ := hT'
  have hTm := mem_homTensorPi.1 hT
  have hTm' := mem_homTensorPi.1 hT'
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  haveI : σ.IsIrreducible := hσ
  haveI : σ'.IsIrreducible := hσ'
  haveI : Nontrivial W := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ.asModule
  haveI : Nontrivial W' := IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GfC V)) σ'.asModule
  constructor
  · rintro ⟨A, hA⟩
    have hAs : ∀ g x, A.symm (π' g x) = π g (A.symm x) := fun g x => by
      apply A.injective
      rw [hA, LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
    let Ac : H' →L[ℂ] H := A.symm.toLinearIsometry.toContinuousLinearMap
    let T'' : W' →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H :=
      (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H' H Ac).toLinearMap ∘ₗ T'
    have hT''v : ∀ w y, T'' w y = A.symm (T' w y) := fun _ _ => rfl
    have hT'' : ∀ w, T'' w ∈ homDS M π ⊤ := fun w => ⟨fun _ => trivial, fun τ g y => by
      rw [hT''v, hT''v, hTm'.2.2, hAs]⟩
    let B : W →ₗ[ℂ] W →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    let C : W →ₗ[ℂ] W' →ₛₗ[starRingEnd ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
      (fun v w => bePi (T v) (T'' w))
      (fun _ _ _ => by simp [bePi, inner_add_right]) (fun _ _ _ => by simp [bePi])
      (fun _ _ _ => by simp [bePi, inner_add_left]) (fun _ _ _ => by simp [bePi, inner_smul_left, mul_comm])
    have hBpos : ∀ x, x ≠ 0 → 0 < (B x x).re := fun x hx =>
      bePi_self_pos hδ hπ.unitary (hT.1 x) ((map_ne_zero_iff T hTi).2 hx)
    have hB : ∀ g x y, B (σ g x) (σ g y) = B x y := fun g x y => by
      change ⟪T (σ g y) _, T (σ g x) _⟫_ℂ = ⟪T y _, T x _⟫_ℂ
      rw [hTm.2.1, hTm.2.1, inner_map_map hπ.unitary]
    have hC : ∀ g x y, C (σ g x) (σ' g y) = C x y := fun g x y => by
      change ⟪T'' (σ' g y) _, T (σ g x) _⟫_ℂ = ⟪T'' y _, T x _⟫_ℂ
      rw [hT''v, hT''v, hTm'.2.1, hAs, hTm.2.1, inner_map_map hπ.unitary]
    obtain ⟨K₀, hKo, hKc⟩ := GlobalTheory.CuspDec.exists_compact_open V
    obtain ⟨φ, hφ, hCB⟩ := GlobalTheory.InvPairing.exists_intertwiner (GfC V) K₀ hKo hKc W W' σ σ' hσa hσa'.1 B C hBpos hB hC
    obtain ⟨w', hw'⟩ := exists_ne (0 : W')
    have h1 : T'' w' ≠ 0 := by
      intro h
      apply hw'
      apply hTi'
      rw [map_zero]
      ext y
      apply A.symm.injective
      rw [← hT''v, h]
      simp
    obtain ⟨y', hy'⟩ : ∃ y', T'' w' y' ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    obtain ⟨w, y, hwy⟩ : ∃ w y, ⟪T'' w' y', T w y⟫_ℂ ≠ 0 := by
      by_contra hn
      push_neg at hn
      apply hy'
      have hsub : Submodule.span ℂ {v | ∃ w y, v = T w y} ≤ (ℂ ∙ T'' w' y')ᗮ := Submodule.span_le.2 (by
        rintro _ ⟨w, y, rfl⟩
        exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (hn w y))
      have hcl := Submodule.topologicalClosure_minimal _ hsub (Submodule.isClosed_orthogonal _)
      rw [hTd] at hcl
      exact inner_self_eq_zero.1 (Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hcl Submodule.mem_top))
    have hC0 : C w w' ≠ 0 := fun h => hwy (by
      rw [inner_eq_bePi hδ hπ.unitary (hT.1 w) (hT'' w') y y']
      change C w w' * _ = 0
      rw [h, zero_mul])
    have hφ0 : φ w' ≠ 0 := fun h => hC0 (by rw [hCB, h, map_zero])
    let f : Representation.IntertwiningMap σ' σ := ⟨φ, fun g => LinearMap.ext fun y => hφ g y⟩
    rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | hf0
    · exact ⟨(Representation.IntertwiningMap.ofBijective f hb).symm⟩
    · exact absurd (congrArg (fun F : Representation.IntertwiningMap σ' σ => F w') hf0) hφ0
  · rintro ⟨e⟩
    let T₂ : W →ₗ[ℂ] ContinuousMultilinearMap ℂ M.H H' := T' ∘ₗ e.toLinearMap
    have hT₂ : T₂ ∈ homFinDS σ M π' ⊤ := by
      refine mem_homTensorPi.2 ⟨fun _ _ => trivial, fun g w y => ?_, fun τ g w y => hTm'.2.2 τ g (e w) y⟩
      change T' (e (σ g w)) y = _
      rw [show e (σ g w) = σ' g (e w) from Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g w]
      exact hTm'.2.1 g (e w) y
    obtain ⟨B, hB, hBv⟩ := GlobalTheory.TrExt.exists_homIn_extend D V S M W σ hσ hσa H π hπ.unitary T hTf hTi hTd H' π'
      hπ'.unitary ⊤ isClosed_univ T₂ hT₂
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    have h1 : T' (e w) ≠ 0 := fun h => hw (e.injective (hTi' (h.trans (map_zero T').symm) |>.trans (map_zero e).symm))
    obtain ⟨y, hy⟩ : ∃ y, T' (e w) y ≠ 0 := by
      by_contra hn
      push_neg at hn
      exact h1 (ContinuousMultilinearMap.ext hn)
    have hB0 : B ≠ 0 := fun h => hy (by rw [← show B (T w y) = T' (e w) y from hBv w y, h]; rfl)
    have hm : multIn π π' ⊤ ≠ 0 := by
      intro h0
      rw [multIn, Submodule.rank_eq_zero] at h0
      exact hB0 (by simpa [h0] using hB)
    obtain ⟨f, hf⟩ := uEquiv_of_multIn_ne_zero hπ hπ' hm
    exact ⟨f, hf⟩

end GlobalTheory.AutMult
