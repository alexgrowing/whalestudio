import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNontrivialDerivativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerivativeZeroWhittakerKernelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquivStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicSmoothStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishingStatement

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem irrAdm : GlobalTheory.Published.IrreducibleAdmissibleGL := fun k _ _ _ _ n V _ _ π hs hi =>
  (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).1 (Fin n) V π hs hi

theorem twJ_congr {G G' V : Type} [Group G] [Group G'] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
    {π' : Representation ℂ G' V} {N : Subgroup G} {N' : Subgroup G'} {θ : N →* ℂˣ} {θ' : N' →* ℂˣ}
    (h : twKer π N θ = twKer π' N' θ') :
    Nontrivial (TwJacquet π N θ) ↔ Nontrivial (TwJacquet π' N' θ') := by
  rw [Submodule.Quotient.nontrivial_iff, Submodule.Quotient.nontrivial_iff, h]

theorem exists_highest (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hn : Nontrivial V)
    (hg : ¬ IsGenericFor ψ π) :
    ∃ n, 0 < n ∧ n < N ∧ Nontrivial (TwJacquet π (derUnip k N n) (derChar k ψ N n)) ∧
      ∀ m < n, Subsingleton (TwJacquet π (derUnip k N m) (derChar k ψ N m)) := by
  have h0 : ¬ Nontrivial (TwJacquet π (derUnip k N 0) (derChar k ψ N 0)) := fun h =>
    hg ((twJ_congr (GlobalTheory.T.derivative_zero_whittaker_kernel k ψ N V π)).1 h)
  rcases N with _ | m
  · exfalso
    refine hg ?_
    show Nontrivial (V ⧸ twKer π (unipB k (Fin 0)) (whitChar ψ 0))
    have hb : twKer π (unipB k (Fin 0)) (whitChar ψ 0) = ⊥ := by
      unfold twKer
      rw [Submodule.span_eq_bot]
      rintro w ⟨u, v, rfl⟩
      have hu : (u : GL (Fin 0) k) = 1 := Subsingleton.elim _ _
      have hu' : u = 1 := Subtype.ext hu
      subst hu'
      simp
    rw [hb]
    exact (Submodule.quotEquivOfEqBot ⊥ rfl).toEquiv.nontrivial
  have hex : ∃ n, n ≤ m ∧ Nontrivial (TwJacquet π (derUnip k (m + 1) n) (derChar k ψ (m + 1) n)) := by
    obtain ⟨n, hnm, h⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hc h1 m V (resM k π).ρ (isSmooth_comp hs _ continuous_subtype_val) hn
    exact ⟨n, hnm, (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ m n V π)).1 h⟩
  classical
  have hmin := fun (l : ℕ) (hl : l < Nat.find hex) => Nat.find_min hex hl
  obtain ⟨hle, hnt⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, Nat.pos_of_ne_zero fun e => h0 (e ▸ hnt), by omega, hnt, fun l hl => ?_⟩
  have := hmin l hl
  rw [not_and] at this
  exact not_nontrivial_iff_subsingleton.1 (this (by omega))

theorem isSmooth_iterPhi (ψ : AddChar k Circle) (n : ℕ) : ∀ (j : ℕ) (τ : MRep k (n + j)), IsSmooth τ.ρ →
    IsSmooth (iterPhi k ψ j τ).ρ
  | 0, _, h => h
  | j + 1, τ, h => isSmooth_iterPhi ψ n j (MRep.phiM k ψ τ) (GlobalTheory.T.smooth_phi_minus k ψ _ _ τ.ρ h)

theorem isSmooth_resM {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin (n + 1)) k) V}
    (h : IsSmooth π) : IsSmooth (resM k π).ρ := isSmooth_comp h _ continuous_subtype_val

theorem isSmooth_deriv (ψ : AddChar k Circle) {n : ℕ} (j : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin (n + j + 1)) k) V} (h : IsSmooth π) : IsSmooth (GlobalTheory.BZMir.deriv k ψ j π) :=
  GlobalTheory.T.smooth_psi_minus k _ _ _ (isSmooth_iterPhi ψ n j _ (isSmooth_resM h))

theorem iterPhi_derUnip (ψ : AddChar k Circle) (n₂ n' : ℕ) (hn : n₂ ≤ n') : ∀ (j : ℕ) (τ : MRep k (n' + j)),
    Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (derUnipM k n' n₂) (derCharM k ψ n' n₂) ≃ₗ[ℂ]
      TwJacquet τ.ρ (derUnipM k (n' + j) n₂) (derCharM k ψ (n' + j) n₂))
  | 0, _ => ⟨LinearEquiv.refl _ _⟩
  | j + 1, τ => by
    obtain ⟨e₁⟩ := iterPhi_derUnip ψ n₂ n' hn j (MRep.phiM k ψ τ)
    obtain ⟨e₂⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ (n' + j) n₂ (by omega) _ τ.ρ
    exact ⟨e₁.trans e₂⟩

theorem phi_vanish (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V) (hs : IsSmooth π)
    (hlow : ∀ m < n + 1, Subsingleton (TwJacquet π (derUnip k (n + 1 + j + 1) m) (derChar k ψ (n + 1 + j + 1) m))) :
    Subsingleton (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n)) := by
  by_contra hcon
  have hnt : Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n)) :=
    not_subsingleton_iff_nontrivial.1 hcon
  have hT := isSmooth_iterPhi ψ (n + 1) j (resM k π) (isSmooth_resM hs)
  obtain ⟨m, hm, h⟩ := GlobalTheory.T.exists_nontrivial_derivative k ψ hc h1 n _ (phiMinus k ψ (iterPhi k ψ j (resM k π)).ρ)
    (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hT) hnt
  obtain ⟨e₂⟩ := GlobalTheory.T.twisted_jacquet_phi_minus_equiv k ψ n m hm _ (iterPhi k ψ j (resM k π)).ρ
  obtain ⟨e₁⟩ := iterPhi_derUnip ψ m (n + 1) (by omega) j (resM k π)
  have h3 : Nontrivial (TwJacquet (resM k π).ρ (derUnipM k (n + 1 + j) m) (derCharM k ψ (n + 1 + j) m)) :=
    (e₂.trans e₁).symm.toEquiv.nontrivial
  have h4 := (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + 1 + j) m V π)).1 h3
  exact not_subsingleton_iff_nontrivial.2 h4 (hlow m (by omega))

theorem deriv_nontrivial (ψ : AddChar k Circle) (n j : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (h : Nontrivial (TwJacquet π (derUnip k (n + 1 + j + 1) (n + 1)) (derChar k ψ (n + 1 + j + 1) (n + 1)))) :
    Nontrivial (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1) := by
  obtain ⟨e⟩ := GlobalTheory.T.twisted_jacquet_iterated_phi_equiv k ψ (n + 1) j (resM k π)
  have h2 := (twJ_congr (GlobalTheory.T.restriction_mirabolic_twisted_kernel k ψ (n + 1 + j) (n + 1) V π)).2 h
  exact e.toEquiv.nontrivial

theorem detChar_zero {n : ℕ} (g : GL (Fin n) k) : ((detChar (Fin n) (absPow k ((0 : ℕ) : ℂ)) g : ℂˣ) : ℂ) = 1 := by
  have : absPow k ((0 : ℕ) : ℂ) = 1 := by
    rw [Nat.cast_zero, absPow_zero]
  rw [this]
  simp [detChar]

set_option maxHeartbeats 2000000 in

theorem pair_iter (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n : ℕ) : ∀ (j s : ℕ) (τ τ' : MRep k (n + 1 + j)),
    IsSmooth τ.ρ → IsSmooth τ'.ρ → ∀ B : τ.V →ₗ[ℂ] τ'.V →ₗ[ℂ] ℂ,
    (∀ (p : Mir k (n + 1 + j)) v v', B (τ.ρ p v) (τ'.ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v') →
    (∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0) →
    Subsingleton (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k (n + 1)) (mirChar k ψ n)) →
    ∃ B' : TwJacquet (iterPhi k ψ j τ).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ]
        TwJacquet (iterPhi k ψ⁻¹ j τ').ρ (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (derivM k ψ j τ g w) (derivM k ψ⁻¹ j τ' g w') =
        ((detChar (Fin (n + 1)) (absPow k ((s + j : ℕ) : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0)
  | 0, s, τ, τ', hs, hs', B, hB, hn, hv =>
    GlobalTheory.T.invariant_pairing_mirabolic_vanishing k ψ hc h1 n s τ.V τ'.V τ.ρ τ'.ρ hs hs' B hB hn hv
  | j + 1, s, τ, τ', hs, hs', B, hB, hn, hv => by
    obtain ⟨B₁, hB₁, hn₁⟩ := GlobalTheory.T.invariant_pairing_mirabolic_smooth k ψ hc h1 (n + 1 + j) s _ _ τ.ρ τ'.ρ hs hs' B hB hn
    obtain ⟨B₂, hB₂, hn₂⟩ := pair_iter ψ hc h1 n j (s + 1) (MRep.phiM k ψ τ) (MRep.phiM k ψ⁻¹ τ')
      (GlobalTheory.T.smooth_phi_minus k ψ _ _ _ hs) (GlobalTheory.T.smooth_phi_minus k ψ⁻¹ _ _ _ hs') B₁ hB₁ hn₁ hv
    refine ⟨B₂, fun g w w' => ?_, hn₂⟩
    have e : s + (j + 1) = s + 1 + j := by omega
    rw [e]
    exact hB₂ g w w'

set_option maxHeartbeats 2000000 in

theorem pair_deriv (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) (n j : ℕ) {V V' : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (π : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V)
    (π' : Representation ℂ (GL (Fin (n + 1 + j + 1)) k) V') (hs : IsSmooth π) (hs' : IsSmooth π')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (hB : ∀ g v v', B (π g v) (π' g v') = B v v') (hn : ∀ v, v ≠ 0 → ∃ v', B v v' ≠ 0)
    (hv : Subsingleton (TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) (mirChar k ψ n))) :
    ∃ B' : TwJacquet (iterPhi k ψ j (resM k π)).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ]
        TwJacquet (iterPhi k ψ⁻¹ j (resM k π')).ρ (MirUin k (n + 1)) 1 →ₗ[ℂ] ℂ,
      (∀ (g : GL (Fin (n + 1)) k) w w', B' (GlobalTheory.BZMir.deriv k ψ j π g w) (GlobalTheory.BZMir.deriv k ψ⁻¹ j π' g w') =
        ((detChar (Fin (n + 1)) (absPow k (j : ℂ)) g : ℂˣ) : ℂ) * B' w w') ∧
      (∀ w, w ≠ 0 → ∃ w', B' w w' ≠ 0) := by
  have hB0 : ∀ (p : Mir k (n + 1 + j)) v v', B ((resM k π).ρ p v) ((resM k π').ρ p v') =
      ((detChar (Fin (n + 1 + j + 1)) (absPow k ((0 : ℕ) : ℂ)) (p : GL (Fin (n + 1 + j + 1)) k) : ℂˣ) : ℂ) * B v v' := by
    intro p v v'
    rw [detChar_zero, one_mul]
    exact hB (p : GL (Fin (n + 1 + j + 1)) k) v v'
  obtain ⟨B', h2, h3⟩ := pair_iter ψ hc h1 n j 0 (resM k π) (resM k π') (isSmooth_resM hs) (isSmooth_resM hs') B
    hB0 hn hv
  refine ⟨B', fun g w w' => ?_, h3⟩
  have := h2 g w w'
  rwa [Nat.zero_add] at this

end Proofs
end GlobalTheory.CompanionTheory.BZCuspPair
