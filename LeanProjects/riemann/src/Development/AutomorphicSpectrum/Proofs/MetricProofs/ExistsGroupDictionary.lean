import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsLatticeEmbeddingStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LatticeStabilizerEquivAutomorphismsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameInversePropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitaryRepresentationStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanUnitarySurjectiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ArchimedeanActionOnLatticeVectorsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsMajorantOfPositiveFrameStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAdaptedFrameBisStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameDeterminesLatticeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameOfEquivalentStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormSqEqAdaptedFrameSumStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTranslatedRiemannLatticeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicAdaptedFrameOnBallStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChangeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusMulStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusTransitiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroContinuousStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExistsStatement

noncomputable section

open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem eqvBy_symm {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] {R R' : RiemLat E g Λ} (h : R.EqvBy R' 1) : R'.EqvBy R 1 := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k.symm, fun x => ?_⟩
  have := hk x
  simp only [LinearEquiv.coe_one, id_eq] at this ⊢
  rw [this, LinearEquiv.symm_apply_apply]

theorem zero_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by
    ext a b
    simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem star_mulVec_dot {m k : Type} [Fintype m] [Fintype k] (c : Matrix m k ℂ) (y : k → ℂ) :
    star (c *ᵥ y) ⬝ᵥ (c *ᵥ y) = star y ⬝ᵥ ((cᴴ * c) *ᵥ y) := by
  rw [star_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec (star y) cᴴ]

theorem groupDict_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ)
    (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (GroupDict F) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ H F
  classical
  obtain ⟨C⟩ := GlobalTheory.T.exists_lattice_embedding E Ψ j j' n g Λ H F
  have h0 : (0 : Fin n → ℂ) ∈ ballDom F.q := zero_mem_ballDom F.q
  have hform : ∀ t, (F.R t).form = F.form := F.form_eq
  obtain ⟨A0, hA0⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R 0) (hform 0) (F.sig 0 h0)
  have fct := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  obtain ⟨hmul, hone, huni, hcont⟩ := GlobalTheory.T.archimedean_unitary_representation E Ψ j j' n g Λ F C
  have hinv : ∀ (a : C.Arch) τ, C.tm a τ * C.tm a⁻¹ τ = 1 := by
    intro a τ
    rw [← hmul, mul_inv_cancel, hone]
  have hinv' : ∀ (a : C.Arch) τ, C.tm a⁻¹ τ * C.tm a τ = 1 := by
    intro a τ
    rw [← hmul, inv_mul_cancel, hone]
  let Pt : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ => (C.cinv (A0 τ) τ)ᴴ * C.cinv (A0 τ) τ
  obtain ⟨M, hMlen, hMstab⟩ := GlobalTheory.T.exists_majorant_of_positive_frame E Ψ j j' n g Λ F C Pt (fun τ => (fct τ).2.2.1) (fun τ => (fct τ).2.2.2.1)

  have hrot : ∀ a : C.Arch, ∃ R' : RiemLat E g Λ, R'.form = (F.R 0).form ∧ R'.B = (F.R 0).B ∧
      (∀ x, R'.P x = C.perExt (F.R 0) fun τ => C.tm a⁻¹ τ *ᵥ C.vec x τ) ∧
      C.IsAdapted R' (fun τ => C.tm a τ * A0 τ) := by
    intro a
    obtain ⟨R', h1, h2, h3, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R 0) (C.tm a) (C.tm a⁻¹) (hform 0) (hinv a)
      (huni a)
    exact ⟨R', h1, h2, h3, h4 A0 hA0⟩
  choose rot rform rB rP rad using hrot
  have rform' : ∀ a, (rot a).form = F.form := fun a => (rform a).trans (hform 0)
  have rsig : ∀ a, (rot a).HasSig F.σ j j' := by
    intro a
    have := F.sig 0 h0
    unfold RiemLat.HasSig at this ⊢
    rw [rB a]
    exact this
  have hu : ∀ a, ∃! t, t ∈ ballDom F.q ∧ (F.R t).EqvBy (rot a) 1 := fun a => F.univ (rot a) (rform' a) (rsig a)
  have hex := fun a => (hu a).exists
  choose π hπ using hex
  have huniq : ∀ a t, t ∈ ballDom F.q → (F.R t).EqvBy (rot a) 1 → π a = t := fun a t ht he =>
    (hu a).unique (hπ a) ⟨ht, he⟩
  have radπ : ∀ a, C.IsAdapted (F.R (π a)) (fun τ => C.tm a τ * A0 τ) := fun a =>
    GlobalTheory.T.adapted_frame_of_equivalent E Ψ j j' n g Λ F C (rot a) (F.R (π a)) _ (rad a) (eqvBy_symm (hπ a).2)
  have aUnit : ∀ (a : C.Arch) τ, (C.tm a τ * A0 τ)ᴴ * C.sgr τ * (C.tm a τ * A0 τ) = sgI j j' := fun a τ =>
    ((fct τ).2.2.2.2.1 _ _ (hinv a τ) (huni a τ)).1
  have aCinv : ∀ (a : C.Arch) τ, C.cinv (C.tm a τ * A0 τ) τ = C.cinv (A0 τ) τ * C.tm a⁻¹ τ := fun a τ =>
    ((fct τ).2.2.2.2.1 _ _ (hinv a τ) (huni a τ)).2.1
  let u : C.Arch → Ψ → Matrix (Sg j j') (Sg j j') ℂ := fun a τ => C.cinv (A0 τ) τ * (C.tm a τ * A0 τ)
  have uU : ∀ a τ, IsSgU (u a τ) := fun a τ => ((fct τ).2.2.2.2.1 _ _ (hinv a τ) (huni a τ)).2.2.1
  have uMul : ∀ a b τ, u (a * b) τ = u a τ * u b τ := by
    intro a b τ
    have h1 : A0 τ * C.cinv (A0 τ) τ = 1 := (fct τ).2.1
    show C.cinv (A0 τ) τ * (C.tm (a * b) τ * A0 τ) = C.cinv (A0 τ) τ * (C.tm a τ * A0 τ) * (C.cinv (A0 τ) τ * (C.tm b τ * A0 τ))
    rw [hmul]
    have e : C.cinv (A0 τ) τ * (C.tm a τ * A0 τ) * (C.cinv (A0 τ) τ * (C.tm b τ * A0 τ)) =
        C.cinv (A0 τ) τ * C.tm a τ * ((A0 τ * C.cinv (A0 τ) τ) * (C.tm b τ * A0 τ)) := by
      simp only [Matrix.mul_assoc]
    rw [e, h1, Matrix.one_mul]
    simp only [Matrix.mul_assoc]
  obtain ⟨Z, G₁, hZ, hG₁, hZeq, hpot⟩ := GlobalTheory.T.holomorphic_adapted_frame_on_ball E Ψ j j' n g Λ F C A0 hA0
  have hZπ : ∀ a, Z (π a) = moebBall F.q (u a) 0 := fun a => hZeq _ (hπ a).1 _ (radπ a)

  have hsurj : ∀ t ∈ ballDom F.q, ∃ a, π a = t := by
    intro t ht
    obtain ⟨At, hAt⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R t) (hform t) (F.sig t ht)
    obtain ⟨a, ha⟩ := GlobalTheory.T.archimedean_unitary_surjective E Ψ j j' n g Λ F C (fun τ => At τ * C.cinv (A0 τ) τ)
      (fun τ => (fct τ).2.2.2.2.2 _ (hAt.unit τ))
    have hAa : (fun τ => C.tm a τ * A0 τ) = At := by
      funext τ
      rw [ha τ, Matrix.mul_assoc, (fct τ).1, Matrix.mul_one]
    have h1 := rad a
    rw [hAa] at h1
    exact ⟨a, huniq a t ht (GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C (F.R t) (rot a) At (hform t) (rform' a) hAt h1)⟩

  let v : C.Arch → C.Arch → Ψ → Matrix (Sg j j') (Sg j j') ℂ := fun a b τ =>
    C.cinv (C.tm a τ * A0 τ) τ * (C.tm b τ * A0 τ)
  have vEq : ∀ a b τ, v a b τ = u (a⁻¹ * b) τ := by
    intro a b τ
    show C.cinv (C.tm a τ * A0 τ) τ * (C.tm b τ * A0 τ) = C.cinv (A0 τ) τ * (C.tm (a⁻¹ * b) τ * A0 τ)
    rw [aCinv, hmul]
    simp only [Matrix.mul_assoc]
  have hfib1 : ∀ a b, π a = π b ↔ ∀ τ, (v a b τ)ᴴ * v a b τ = 1 := by
    intro a b
    have key := GlobalTheory.T.adapted_frame_change_unitary E Ψ j j' n g Λ F C (F.R (π a)) _ (fun τ => C.tm b τ * A0 τ) (hform _) (radπ a) (aUnit b)
    rw [← show (C.IsAdapted (F.R (π a)) (fun τ => C.tm b τ * A0 τ)) ↔ π a = π b from ?_]
    · exact key
    constructor
    · intro h
      exact (huniq b (π a) (hπ a).1 (GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C (F.R (π a)) (rot b) _ (hform _) (rform' b) h (rad b))).symm
    · intro h
      rw [h]
      exact radπ b
  have hfib2 : ∀ a b, π a = π b ↔ a⁻¹ * b ∈ M.stab := by
    intro a b
    rw [hfib1, hMstab]
    refine forall_congr' fun τ => ?_
    rw [vEq]
    exact ((fct τ).2.2.2.2.1 _ _ (hinv _ τ) (huni _ τ)).2.2.2
  have hfib3 : ∀ a b, Z (π a) = Z (π b) → π a = π b := by
    intro a b h
    rw [hZπ, hZπ] at h
    rw [hfib1]
    have hb : (fun τ => u a τ * u (a⁻¹ * b) τ) = u b := by
      funext τ
      rw [← uMul, mul_inv_cancel_left]
    have := (GlobalTheory.T.ball_mobius_zero_eq_iff_unitary Ψ j j' n F.q (u a) (u (a⁻¹ * b)) (uU a) (uU _)).1 (by rw [hb]; exact h)
    intro τ
    rw [vEq]
    exact this τ
  have hbij : Set.BijOn Z (ballDom F.q) (ballDom F.q) := by
    have hmaps : Set.MapsTo Z (ballDom F.q) (ballDom F.q) := by
      intro t ht
      obtain ⟨a, rfl⟩ := hsurj t ht
      rw [hZπ]
      exact (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n F.q (u a) (uU a)).2.1 h0
    refine ⟨hmaps, ?_, ?_⟩
    · intro t ht t' ht' h
      obtain ⟨a, rfl⟩ := hsurj t ht
      obtain ⟨b, rfl⟩ := hsurj t' ht'
      exact hfib3 a b h
    · intro s hs
      obtain ⟨w, hw, hws⟩ := GlobalTheory.T.ball_mobius_transitive Ψ j j' n F.q s hs
      obtain ⟨a, ha⟩ := GlobalTheory.T.archimedean_unitary_surjective E Ψ j j' n g Λ F C (fun τ => (A0 τ * w τ) * C.cinv (A0 τ) τ) (fun τ => by
        refine (fct τ).2.2.2.2.2 _ ?_
        have hw' := hw τ
        unfold IsSgU at hw'
        rw [← hw', ← (hA0.unit τ)]
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc])
      have hua : u a = w := by
        funext τ
        show C.cinv (A0 τ) τ * (C.tm a τ * A0 τ) = w τ
        rw [ha τ, Matrix.mul_assoc (A0 τ * w τ), (fct τ).1, Matrix.mul_one, ← Matrix.mul_assoc, (fct τ).1, Matrix.one_mul]
      refine ⟨π a, (hπ a).1, ?_⟩
      rw [hZπ, hua, hws]
  obtain ⟨Y, hY, hYZ⟩ := GlobalTheory.T.ball_automorphism_inverse_exists Ψ j j' n F.q Z G₁ hZ hbij hG₁ hpot
  have hπY : ∀ a, π a = Y (moebBall F.q (u a) 0) := fun a => by
    rw [← hZπ, (hYZ _ (hπ a).1).2.2]
  have hucont : Continuous fun a : C.Arch => moebBall F.q (u a) 0 := by
    refine GlobalTheory.T.ball_mobius_zero_continuous Ψ j j' n F.q C.Arch u (fun τ => ?_) uU
    exact continuous_const.matrix_mul ((hcont τ).matrix_mul continuous_const)
  have hmem : ∀ a, moebBall F.q (u a) 0 ∈ ballDom F.q := fun a =>
    (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n F.q (u a) (uU a)).2.1 h0
  obtain ⟨α, hα⟩ := GlobalTheory.T.lattice_stabilizer_equiv_automorphisms E Ψ j j' n g Λ F C
  refine ⟨{ h := C.h, e := C.e, e_inj := C.e_inj, e_smul := C.e_smul, Dn := C.Dn, integral := C.integral, orth := C.orth,
            M := M, κ := 2 * C.c, κ_pos := by have := C.c_pos; positivity, π := π, π_cont := ?_, π_range := ?_,
            π_fibre := hfib2, len := ?_, α := α, α_eq := hα, α_act := ?_, act := ?_ }⟩
  · have : π = fun a => Y (moebBall F.q (u a) 0) := funext hπY
    rw [this]
    exact hY.continuousOn.comp_continuous hucont hmem
  · ext t
    constructor
    · rintro ⟨a, rfl⟩
      exact (hπ a).1
    · intro ht
      exact hsurj t ht
  · intro a x
    rw [GlobalTheory.T.normSq_eq_adapted_frame_sum E Ψ j j' n g Λ F C _ _ (hform _) (radπ a) x, hMlen a x]
    congr 1
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [aCinv, ← Matrix.mulVec_mulVec, star_mulVec_dot]
  · intro γ a
    obtain ⟨k₁, hk₁⟩ := (hπ a).2
    obtain ⟨k₂, hk₂⟩ := (hπ (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ * a)).2
    refine ⟨k₁.trans k₂.symm, fun x => ?_⟩
    have e1 : (rot (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ * a)).P ((α γ).1 x) = (rot a).P x := by
      rw [rP, rP]
      congr 1
      funext τ
      have hv : C.vec ((α γ).1 x) τ = C.tm (archEmbed C.h (Pi.basisFun E (Fin (j + j'))) γ) τ *ᵥ C.vec x τ := by
        rw [GlobalTheory.T.archimedean_action_on_lattice_vectors E Ψ j j' n g Λ F C]
        funext i
        show embOf (F.σ τ) (C.e ((α γ).1 x) i) = _
        rw [hα]
      rw [hv, Matrix.mulVec_mulVec, ← hmul, _root_.mul_inv_rev, inv_mul_cancel_right]
    have e2 := hk₂ ((α γ).1 x)
    have e3 := hk₁ x
    simp only [LinearEquiv.coe_one, id_eq] at e2 e3
    rw [e1, e3] at e2
    simp only [LinearEquiv.trans_apply]
    rw [e2, LinearEquiv.symm_apply_apply]
  · intro a₀
    obtain ⟨hm1, hm2, G₂, hG₂, hpot₂⟩ := GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n F.q (u a₀) (uU a₀)
    have hZm : Set.MapsTo Z (ballDom F.q) (ballDom F.q) := hbij.mapsTo
    have hYm : Set.MapsTo Y (ballDom F.q) (ballDom F.q) := fun t ht => (hYZ t ht).1
    have hAm : Set.MapsTo (fun t => Y (moebBall F.q (u a₀) (Z t))) (ballDom F.q) (ballDom F.q) := fun t ht =>
      hYm (hm2 (hZm ht))
    have hAd : DifferentiableOn ℂ (fun t => Y (moebBall F.q (u a₀) (Z t))) (ballDom F.q) :=
      hY.comp (hm1.comp hZ hZm) (hm2.comp hZm)
    refine ⟨fun t => Y (moebBall F.q (u a₀) (Z t)),
      fun t => G₁ t + G₂ (Z t) - G₁ (Y (moebBall F.q (u a₀) (Z t))), hAd,
      (hG₁.add (hG₂.comp hZ hZm)).sub (hG₁.comp hAd hAm), ?_, ?_⟩
    · intro a
      show π (a₀ * a) = Y (moebBall F.q (u a₀) (Z (π a)))
      rw [hπY (a₀ * a), hZπ a, ← GlobalTheory.T.ball_mobius_mul Ψ j j' n F.q (u a₀) (u a) (uU a₀) (uU a) 0 h0]
      congr 2
      funext τ
      exact uMul a₀ a τ
    · intro t ht
      have hs := hZm ht
      have hA := hAm ht
      have e1 := hpot _ hA
      have e2 : Z (Y (moebBall F.q (u a₀) (Z t))) = moebBall F.q (u a₀) (Z t) := (hYZ _ (hm2 hs)).2.1
      rw [e2, hpot₂ _ hs, hpot t ht] at e1
      simp only [Complex.add_re, Complex.sub_re]
      linarith

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
