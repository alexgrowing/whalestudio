import Development.WeilBound.CoreStatements.VolumeEquality.BallVolDefs
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameInversePropertiesStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsAdaptedFrameBisStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameDeterminesLatticeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameOfEquivalentStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AdaptedFrameChangeUnitaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsTranslatedRiemannLatticeStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicAdaptedFrameOnBallStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusMulStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusZeroEqIffUnitaryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusTransitiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusHolomorphicPotentialChangeStatement

noncomputable section

namespace SheetDecomposition

open NumberField Matrix MeasureTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.Dict GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas
open scoped ComplexOrder

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Type} [Fintype Ψ] {j j' n g : ℕ} {Λ : Type}
  [AddCommGroup Λ] [Module (𝓞 E) Λ] {F : UnivFam E Ψ j j' n g Λ} (C : LatEmb F)

theorem stdZ_perExt_vec (R : RiemLat E g Λ) (x : Λ) : C.perExt R (C.vec x) = R.P x := by
  let v : Λ →+ (Ψ → Fin (j + j') → ℂ) := AddMonoidHom.mk' C.vec fun a b => by
    funext τ i
    simp [LatEmb.vec]
  have h : ((C.perExt R).toAddMonoidHom.comp v).toIntLinearMap = R.P.toIntLinearMap := by
    refine C.lam.ext fun k => ?_
    have e : C.vec (C.lam k) = C.bas k := by
      funext τ i
      exact (C.bas_eq k τ i).symm
    show C.perExt R (C.vec (C.lam k)) = R.P (C.lam k)
    rw [e, LatEmb.perExt, Module.Basis.constr_basis]
  exact LinearMap.congr_fun h x

theorem stdZ_sgU (τ : Ψ) {A A' : Matrix (Fin (j + j')) (Sg j j') ℂ} (hA : Aᴴ * C.sgr τ * A = sgI j j')
    (hA' : A'ᴴ * C.sgr τ * A' = sgI j j') : IsSgU (C.cinv A τ * A') := by
  have h1 := (GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ A hA).2.1
  have e : A' = A * (C.cinv A τ * A') := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  unfold IsSgU
  generalize C.cinv A τ * A' = v at e ⊢
  rw [e] at hA'
  refine Eq.trans ?_ hA'
  rw [← hA]
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem stdZ_eqvBy_symm {R R' : RiemLat E g Λ} (h : R.EqvBy R' 1) : R'.EqvBy R 1 := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k.symm, fun x => ?_⟩
  have := hk x
  simp only [LinearEquiv.coe_one, id_eq] at this ⊢
  rw [this, LinearEquiv.symm_apply_apply]

omit [Fintype Ψ] in
theorem stdZ_zero_mem (q : Ψ × Fin j × Fin j' ≃ Fin n) : (0 : Fin n → ℂ) ∈ ballDom q := by
  intro τ
  have : ballMat q 0 τ = 0 := by
    ext a b
    simp [ballMat]
  rw [this]
  simpa using Matrix.PosDef.one

theorem stdZ_reach (A : Ψ → Matrix (Fin (j + j')) (Sg j j') ℂ) (hA : ∀ τ, (A τ)ᴴ * C.sgr τ * A τ = sgI j j') :
    ∃ t ∈ ballDom F.q, C.IsAdapted (F.R t) A := by
  have h0 := stdZ_zero_mem F.q
  obtain ⟨A0, hA0⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R 0) (F.form_eq 0) (F.sig 0 h0)
  have f0 := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  have f1 := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A τ) (hA τ)
  obtain ⟨R', h1, h2, -, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R 0) (fun τ => A τ * C.cinv (A0 τ) τ)
    (fun τ => A0 τ * C.cinv (A τ) τ) (F.form_eq 0) (fun τ => by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (C.cinv (A0 τ) τ), (f0 τ).1, Matrix.one_mul, (f1 τ).2.1])
    (fun τ => (f0 τ).2.2.2.2.2 _ (hA τ))
  have h5 := h4 A0 hA0
  have e : (fun τ => A τ * C.cinv (A0 τ) τ * A0 τ) = A := by
    funext τ
    rw [Matrix.mul_assoc, (f0 τ).1, Matrix.mul_one]
  rw [e] at h5
  have hs : R'.HasSig F.σ j j' := by
    have := F.sig 0 h0
    unfold RiemLat.HasSig at this ⊢
    rw [h2]
    exact this
  obtain ⟨t, ht, he⟩ := (F.univ R' (h1.trans (F.form_eq 0)) hs).exists
  exact ⟨t, ht, GlobalTheory.T.adapted_frame_of_equivalent E Ψ j j' n g Λ F C R' (F.R t) A h5 (stdZ_eqvBy_symm he)⟩

end

theorem stdZ : StdZ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F C
  have h0 := stdZ_zero_mem F.q
  obtain ⟨A0, hA0⟩ := GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R 0) (F.form_eq 0) (F.sig 0 h0)
  have f0 := fun τ => GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A0 τ) (hA0.unit τ)
  obtain ⟨Z, G, hZ, hG, hZeq, hpot⟩ := GlobalTheory.T.holomorphic_adapted_frame_on_ball E Ψ j j' n g Λ F C A0 hA0
  have had : ∀ t ∈ ballDom F.q, ∃ A, C.IsAdapted (F.R t) A := fun t ht =>
    GlobalTheory.T.exists_adapted_frame_bis E Ψ j j' n g Λ F C (F.R t) (F.form_eq t) (F.sig t ht)
  have hmaps : Set.MapsTo Z (ballDom F.q) (ballDom F.q) := by
    intro t ht
    obtain ⟨A, hA⟩ := had t ht
    rw [hZeq t ht A hA]
    exact (GlobalTheory.T.ball_mobius_holomorphic_potential_change Ψ j j' n F.q _ fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ)).2.1 h0
  have hinj : Set.InjOn Z (ballDom F.q) := by
    intro t ht t' ht' h
    obtain ⟨A, hA⟩ := had t ht
    obtain ⟨A', hA'⟩ := had t' ht'
    rw [hZeq t ht A hA, hZeq t' ht' A' hA'] at h
    have e : (fun τ => C.cinv (A0 τ) τ * A' τ) = fun τ => (C.cinv (A0 τ) τ * A τ) * (C.cinv (A τ) τ * A' τ) := by
      funext τ
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (A τ), (GlobalTheory.T.adapted_frame_inverse_properties E Ψ j j' n g Λ F C τ (A τ) (hA.unit τ)).2.1,
        Matrix.one_mul]
    rw [e] at h
    have h1 := (GlobalTheory.T.ball_mobius_zero_eq_iff_unitary Ψ j j' n F.q _ _ (fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ))
      (fun τ => stdZ_sgU C τ (hA.unit τ) (hA'.unit τ))).1 h
    have h2 := (GlobalTheory.T.adapted_frame_change_unitary E Ψ j j' n g Λ F C (F.R t) A A' (F.form_eq t) hA hA'.unit).2 h1
    have h3 := GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C (F.R t) (F.R t') A' (F.form_eq t) (F.form_eq t') h2 hA'
    exact (F.univ (F.R t') (F.form_eq _) (F.sig _ ht')).unique ⟨ht, h3⟩ ⟨ht', LinearEquiv.refl _ _, fun _ => rfl⟩
  have hsurj : Set.SurjOn Z (ballDom F.q) (ballDom F.q) := by
    intro s hs
    obtain ⟨w, hw, hws⟩ := GlobalTheory.T.ball_mobius_transitive Ψ j j' n F.q s hs
    obtain ⟨t, ht, hA⟩ := stdZ_reach C (fun τ => A0 τ * w τ) fun τ => by
      have hw' := hw τ
      unfold IsSgU at hw'
      rw [← hw']
      conv_rhs => rw [← hA0.unit τ]
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    refine ⟨t, ht, ?_⟩
    rw [hZeq t ht _ hA, ← hws]
    congr 1
    funext τ
    rw [← Matrix.mul_assoc, (f0 τ).1, Matrix.one_mul]
  refine ⟨A0, hA0.unit, Z, ⟨hmaps, hinj, hsurj⟩, fun S hS hSD => ⟨?_, ?_⟩, ?_⟩
  · exact hS.image_of_continuousOn_injOn (hZ.continuousOn.mono hSD) (hinj.mono hSD)
  · exact ballMeas_image F.q hZ (fun t ht => hmaps ht) hinj
      (fun t ht => ballDens_transform F.q hZ hG (fun t ht => hmaps ht) hpot ht) hS hSD
  intro γ δ hδ _ hu t ht t' ht'
  obtain ⟨A, hA⟩ := had t ht
  let a : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ =>
    (γ : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ))
  let ai : Ψ → Matrix (Fin (j + j')) (Fin (j + j')) ℂ := fun τ =>
    ((γ⁻¹ : GL (Fin (j + j')) E) : Matrix (Fin (j + j')) (Fin (j + j')) E).map (embOf (F.σ τ))
  have hai : ∀ τ, a τ * ai τ = 1 := fun τ => by
    simp only [a, ai]
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hia : ∀ τ, ai τ * a τ = 1 := fun τ => mul_eq_one_comm.1 (hai τ)
  obtain ⟨R', h1, -, h3, h4⟩ := GlobalTheory.T.exists_translated_riemann_lattice E Ψ j j' n g Λ F C (F.R t) a ai (F.form_eq t) hai hu
  have h5 := h4 A hA
  have hP : ∀ x, R'.P (δ x) = (F.R t).P x := fun x => by
    rw [h3, ← stdZ_perExt_vec C (F.R t) x]
    congr 1
    funext τ
    have hv : C.vec (δ x) τ = a τ *ᵥ C.vec x τ := by
      funext i
      show embOf (F.σ τ) (C.e (δ x) i) = _
      rw [hδ]
      exact RingHom.map_mulVec _ _ _ i
    rw [hv, Matrix.mulVec_mulVec, hia, Matrix.one_mulVec]
  have hm : moebBall F.q (rho (fun τ => embOf (F.σ τ)) A0 (fun τ => C.cinv (A0 τ) τ) γ) (Z t) =
      moebBall F.q (fun τ => C.cinv (A0 τ) τ * (a τ * A τ)) 0 := by
    have hU : ∀ τ, IsSgU (rho (fun τ => embOf (F.σ τ)) A0 (fun τ => C.cinv (A0 τ) τ) γ τ) := fun τ =>
      ((f0 τ).2.2.2.2.1 _ _ (hai τ) (hu τ)).2.2.1
    rw [hZeq t ht A hA, ← GlobalTheory.T.ball_mobius_mul Ψ j j' n F.q _ _ hU (fun τ => stdZ_sgU C τ (hA0.unit τ) (hA.unit τ)) 0 h0]
    congr 1
    funext τ
    show C.cinv (A0 τ) τ * (a τ * A0 τ) * (C.cinv (A0 τ) τ * A τ) = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (A0 τ), (f0 τ).2.1, Matrix.one_mul]
  rw [hm]
  constructor
  · rintro ⟨k, hk⟩
    refine hZeq t' ht' _ (GlobalTheory.T.adapted_frame_of_equivalent E Ψ j j' n g Λ F C R' (F.R t') _ h5 ⟨k, fun x => ?_⟩)
    obtain ⟨y, rfl⟩ := δ.surjective x
    exact (hk y).trans (congrArg k (hP y).symm)
  · intro h
    obtain ⟨t'', ht'', hA''⟩ := stdZ_reach C _ h5.unit
    obtain rfl : t'' = t' := hinj ht'' ht' ((hZeq t'' ht'' _ hA'').trans h.symm)
    obtain ⟨k, hk⟩ := GlobalTheory.T.adapted_frame_determines_lattice E Ψ j j' n g Λ F C R' (F.R t'') _ (h1.trans (F.form_eq t)) (F.form_eq _) h5 hA''
    exact ⟨k, fun x => (hk (δ x)).trans (congrArg k (hP x))⟩

end SheetDecomposition
