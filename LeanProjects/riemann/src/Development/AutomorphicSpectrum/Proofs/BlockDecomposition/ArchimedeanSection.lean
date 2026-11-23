import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRealCoords
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousBiadditiveBounded
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnRingInverseOfIsOpenEmbeddingUnits
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyReal
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SecInf

theorem exists_quadratic_section {N : ℕ} (q : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ))
    (h1 : ∀ u u' v, q (u + u') v = q u v + q u' v) (h2 : ∀ u v v', q u (v + v') = q u v + q u v')
    (hc : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => q p.1 p.2)) (a : Fin N → ℝ) :
    ∃ (T : Set (Fin N → ℝ)) (ψ : (Fin N → ℝ) → (Fin N → ℝ)), IsOpen T ∧ a ∈ T ∧ ContinuousOn ψ T ∧
      ∀ s ∈ T, a + ψ s + q (ψ s) (ψ s) = s := by
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.CompanionTheory.Arch.continuous_biadditive_bounded N N N q h1 h2 hc
  have hz : q 0 0 = 0 := by
    have := h1 0 0 0
    simpa using this
  set Φ : (Fin N → ℝ) → (Fin N → ℝ) := fun y => a + y + q y y with hΦ
  have hd : HasStrictFDerivAt Φ
      ((ContinuousLinearEquiv.refl ℝ (Fin N → ℝ) : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) :
        (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) 0 := by
    rw [hasStrictFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro ε hε
    have hu : Filter.Tendsto (fun p : (Fin N → ℝ) × (Fin N → ℝ) => C * (‖p.1‖ + ‖p.2‖))
        (𝓝 ((0 : Fin N → ℝ), (0 : Fin N → ℝ))) (𝓝 0) := by
      have hcont : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => C * (‖p.1‖ + ‖p.2‖)) := by
        fun_prop
      simpa using hcont.tendsto ((0 : Fin N → ℝ), (0 : Fin N → ℝ))
    filter_upwards [hu.eventually (ge_mem_nhds hε)] with p hp
    have hexp : q p.1 p.1 - q p.2 p.2 = q (p.1 - p.2) p.1 + q p.2 (p.1 - p.2) := by
      have e1 : q p.1 p.1 = q (p.1 - p.2) p.1 + q p.2 p.1 := by
        rw [← h1, sub_add_cancel]
      have e2 : q p.2 p.1 = q p.2 (p.1 - p.2) + q p.2 p.2 := by
        rw [← h2, sub_add_cancel]
      rw [e1, e2]
      abel
    have hval : Φ p.1 - Φ p.2 - ((ContinuousLinearEquiv.refl ℝ (Fin N → ℝ) : (Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)) :
        (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (p.1 - p.2) = q (p.1 - p.2) p.1 + q p.2 (p.1 - p.2) := by
      rw [← hexp]
      simp only [hΦ, ContinuousLinearEquiv.coe_refl', id]
      simp
      abel
    rw [hval]
    calc ‖q (p.1 - p.2) p.1 + q p.2 (p.1 - p.2)‖
        ≤ ‖q (p.1 - p.2) p.1‖ + ‖q p.2 (p.1 - p.2)‖ := norm_add_le _ _
      _ ≤ C * ‖p.1 - p.2‖ * ‖p.1‖ + C * ‖p.2‖ * ‖p.1 - p.2‖ := add_le_add (hC _ _) (hC _ _)
      _ = (C * (‖p.1‖ + ‖p.2‖)) * ‖p.1 - p.2‖ := by ring
      _ ≤ ε * ‖p.1 - p.2‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
  let P := hd.toOpenPartialHomeomorph Φ
  have hcoe : ∀ y, P y = Φ y := fun y => rfl
  have h0 : (0 : Fin N → ℝ) ∈ P.source := hd.mem_toOpenPartialHomeomorph_source
  have ha : P 0 = a := by
    rw [hcoe]
    simp [hΦ, hz]
  refine ⟨P.target, P.symm, P.open_target, ?_, P.continuousOn_symm, ?_⟩
  · rw [← ha]
    exact P.map_source h0
  · intro s hs
    have := P.right_inv hs
    rw [hcoe] at this
    exact this

theorem exists_ring_section {A : Type} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] {N : ℕ}
    (e : A ≃+ (Fin N → ℝ)) (he : Continuous e) (he' : Continuous e.symm)
    (τ : A →+ A) (hτ : Continuous τ) (c d k : A) :
    ∃ (O : Set A) (Y : A → A), IsOpen O ∧ c ∈ O ∧ ContinuousOn Y O ∧
      ∀ S ∈ O, c + Y S + k * (τ (Y S) * d * Y S) = S := by
  obtain ⟨T, ψ, hT, haT, hψ, hs⟩ := exists_quadratic_section
    (fun u v => e (k * (τ (e.symm u) * d * e.symm v)))
    (by
      intro u u' v
      simp only [map_add, add_mul, mul_add])
    (by
      intro u v v'
      simp only [map_add, add_mul, mul_add])
    (by
      have h1 : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => e.symm p.1) :=
        he'.comp continuous_fst
      have h2 : Continuous (fun p : (Fin N → ℝ) × (Fin N → ℝ) => e.symm p.2) :=
        he'.comp continuous_snd
      exact he.comp (continuous_const.mul (((hτ.comp h1).mul continuous_const).mul h2)))
    (e c)
  refine ⟨e ⁻¹' T, fun S => e.symm (ψ (e S)), hT.preimage he, haT, ?_, ?_⟩
  · exact he'.comp_continuousOn (hψ.comp he.continuousOn (fun x hx => hx))
  · intro S hS
    have h := congrArg e.symm (hs (e S) hS)
    simpa [map_add] using h

theorem tau_mul_mul_eq {A : Type} [Ring A] (τ : A →+ A) (hτm : ∀ x y, τ (x * y) = τ y * τ x)
    (hτ1 : τ 1 = 1) (hττ : ∀ x, τ (τ x) = x) (h c d S Y : A) (hcen : ∀ x, h * x = x * h)
    (hh : h + h = 1) (hτh : τ h = h) (hcd : c * d = 1) (hdc : d * c = 1) (hτc : τ c = c) (hτS : τ S = S)
    (hY : c + Y + h * h * (τ Y * d * Y) = S) :
    τ (1 + h * (d * Y)) * c * (1 + h * (d * Y)) = S := by
  have hτd : τ d = d := by
    calc τ d = τ d * (c * d) := by rw [hcd, mul_one]
      _ = τ (c * d) * d := by rw [hτm, hτc, mul_assoc]
      _ = d := by rw [hcd, hτ1, one_mul]
  have hYY : τ Y = Y := by
    have h3 := congrArg τ hY
    simp only [map_add, hτm, hτc, hττ, hτd, hτh, hτS] at h3
    have h4 : τ Y * (d * Y) * (h * h) = h * h * (τ Y * d * Y) := by
      rw [mul_assoc (τ Y) d Y]
      generalize τ Y * (d * Y) = x
      calc x * (h * h) = x * h * h := (mul_assoc _ _ _).symm
        _ = h * x * h := by rw [hcen x]
        _ = h * (x * h) := mul_assoc _ _ _
        _ = h * (h * x) := by rw [hcen x]
        _ = h * h * x := (mul_assoc _ _ _).symm
    rw [h4] at h3
    exact add_left_cancel (add_right_cancel (h3.trans hY.symm))
  rw [hYY] at hY
  have e1 : τ (1 + h * (d * Y)) = 1 + h * (Y * d) := by
    rw [map_add, hτ1, hτm, hτm, hτd, hYY, hτh, hcen]
  have e2 : c * (h * (d * Y)) = h * Y := by
    rw [← mul_assoc, ← hcen, mul_assoc, ← mul_assoc c, hcd, one_mul]
  have e3 : h * (Y * d) * c = h * Y := by
    rw [mul_assoc, mul_assoc, hdc, mul_one]
  have e4 : h * Y * (h * (d * Y)) = h * h * (Y * d * Y) := by
    rw [mul_assoc h Y, ← mul_assoc Y h, ← hcen Y, mul_assoc h Y, ← mul_assoc h h, ← mul_assoc Y d Y]
  rw [e1]
  calc (1 + h * (Y * d)) * c * (1 + h * (d * Y))
      = c + c * (h * (d * Y)) + (h * (Y * d) * c + h * (Y * d) * c * (h * (d * Y))) := by
        simp only [add_mul, mul_add, one_mul, mul_one]
        abel
    _ = c + (h + h) * Y + h * h * (Y * d * Y) := by
        rw [e2, e3, e4, add_mul]
        abel
    _ = S := by rw [hh, one_mul]; exact hY

theorem exists_section_ring {A X : Type} [Ring A] [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace X]
    {N : ℕ} (e : A ≃+ (Fin N → ℝ)) (he : Continuous e) (he' : Continuous e.symm)
    (τ : A →+ A) (hτ : Continuous τ) (hτm : ∀ x y, τ (x * y) = τ y * τ x) (hτ1 : τ 1 = 1)
    (hττ : ∀ x, τ (τ x) = x) (h : A) (hcen : ∀ x, h * x = x * h) (hh : h + h = 1) (hτh : τ h = h)
    (hU : IsOpen {x : A | IsUnit x}) (hinv : ContinuousOn (Ring.inverse : A → A) {x | IsUnit x})
    (hfin : ∀ x y : A, IsUnit (x * y) → IsUnit y)
    (ι : X → A) (hι : Continuous ι) (hτι : ∀ x, τ (ι x) = ι x) (c : X) (hc : IsUnit (ι c)) :
    ∃ O : Set X, IsOpen O ∧ c ∈ O ∧ ∀ S₀ ∈ O, ∃ f finv : X → A,
      ContinuousOn f O ∧ ContinuousOn finv O ∧
      ∀ S ∈ O, f S * finv S = 1 ∧ finv S * f S = 1 ∧ ι S = τ (f S) * ι S₀ * f S := by
  set d : A := Ring.inverse (ι c) with hd
  have hcd : ι c * d = 1 := Ring.mul_inverse_cancel _ hc
  have hdc : d * ι c = 1 := Ring.inverse_mul_cancel _ hc
  obtain ⟨O₁, Y, hO₁, hcO, hYc, hY⟩ := exists_ring_section e he he' τ hτ (ι c) d (h * h)
  set G : X → A := fun x => 1 + h * (d * Y (ι x)) with hG
  set O : Set X := ι ⁻¹' (O₁ ∩ {x | IsUnit x}) with hOdef
  have hO : IsOpen O := (hO₁.inter hU).preimage hι
  have hGc : ContinuousOn G O := by
    have hYO : ContinuousOn (fun x => Y (ι x)) O :=
      hYc.comp hι.continuousOn (fun x hx => hx.1)
    exact continuousOn_const.add (continuousOn_const.mul (continuousOn_const.mul hYO))
  have hGS : ∀ x ∈ O, τ (G x) * ι c * G x = ι x := fun x hx =>
    tau_mul_mul_eq τ hτm hτ1 hττ h (ι c) d (ι x) (Y (ι x)) hcen hh hτh hcd hdc (hτι c) (hτι x) (hY _ hx.1)
  have hGU : ∀ x ∈ O, IsUnit (G x) := fun x hx =>
    hfin (τ (G x) * ι c) (G x) (by rw [hGS x hx]; exact hx.2)
  refine ⟨O, hO, ⟨hcO, hc⟩, ?_⟩
  intro S₀ hS₀
  have hG0 := hGU S₀ hS₀
  have r1 : G S₀ * Ring.inverse (G S₀) = 1 := Ring.mul_inverse_cancel _ hG0
  have r2 : Ring.inverse (G S₀) * G S₀ = 1 := Ring.inverse_mul_cancel _ hG0
  refine ⟨fun S => Ring.inverse (G S₀) * G S, fun S => Ring.inverse (G S) * G S₀,
    continuousOn_const.mul hGc, (hinv.comp hGc hGU).mul continuousOn_const, ?_⟩
  intro S hS
  have s1 : G S * Ring.inverse (G S) = 1 := Ring.mul_inverse_cancel _ (hGU S hS)
  have s2 : Ring.inverse (G S) * G S = 1 := Ring.inverse_mul_cancel _ (hGU S hS)
  refine ⟨?_, ?_, ?_⟩
  · show Ring.inverse (G S₀) * G S * (Ring.inverse (G S) * G S₀) = 1
    rw [mul_assoc, ← mul_assoc (G S), s1, one_mul, r2]
  · show Ring.inverse (G S) * G S₀ * (Ring.inverse (G S₀) * G S) = 1
    rw [mul_assoc, ← mul_assoc (G S₀), r1, one_mul, s2]
  · have t1 : τ (Ring.inverse (G S₀)) * τ (G S₀) = 1 := by
      rw [← hτm, r1, hτ1]
    show ι S = τ (Ring.inverse (G S₀) * G S) * ι S₀ * (Ring.inverse (G S₀) * G S)
    rw [hτm, ← hGS S₀ hS₀, ← hGS S hS]
    calc τ (G S) * ι c * G S
        = τ (G S) * (1 * ι c * 1) * G S := by simp only [mul_assoc, one_mul, mul_one]
      _ = τ (G S) * ((τ (Ring.inverse (G S₀)) * τ (G S₀)) * ι c * (G S₀ * Ring.inverse (G S₀))) * G S := by
          rw [t1, r1]
      _ = _ := by simp only [mul_assoc]

end GlobalTheory.CompanionTheory.SecInf

namespace GlobalTheory.CompanionTheory.SecInf

theorem exists_section_matrix {B X : Type} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [TopologicalSpace X] {n N : ℕ} (hunits : IsOpenEmbedding (Units.val : Bˣ → B))
    (e₀ : (Fin n → Fin n → B) ≃+ (Fin N → ℝ)) (he₀ : Continuous e₀) (he₀' : Continuous e₀.symm)
    (s : B →+* B) (hsig : Continuous s) (hinvol : ∀ b, s (s b) = b) (t : B) (ht2 : t + t = 1) (hst : s t = t)
    (ι : X → Matrix (Fin n) (Fin n) B) (hι : Continuous ι) (hτι : ∀ x i j, s (ι x j i) = ι x i j)
    (c : X) (hc : IsUnit (ι c).det) :
    ∃ O : Set X, IsOpen O ∧ c ∈ O ∧ ∀ S₀ ∈ O, ∃ f finv : X → Matrix (Fin n) (Fin n) B,
      ContinuousOn f O ∧ ContinuousOn finv O ∧
      ∀ S ∈ O, f S * finv S = 1 ∧ finv S * f S = 1 ∧ ι S = cT s (f S) * ι S₀ * f S := by
  let e : Matrix (Fin n) (Fin n) B ≃+ (Fin N → ℝ) := Matrix.ofAddEquiv.symm.trans e₀
  let τ : Matrix (Fin n) (Fin n) B →+ Matrix (Fin n) (Fin n) B :=
    { toFun := cT s
      map_zero' := by ext i j; simp [cT]
      map_add' := by intro x y; ext i j; simp [cT] }
  have hτv : ∀ x, τ x = cT s x := fun _ => rfl
  have he : Continuous e := he₀
  have he' : Continuous e.symm := he₀'
  exact exists_section_ring (X := X) e he he' τ
    (by
      show Continuous fun x : Matrix (Fin n) (Fin n) B => cT s x
      unfold cT
      exact (Continuous.matrix_map continuous_id hsig).matrix_transpose)
    (fun x y => cT_mul _ x y) (cT_one _)
    (by
      intro x
      ext i j
      simp [hτv, cT, hinvol])
    (t • (1 : Matrix (Fin n) (Fin n) B))
    (by
      intro x
      simp)
    (by
      rw [← add_smul, ht2, one_smul])
    (by
      rw [hτv]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [cT, hst]
      · simp [cT, hij, Ne.symm hij])
    (by
      have hset : {x : Matrix (Fin n) (Fin n) B | IsUnit x} =
          Set.range (Units.val : GL (Fin n) B → Matrix (Fin n) (Fin n) B) := by
        ext x
        simp [IsUnit]
      rw [hset]
      exact (GlobalTheory.CompanionTheory.SW.GLOpen.isOpenEmbedding_val_GL _ hunits n).isOpen_range)
    (by
      have hinvB := GlobalTheory.CompanionTheory.SW.GLOpen.continuousOn_ringInverse_of_isOpenEmbedding_units _ hunits
      have hdet : Continuous (fun M : Matrix (Fin n) (Fin n) B => M.det) :=
        continuous_id.matrix_det
      have hadj : Continuous (fun M : Matrix (Fin n) (Fin n) B => M.adjugate) :=
        continuous_id.matrix_adjugate
      have hmaps : Set.MapsTo (fun M : Matrix (Fin n) (Fin n) B => M.det)
          {M | IsUnit M} {x | IsUnit x} := fun M hM => (Matrix.isUnit_iff_isUnit_det M).mp hM
      have hfun : (Ring.inverse : Matrix (Fin n) (Fin n) B → _) =
          fun M => Ring.inverse M.det • M.adjugate := by
        funext M
        rw [← Matrix.nonsing_inv_eq_ringInverse, Matrix.inv_def]
      rw [hfun]
      exact (hinvB.comp hdet.continuousOn hmaps).smul hadj.continuousOn)
    (by
      intro x y hxy
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul] at hxy
      rw [Matrix.isUnit_iff_isUnit_det]
      exact isUnit_of_mul_isUnit_right hxy)
    ι hι
    (by
      intro S
      ext i j
      exact hτι S i j)
    c ((Matrix.isUnit_iff_isUnit_det _).2 hc)

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
set_option synthInstance.maxSize 2000 in

theorem secInf : PositivityTheory.PfSWUS.SchInf.SecInf := by
  intro F E _ _ _ _ _ σ hσ n c hc
  have hR : GlobalTheory.CompanionTheory.SW.IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hunits : IsOpenEmbedding (Units.val : (Ainf F ⊗[F] E)ˣ → Ainf F ⊗[F] E) :=
    GlobalTheory.T.units_open_embedding_local_tensor F E σ hσ (Ainf F) hR
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, -, -, -, hsig, -, -, -, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Ainf F)
  haveI := iTR
  obtain ⟨N, e₀, he₀, he₀'⟩ := GlobalTheory.CompanionTheory.SW.SchwartzFib.exists_real_coords F E n n
  have hinvol : ∀ b : Ainf F ⊗[F] E, sigR (Ainf F) σ (sigR (Ainf F) σ b) = b := by
    have hσσ : ∀ x, σ (σ x) = x := by
      intro x
      let φ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
      apply φ.injective
      rw [hσ.2.2.2 φ, hσ.2.2.2 φ]
      simp
    intro b
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [sigR, hσσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have ht2 : algebraMap F (Ainf F ⊗[F] E) (1 / 2) + algebraMap F (Ainf F ⊗[F] E) (1 / 2) = 1 := by
    have h12 : (1 / 2 : F) + 1 / 2 = 1 := by norm_num
    rw [← map_add, h12, map_one]
  have hst : sigR (Ainf F) σ (algebraMap F (Ainf F ⊗[F] E) (1 / 2)) = algebraMap F (Ainf F ⊗[F] E) (1 / 2) :=
    (Algebra.TensorProduct.map (AlgHom.id F (Ainf F)) σ).commutes (1 / 2)
  exact exists_section_matrix (X := HermR (Ainf F) σ n) hunits e₀ he₀ he₀' (sigR (Ainf F) σ) hsig hinvol _ ht2 hst
    (fun S => (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) continuous_subtype_val
    (fun S i j => S.2 i j) c hc

end GlobalTheory.CompanionTheory.SecInf
