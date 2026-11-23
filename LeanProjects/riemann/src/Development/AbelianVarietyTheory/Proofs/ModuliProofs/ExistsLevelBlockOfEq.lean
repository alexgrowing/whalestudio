import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermFormConjDiag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameOfPeriodLinear
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOfTriangular
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing

open AlgebraicGeometry CategoryTheory NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameFibre

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem exists_smul_eq {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hspan : Submodule.span E (Set.range φ) = ⊤) (u : Fin r → E) :
    ∃ (c : 𝓞 E) (v : L), c ≠ 0 ∧ (c : E) • u = φ v := by
  have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hspan]; trivial
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨v, rfl⟩ := hx; exact ⟨1, v, one_ne_zero, by simp⟩
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, v, hc, hv⟩ := hx
    obtain ⟨d, w, hd, hw⟩ := hy
    refine ⟨c * d, d • v + c • w, mul_ne_zero hc hd, ?_⟩
    rw [map_add, map_smul, map_smul, ← hv, ← hw]
    ext k
    simp [Algebra.smul_def]
    ring
  | smul a x _ hx =>
    obtain ⟨c, v, hc, hv⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
    have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
    have hd1 : algebraMap (𝓞 E) E d ≠ 0 := by simpa using hd0
    refine ⟨c * d, n • v, mul_ne_zero hc hd0, ?_⟩
    rw [map_smul, ← hv]
    ext k
    simp only [Pi.smul_apply, smul_eq_mul, RingOfIntegers.coe_eq_algebraMap, map_mul]
    rw [Algebra.smul_def]
    field_simp

theorem exists_matrix {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (ψ : L →ₗ[𝓞 E] (Fin r → E)) : ∃ A : Matrix (Fin r) (Fin r) E, ∀ v, A *ᵥ φ v = ψ v := by
  haveI : IsLocalizedModule (𝓞 E)⁰ φ :=
    { map_units := fun s => (isLocalizedModule_id (𝓞 E)⁰ (Fin r → E) E).map_units s
      surj := fun u => by
        obtain ⟨c, v, hc, hv⟩ := exists_smul_eq φ hspan u
        exact ⟨(v, ⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩), hv⟩
      exists_of_eq := fun h => ⟨1, by rw [hφ h]⟩ }
  have hb := IsLocalizedModule.isBaseChange (𝓞 E)⁰ E φ
  exact ⟨LinearMap.toMatrix' (hb.lift ψ), fun v => by
    rw [LinearMap.toMatrix'_mulVec, hb.lift_eq]⟩

theorem exists_gl {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (gam : L ≃ₗ[𝓞 E] L) : ∃ γ : GL (Fin r) E,
      ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ (gam v) := by
  obtain ⟨A, hA⟩ := exists_matrix φ hφ hspan (φ ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := exists_matrix φ hφ hspan (φ ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v, A *ᵥ φ v = φ (gam v) := hA
  have hB' : ∀ v, B *ᵥ φ v = φ (gam.symm v) := hB
  have hAB : A * B = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB', hA', Matrix.one_mulVec,
      LinearEquiv.apply_symm_apply]
  exact ⟨⟨A, B, hAB, mul_eq_one_comm.1 hAB⟩, hA'⟩

theorem eq_zero_of_trace (t : E) (ht : ∀ a : 𝓞 E, Algebra.trace ℚ E ((a : E) * t) = 0) : t = 0 := by
  refine (traceForm_nondegenerate ℚ E).1 t fun e => ?_
  have halg : IsAlgebraic ℤ e :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨k, hk, hki⟩ := halg.exists_integral_multiple
  have h : Algebra.trace ℚ E ((k • e) * t) = 0 := ht ⟨k • e, hki⟩
  rw [smul_mul_assoc, map_zsmul, smul_eq_zero] at h
  rw [Algebra.traceForm_apply, mul_comm]
  exact h.resolve_left hk

variable [IsCMField E]

theorem herm_smul_smul (G : Matrix (Fin r) (Fin r) E) (c d : E) (x y : Fin r → E) :
    FD.herm G (c • x) (d • y) = c * FD.cc d * FD.herm G x y := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem herm_of_trace {L : Type} [AddCommGroup L] [Module (𝓞 E) L] (φ : L →ₗ[𝓞 E] (Fin r → E))
    (hspan : Submodule.span E (Set.range φ) = ⊤) (G A : Matrix (Fin r) (Fin r) E) (ξ : E) (hξ : ξ ≠ 0)
    (h : ∀ v w, Algebra.trace ℚ E (ξ * FD.herm G (A *ᵥ φ v) (A *ᵥ φ w)) =
      Algebra.trace ℚ E (ξ * FD.herm G (φ v) (φ w))) (x y : Fin r → E) :
    FD.herm G (A *ᵥ x) (A *ᵥ y) = FD.herm G x y := by
  have h1 : FD.cc (1 : E) = 1 := map_one (IsCMField.complexConj E)
  have key : ∀ v w, FD.herm G (A *ᵥ φ v) (A *ᵥ φ w) = FD.herm G (φ v) (φ w) := by
    intro v w
    apply mul_left_cancel₀ hξ
    rw [← sub_eq_zero]
    refine eq_zero_of_trace _ fun a => ?_
    have h2 := h (a • v) w
    have h3 : φ (a • v) = (a : E) • φ v := by rw [map_smul]; rfl
    have h4 := herm_smul_smul G (a : E) 1 (A *ᵥ φ v) (A *ᵥ φ w)
    have h5 := herm_smul_smul G (a : E) 1 (φ v) (φ w)
    rw [one_smul, h1, mul_one] at h4 h5
    rw [h3, Matrix.mulVec_smul, h4, h5] at h2
    rw [mul_sub, map_sub, mul_left_comm, h2, mul_left_comm, sub_self]
  obtain ⟨c, v, hc, hv⟩ := exists_smul_eq φ hspan x
  obtain ⟨d, w, hd, hw⟩ := exists_smul_eq φ hspan y
  have h2 := key v w
  rw [← hv, ← hw, Matrix.mulVec_smul, Matrix.mulVec_smul, herm_smul_smul, herm_smul_smul] at h2
  refine mul_left_cancel₀ (mul_ne_zero ?_ ?_) h2
  · simpa using hc
  · exact (map_ne_zero (IsCMField.complexConj E)).2 (by simpa using hd)

theorem lact_mem_GG {Ψ : Finset (E →+* ℂ)} {G : Matrix (Fin r) (Fin r) E} {q : ℕ} {γ : GL (Fin r) E}
    (hγ : ∀ u v, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      FD.herm G u v) {x : FD.Frame Ψ r} (hx : x ∈ FD.GG Ψ G q) : FD.lact γ x ∈ FD.GG Ψ G q := by
  intro τ
  have e1 : FD.mat (FD.lact γ x) τ = (γ : Matrix (Fin r) (Fin r) E).map τ.1 * FD.mat x τ := rfl
  refine ⟨?_, fun i => ?_⟩
  · have hu : IsUnit ((γ : Matrix (Fin r) (Fin r) E).map τ.1).det :=
      (Matrix.isUnit_iff_isUnit_det _).1 (γ.isUnit.map τ.1.mapMatrix)
    rw [e1, Matrix.det_mul]
    exact mul_ne_zero hu.ne_zero (hx τ).1
  · have h := (hx τ).2 i
    have e2 : FD.gram τ.1 G (FD.mat (FD.lact γ x) τ) = FD.gram τ.1 G (FD.mat x τ) := by
      ext a b
      simp only [FD.gram, Matrix.of_apply, e1, PerMove.col_mul, PerMove.hermC_unitary _ _ _ hγ]
    unfold FD.dmin at h ⊢
    rwa [e2]

theorem exists_level_block_of_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : (U.Di i).La →ₗ[𝓞 E] (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (idx : Fin g ≃ Ψ × Fin r) (Pf : FD.Frame Ψ r → ((U.Di i).La →+ (Fin g → ℂ))), (∀ τ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) → (∀ k, ty k = if ((idx k).2 : ℕ) < (U.Di i).q then ComplexEmbedding.conjugate (idx k).1.1 else (idx k).1.1) → FD.cc ξ = -ξ → (∀ τ ∈ Ψ, 0 < (τ ξ).im) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, (((U.Di i).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → r = (U.Di i).p + (U.Di i).q → (∀ x v k, Pf x v k = if ((idx k).2 : ℕ) < (U.Di i).q then FD.hermC (idx k).1.1 Gm (FD.col (FD.mat x (idx k).1) (idx k).2) (FD.Data.emb (idx k).1.1 (φ v)) else ((FD.mat x (idx k).1)⁻¹ *ᵥ FD.Data.emb (idx k).1.1 (φ v)) (idx k).2) → ∀ x ∈ FD.GG Ψ Gm (U.Di i).q, ∀ x' ∈ FD.GG Ψ Gm (U.Di i).q, U.u i (Pf x) = U.u i (Pf x') → ∃ (γ : GL (Fin r) E) (b : FD.Frame Ψ r), FD.IsUStab Gm (LinearMap.range φ) γ ∧ (∀ v, ∃ w, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ v + l.M • φ w) ∧ (∀ v, ∃ w, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ v + l.A • φ w) ∧ x' = FD.rmul (FD.lact γ x) b ∧ ∀ τ (a c : Fin r), (c : ℕ) < (U.Di i).q → (U.Di i).q ≤ (a : ℕ) → b τ a c = 0 := by
  classical
  intro E _ _ _ H D l Xo σ g ty U i r ξ Gm φ Ψ idx Pf hΨ hty hξ hpos hlat hr hPf x hx x' hx' hu
  have hper := (FramePeriod.isPeriod_frame E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hlat hr).2
  obtain ⟨gam, h, hiso, hhalf, hA, hh⟩ :=
    (U.fibre i _ _ ((hper x hx).2 _ (hPf x)) ((hper x' hx').2 _ (hPf x'))).1 hu
  have hM := LevelHalf.trivial_mod_of_trivial_on_half E H (U.Di i) l gam hiso hhalf
  obtain ⟨γ, hγ⟩ := exists_gl φ hlat.1 hlat.2.1 gam
  have hξ0 : ξ ≠ 0 := by
    have hcm := FramePeriod.cmType H Ψ hΨ
    obtain ⟨s⟩ : Nonempty (E →+* ℂ) := inferInstance
    obtain ⟨τ, hτ⟩ : ∃ τ, τ ∈ Ψ := by
      by_cases h : ComplexEmbedding.conjugate s ∈ Ψ
      · exact ⟨_, h⟩
      · exact ⟨s, (hcm s).2 h⟩
    rintro rfl
    simpa using hpos τ hτ
  have hun := herm_of_trace φ hlat.2.1 Gm γ ξ hξ0 fun v w => by
    rw [hγ, hγ, ← hlat.2.2.2.2, ← hlat.2.2.2.2, hiso]
  have hmove := (per_move E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty hξ hpos hlat).2.1 x γ (Pf x)
    (Pf (FD.lact γ x)) hun (hPf x) (hPf _)
  obtain ⟨b, hb, hb0, -⟩ := FramePeriod.frame_of_period_linear E H (U.Di i) r ξ Gm φ Ψ hΨ g idx ty hty
    hξ hpos hlat (Pf (FD.lact γ x)) _ (lact_mem_GG hun hx) x' hx' (hPf _) (Pf x') (hPf _)
    (LinearMap.toMatrix' h.toLinearMap) fun v => by
      obtain ⟨a, rfl⟩ := gam.surjective v
      rw [LinearMap.toMatrix'_mulVec, hh, hmove a (gam a) (hγ a).symm]
      rfl
  refine ⟨γ, b, ⟨hun, fun y => ⟨?_, ?_⟩⟩, fun v => ?_, fun v => ?_, hb, hb0⟩
  · rintro ⟨v, rfl⟩
    exact ⟨gam v, (hγ v).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨gam.symm v, ?_⟩
    apply (Matrix.mulVec_injective_of_isUnit γ.isUnit)
    rw [hγ, LinearEquiv.apply_symm_apply, hv]
  · obtain ⟨e, he⟩ := hM v
    exact ⟨e, by rw [hγ, he, map_add, map_nsmul]⟩
  · obtain ⟨e, he⟩ := hA v
    exact ⟨e, by rw [hγ, he, map_add, map_nsmul]⟩

end GlobalTheory.FrameFibre
