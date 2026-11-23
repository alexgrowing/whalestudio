import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.MarkSpec
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Formalism.LocalToGlobal.ProjectiveLattices.ComponentWModel
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs
import Formalism.LocalToGlobal.ProjectiveLattices.DatProofs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SignatureHermitianModelOfDatum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelGoodAndSign
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.PosIndexMapEqCardOfCongrDiagonal

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi
open scoped TensorProduct Topology
open GlobalTheory.RecDict

noncomputable section

namespace GlobalTheory.RecDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix in

theorem negIndex_transpose_of_hasSignature {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : GlobalTheory.Inertia.negIndex Jᵀ = q ∧ J.det ≠ 0 := by
  obtain ⟨e, P, hP⟩ := h
  have hd : Formalism.UG.Jpq p q = diagonal (Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)) := by
    rw [← fromBlocks_diagonal, Formalism.UG.Jpq]
    congr 1
    rw [← diagonal_neg]
    rfl
  have hPd : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).det ≠ 0 := P.det_ne_zero
  constructor
  · have ht := congrArg Matrix.transpose hP
    rw [hd, diagonal_transpose, transpose_mul, transpose_mul, Formalism.UG.cT, transpose_transpose,
      ← Matrix.mul_assoc] at ht
    have h1 := GlobalTheory.Inertia.negIndex_eq_card_of_congr_diagonal hPd ht
    have h2 : (J.reindex e e)ᵀ = Jᵀ.submatrix e.symm e.symm := rfl
    rw [h2, GlobalTheory.Inertia.negIndex_submatrix_equiv] at h1
    rw [h1, Finset.card_filter, Fintype.sum_sum_type]
    simp [not_lt.2 (zero_le_one' ℝ)]
  · intro h0
    have h1 := congrArg Matrix.det hP
    rw [det_mul, det_mul, det_reindex_self, h0, hd, det_diagonal] at h1
    simp only [mul_zero, zero_mul] at h1
    refine Finset.prod_ne_zero_iff.2 (fun k _ => ?_) h1.symm
    rcases k with k | k <;> simp

variable {D : D7}

theorem cc_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (a b : Fin r) :
    cc (gmW V hr a b) = gmW V hr b a := by
  subst hr
  show IsCMField.complexConj D.host.E (-(V.hT (V.frame b) (V.frame a))) = -(V.hT (V.frame a) (V.frame b))
  rw [map_neg]
  exact congrArg Neg.neg (LinearMap.isSymm_def.1 V.herm (V.frame b) (V.frame a))

theorem herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm) =
      -V.hT y x := by
  subst hr
  rw [Formalism.L2.Pj.DatLin.sesq_repr V.hT V.frame y x, Finset.sum_comm, herm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  show V.frame.repr x a * (-(V.hT (V.frame b) (V.frame a))) * star (V.frame.repr y b) = _
  ring

theorem trace_herm_gmW (V : HSp D) {r : ℕ} (hr : V.rank = r) (x y : V.V) :
    Algebra.trace ℚ D.host.E (D.host.xi0 *
      herm (gmW V hr) (V.frame.equivFun x ∘ Fin.cast hr.symm) (V.frame.equivFun y ∘ Fin.cast hr.symm)) =
      Algebra.trace ℚ D.host.E (D.host.xi0 * V.hT x y) := by
  rw [herm_gmW, ← trace_cc D (D.host.xi0 * V.hT x y), map_mul (IsCMField.complexConj D.host.E), conj_xi0_alt]
  have h : IsCMField.complexConj D.host.E (V.hT x y) = V.hT y x := LinearMap.isSymm_def.1 V.herm x y
  rw [h, mul_neg, neg_mul]

theorem posIndex_gmW (V : HSp D) (hV : V.SigOK) {r : ℕ} (hr : V.rank = r) (τ : D.host.E →+* ℂ) :
    GlobalTheory.Inertia.posIndex ((gmW V hr).map τ) = (V.sig τ).2 ∧ (gmW V hr).det ≠ 0 := by
  subst hr
  obtain ⟨h1, h2⟩ := negIndex_transpose_of_hasSignature (hV τ)
  have e : gmW V rfl = -V.gram.transpose := rfl
  constructor
  · rw [← h1, ← GlobalTheory.Inertia.posIndex_neg, e]
    congr 1
    ext a b
    simp
  · rw [e, Matrix.det_neg, Matrix.det_transpose]
    refine mul_ne_zero (pow_ne_zero _ (by simp)) fun h0 => h2 ?_
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem finVec_mem_latHat_iff (V : HSp D) (v : Fin V.rank → D.host.E) :
    finVec V v ∈ latHat V ↔ V.frame.equivFun.symm v ∈ V.L0 := by
  let f : V.V ≃ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := V.frame.equivFun.restrictScalars (𝓞 D.host.E)
  let L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := V.L0.map f.toLinearMap
  have hfg : L.FG := V.standardTuple_isLattice.fg.map _
  have hsp : Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have : (L : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := rfl
    rw [this, Submodule.span_image, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have h := (GlobalTheory.AdLat.hat_rational_points_and_approx D.host.F D.host.E V.rank L hfg hsp).1 v
  have e : latHat V = GlobalTheory.AdLat.hat D.host.F (L : Set (Fin V.rank → D.host.E)) := by
    unfold latHat GlobalTheory.AdLat.hat
    congr 1
    ext z
    constructor
    · rintro ⟨a, ha, x, hx, rfl⟩
      exact ⟨a, ha, f x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨a, ha, _, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨a, ha, x, hx, rfl⟩
  rw [e]
  refine h.trans ?_
  constructor
  · rintro ⟨x, hx, rfl⟩
    show V.frame.equivFun.symm (V.frame.equivFun x) ∈ V.L0
    rwa [LinearEquiv.symm_apply_apply]
  · intro hv
    exact ⟨_, hv, V.frame.equivFun.apply_symm_apply v⟩

theorem latG_one (V : HSp D) :
    latG V 1 = (Submodule.span (𝓞 D.host.E)
      {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ V.L0, v = a • x}).map
        (V.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
  have hg : gLat V 1 = latHat V := by
    rw [gLat, map_one]
    ext z
    simp
  rw [Submodule.map_span, latG, hg]
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, v, hv, rfl⟩
    refine ⟨a • V.frame.equivFun.symm v, ⟨a, ha, _, (finVec_mem_latHat_iff V v).1 hv, rfl⟩, ?_⟩
    show V.frame.equivFun (a • V.frame.equivFun.symm v) = a • v
    rw [map_smul, LinearEquiv.apply_symm_apply]
  · rintro ⟨_, ⟨a, ha, x, hx, rfl⟩, rfl⟩
    refine ⟨a, ha, V.frame.equivFun x, (finVec_mem_latHat_iff V _).2 ?_, ?_⟩
    · rwa [LinearEquiv.symm_apply_apply]
    · show V.frame.equivFun (a • x) = _
      rw [map_smul]

theorem span_latW (D : D7) (j : ℕ) :
    Submodule.span D.host.E (latW D j : Set (D.sp.W j).V) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  obtain ⟨s, hs, hsy⟩ := exists_smul_mem_latW D j y
  have hs0 : algebraMap (𝓞 D.host.E) D.host.E s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have e : y = (algebraMap (𝓞 D.host.E) D.host.E s)⁻¹ • (s • y) := by
    rw [← algebraMap_smul D.host.E s y, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hsy)

theorem exists_latEmb_sign_one : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j (hj : InR D j), ∃ io : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin (D.sp.W j).rank → D.host.E), LatEmb (D.sp.W j) io ∧ LatIsom (D.sp.W j) (Q.Dw j).EF io ∧ (∀ a b, cc (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) a b) = gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2) b a) ∧ (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)).det ≠ 0 ∧ Submodule.span D.host.E (Set.range io) = ⊤ ∧ ∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) = Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (gmW (D.sp.W j) (D.sp.W_rank j hj.1 hj.2)) (io x ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm) (io y ∘ Fin.cast (D.sp.W_rank j hj.1 hj.2).symm)) := by
  intro D Q hQ j hj
  obtain ⟨hp, hq, φ, ε, hinj, hrange, hEF⟩ := hQ.2.2.2 j hj
  have hr := D.sp.W_rank j hj.1 hj.2
  let f := ((D.sp.W j).frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap
  have hf : ∀ x, f x = (D.sp.W j).frame.equivFun x := fun _ => rfl
  have hio : Function.Injective (f ∘ₗ φ) := (D.sp.W j).frame.equivFun.injective.comp hinj
  have hdet := (posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).2
  have hφ : Set.range φ = (latW D j : Set (D.sp.W j).V) := by
    rw [← LinearMap.coe_range, hrange]
    rfl
  have hspan : Submodule.span D.host.E (Set.range (f ∘ₗ φ)) = ⊤ := by
    have : Set.range (f ∘ₗ φ) = (D.sp.W j).frame.equivFun.toLinearMap '' Set.range φ := by
      rw [← Set.range_comp]
      rfl
    rw [this, Submodule.span_image, hφ, span_latW, Submodule.map_top, LinearEquiv.range]
  have hε : ε = 1 := by
    rcases Int.units_eq_one_or ε with h | h
    · exact h
    exfalso
    subst h
    let c : (Fin (D.sp.W j).rank → D.host.E) ≃ₗ[D.host.E] (Fin D.R.r → D.host.E) :=
      LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr hr.symm)
    let ψ : (Q.Dw j).La →ₗ[𝓞 D.host.E] (Fin D.R.r → D.host.E) :=
      (c.restrictScalars (𝓞 D.host.E)).toLinearMap ∘ₗ f ∘ₗ φ
    have hψ : ∀ x, ψ x = (D.sp.W j).frame.equivFun (φ x) ∘ Fin.cast hr.symm := fun _ => rfl
    have hτ : D.host.φ₀ (Q.H.rt : D.host.E) = Q.H.rt0 := by rw [hQ.1.2.1, hQ.1.2.2.1]
    have hξ : cc (-D.host.xi0) = -(-D.host.xi0) := by
      rw [cc, map_neg, conj_xi0_alt]
    have hsp : Submodule.span D.host.E (Set.range ψ) = ⊤ := by
      have : Set.range ψ = c.toLinearMap '' Set.range (f ∘ₗ φ) := by
        rw [← Set.range_comp]
        rfl
      rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
    have hform : ∀ x y, (((Q.Dw j).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ D.host.E (-D.host.xi0 * herm (gmW (D.sp.W j) hr) (ψ x) (ψ y)) := by
      intro x y
      rw [hEF, hψ, hψ, neg_mul, map_neg, trace_herm_gmW]
      simp
    obtain ⟨P, hP, hPg⟩ := (GlobalTheory.HermSign.signature_of_model D.host.E Q.H (Q.Dw j) D.R.r (-D.host.xi0)
      (gmW (D.sp.W j) hr) ψ hξ ⟨c.injective.comp hio, hsp, cc_gmW _ hr, hdet, hform⟩ D.host.φ₀ hτ).2
      ((level_good_and_sign D Q hQ).2.2 _ hτ)
    have hm := D.R.m_add_three_le_k
    have h1 := hj.1
    have h2 := hj.2
    have hle : (Q.Dw j).p ≤ D.R.r := by
      rw [hp]
      simp only [Ranks.sigW, Ranks.r]
      omega
    have h3 := (GlobalTheory.Inertia.gram_eq_sgn_iff D.host.φ₀ (cc_gmW _ hr) hdet _).1 ⟨hle, P, hP, hPg⟩
    rw [(posIndex_gmW (D.sp.W j) (D.sp.W_sig j) hr D.host.φ₀).1, D.sp.W_sigval j hj.1 hj.2, hp] at h3
    simp only [Ranks.sigW] at h3
    omega
  subst hε
  refine ⟨f ∘ₗ φ, ⟨hio, ?_⟩, ⟨1, fun x y => ?_⟩, cc_gmW _ hr, hdet, hspan, fun x y => ?_⟩
  · rw [latG_one, LinearMap.range_comp, hrange]
  · rw [hEF, LinearMap.comp_apply, LinearMap.comp_apply, hf, hf, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply]
  · rw [hEF, LinearMap.comp_apply, LinearMap.comp_apply, hf, hf, neg_neg, trace_herm_gmW]
    simp

end GlobalTheory.RecDict
