import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ModelsAt
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolArcEqFlowOrbit
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardCompLePeriodSpaces
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FamilyUnifExpUnique
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEqNsmulOfDvdPairing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PerFrLact
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt Formalism.L2.LamCM GlobalTheory GlobalTheory.ArcQ GlobalTheory.LamF GlobalTheory.ArcCM
open scoped LaurentSeries
open scoped Matrix

namespace GlobalTheory.FrameMatch

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem flow_lact_rmul (X : Data E r) (gm : GL (Fin r) E)
    (hgm : ∀ u v, herm X.Gm ((gm : Matrix (Fin r) (Fin r) E) *ᵥ u) ((gm : Matrix (Fin r) (Fin r) E) *ᵥ v) =
      herm X.Gm u v) (ξ : Fin r → E) (s : X.Ψ → ℂ) (x b : Frame X.Ψ r) :
    X.flow ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) s (rmul (lact gm x) b) = rmul (lact gm (X.flow ξ s x)) b := by
  funext τ
  have key : X.flowMat ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) τ (s τ) * (gm : Matrix (Fin r) (Fin r) E).map τ.1 =
      (gm : Matrix (Fin r) (Fin r) E).map τ.1 * X.flowMat ξ τ (s τ) := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, EmbeddingHermitianPairs.flowMat_mulVec, EmbeddingHermitianPairs.flowMat_mulVec,
      GlobalTheory.PerMove.emb_mulVec, GlobalTheory.PerMove.hermC_unitary _ _ _ hgm, Matrix.mulVec_add, Matrix.mulVec_smul]
  change X.flowMat _ τ (s τ) * ((gm : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ * mat b τ) =
    (gm : Matrix (Fin r) (Fin r) E).map τ.1 * (X.flowMat ξ τ (s τ) * mat x τ) * mat b τ
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, key, Matrix.mul_assoc (_ : Matrix (Fin r) (Fin r) ℂ) _ (mat x τ)]

theorem fj_lact_rmul (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P) {gm : GL (Fin r) E}
    (hgm : gm ∈ X.Γ) {ξ : Fin r → E} (hξ : herm X.Gm ξ ξ = 0) (ν : X.Ψ → ℝ) {x b : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hb : b ∈ Bor X.Ψ r) :
    X.fj la ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) ν P (rmul (lact gm x) b) =
      bchar la b * X.χ la gm * X.fj la ξ ν P x := by
  have h : ∀ s : X.Ψ → ℝ, P (X.flow ((gm : Matrix (Fin r) (Fin r) E) *ᵥ ξ) (fun τ => (s τ : ℂ)) (rmul (lact gm x) b)) =
      bchar la b * X.χ la gm * P (X.flow ξ (fun τ => (s τ : ℂ)) x) := fun s => by
    have h1 : X.flow ξ (fun τ => (s τ : ℂ)) x ∈ X.dom := TransvectionPeriodicity.flow_real_mem_dom X hξ s x hx
    rw [flow_lact_rmul X gm (X.Γ_stab gm hgm).1, hP.2.1 _ ((AR.Up.PairUnfoldPf.lact_mem_dom_iff X hgm _).2 h1) b hb,
      hP.2.2 gm hgm _ h1, _root_.mul_assoc]
  unfold Data.fj
  split_ifs
  · simp only [h, _root_.mul_assoc (bchar la b * X.χ la gm), MeasureTheory.integral_const_mul]
    ring
  · simp
  · simp

theorem row_eq_of_lattice (X : Data E r) (τ : E →+* ℂ) (A B : Matrix (Fin r) (Fin r) ℂ) (a : Fin r)
    (h : ∀ v ∈ X.Λ, (A *ᵥ Data.emb τ v) a = (B *ᵥ Data.emb τ v) a) (j : Fin r) : A a j = B a j := by
  obtain ⟨d, hd, hv⟩ := HermitianTraceFormVanishing.exists_smul_mem (R := 𝓞 E) (F := E) X.Λ (x := Pi.single j 1)
    (by rw [X.Λ_span]; trivial)
  have h2 := h _ hv
  have hemb : Data.emb τ (d • (Pi.single j 1 : Fin r → E)) = τ d • (Pi.single j 1 : Fin r → ℂ) := by
    funext k
    by_cases hk : k = j <;> simp [Data.emb, Algebra.smul_def, hk]
  rw [hemb, Matrix.mulVec_smul, Matrix.mulVec_smul] at h2
  simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec_single_one, Matrix.col_apply] at h2
  refine mul_left_cancel₀ ?_ h2
  simpa using hd

theorem exists_bor (X : Data E r) {y y' : Frame X.Ψ r} (hy : y ∈ X.dom) (hy' : y' ∈ X.dom) (q : ℕ)
    (h1 : ∀ τ (a : Fin r), (a : ℕ) < q → FD.col (mat y' τ) a = FD.col (mat y τ) a)
    (h2 : ∀ τ (a : Fin r), ¬ (a : ℕ) < q → ∀ j, (mat y' τ)⁻¹ a j = (mat y τ)⁻¹ a j) :
    ∃ b ∈ Bor X.Ψ r, y' = rmul y b := by
  refine ⟨fun τ => ((mat y τ)⁻¹ * mat y' τ : Matrix (Fin r) (Fin r) ℂ), fun τ => ⟨?_, fun a c hca => ?_⟩, ?_⟩
  · change ((mat y τ)⁻¹ * mat y' τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (Matrix.isUnit_nonsing_inv_det _ (hy τ).1.isUnit).ne_zero (hy' τ).1
  · change ((mat y τ)⁻¹ * mat y' τ) a c = 0
    by_cases ha : (a : ℕ) < q
    · have h3 := congrFun (congrFun (Matrix.nonsing_inv_mul (mat y τ) (hy τ).1.isUnit) a) c
      rw [Matrix.one_apply_ne hca.ne'] at h3
      rw [← h3, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => congrArg _ (congrFun (h1 τ c (lt_trans hca ha)) j)
    · have h3 := congrFun (congrFun (Matrix.nonsing_inv_mul (mat y' τ) (hy' τ).1.isUnit) a) c
      rw [Matrix.one_apply_ne hca.ne'] at h3
      rw [← h3, Matrix.mul_apply, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun j _ => by rw [h2 τ a ha j]
  · funext τ
    change mat y' τ = mat y τ * ((mat y τ)⁻¹ * mat y' τ)
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hy τ).1.isUnit]

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}

theorem exists_isometry {σ' : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (F : FamilyUnif Xo σ' ty) (i : Fin F.n)
    (P P' : (F.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (F.Di i) ty P) (hP' : IsPeriod (F.Di i) ty P')
    (hu : F.u i P = F.u i P') (hex : ∀ z, (F.ex i P z).left = (F.ex i P' z).left) :
    ∃ gam : (F.Di i).La ≃ₗ[𝓞 E] (F.Di i).La, (∀ a, P' (gam a) = P a) ∧
      (∀ a b, (F.Di i).EF (gam a) (gam b) = (F.Di i).EF a b) ∧ ∀ a, ∃ e, gam a = a + l.M • e := by
  obtain ⟨h, gam, hh, hPh, hiso, hM, -⟩ := GlobalTheory.familyUnif_exp_unique E H Dw l Xo σ' g ty F i i P P' hP hP' hu
  haveI := hP'.2.2.1
  have h1 : ∀ z, h z = z := fun z => sub_eq_zero.1 <|
    GlobalTheory.ExpUniqFamily.linear_eq_zero_of_discrete P'.range (h.toLinearMap - LinearMap.id) (fun z =>
      (F.ex_ker i P' hP' _).1 <| (GlobalTheory.ExpUniqFamily.eq_iff_sub (F.ex i P') (F.ex_add i P' hP') _ _).1
        (Over.OverMorphism.ext ((hh z).trans (hex z)))) z
  refine ⟨gam, fun a => (hPh a).trans (h1 _), hiso,
    GlobalTheory.LevelHalf.trivial_mod_of_trivial_on_half E H (F.Di i) l gam hiso fun a ha => ?_⟩
  refine Submodule.smul_induction_on ha ?_ ?_
  · intro v hv b _
    obtain ⟨c, e, rfl⟩ := F.t_surj i b
    obtain ⟨e₁, he₁⟩ := hM (v • c) (Submodule.smul_mem_smul hv Submodule.mem_top)
    obtain ⟨m, hm⟩ : l.M ∣ l.M' := Nat.dvd_lcm_left _ _
    refine ⟨e₁ + m • (gam (v • e) - v • e), ?_⟩
    rw [smul_add, ← map_smul, smul_comm v, map_add, he₁, map_nsmul, hm, smul_add, smul_smul, smul_sub]
    abel
  · rintro x y ⟨e, he⟩ ⟨e', he'⟩
    exact ⟨e + e', by rw [map_add, he, he', smul_add]; abel⟩

variable {c : Coeff l} {σ : c.F →+* ℂ} {U : Unf Xo c σ r} (Uw : UnfWit U)

theorem comp_eq (hU : IsUnf U) {k k' : U.Comp} (x : (U.X k).dom) (x' : (U.X k').dom)
    (hu : Uw.F.u (Uw.ik k) (Uw.Pm k x) = Uw.F.u (Uw.ik k') (Uw.Pm k' x'))
    (hex : ∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left = (Uw.F.ex (Uw.ik k') (Uw.Pm k' x') z).left) : k' = k := by
  have hbor := GlobalTheory.CompInj.frBor_of_eq (U.un k x) (U.un k' x')
    (((Uw.lie k' x').1.trans hu.symm).trans (Uw.lie k x).1.symm) fun τ i => by
      have h' := (Uw.lie k' x').2 τ i
      simp only [← hex] at h'
      exact ((GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo _ _ _ Uw.F _ _ (Uw.period k x)).2.1 _).unique h'
        ((Uw.lie k x).2 τ i)
  obtain ⟨gm, -, b, -, h⟩ := (hU.2.2.2.1 k k' _ _).1 hbor
  exact congrArg Sigma.fst h

theorem exists_move (hσ : GoodEmb c σ) (hU : IsUnf U) (hpr : GlobalTheory.FrameNorm.HasPrinc U l.M) (k : U.Comp)
    (x x' : (U.X k).dom) (hu : Uw.F.u (Uw.ik k) (Uw.Pm k x) = Uw.F.u (Uw.ik k) (Uw.Pm k x'))
    (hex : ∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left = (Uw.F.ex (Uw.ik k) (Uw.Pm k x') z).left) :
    ∃ gm ∈ (U.X k).Γ, ∃ b ∈ Bor (U.X k).Ψ r, x'.1 = rmul (lact gm x.1) b ∧ ∀ t t', Uw.Pm k x t = Uw.Pm k x' t' →
      (Uw.φ k t' : Fin r → E) = (gm : Matrix (Fin r) (Fin r) E) *ᵥ (Uw.φ k t : Fin r → E) := by
  obtain ⟨gam, hP, hiso, hM⟩ := exists_isometry Uw.F _ _ _ (Uw.period k x) (Uw.period k x') hu hex
  let φ : (Uw.F.Di (Uw.ik k)).La →ₗ[𝓞 E] (Fin r → E) := (U.X k).Λ.subtype ∘ₗ (Uw.φ k).toLinearMap
  have hrange : LinearMap.range φ = (U.X k).Λ := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]
  have hφ : Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ _ ∧ _ ∧ _ :=
    ⟨Subtype.val_injective.comp (Uw.φ k).injective, by rw [← LinearMap.coe_range, hrange]; exact (U.X k).Λ_span,
      (U.X k).Gm_herm, (U.X k).Gm_det, Uw.iso k⟩
  obtain ⟨gm, hgm, hgmφ⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry E H _ _ r (-(U.X k).ξ0) (U.X k).Gm φ φ gam
    (by rw [HermitianTraceFormVanishing.cc_neg, (U.X k).ξ0_im]) hφ hφ hiso
  have hg : ∀ a, (Uw.φ k (gam a) : Fin r → E) = (gm : Matrix (Fin r) (Fin r) E) *ᵥ (Uw.φ k a : Fin r → E) := hgmφ
  have hs : ∀ w ∈ (U.X k).Λ, ∃ a, (Uw.φ k a : Fin r → E) = w := fun w hw =>
    ⟨(Uw.φ k).symm ⟨w, hw⟩, by rw [LinearEquiv.apply_symm_apply]⟩
  have hΓ : gm ∈ (U.X k).Γ := by
    refine hpr k gm ⟨hgm, fun w => ⟨fun hw => ?_, fun hw => ?_⟩⟩ fun w hw => ?_
    · obtain ⟨a, rfl⟩ := hs w hw
      rw [← hg]
      exact (Uw.φ k _).2
    · obtain ⟨a, ha⟩ := hs _ hw
      obtain ⟨a, rfl⟩ := gam.surjective a
      rw [hg] at ha
      rw [← Matrix.mulVec_injective_iff_isUnit.2 gm.isUnit ha]
      exact (Uw.φ k _).2
    · obtain ⟨a, rfl⟩ := hs w hw
      obtain ⟨e, he⟩ := hM a
      refine ⟨_, (Uw.φ k e).2, ?_⟩
      rw [← hg, he, map_add, map_nsmul, Nat.cast_smul_eq_nsmul]
      simp
  have hy : lact gm x.1 ∈ (U.X k).dom := (AR.Up.PairUnfoldPf.lact_mem_dom_iff (U.X k) hΓ _).2 x.2
  obtain ⟨idx, -, -, hper⟩ := GlobalTheory.ArcFlow.exists_idx Uw hσ hU k
  have key : ∀ w ∈ (U.X k).Λ, ∀ j, perFr (U.X k) x'.1 w (relab c σ (Uw.e j).1) (Uw.e j).2 =
      perFr (U.X k) (lact gm x.1) w (relab c σ (Uw.e j).1) (Uw.e j).2 := fun w hw j => by
    obtain ⟨a, rfl⟩ := hs w hw
    obtain ⟨a, rfl⟩ := gam.surjective a
    rw [← Uw.Pm_eq, hP, hg, GlobalTheory.PerGam.perFr_lact _ gm hgm, Uw.Pm_eq]
  obtain ⟨b, hb, hxb⟩ := exists_bor (U.X k) hy x'.2 Dw.q
    (fun τ a ha => GlobalTheory.ArcFlow.eq_of_hermC_lattice (U.X k) τ.1 _ _ fun w hw => by
      have h1 := key w hw (idx.symm (τ, a))
      rw [hper, hper] at h1
      simpa only [Equiv.apply_symm_apply, if_pos ha] using h1)
    (fun τ a ha => row_eq_of_lattice (U.X k) τ.1 _ _ a fun w hw => by
      have h1 := key w hw (idx.symm (τ, a))
      rw [hper, hper] at h1
      simpa only [Equiv.apply_symm_apply, if_neg ha] using h1)
  refine ⟨gm, hΓ, b, hb, hxb, fun t t' ht => ?_⟩
  rw [← hg, (Uw.period k x').2.1 ((hP t).trans ht)]

theorem fj_eq_zero_iff_of_same_exp : Known → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (Uw : UnfWit U) (k k' : U.Comp) (x : (U.X k).dom) (x' : (U.X k').dom) (t : (Uw.F.Di (Uw.ik k)).La) (t' : (Uw.F.Di (Uw.ik k')).La) (a' : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (ν₀ : E), GoodEmb c σ → IsUnf U → GlobalTheory.FrameNorm.HasPrinc U l.M → Dom a' n → (∀ k, ∀ gm ∈ (U.X k).Γ, (U.X k).χ (laU U a' n k) gm = 1) → (U.X k).IsIso (Uw.φ k t : Fin r → E) → Uw.F.u (Uw.ik k) (Uw.Pm k x) = Uw.F.u (Uw.ik k') (Uw.Pm k' x') → (∀ z, (Uw.F.ex (Uw.ik k) (Uw.Pm k x) z).left = (Uw.F.ex (Uw.ik k') (Uw.Pm k' x') z).left) → Uw.Pm k x t = Uw.Pm k' x' t' → ∀ F ∈ sec Xo c a' n, ((U.X k).fj (laU U a' n k) (Uw.φ k t : Fin r → E) (fun τ => (τ.1 ν₀).re) (rdU U F k) x.1 = 0 ↔ (U.X k').fj (laU U a' n k') (Uw.φ k' t' : Fin r → E) (fun τ => (τ.1 ν₀).re) (rdU U F k') x'.1 = 0) := by
  intro _ E _ _ _ H Dw l Xo c σ r U Uw k k' x x' t t' a' n ν₀ hσ hU hpr hD hχ hiso hu hex ht F hF
  obtain rfl := comp_eq Uw hU x x' hu hex
  obtain ⟨gm, hgm, b, hb, hxb, hφ⟩ := exists_move Uw hσ hU hpr k' x x' hu hex
  rw [hφ t t' ht, hxb, fj_lact_rmul (U.X k') (hU.2.2.2.2.1 a' n hD F hF k') hgm hiso.2.1 _ x.2 hb, hχ k' gm hgm,
    _root_.mul_one,
    mul_eq_zero, or_iff_right (AR.Up.PairUnfoldPf.bchar_ne (U.X k') hb _)]

end GlobalTheory.FrameMatch
