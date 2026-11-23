import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormProdSignMulDetSubmatrixSubOneLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupLeOfBoundAtThickPoints
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsContinuousGramSchmidt
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul

open NumberField ReciprocityTheory.ChartRestriction.G.FD Topology

namespace GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace CuspNet

theorem transvMat_natCast_smul {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (v : Fin r → E) (n : ℕ)
    (α : E) : transvMat G ((n : E) • v) α = transvMat G v ((n : E) ^ 2 * α) := by
  ext a b
  have h : ∑ k, G b k * cc (((n : E) • v) k) = n * ∑ k, G b k * cc (v k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [cc, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
    ring
  simp only [transvMat, Matrix.of_apply, h]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_transvection_level {r : ℕ} (X : DataX E r) (la : Wt X.Ψ r) :
    ∃ M : ℝ, 0 < M ∧ ∀ v ∈ X.L', herm X.Gm v v = 0 → ∀ b : E, cc b = b → IsIntegral ℤ b →
      ∃ γ ∈ X.Γ, X.χ la γ = 1 ∧
        ∀ τ : X.Ψ, (γ : Matrix (Fin r) (Fin r) E).map τ.1 = X.flowMat v τ ((M : ℂ) * τ.1 b) := by
  obtain ⟨n, hn, hχ⟩ := X.χ_fin la
  have h1 := X.m_pos
  have h2 := X.NC_pos
  refine ⟨((X.m * X.NC ^ 2 * n : ℕ) : ℝ), by positivity, fun v hv hvv b hb hbi => ?_⟩
  have hξ : herm X.Gm ((X.NC : E) • v) ((X.NC : E) • v) = 0 := by
    have h : herm X.Gm ((X.NC : E) • v) ((X.NC : E) • v) = (X.NC : E) ^ 2 * herm X.Gm v v := by
      simp only [herm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      simp only [cc, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast]
      ring
    rw [h, hvv, mul_zero]
  obtain ⟨γ, hγ, hγm⟩ := X.transv _ (X.NC_sub v hv) hξ b hb hbi
  refine ⟨γ ^ n, pow_mem hγ n, ?_, fun τ => ?_⟩
  · rw [TransvectionPeriodicity.chi_pow X.toData la hγ, hχ γ hγ]
  · rw [Units.val_pow_eq_pow_val, hγm, transvMat_natCast_smul, TransvectionPeriodicity.transvMat_pow X.Gm hvv]
    refine TransvectionPeriodicity.transvMat_map X.toData v τ _ _ ?_
    simp only [map_mul, map_pow, map_natCast, TransvectionPeriodicity.emb_kappa]
    push_cast
    ring

theorem exists_firstMinimum_lower_bound_near_max {r : ℕ} (hr : 0 < r) (X : DataX E r) (la : Wt X.Ψ r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ P ∈ X.SS la, ∀ z ∈ X.dom,
      (∀ x ∈ X.dom, X.pnorm la P x ≤ 2 * X.pnorm la P z) → 0 < X.pnorm la P z → ε ≤ X.la1 z := by
  obtain ⟨M, hM, hT⟩ := exists_transvection_level X la
  have hsp : 0 ≤ ∑ τ, X.spread la τ :=
    Finset.sum_nonneg fun τ _ => flowTermNormDecay.spread_nonneg' X.toData la τ
  set w : ℝ := 1 + ∑ τ, X.spread la τ with hw
  have hw0 : 0 < w := by linarith
  have hk0 := X.minWeight_pos
  have hNA : (0 : ℝ) < X.NA := by exact_mod_cast X.NA_pos
  have hep : 0 < epStar M (fdeg E) w X.k0 := by
    have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hpi := Real.pi_pos
    exact lt_min one_pos (by positivity)
  refine ⟨Real.sqrt (X.k0 * epStar M (fdeg E) w X.k0 / (X.NA : ℝ) ^ 2), by positivity,
    fun P hP z hz hhalf hpos => ?_⟩
  have hmax := maxBound_holds r X la P M w hP hM (by linarith) hw0 hT z hz hhalf hpos
  have hc : ∀ τ : X.Ψ, X.c τ = X.k0 := fun τ => by
    simp only [Data.c]
    rw [X.ξ0_abs τ]
    ring
  refine Real.sqrt_le_sqrt (le_csInf ?_ ?_)
  · by_contra hne
    have hbot : ∀ v ∈ X.Λ, v = 0 := fun v hv => by
      by_contra hv0
      exact hne ⟨_, v, hv, hv0, rfl⟩
    have h1 : Submodule.span E (X.Λ : Set (Fin r → E)) = ⊥ := Submodule.span_eq_bot.2 hbot
    have h2 : (1 : Fin r → E) ∈ Submodule.span E (X.Λ : Set (Fin r → E)) := by
      rw [X.Λ_span]; exact Submodule.mem_top
    rw [h1, Submodule.mem_bot] at h2
    exact one_ne_zero (congrFun h2 ⟨0, hr⟩)
  · rintro _ ⟨v, hv, hv0, rfl⟩
    have hpos : ∀ τ : X.Ψ, 0 < X.maj z τ (Data.emb τ.1 v) := fun τ => by
      refine X.maj_pos hz τ fun h => hv0 ?_
      funext a
      have := congr_fun h a
      simpa [Data.emb] using this
    obtain ⟨τ, hτ⟩ := hmax ((X.NA : E) • v) (X.NA_sub v hv)
      (smul_ne_zero (Nat.cast_ne_zero.2 X.NA_pos.ne') hv0)
    have he : Data.emb τ.1 ((X.NA : E) • v) = (X.NA : ℂ) • Data.emb τ.1 v := by
      funext a
      simp [Data.emb]
    rw [he, maj_complex_smul_normSq, Complex.norm_natCast] at hτ
    calc X.k0 * epStar M (fdeg E) w X.k0 / (X.NA : ℝ) ^ 2
        ≤ X.c τ * X.maj z τ (Data.emb τ.1 v) := by
          rw [div_le_iff₀ (by positivity), hc]
          nlinarith
      _ ≤ ∑ τ, X.c τ * X.maj z τ (Data.emb τ.1 v) :=
          Finset.single_le_sum (f := fun τ : X.Ψ => X.c τ * X.maj z τ (Data.emb τ.1 v))
            (fun σ _ => by rw [hc]; exact (mul_pos hk0 (hpos σ)).le) (Finset.mem_univ τ)

theorem exists_finset_rmul_near_one {r : ℕ} (X : Data E r) {K : Set (Frame X.Ψ r)}
    (hK : IsCompact K) (hKd : K ⊆ X.dom) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : Finset (Frame X.Ψ r), (∀ y ∈ N, y ∈ K) ∧ ∀ x ∈ K, ∃ A : Frame X.Ψ r,
      (∀ τ a b, ‖A τ a b - (if a = b then 1 else 0)‖ ≤ δ) ∧ rmul x A ∈ N := by
  obtain ⟨N, hN, hcov⟩ := hK.elim_nhdsWithin_subcover
    (fun y => {x | ∀ τ a b, ‖((mat x τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖ ≤ δ})
    (fun y hy => by
      simp only [Set.ofPred_forall]
      refine Filter.iInter_mem.2 fun τ => Filter.iInter_mem.2 fun a =>
        Filter.iInter_mem.2 fun b => ?_
      have hc : ContinuousOn (fun x : Frame X.Ψ r =>
          ‖((mat x τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖) K := by
        refine (ContinuousOn.sub ?_ continuousOn_const).norm
        simp only [Matrix.mul_apply]
        refine continuousOn_finsetSum _ fun k _ => ContinuousOn.mul ?_ continuousOn_const
        exact GramSchmidtCont.continuousOn_inv_apply (GramSchmidtCont.continuous_mat X τ)
          (fun x hx => (hKd hx τ).1) a k
      have h0 : ‖((mat y τ)⁻¹ * mat y τ) a b - (if a = b then 1 else 0)‖ < δ := by
        rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hKd hy τ).1), Matrix.one_apply,
          sub_self, norm_zero]
        exact hδ
      exact (hc y hy).eventually (eventually_le_nhds h0))
  refine ⟨N, hN, fun x hx => ?_⟩
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (hcov hx)
  refine ⟨fun τ => ((mat x τ)⁻¹ * mat y τ : Matrix (Fin r) (Fin r) ℂ), hxy, ?_⟩
  convert hy using 1
  funext τ
  show mat x τ * ((mat x τ)⁻¹ * mat y τ) = mat y τ
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ (isUnit_iff_ne_zero.2 (hKd hx τ).1)]

theorem continuousOn_rmul_bOf {r : ℕ} (X : Data E r) :
    ContinuousOn (fun x => rmul x (FrameDegreeData.bOf X x)) X.dom := by
  refine continuousOn_pi.2 fun τ => ?_
  exact (GramSchmidtCont.continuous_mat X τ).continuousOn.mul
    ((GramSchmidtCont.continuous_mat X τ).comp_continuousOn (GramSchmidtCont.continuousOn_bOf X))

end CuspNet

theorem ss_finite_dimensional (hM2 : MahlerCompactnessCriterion (E := E)) {r : ℕ} (X : DataX E r) (la : Wt X.Ψ r) :
    ∃ N : Finset (Frame X.Ψ r), (∀ y ∈ N, y ∈ X.dom) ∧ ∀ P ∈ X.SS la, ∀ x ∈ X.dom, ∃ y ∈ N, X.pnorm la P x ≤ 4 * X.pnorm la P y := by
  classical
  rcases X.dom.eq_empty_or_nonempty with hdom | ⟨x0, hx0⟩
  · exact ⟨∅, by simp, fun P _ x hx => by simp [hdom] at hx⟩
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · refine ⟨{x0}, by simpa using hx0, fun P _ x _ => ⟨x0, Finset.mem_singleton_self _, ?_⟩⟩
    rw [Subsingleton.elim x x0]
    linarith [BoundedSectionAlgebra.pnorm_nonneg X.toData la P x0]
  obtain ⟨ε, hε, hthick⟩ := CuspNet.exists_firstMinimum_lower_bound_near_max hr X la
  obtain ⟨K, hK, hKd, hKm⟩ := hM2 r X.toData ε hε
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hK'd : (fun x => rmul x (FrameDegreeData.bOf X.toData x)) '' K ⊆ X.dom := by
    rintro _ ⟨x, hx, rfl⟩
    exact OrthogonalFrameDomain.rmul_mem_dom X.toData (hKd hx) (FrameDegreeData.bOf_mem X.toData (hKd hx))
  obtain ⟨N, hN, hnet⟩ := CuspNet.exists_finset_rmul_near_one X.toData
    (hK.image_of_continuousOn ((CuspNet.continuousOn_rmul_bOf X.toData).mono hKd)) hK'd
    (δ := 1 / (1000 * (r : ℝ) ^ 2 * (1 + ∑ τ, ∑ i, |(la τ i : ℝ)|))) (by positivity)
  refine ⟨insert x0 N, fun y hy => ?_, fun P hP x hx => ?_⟩
  · rcases Finset.mem_insert.1 hy with rfl | hy
    · exact hx0
    · exact hK'd (hN y hy)
  by_cases hx' : X.pnorm la P x ≤ 0
  · exact ⟨x0, Finset.mem_insert_self _ _, by linarith [BoundedSectionAlgebra.pnorm_nonneg X.toData la P x0]⟩
  push Not at hx'
  obtain ⟨C, hC⟩ := hP.1.2
  set T : Set ℝ := (fun y => X.pnorm la P y) '' X.dom with hT
  have hbdd : BddAbove T := ⟨C, by rintro _ ⟨y, hy, rfl⟩; exact hC y hy⟩
  have hne : T.Nonempty := ⟨_, x, hx, rfl⟩
  have hle : ∀ y ∈ X.dom, X.pnorm la P y ≤ sSup T := fun y hy => le_csSup hbdd ⟨y, hy, rfl⟩
  have hxS := hle x hx
  have hhalf : sSup T / 2 < sSup T := by linarith
  obtain ⟨_, ⟨z, hz, rfl⟩, hzS⟩ := exists_lt_of_lt_csSup hne hhalf
  have hzS' : sSup T / 2 < X.pnorm la P z := hzS
  obtain ⟨γ, hγ, b, hb, hk⟩ := hKm z hz
    (hthick P hP z hz (fun y hy => by have := hle y hy; linarith) (by linarith))
  have h1 := NormFactor.pnormInv_holds r X.toData la P hP.1.1 γ hγ z hz b hb
  set k := lact γ (rmul z b) with hkdef
  have hkd := hKd hk
  have h2 := FrameDegreeData.pnorm_rmul X.toData la P hP.1.1.2.1 k hkd _ (FrameDegreeData.bOf_mem X.toData hkd)
  obtain ⟨A, hA, hAN⟩ := hnet _ ⟨k, hk, rfl⟩
  have h3 := (pnorm_near_half_max X.toData la P hP.1.1.1 (sSup T) hle _
    (FrameDegreeData.ortho_bOf X.toData hkd) (by rw [h2, h1]; exact hzS'.le) A hA).2
  exact ⟨_, Finset.mem_insert_of_mem hAN, by linarith⟩

namespace CuspNet

theorem span_restrict_ss_eq {r : ℕ} (X : Data E r) (la : Wt X.Ψ r) {f : X.dom → ℂ}
    (hf : f ∈ Submodule.span ℂ ((fun P : Frame X.Ψ r → ℂ => X.dom.domRestrict P) '' X.SS la)) :
    ∃ P ∈ X.SS la, X.dom.domRestrict P = f := by
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X la la 0
  induction hf using Submodule.span_induction with
  | mem f hf => exact hf
  | zero => exact ⟨0, h0, rfl⟩
  | add f g _ _ hf hg =>
    obtain ⟨P, hP, rfl⟩ := hf
    obtain ⟨Q, hQ, rfl⟩ := hg
    exact ⟨P + Q, hadd P hP Q hQ, rfl⟩
  | smul a f _ hf =>
    obtain ⟨P, hP, rfl⟩ := hf
    exact ⟨a • P, hsmul a P hP, rfl⟩

theorem rank_span_restrict_ss_le {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (N : Finset (Frame X.Ψ r)) (hN : ∀ y ∈ N, y ∈ X.dom) {C : ℝ}
    (hb : ∀ P ∈ X.SS la, ∀ x ∈ X.dom, ∃ y ∈ N, X.pnorm la P x ≤ C * X.pnorm la P y) :
    Module.rank ℂ (Submodule.span ℂ
      ((fun P : Frame X.Ψ r → ℂ => X.dom.domRestrict P) '' X.SS la)) ≤ N.card := by
  set V := Submodule.span ℂ ((fun P : Frame X.Ψ r → ℂ => X.dom.domRestrict P) '' X.SS la) with hV
  let ev : V →ₗ[ℂ] (N → ℂ) :=
    (LinearMap.funLeft ℂ ℂ fun y : N => (⟨y.1, hN y.1 y.2⟩ : X.dom)).comp V.subtype
  have hinj : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨f, hf⟩ h0
    obtain ⟨P, hP, rfl⟩ := span_restrict_ss_eq X la hf
    refine Subtype.ext (funext fun x => ?_)
    obtain ⟨y, hy, hxy⟩ := hb P hP x.1 x.2
    have hPy : P y = 0 := congrFun h0 ⟨y, hy⟩
    have h1 : X.pnorm la P y = 0 := by simp [Data.pnorm, hPy]
    rw [h1, mul_zero] at hxy
    have h2 : ‖P x.1‖ * X.nfac la x.1 ≤ 0 := hxy
    have h3 := flowTermNormDecay.nfac_pos X la x.2
    have h4 : ‖P x.1‖ ≤ 0 := by
      by_contra h
      push Not at h
      linarith [mul_pos h h3]
    exact norm_le_zero_iff.1 h4
  have h := LinearMap.rank_le_of_injective ev hinj
  simpa using h

end CuspNet

theorem ss_card_le_of_linearIndependent (hM2 : MahlerCompactnessCriterion (E := E)) {r : ℕ} (X : DataX E r)
    (la : Wt X.Ψ r) :
    ∃ N : Finset (Frame X.Ψ r), (∀ y ∈ N, y ∈ X.dom) ∧
      (∀ P ∈ X.SS la, ∀ x ∈ X.dom, ∃ y ∈ N, X.pnorm la P x ≤ 4 * X.pnorm la P y) ∧
      (∀ (ι : Type) (P : ι → Frame X.Ψ r → ℂ), (∀ i, P i ∈ X.SS la) →
        LinearIndependent ℂ (fun i => X.dom.domRestrict (P i)) → Cardinal.mk ι ≤ N.card) ∧
      FiniteDimensional ℂ (Submodule.span ℂ
        ((fun P : Frame X.Ψ r → ℂ => X.dom.domRestrict P) '' X.SS la)) ∧
      Module.finrank ℂ (Submodule.span ℂ
        ((fun P : Frame X.Ψ r → ℂ => X.dom.domRestrict P) '' X.SS la)) ≤ N.card := by
  obtain ⟨N, hN, hb⟩ := ss_finite_dimensional hM2 X la
  have hrk := CuspNet.rank_span_restrict_ss_le X.toData la N hN hb
  refine ⟨N, hN, hb, fun ι P hP hli => ?_, ?_, Module.finrank_le_of_rank_le hrk⟩
  · refine le_trans ?_ hrk
    have h : LinearIndependent ℂ (fun i => (⟨X.dom.domRestrict (P i),
        Submodule.subset_span ⟨P i, hP i, rfl⟩⟩ : Submodule.span ℂ
          ((fun P : Frame X.Ψ r → ℂ => X.dom.domRestrict P) '' X.SS la))) :=
      LinearIndependent.of_comp (Submodule.subtype _) hli
    exact h.cardinal_le_rank
  · exact Module.rank_lt_aleph0_iff.1 (hrk.trans_lt (Cardinal.natCast_lt_aleph0))

end GlobalTheory
