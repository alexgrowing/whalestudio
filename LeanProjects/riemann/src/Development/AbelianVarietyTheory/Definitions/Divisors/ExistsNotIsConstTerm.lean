import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ContDiff

namespace GlobalTheory.UAut.Model

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem foldr_char {φ : GAd σ J → ℂ} (hφ : ∀ g h, φ (g * h) = φ g * φ h) (l : List (ℝ → GAd σ J)) :
    ∃ c : ℂ, l.foldr lineDer φ = c • φ := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons γ l ih =>
    obtain ⟨c, h⟩ := ih
    refine ⟨c * deriv (fun t => φ (γ t)) 0, ?_⟩
    rw [List.foldr_cons, h]
    funext g
    simp only [lineDer, Pi.smul_apply, smul_eq_mul, hφ, ← mul_assoc, deriv_const_mul_field']
    ring

theorem isAut_char (K : Subgroup (GAd σ J)) {φ : GAd σ J → ℂ} (hφ : ∀ g h, φ (g * h) = φ g * φ h)
    (hm : IsSmoothModerate σ J φ) : IsAut σ J K φ := by
  refine ⟨hm, ?_, ?_⟩ <;> refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
  · rintro _ ⟨k, rfl⟩
    exact Submodule.mem_span_singleton.2 ⟨φ k, funext fun g => by simp [hφ, mul_comm]⟩
  · rintro _ ⟨z, -, rfl⟩
    choose c hc using foldr_char hφ
    exact Submodule.mem_span_singleton.2 ⟨z.sum fun l a => a * c l, funext fun g => by
      simp [dop, hc, Finsupp.sum, Finset.sum_mul, mul_assoc]⟩

theorem isAut_one (K : Subgroup (GAd σ J)) : IsAut σ J K fun _ => 1 :=
  isAut_char K (by simp) (isSmoothModerate_const σ J 1)

theorem exists_central_line (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w) :
    ∃ γ : ℝ → GAd σ J, IsCentral σ J (Finsupp.single [γ] 1) ∧
      ∀ t : ℝ, archMat σ J τ (projArch σ J w (γ t)) = NormedSpace.exp (t • (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))) := by
  have hZ : (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * J.map τ.1 + J.map τ.1 * (Complex.I • 1) = 0 := by
    simp [conjTranspose_smul]
  obtain ⟨γ, -, hγ⟩ := exists_isRealLine h hJ τ hZ
  have inj : Function.Injective (archMat σ J τ) := fun a b e => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
    exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))
  have hc : ∀ t a, embArch σ J w (projArch σ J w (γ t)) * a = a * embArch σ J w (projArch σ J w (γ t)) := fun t a => by
    refine GAd_ext σ J (fun u => ?_) fun v => by simp
    by_cases e : u = w
    · subst e
      apply inj
      simp only [map_mul, projArch_embArch_self, hγ]
      refine (Commute.exp_left ?_).eq
      exact ((Commute.one_left _).smul_left _).smul_left _
    · simp [projArch_embArch_ne σ J e]
  refine ⟨fun t => embArch σ J w (projArch σ J w (γ t)), ⟨?_, fun f _ a _ g => ?_⟩, fun t => by simp [hγ]⟩
  · intro l hl δ hδ
    obtain rfl : l = _ := by simpa using hl
    obtain rfl : δ = _ := by simpa using hδ
    exact ⟨w, τ, _, hZ, fun t => ⟨_, rfl, hγ t⟩⟩
  · simp [dop, lineDer, mul_assoc, hc]

theorem isConstTerm_const {r : ℕ} (C : Matrix (Fin n) (Fin r) E) (c : ℂ) : IsConstTerm σ J C (fun _ => c) fun _ => c :=
  fun μ 𝓕 _ _ h _ => by simp [Measure.real, h]

theorem isConstTerm_zero {r : ℕ} {C : Matrix (Fin n) (Fin r) E} {φ : GAd σ J → ℂ} (h : IsCuspidal σ J φ)
    (hC : 0 < r ∧ LinearIndependent E C.transpose ∧ Formalism.UG.cT (σ : E →+* E) C * J * C = 0) :
    IsConstTerm σ J C φ 0 := fun μ 𝓕 h1 h2 _ g => (h r C hC μ 𝓕 h1 h2 g).symm

theorem exists_not_isConstTerm (h : ¬ IsCuspidal σ J fun _ => 1) :
    ∃ (r : ℕ) (C : Matrix (Fin n) (Fin r) E), 0 < r ∧ Formalism.UG.cT (σ : E →+* E) C * J * C = 0 ∧
      ¬ IsConstTerm σ J C (fun _ => 1) 0 := by
  simp only [IsCuspidal, not_forall] at h
  obtain ⟨r, C, hC, μ, 𝓕, h1, h2, g, h3⟩ := h
  have h4 : μ.real 𝓕 ≠ 0 := fun e => h3 (by simp [e])
  have h5 : μ 𝓕 ≠ 0 := fun e => h4 (by simp [Measure.real, e])
  have h6 : μ 𝓕 ≠ ⊤ := fun e => h4 (by simp [Measure.real, e])
  refine ⟨r, C, hC.1, hC.2.2, fun H => ?_⟩
  have h7 : ((μ 𝓕)⁻¹ • μ) 𝓕 = 1 := by simp [ENNReal.inv_mul_cancel h5 h6]
  have := H ((μ 𝓕)⁻¹ • μ) 𝓕 (Measure.IsHaarMeasure.smul μ (ENNReal.inv_ne_zero.2 h6) (ENNReal.inv_ne_top.2 h5))
    (h2.mono Measure.smul_absolutelyContinuous) h7 g
  exact h4 (by simpa [Measure.real, h6] using this)

example (D : Formalism.BasicNotions.D7) : ∃ (r : ℕ) (C : Matrix _ (Fin r) D.host.E), 0 < r ∧
    ¬ IsConstTerm D.sp.cm.sig (GlobalTheory.CuspDecay.Model.plane D).gram C (fun _ => 1) 0 := by
  obtain ⟨r, C, h, -, h'⟩ := exists_not_isConstTerm (σ := D.sp.cm.sig) (J := (GlobalTheory.CuspDecay.Model.plane D).gram)
    (GlobalTheory.CuspDecay.Model.not_isCuspFun_one_plane D)
  exact ⟨r, C, h, h'⟩

theorem isMaxCpt_infPts (h : IsCompact (infPts σ J : Set (GAd σ J))) : IsMaxCpt σ J (infPts σ J) :=
  ⟨⟨le_rfl, h⟩, fun _ hK _ => hK.1⟩

theorem isSqInt_of_bounded (hP : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    [Countable (ratPts σ J)] {φ : GAd σ J → ℂ} (hc : Continuous φ) {M : ℝ} (hM : ∀ g, ‖φ g‖ ≤ M) : IsSqInt σ J φ := by
  intro μ 𝓕 h1 h2
  obtain ⟨S, hS, hcov, -, hμ, -⟩ := exists_cover hP h hJ
  have hle : μ 𝓕 ≤ μ S := by
    rw [h2.measure_eq_tsum S]
    refine le_trans (measure_mono fun g hg => ?_) (measure_iUnion_le _)
    obtain ⟨γ, hγ, s, hs, rfl⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨s, hs, rfl⟩, hg⟩
  refine Measure.integrableOn_of_bounded (M := M ^ 2) (hle.trans_lt (hμ μ h1)).ne
    (hc.norm.pow 2).aestronglyMeasurable (.of_forall fun g => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hM g) 2

theorem exists_exp (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) : ∃ Z : Matrix (Fin n) (Fin n) ℂ, ∀ t : ℝ,
      archMat σ J τ (projArch σ J w (γ t)) = NormedSpace.exp (t • Z) := by
  obtain ⟨u, τ', Z, -, hZ⟩ := hγ
  by_cases e : w = u
  · subst e
    rcases infEmb_eq_or_conj h τ' τ with e | e
    · refine ⟨Z, fun t => ?_⟩
      obtain ⟨y, e1, e2⟩ := hZ t
      rw [e1, projArch_embArch_self, ← e2, GlobalTheory.Orb.archMat_apply, GlobalTheory.Orb.archMat_apply, e]
    · refine ⟨(starRingEnd ℂ).mapMatrix Z, fun t => ?_⟩
      obtain ⟨y, e1, e2⟩ := hZ t
      rw [show t • (starRingEnd ℂ).mapMatrix Z = (starRingEnd ℂ).mapMatrix (t • Z) from Matrix.ext fun i j => by simp,
        ← conj_exp, e1, projArch_embArch_self, ← e2, GlobalTheory.Orb.archMat_apply, GlobalTheory.Orb.archMat_apply, e]
      rfl
  · refine ⟨0, fun t => ?_⟩
    obtain ⟨y, e1, -⟩ := hZ t
    simp [e1, projArch_embArch_ne σ J e]

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem isSm_entry (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (i j : Fin n) :
    IsSm σ J fun g => archMat σ J τ (projArch σ J w g) i j := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  intro k γ hγ g
  choose Z hZ using fun a => exists_exp h τ (hγ a)
  have key : ∀ l : List (Fin k), ContDiff ℝ ∞ fun t : Fin k → ℝ =>
      archMat σ J τ (projArch σ J w (l.map fun a => γ a (t a)).prod) := fun l => by
    induction l with
    | nil => simpa using contDiff_const
    | cons a l ih =>
      simp only [List.map_cons, List.prod_cons, map_mul, hZ]
      refine ContDiff.mul ?_ ih
      have : ContDiff ℝ ∞ (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) :=
        contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
      exact this.comp ((contDiff_apply ℝ ℝ a).smul contDiff_const)
  simp only [List.ofFn_eq_map, map_mul]
  exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)).contDiff.comp
    (contDiff_const.mul (key _))

theorem commute_of_isCentral (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {γ : ℝ → GAd σ J}
    {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : ∀ t : ℝ, archMat σ J τ (projArch σ J w (γ t)) = NormedSpace.exp (t • Z))
    (hc : IsCentral σ J (Finsupp.single [γ] 1)) (y : GArch σ J w) :
    Z * archMat σ J τ y = archMat σ J τ y * Z := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  ext i j
  have h1 := hc.2 _ (isSm_entry h τ i j) (embArch σ J w y) ((mem_infPts).2 (projFin_embArch σ J w y)) 1
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) Z 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
    exact this
  let L := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ)
  have d1 := (L.hasFDerivAt.comp_hasDerivAt 0 (hd.mul_const (archMat σ J τ y))).deriv
  have d2 := (L.hasFDerivAt.comp_hasDerivAt 0 (hd.const_mul (archMat σ J τ y))).deriv
  simp only [dop, Finsupp.sum_single_index, zero_mul, one_mul, List.foldr_cons, List.foldr_nil, lineDer, map_mul, hZ,
    projArch_embArch_self] at h1
  exact d1.symm.trans (h1.trans d2)

theorem line_mem_infPts {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (t : ℝ) : γ t ∈ infPts σ J := by
  obtain ⟨w, τ, Z, -, hZ⟩ := hγ
  obtain ⟨y, e, -⟩ := hZ t
  exact e ▸ mem_infPts.2 (projFin_embArch σ J w y)

theorem isAut_of_open {U K : Subgroup (GAd σ J)} (hU : IsOpen (U : Set (GAd σ J))) (hi : infPts σ J ≤ U)
    (hK : K ≤ infPts σ J) {φ : GAd σ J → ℂ} (hl : ∀ γ ∈ ratPts σ J, ∀ g, φ (γ * g) = φ g)
    (hr : ∀ u ∈ U, ∀ g, φ (g * u) = φ g) (hb : ∀ g, ‖φ g‖ ≤ 1) : IsAut σ J K φ := by
  have key : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∃ b : ℂ, l.foldr lineDer φ = b • φ := fun l hl => by
    induction l with
    | nil => exact ⟨1, by simp⟩
    | cons γ l ih =>
      obtain ⟨b, h⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
      refine ⟨0, ?_⟩
      rw [List.foldr_cons, h]
      funext g
      simp [lineDer, hr _ (hi (line_mem_infPts (hl γ List.mem_cons_self) _))]
  refine ⟨⟨hl, ⟨U, hU, fun k hk _ => hr k hk⟩, ?_, fun k γ hγ g => ?_, 0, fun l hl' => ?_⟩, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun g => (continuousAt_const (y := φ g)).congr ?_
    have : {x | g⁻¹ * x ∈ U} ∈ nhds g :=
      (hU.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
    filter_upwards [this] with x hx
    rw [← hr _ hx g, mul_inv_cancel_left]
  · have : ∀ t : Fin k → ℝ, (List.ofFn fun i => γ i (t i)).prod ∈ U := fun t =>
      list_prod_mem fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact hi (line_mem_infPts (hγ i) _)
    simp only [hr _ (this _)]
    exact contDiff_const
  · obtain ⟨b, e⟩ := key l hl'
    exact ⟨‖b‖, fun g => by simpa [e] using mul_le_of_le_one_right (norm_nonneg b) (hb g)⟩
  · exact kfin_iff.2 (GlobalTheory.Doubling.IsKFinite.of_invariant fun g k hk => hr k (hi (hK hk)) g)
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {φ}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    have : dop z φ = ∑ l ∈ z.support, z l • l.foldr lineDer φ := funext fun g => by simp [dop, Finsupp.sum]
    rw [this]
    refine sum_mem fun l hl => Submodule.smul_mem _ _ ?_
    obtain ⟨b, e⟩ := key l (hz.1 l hl)
    exact e ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem infinite_fin (K : Type) [Field K] [NumberField K] : Infinite (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

omit [NumberField E] in
theorem ratLoc_inj (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Function.Injective (ratLoc σ J v) := fun a b h =>
  Subtype.ext (Units.ext (Matrix.ext fun r s => (inclR (F := F) (E := E) (Fv F v)).injective
    (congrArg (fun x => (HA.mat _ _ _ x).1 r s) h)))

theorem exists_isAut_nonconst (hn : 0 < n) (hc : IsCompact (infPts σ J : Set (GAd σ J))) :
    ∃ φ : GAd σ J → ℂ, (∀ K ≤ infPts σ J, IsAut σ J K φ) ∧ φ 1 = 1 ∧ ∃ g, φ g = 0 := by
  classical
  haveI := infinite_fin F
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin σ J
  obtain ⟨v, v', hv⟩ := exists_pair_ne (IsDedekindDomain.HeightOneSpectrum (𝓞 F))
  let m : GRat σ J := ⟨-1, show _ * _ * _ = _ by
    ext i j; simp [Formalism.UG.cT, Matrix.mul_apply, Matrix.one_apply, apply_ite]⟩
  have hm : m ≠ 1 := fun e => by
    have := congrArg (fun x : GRat σ J => x.1.1 ⟨0, hn⟩ ⟨0, hn⟩) e
    norm_num [m] at this
  let g₀ := emb σ J v (ratLoc σ J v m)
  let S : Set (GAd σ J) := Set.image2 (· * ·) (ratPts σ J : Set (GAd σ J)) (infPts σ J : Set (GAd σ J))
  have hS : IsClosed S := IsClosed.mul_right_of_isCompact Subgroup.isClosed_of_discrete hc
  have h0 : g₀ ∉ S := by
    rintro ⟨γ, hγ, a, ha, e⟩
    obtain ⟨γ, rfl⟩ : γ ∈ (ratEmb σ J).range := range_ratEmb σ J ▸ hγ
    have e1 := congrArg (proj σ J v') e
    have e2 := congrArg (proj σ J v) e
    simp only [g₀, map_mul, mem_infPts_iff_forall.1 ha _, proj_ratEmb, mul_one, proj_emb_ne σ J hv.symm,
      proj_emb_self] at e1 e2
    exact hm ((ratLoc_inj v e2).symm.trans (ratLoc_inj v' (e1.trans (map_one _).symm)))
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean {y : GFin σ J | g₀ * ofFin σ J y ∈ Sᶜ}
    ((hS.isOpen_compl.preimage (continuous_const.mul (continuous_ofFin σ J))).mem_nhds (by simpa using h0))
  let U : Subgroup (GAd σ J) := (V : Subgroup (GFin σ J)).comap (projFin σ J)
  let T : Set (GAd σ J) := {g | ∃ γ ∈ ratPts σ J, γ * g ∈ U}
  refine ⟨fun g => if g ∈ T then 1 else 0, fun K hK => isAut_of_open (U := U)
    (V.isOpen.preimage (continuous_projFin σ J)) (fun a ha => ?_) hK (fun γ hγ g => ?_) (fun u hu g => ?_)
    fun g => by split_ifs <;> simp, if_pos ⟨1, one_mem _, by simp⟩, g₀, if_neg ?_⟩
  · change projFin σ J a ∈ (V : Subgroup (GFin σ J))
    rw [mem_infPts.1 ha]; exact one_mem _
  · refine if_congr ⟨fun ⟨δ, hδ, h⟩ => ⟨δ * γ, mul_mem hδ hγ, by rwa [mul_assoc]⟩,
      fun ⟨δ, hδ, h⟩ => ⟨δ * γ⁻¹, mul_mem hδ (inv_mem hγ), by simpa [mul_assoc] using h⟩⟩ rfl rfl
  · exact if_congr (exists_congr fun δ => and_congr_right fun _ => by
      rw [← mul_assoc]; exact U.mul_mem_cancel_right hu) rfl rfl
  · rintro ⟨δ, hδ, h⟩
    refine hV (show (projFin σ J (δ * g₀))⁻¹ ∈ V from V.toSubgroup.inv_mem h)
      ⟨δ⁻¹, inv_mem hδ, δ * g₀ * ofFin σ J (projFin σ J (δ * g₀))⁻¹, mem_infPts.2 (by simp only [map_mul _ (δ * g₀), projFin_ofFin, mul_inv_cancel]), ?_⟩
    simp only [mul_assoc, inv_mul_cancel_left]

theorem isCompact_infPts_one (h : IsCMExt F E σ) :
    IsCompact (infPts σ (1 : Matrix (Fin n) (Fin n) E) : Set (GAd σ (1 : Matrix (Fin n) (Fin n) E))) := by
  have h1 := (isMaxCpt_majCpt (J := (1 : Matrix (Fin n) (Fin n) E)) h (c := fun _ => 1)
    fun w => ⟨fun _ => true, by simp [JR, Formalism.UG.cT_one]⟩).1.2
  convert h1 using 2
  ext g
  rw [mem_majCpt]
  refine (and_iff_left fun w => ?_).symm
  rw [mem_stabArch, inv_one, one_mul, mul_one]
  have := (projArch σ 1 w g).2
  simp only [HR, JR, Matrix.map_one _ (map_zero _) (map_one _)] at this
  exact this

theorem exists_nonconst_one (h : IsCMExt F E σ) (hn : 0 < n) : ∃ K φ, IsMaxCpt σ (1 : Matrix (Fin n) (Fin n) E) K ∧
    IsAut σ 1 K φ ∧ ∃ g, φ g ≠ φ 1 := by
  obtain ⟨φ, h1, h2, g, h3⟩ := exists_isAut_nonconst hn (isCompact_infPts_one h)
  exact ⟨_, φ, isMaxCpt_infPts (isCompact_infPts_one h), h1 _ le_rfl, g, by simp [h2, h3]⟩

theorem hasDerivAt_entry {Z : Matrix (Fin n) (Fin n) ℂ} (P A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (P * NormedSpace.exp (t • Z) * A) i j) ((P * Z * A) i j) 0 := by
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) Z 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
    rw [zero_smul, NormedSpace.exp_zero, one_mul] at this
    exact this
  let L := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ)
  exact L.hasFDerivAt.comp_hasDerivAt 0 ((hd.const_mul P).mul_const A)

theorem entry_le_opNorm (A : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖A i j‖₊ ≤ opNorm A := by
  unfold opNorm
  have h1 : (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ d, A i d * (EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (Fin n)) d = A i j
    simp [EuclideanSpace.single_apply]
  have h2 := ContinuousLinearMap.le_opNNNorm (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A) (EuclideanSpace.single j 1)
  rw [PiLp.nnnorm_single, nnnorm_one, mul_one] at h2
  rw [← h1]
  exact (PiLp.nnnorm_apply_le _ i).trans h2

theorem isAutOn_entry (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (K : Subgroup (GAd σ J)) (i j : Fin n) :
    IsAutOn σ J ⊥ K fun g => archMat σ J τ (projArch σ J w g) i j := by
  let M : GAd σ J →* Matrix (Fin n) (Fin n) ℂ := (archMat σ J τ).comp (projArch σ J w)
  have key : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → ∃ A : Matrix (Fin n) (Fin n) ℂ,
      l.foldr lineDer (fun g => M g i j) = fun g => (M g * A) i j := fun l hl => by
    induction l with
    | nil => exact ⟨1, by simp⟩
    | cons γ l ih =>
      obtain ⟨A, e⟩ := ih fun δ hδ => hl δ (List.mem_cons_of_mem _ hδ)
      obtain ⟨Z, hZ⟩ := exists_exp h τ (hl γ List.mem_cons_self)
      refine ⟨Z * A, ?_⟩
      rw [List.foldr_cons, e]
      funext g
      have : ∀ t, M (γ t) = _ := hZ
      simp only [lineDer, map_mul, this]
      rw [(hasDerivAt_entry _ _ i j).deriv, Matrix.mul_assoc]
  let W : Submodule ℂ (GAd σ J → ℂ) := Submodule.span ℂ (Set.range fun k g => M g i k)
  have hW : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have mem : ∀ A : Matrix (Fin n) (Fin n) ℂ, (fun g => (M g * A) i j) ∈ W := fun A => by
    have : (fun g => (M g * A) i j) = ∑ k, A k j • fun g => M g i k := funext fun g => by
      simp [Matrix.mul_apply, mul_comm]
    rw [this]
    exact sum_mem fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hb : ∀ g k, ‖M g i k‖ ≤ height σ J g := fun g k =>
    ((entry_le_opNorm _ i k).trans (((normInf_le_iff F w).1 (le_htOf _ _) τ).trans (htInf_le_height σ J w g)) :)
  refine ⟨fun γ hγ g => by rw [Subgroup.mem_bot.1 hγ, one_mul], ⟨⊤, isOpen_univ, fun k _ hk g => ?_⟩, ?_,
    isSm_entry h τ i j, ⟨1, fun l hl => ?_⟩, GlobalTheory.Doubling.isKFinite_iff.2 ⟨W, hW, fun k _ => ?_⟩, ?_⟩
  · simp [mem_finPts_iff_forall.1 hk w]
  · have : IsTopologicalRing (w.Completion ⊗[F] E) := GlobalTheory.Doubling.isTopologicalRing_tens
    exact ((Units.continuous_val.comp ((isEmbedding_matHom _ σ J).continuous.comp
      (continuous_projArch σ J w))).matrix_map (GlobalTheory.Orb.continuous_infEmb τ)).matrix_elem i j
  · obtain ⟨A, e⟩ := key l hl
    refine ⟨∑ k, ‖A k j‖, fun g => ?_⟩
    change ‖l.foldr lineDer (fun g => M g i j) g‖ ≤ _
    rw [e, pow_one, Finset.sum_mul]
    simp only [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hb g k) (norm_nonneg _)
  · simpa only [M, MonoidHom.comp_apply, map_mul] using mem (M k)
  · refine Submodule.finiteDimensional_of_le (S₂ := W) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    have : dop z (fun g => M g i j) = ∑ l ∈ z.support, z l • l.foldr lineDer (fun g => M g i j) :=
      funext fun g => by simp [dop, Finsupp.sum]
    change dop z (fun g => M g i j) ∈ W
    rw [this]
    refine sum_mem fun l hl => Submodule.smul_mem _ _ ?_
    obtain ⟨A, e⟩ := key l (hz.1 l hl)
    exact e ▸ mem A

open Polynomial in

theorem not_zfin_exp (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} (τ : EmbOver E w) (i : Fin n) :
    IsSm σ J (fun g => Complex.exp (archMat σ J τ (projArch σ J w g) i i)) ∧
    ¬ FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧
      f = dop z fun g => Complex.exp (archMat σ J τ (projArch σ J w g) i i)}) := by
  refine ⟨fun k γ hγ g => (isSm_entry h τ i i k γ hγ g).cexp, fun hfin => ?_⟩
  let M : GAd σ J →* Matrix (Fin n) (Fin n) ℂ := (archMat σ J τ).comp (projArch σ J w)
  have hZ : (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ * J.map τ.1 + J.map τ.1 * (Complex.I • 1) = 0 := by
    simp [conjTranspose_smul]
  obtain ⟨γ₀, -, hγ⟩ := exists_isRealLine h hJ τ hZ
  have inj : Function.Injective (archMat σ J τ) := fun a b e => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at e
    exact (archEquiv J h τ).injective (Subtype.ext (Units.ext e))
  let γ : ℝ → GAd σ J := fun t => embArch σ J w (projArch σ J w (γ₀ t))
  have hc : ∀ t a, γ t * a = a * γ t := fun t a => by
    refine GAd_ext σ J (fun u => ?_) fun v => by simp [γ]
    by_cases e : u = w
    · subst e
      apply inj
      simp only [γ, map_mul, projArch_embArch_self, hγ]
      refine (Commute.exp_left ?_).eq
      exact ((Commute.one_left _).smul_left _).smul_left _
    · simp [γ, projArch_embArch_ne σ J e]
  have hM : ∀ t : ℝ, M (γ t) = NormedSpace.exp (t • (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ))) := fun t => by
    simp [M, γ, hγ]
  have hcen : ∀ k, IsCentral σ J (Finsupp.single (List.replicate k γ) 1) := fun k => by
    refine ⟨fun l hl δ hδ => ?_, fun f _ a _ g => ?_⟩
    · obtain rfl : l = _ := by simpa using hl
      obtain rfl := List.eq_of_mem_replicate hδ
      exact ⟨w, τ, _, hZ, fun t => ⟨_, rfl, hγ t⟩⟩
    · simp only [dop, Finsupp.sum_single_index, zero_mul, one_mul]
      induction k generalizing g with
      | zero => rfl
      | succ k ih => simp only [List.replicate_succ, List.foldr_cons, lineDer, ih, mul_assoc, hc]
  let T : ℂ[X] →ₗ[ℂ] (GAd σ J → ℂ) :=
    { toFun := fun p g => p.eval (M g i i) * Complex.exp (M g i i)
      map_add' := fun p q => funext fun g => by simp [add_mul]
      map_smul' := fun c p => funext fun g => by simp [mul_assoc] }
  have hD : ∀ p, lineDer γ (T p) = T (C Complex.I * X * (derivative p + p)) := fun p => funext fun g => by
    have d := hasDerivAt_entry (Z := Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) (M g) 1 i i
    simp only [Matrix.mul_one] at d
    have d1 := ((p.hasDerivAt _).comp_of_eq (0 : ℝ) d rfl).mul d.cexp
    change deriv (fun t => p.eval (M (g * γ t) i i) * Complex.exp (M (g * γ t) i i)) 0 = _
    simp only [map_mul, hM]
    refine d1.deriv.trans ?_
    simp [T]
    ring
  have hP : ∀ k, ∃ p : ℂ[X], p ≠ 0 ∧ p.natDegree = k ∧
      (List.replicate k γ).foldr lineDer (fun g => Complex.exp (M g i i)) = T p := fun k => by
    induction k with
    | zero => exact ⟨1, one_ne_zero, by simp, funext fun g => by simp [T]⟩
    | succ k ih =>
      obtain ⟨p, h0, h1, h2⟩ := ih
      have h3 : (derivative p + p).degree = p.degree := degree_add_eq_right_of_degree_lt (degree_derivative_lt h0)
      have h4 : derivative p + p ≠ 0 := fun e => h0 (by rwa [e, degree_zero, eq_comm, degree_eq_bot] at h3)
      have h5 : C Complex.I * X ≠ 0 := mul_ne_zero (by simp) X_ne_zero
      refine ⟨_, mul_ne_zero h5 h4, ?_, by rw [List.replicate_succ, List.foldr_cons, h2, hD]⟩
      rw [natDegree_mul h5 h4, natDegree_eq_of_degree_eq h3, natDegree_C_mul_X _ Complex.I_ne_zero, h1, add_comm]
  have hT : Function.Injective T := (injective_iff_map_eq_zero T).2 fun p hp => by
    refine p.eq_zero_of_infinite_isRoot (Set.Infinite.mono (s := Set.range fun t : ℝ => Complex.exp (t * Complex.I)) ?_ ?_)
    · rintro _ ⟨t, rfl⟩
      have e : M (γ t) i i = Complex.exp (t * Complex.I) := by
        rw [hM, show t • (Complex.I • (1 : Matrix (Fin n) (Fin n) ℂ)) = Matrix.diagonal fun _ => t * Complex.I by
          ext a b; by_cases a = b <;> simp [*, Matrix.one_apply], Matrix.exp_diagonal]
        simp [Complex.exp_eq_exp_ℂ]
      have := congrFun hp (γ t)
      simpa [T, e] using this
    · refine Set.Infinite.of_image Complex.re (Set.Infinite.mono (fun x hx => ?_) (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1)))
      exact ⟨_, ⟨Real.arccos x, rfl⟩, by simp [Complex.exp_ofReal_mul_I_re, Real.cos_arccos hx.1 hx.2]⟩
  choose P h0 h1 h2 using hP
  have hli : LinearIndependent ℂ P := by
    exact Polynomial.Sequence.linearIndependent (S := ⟨P, fun k => by rw [degree_eq_natDegree (h0 k), h1]⟩)
  have h6 := (hli.map' T (LinearMap.ker_eq_bot.2 hT))
  have h7 : FiniteDimensional ℂ (Submodule.span ℂ (Set.range (T ∘ P))) :=
    @Submodule.finiteDimensional_of_le _ _ _ _ _ _ _ hfin (Submodule.span_mono (by
      rintro _ ⟨k, rfl⟩
      exact ⟨_, hcen k, funext fun g => by simpa [dop, M] using (congrFun (h2 k) g).symm⟩))
  haveI : Finite ℕ := Module.Finite.finite_basis (Module.Basis.span h6)
  exact not_finite ℕ

example : haveI : IsCMField (CyclotomicField 4 ℚ) :=
      IsCyclotomicExtension.Rat.isCMField (CyclotomicField 4 ℚ) (S := {4}) ⟨4, rfl, by norm_num⟩
    ∃ K φ, IsMaxCpt (IsCMField.complexConj (CyclotomicField 4 ℚ) : CyclotomicField 4 ℚ →ₐ[maximalRealSubfield (CyclotomicField 4 ℚ)] _)
      (1 : Matrix (Fin 1) (Fin 1) _) K ∧ IsAut _ 1 K φ ∧ ∃ g, φ g ≠ φ 1 :=
  haveI : IsCMField (CyclotomicField 4 ℚ) :=
      IsCyclotomicExtension.Rat.isCMField (CyclotomicField 4 ℚ) (S := {4}) ⟨4, rfl, by norm_num⟩
  exists_nonconst_one (isCMExt_of_isCMField _) one_pos

end GlobalTheory.UAut.Model

end
