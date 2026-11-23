import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ArchSz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnderMemAndPlaceAboveEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlLatCongMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharInvertibleMatrixBallMemSubfield
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepth
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumRightInverse
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel GlobalTheory.ConjSize

open scoped Pointwise in
private theorem sum_rightInv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G)
    (hKo : IsOpen (K : Set G)) (hKt : μ K ≠ ⊤) {S : Set G} (hS : IsCompact S)
    (hSK : ∀ s ∈ S, ∀ k ∈ K, s * k ∈ S) :
    ∃ t : Finset (G ⧸ K), (∀ Q ∈ t, Q.out ∈ S) ∧ ∀ f : G → ℂ, (∀ s ∈ S, ∀ k ∈ K, f (s * k) = f s) →
      ∫ g in S, f g ∂μ = ∑ Q ∈ t, f Q.out * μ.real K :=
  _root_.UpperTheory.Reformulated.B.SumRightInverse.sum_rightInv μ K hKo hKt hS hSK

section
variable {k : Type} [Field k] [ValuativeRel k] {A : Type} [Fintype A] [DecidableEq A]

private theorem inv_small (g : GL A k) (c : k)
    (hdet : ∀ y : Matrix A A k, (∀ i j, valuation k (y i j - g.val i j) ≤ valuation k c) → y.det ≠ 0) (i j : A) :
    valuation k ((g⁻¹).val i j) * valuation k c ≤ 1 := by
  by_contra hlt
  rw [not_le] at hlt
  set a := (g⁻¹).val i j with ha
  have ha0 : a ≠ 0 := by
    intro h; rw [h] at hlt; simp at hlt
  have hv0 : 0 < valuation k a := zero_lt_iff.2 (by simpa using ha0)
  have hd : valuation k a⁻¹ ≤ valuation k c := by
    rw [map_inv₀, inv_le_iff_one_le_mul₀' hv0]; exact hlt.le
  refine hdet (g.val - Matrix.single j i a⁻¹) (fun p q => ?_) ?_
  · rw [Matrix.sub_apply, sub_sub_cancel_left, Valuation.map_neg, Matrix.single_apply]
    split_ifs
    · exact hd
    · simp
  · rw [← Matrix.exists_mulVec_eq_zero_iff]
    refine ⟨fun l => (g⁻¹).val l j, fun h => ha0 (congrFun h i), ?_⟩
    rw [Matrix.sub_mulVec, Matrix.single_mulVec, ← ha, inv_mul_cancel₀ ha0]
    funext p
    have : (g.val * (g⁻¹).val) p j = (1 : Matrix A A k) p j := by rw [Units.mul_inv]
    rw [Matrix.mul_apply] at this
    simp only [Pi.sub_apply, Matrix.mulVec, dotProduct, this, Matrix.one_apply, Function.update_apply,
      Pi.zero_apply, sub_self]

private theorem val_sub_le {x y z c : k} (h : valuation k (y - x) ≤ valuation k c)
    (h' : valuation k (z - x) ≤ valuation k c) : valuation k (y - z) ≤ valuation k c := by
  have : y - z = (y - x) - (z - x) := by ring
  rw [this]
  exact ((valuation k).map_sub _ _).trans (max_le h h')

private theorem inv_mul_int (x : Matrix A A k) (c : k)
    (hdet : ∀ y : Matrix A A k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k c) → y.det ≠ 0)
    (g h : GL A k) (hg : ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k c)
    (hh : ∀ i j, valuation k (h.val i j - x i j) ≤ valuation k c) (i j : A) : (g⁻¹ * h).val i j ∈ 𝒪[k] := by
  have e : (g⁻¹ * h).val = 1 + (g⁻¹).val * (h.val - g.val) := by
    rw [Matrix.mul_sub, Units.inv_mul, Units.val_mul, add_sub_cancel]
  have hs := inv_small g c fun y hy => hdet y fun p q =>
    val_sub_le (hy p q) (by rw [Valuation.map_sub_swap]; exact hg p q)
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  refine add_mem ?_ (Subring.sum_mem _ fun l _ => ?_)
  · rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Valuation.mem_integer_iff, map_mul]
    exact (mul_le_mul_right (val_sub_le (hh l j) (hg l j)) _).trans (hs i l)

end

open scoped Pointwise in
theorem UpperTheory.unramified_character_invariant :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {A : Type} [Fintype A] [DecidableEq A] {K : Type} [Field K] (ι τ : K →+* ℂ) {J : Subgroup (GL A k)}, IsOpen (J : Set (GL A k)) → J ≤ GlobalTheory.SplitWeil.KO k A → ∀ (ν : kˣ →* ℂˣ) {ϖ : kˣ} {e : ℕ}, IsUnif ϖ → CondLE ϖ e ν → (∀ u, Un ι τ (ν u : ℂ)) → (∀ u : kˣ, apow u (1 / 2) ∈ Set.range ι) → ∀ (n : ℕ) (x : Matrix A A k), (∀ i j, valuation k (x i j) ≤ 1) → (∀ y : Matrix A A k, (∀ i j, valuation k (y i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)) → y.det ≠ 0) → Sz ι τ (∫ g in {g : GL A k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)}, (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2) ∂(haarVol J)) ((haarVol J).real (GlobalTheory.SplitWeil.KO k A : Set (GL A k))) := by
  intro k _ _ _ _ _ _ A _ _ K _ ι τ J hJo hJK ν ϖ e hϖ hcond hν hap n x hx hdet
  haveI := isHaarMeasure_haarVol hJo hJK
  obtain ⟨hSc, hSo⟩ := GlobalTheory.GLBallInt.isCompact_isOpen_glBall x (ϖ ^ e) hdet
  set S := {g : GL A k | ∀ i j, valuation k (g.val i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k)} with hSdef
  set K' : Subgroup (GL A k) :=
    J ⊓ GlobalTheory.SplitFlip.glLatCong (ϖ ^ e) (GlobalTheory.SplitFlip.stdLat k A) ⊓ GlobalTheory.GLBallInt.rightStab S with hKdef
  have hKo : IsOpen (K' : Set (GL A k)) := by
    simp only [hKdef, Subgroup.coe_inf]
    exact (hJo.inter (GlobalTheory.FunObj.GivenAdm.isOpen_glLatCong _)).inter (GlobalTheory.GLBallInt.isOpen_rightStab hSc hSo)
  have hKJ : K' ≤ J := inf_le_left.trans inf_le_left
  have hJc : IsCompact (J : Set (GL A k)) := isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen hJo) hJK
  have hKt : haarVol J K' ≠ ⊤ :=
    ((measure_mono (show (K' : Set (GL A k)) ⊆ J from hKJ)).trans_lt (by simp [haarVol_self hJo hJK])).ne
  have hinv : ∀ s ∈ S, ∀ k' ∈ K', ((ν (gdet (s * k')) : ℂ) * apow (gdet (s * k')) ((n : ℂ) / 2)) =
      (ν (gdet s) : ℂ) * apow (gdet s) ((n : ℂ) / 2) := by
    intro s _ k' hk
    have hu : gdet k' ∈ unitCong (ϖ ^ e) :=
      GlobalTheory.FunObj.GivenAdm.gdet_mem_unitCong (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hk).1).2
    rw [gdet_mul, map_mul, Units.val_mul, apow_mul, hcond _ hu, apow_of_valuation_eq_one hu.1]
    simp
  obtain ⟨t, htS, ht⟩ := sum_rightInv (haarVol J) K' hKo hKt hSc
    (fun s hs k' hk => ((Subgroup.mem_inf.1 hk).2 s).1 hs)
  rw [ht (fun g => (ν (gdet g) : ℂ) * apow (gdet g) ((n : ℂ) / 2)) hinv]
  have h1 := ht (fun _ => (1 : ℂ)) (fun _ _ _ _ => rfl)
  rw [setIntegral_const, Finset.sum_const, nsmul_eq_mul, one_mul, Complex.real_smul, mul_one] at h1
  have h1' : (haarVol J).real S = t.card * (haarVol J).real K' := by exact_mod_cast h1
  obtain ⟨m, hm⟩ := GlobalTheory.GLBallInt.measureReal_eq_inv_natCast (haarVol J) hJc (haarVol_self hJo hJK) hKo hKJ
  have hϖe : valuation k ((ϖ ^ e : kˣ) : k) ≤ 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow]
    exact pow_le_one' (hϖ.trans_lt uniformizer_lt_one).le _
  have hdv : ∀ g ∈ S, valuation k ((gdet g : kˣ) : k) ≤ 1 := by
    intro g hg
    have hint : ∀ i j, g.val i j ∈ 𝒪[k] := fun i j => by
      have : g.val i j = (g.val i j - x i j) + x i j := by ring
      rw [this]
      exact add_mem ((Valuation.mem_integer_iff _ _).2 ((hg i j).trans hϖe))
        ((Valuation.mem_integer_iff _ _).2 (hx i j))
    have : g.val.det ∈ 𝒪[k] := by
      rw [Matrix.det_apply']
      exact Subring.sum_mem _ fun σ _ => mul_mem (intCast_mem _ _) (Subring.prod_mem _ fun i _ => hint _ _)
    exact (Valuation.mem_integer_iff _ _).1 this
  have hsz : Sz ι τ (∑ Q ∈ t, (ν (gdet Q.out) : ℂ) * apow (gdet Q.out) ((n : ℂ) / 2) * ((haarVol J).real K' : ℝ))
      (t.card * (haarVol J).real K') := by
    refine Sz.sum_card t fun Q hQ => ?_
    have h2 := (hν (gdet Q.out)).mul_sz (sz_apow_of_le_one (τ := τ) _ (hap _) n (hdv _ (htS Q hQ)))
    have h3 := h2.mul (Sz.inv_nat (ι := ι) (τ := τ) m)
    rw [hm]
    simpa using h3
  refine hsz.mono ?_
  rw [← h1']
  let x' : GL A k := Matrix.GeneralLinearGroup.mkOfDetNeZero x (hdet x fun i j => by simp)
  have hx' : ∀ i j, valuation k (x'.val i j - x i j) ≤ valuation k ((ϖ ^ e : kˣ) : k) := fun i j => by
    show valuation k (x i j - x i j) ≤ _
    simp
  have hsub : S ⊆ x' • (GlobalTheory.SplitWeil.KO k A : Set (GL A k)) := fun g hg =>
    ⟨x'⁻¹ * g, (mem_KO_iff _).2 ⟨inv_mul_int x _ hdet x' g hx' hg, by
      rw [mul_inv_rev, inv_inv]; exact inv_mul_int x _ hdet g x' hg hx'⟩, by simp⟩
  rw [measureReal_def, measureReal_def]
  refine ENNReal.toReal_mono isCompact_KO.measure_lt_top.ne ?_
  exact (measure_mono hsub).trans (measure_smul _ _ _).le
