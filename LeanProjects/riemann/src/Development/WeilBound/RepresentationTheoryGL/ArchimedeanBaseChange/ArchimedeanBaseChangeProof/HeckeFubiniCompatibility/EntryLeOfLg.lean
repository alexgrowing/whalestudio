import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace PMul

section Loc

variable {n : ℕ}

theorem mem_GLs_val (y : G n) : y.val ∈ GLs n := (Matrix.isUnits_det_units y).ne_zero

theorem entry_le_of_lg {y : G n} {R : ℝ} (h : lg y.val ≤ R) (p q : Fin n) :
    ‖y.val p q‖ ≤ Real.exp R ∧ ‖(y⁻¹ : G n).val p q‖ ≤ Real.exp R := by
  unfold lg at h
  set S := ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y.val)⁻¹ a b‖ ^ 2) with hS
  have hS0 : 0 ≤ S := by positivity
  have h1 : 1 + S ≤ Real.exp R := (Real.log_le_iff_le_exp (by linarith)).1 h
  have hterm : ‖y.val p q‖ ^ 2 + ‖(y.val)⁻¹ p q‖ ^ 2 ≤ S := by
    have e1 : ‖y.val p q‖ ^ 2 + ‖(y.val)⁻¹ p q‖ ^ 2 ≤ ∑ b, (‖y.val p b‖ ^ 2 + ‖(y.val)⁻¹ p b‖ ^ 2) :=
      Finset.single_le_sum (f := fun b => ‖y.val p b‖ ^ 2 + ‖(y.val)⁻¹ p b‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ q)
    have e2 : ∑ b, (‖y.val p b‖ ^ 2 + ‖(y.val)⁻¹ p b‖ ^ 2) ≤ S :=
      Finset.single_le_sum (f := fun a => ∑ b, (‖y.val a b‖ ^ 2 + ‖(y.val)⁻¹ a b‖ ^ 2)) (fun _ _ => by positivity)
        (Finset.mem_univ p)
    linarith
  have hinv : (y⁻¹ : G n).val = (y.val)⁻¹ := Matrix.coe_units_inv y
  rw [hinv]
  have a1 := norm_nonneg (y.val p q)
  have a2 := norm_nonneg ((y.val)⁻¹ p q)
  constructor <;> nlinarith [sq_nonneg (‖y.val p q‖ - 1), sq_nonneg (‖(y.val)⁻¹ p q‖ - 1)]

theorem isCompact_lg (R : ℝ) : IsCompact {y : G n | lg y.val ≤ R} := by
  set B : Set (Mat n) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) (Real.exp R)
  have hB : IsCompact B := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hK : IsCompact (Units.embedProduct (Mat n) ⁻¹' (B ×ˢ (MulOpposite.op '' B))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hB.prod (hB.image MulOpposite.continuous_op))
  have hcl : IsClosed {y : G n | lg y.val ≤ R} := by
    refine isClosed_le ?_ continuous_const
    have hc : Continuous fun y : G n => (1 : ℝ) + ∑ a, ∑ b, (‖y.val a b‖ ^ 2 + ‖(y.val)⁻¹ a b‖ ^ 2) := by
      have hinv : (fun y : G n => (y.val)⁻¹) = fun y : G n => (y⁻¹ : G n).val := funext fun y => (Matrix.coe_units_inv y).symm
      have c1 : Continuous fun y : G n => (y.val)⁻¹ := by rw [hinv]; exact Units.continuous_val.comp continuous_inv
      have c0 : Continuous fun y : G n => y.val := Units.continuous_val
      refine continuous_const.add (continuous_finsetSum _ fun p _ => continuous_finsetSum _ fun q _ => ?_)
      exact (((continuous_apply q).comp ((continuous_apply p).comp c0)).norm.pow 2).add
        (((continuous_apply q).comp ((continuous_apply p).comp c1)).norm.pow 2)
    exact hc.log fun y => by positivity
  refine hK.of_isClosed_subset hcl fun y hy => ?_
  have h := fun p q => entry_le_of_lg (y := y) hy p q
  refine ⟨fun p _ q _ => ?_, ⟨(y⁻¹ : G n).val, fun p _ q _ => ?_, rfl⟩⟩
  · simpa [Metric.mem_closedBall, dist_zero_right] using (h p q).1
  · simpa [Metric.mem_closedBall, dist_zero_right] using (h p q).2

section Nrm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem isMult_cts [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
    {val : Inf n → ℂ} {T : ℝ} (h : IsMult μ M k val T) :
    Continuous (fun y : G n => k y.val) ∧ HasCompactSupport (fun y : G n => k y.val) := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  have hcont : ContinuousOn (fun x => ∑ i, c i • ks i x) (GLs n) :=
    continuousOn_finsetSum _ fun i _ => ((hks i).2.1.continuousOn).const_smul (c i)
  refine ⟨?_, ?_⟩
  · have e : (fun y : G n => k y.val) = fun y => ∑ i, c i • ks i y.val := funext fun y => hk _ (mem_GLs_val y)
    rw [e]
    exact hcont.comp_continuous Units.continuous_val mem_GLs_val
  · choose R hR using fun i => (hks i).2.2.1
    refine HasCompactSupport.intro (isCompact_lg (∑ i, |R i|)) fun y hy => ?_
    have hy' : ∑ i, |R i| < lg y.val := not_le.1 hy
    rw [hk _ (mem_GLs_val y)]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hle : R i ≤ ∑ i, |R i| := (le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |R i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i))
    rw [hR i _ (mem_GLs_val y) (lt_of_le_of_lt hle hy'), smul_zero]

end Nrm

theorem ent_cont (M : KMod n) (i j : Ix M) : Continuous fun A : M.V →L[ℂ] M.V => ent M A i j := by
  unfold ent
  exact continuous_const.inner (continuous_id.clm_apply continuous_const)

theorem ent_mul (M : KMod n) (A B : M.V →L[ℂ] M.V) (i j : Ix M) :
    ent M (A * B) i j = ∑ m, ent M A i m * ent M B m j := by
  unfold ent
  have hx : B (stdOrthonormalBasis ℂ M.V j) = ∑ m, inner ℂ (stdOrthonormalBasis ℂ M.V m)
      (B (stdOrthonormalBasis ℂ M.V j)) • stdOrthonormalBasis ℂ M.V m :=
    ((stdOrthonormalBasis ℂ M.V).sum_repr' _).symm
  rw [ContinuousLinearMap.mul_apply]
  conv_lhs => rw [hx]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, inner_smul_right, mul_comm]

theorem loc_cts {M : KMod n} {k k' : Mat n → (M.V →L[ℂ] M.V)} (hk : Continuous fun y : G n => k y.val)
    (hks : HasCompactSupport fun y : G n => k y.val) (hk' : Continuous fun y : G n => k' y.val) (x : G n)
    (i m j : Ix M) :
    Continuous (fun y : G n => ent M (k y.val) i m * ent M (k' (y⁻¹ * x).val) m j) ∧
      HasCompactSupport (fun y : G n => ent M (k y.val) i m * ent M (k' (y⁻¹ * x).val) m j) := by
  refine ⟨((ent_cont M i m).comp hk).mul ((ent_cont M m j).comp (hk'.comp (continuous_inv.mul continuous_const))), ?_⟩
  exact HasCompactSupport.mul_right (hks.comp_left (g := fun A => ent M A i m) (ent_zero M i m))

theorem ent_conv [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (M : KMod n)
    {k k' : Mat n → (M.V →L[ℂ] M.V)} (hk : Continuous fun y : G n => k y.val)
    (hks : HasCompactSupport fun y : G n => k y.val) (hk' : Continuous fun y : G n => k' y.val) (x : G n)
    (i j : Ix M) :
    ent M (PositivityTheory.RgBcC.conv μ M k k' x.val) i j =
      ∑ m, ∫ y, ent M (k y.val) i m * ent M (k' (y⁻¹ * x).val) m j ∂μ := by
  have e : PositivityTheory.RgBcC.conv μ M k k' x.val = ∫ y, k y.val * k' (y⁻¹ * x).val ∂μ := by
    unfold PositivityTheory.RgBcC.conv
    simp only [Units.val_mul]
  have hFc : Continuous fun y : G n => k y.val * k' (y⁻¹ * x).val :=
    hk.mul (hk'.comp (continuous_inv.mul continuous_const))
  have hFs : HasCompactSupport fun y : G n => k y.val * k' (y⁻¹ * x).val := hks.mul_right
  have hFi := hFc.integrable_of_hasCompactSupport (μ := μ) hFs
  have h1 : ent M (∫ y, k y.val * k' (y⁻¹ * x).val ∂μ) i j =
      ∫ y, ent M (k y.val * k' (y⁻¹ * x).val) i j ∂μ := by
    unfold ent
    rw [ContinuousLinearMap.integral_apply hFi, ← integral_inner]
    exact (hFc.clm_apply continuous_const).integrable_of_hasCompactSupport
      (hFs.comp_left (g := fun A : M.V →L[ℂ] M.V => A (stdOrthonormalBasis ℂ M.V j)) (by simp))
  rw [e, h1]
  calc ∫ y, ent M (k y.val * k' (y⁻¹ * x).val) i j ∂μ
      = ∫ y, ∑ m, ent M (k y.val) i m * ent M (k' (y⁻¹ * x).val) m j ∂μ := by
        congr 1; funext y; exact ent_mul M _ _ i j
    _ = _ := integral_finsetSum _ fun m _ =>
        (loc_cts hk hks hk' x i m j).1.integrable_of_hasCompactSupport (loc_cts hk hks hk' x i m j).2

end Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

def fA {M : Mods E n} (k k' : Kers M) (i j m : IxA M) (y : GA E n) (v : InfinitePlace E) (x : G n) : ℂ :=
  ent (M v) (k v x.val) (i v) (m v) * ent (M v) (k' v (x⁻¹ * gInf v y).val) (m v) (j v)

theorem fA_cts [MeasurableSpace (G n)] {μ μ' : Measure (G n)} {M : Mods E n} {k k' : Kers M} {val val' T T'}
    (hk : IsMults μ k val T) (hk' : IsMults μ' k' val' T') (i j m : IxA M) (y : GA E n) (v : InfinitePlace E) :
    Continuous (fA k k' i j m y v) ∧ HasCompactSupport (fA k k' i j m y v) :=
  loc_cts (isMult_cts (hk v)).1 (isMult_cts (hk v)).2 (isMult_cts (hk' v)).1 (gInf v y) (i v) (m v) (j v)

theorem entA_convK [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] {μ' : Measure (G n)}
    {M : Mods E n} {k k' : Kers M} {val val' T T'} (hk : IsMults μ k val T) (hk' : IsMults μ' k' val' T')
    (i j : IxA M) (y : GA E n) :
    entA (convK μ k k') i j y = ∑ m : IxA M, ∏ v, ∫ x, fA k k' i j m y v x ∂μ := by
  unfold entA convK
  rw [Finset.prod_congr rfl fun v _ => ent_conv μ (M v) (isMult_cts (hk v)).1 (isMult_cts (hk v)).2
    (isMult_cts (hk' v)).1 (gInf v y) (i v) (j v)]
  rw [Fintype.prod_sum]
  rfl

theorem mulF_fin [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
    {κ : Type} [Fintype κ] {ψ ψ' : Matrix κ κ (Hf E a b → ℂ)} (hψ : IsFinM ψ) (hψ' : IsFinM ψ') : IsFinM (mulF ν ψ ψ') := by
  intro x y
  refine ⟨continuous_finsetSum _ fun z _ => ?_, ?_⟩
  · have e : (fun g => ∫ h, ψ x z h * ψ' z y (h⁻¹ * g) ∂ν) =
        fun g => ∫ h in tsupport (ψ x z), ψ x z h * ψ' z y (h⁻¹ * g) ∂ν := by
      funext g
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh => ?_).symm
      rw [image_eq_zero_of_notMem_tsupport hh, zero_mul]
    rw [e]
    refine continuous_parametric_integral_of_continuous ?_ (hψ x z).2.isCompact
    exact ((hψ x z).1.comp continuous_snd).mul ((hψ' z y).1.comp (continuous_snd.inv.mul continuous_fst))
  · refine HasCompactSupport.intro (isCompact_iUnion fun z => (hψ x z).2.isCompact.mul (hψ' z y).2.isCompact)
      fun g hg => ?_
    refine Finset.sum_eq_zero fun z _ => ?_
    have : ∀ h, ψ x z h * ψ' z y (h⁻¹ * g) = 0 := by
      intro h
      by_cases h1 : h ∈ tsupport (ψ x z)
      · have h2 : h⁻¹ * g ∉ tsupport (ψ' z y) := fun h2 =>
          hg (Set.mem_iUnion.2 ⟨z, Set.mem_mul.2 ⟨h, h1, h⁻¹ * g, h2, mul_inv_cancel_left h g⟩⟩)
        rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
    simp [this]

theorem mulM_tens (D : Dom E a b) [MeasurableSpace (G a)] [BorelSpace (G a)] [MeasurableSpace (G b)] [BorelSpace (G b)]
    [MeasurableSpace (Hf E a b)] [BorelSpace (Hf E a b)] (μa : Measure (G a)) [μa.IsHaarMeasure]
    (μb : Measure (G b)) [μb.IsHaarMeasure] (ν : Measure (Hf E a b)) [ν.IsHaarMeasure]
    {Ma : Mods E a} {Mb : Mods E b} {κ : Type} [Fintype κ]
    {ka ka' : Kers Ma} {kb kb' : Kers Mb} {va va' vb vb'} {T T' : ℝ} {ψ ψ' : Matrix κ κ (Hf E a b → ℂ)}
    (hC : Compat D μa μb ν) (hka : IsMults μa ka va T) (hkb : IsMults μb kb vb T) (hka' : IsMults μa ka' va' T')
    (hkb' : IsMults μb kb' vb' T') (hψ : IsFinM ψ) (hψ' : IsFinM ψ') :
    mulM D.μ (tens ka kb ψ) (tens ka' kb' ψ') = tens (convK μa ka ka') (convK μb kb kb') (mulF ν ψ ψ') := by
  funext i j y
  have step : ∀ k : Io Ma Mb κ, ∫ z, tens ka kb ψ i k z * tens ka' kb' ψ' k j (z⁻¹ * y) ∂D.μ =
      (∏ v, ∫ x, fA ka ka' i.1.1 j.1.1 k.1.1 y.1 v x ∂μa) * (∏ v, ∫ x, fA kb kb' i.1.2 j.1.2 k.1.2 y.2 v x ∂μb) *
        ∫ h, ψ i.2 k.2 h * ψ' k.2 j.2 (h⁻¹ * hFin y) ∂ν := by
    intro k
    have e : (fun z => tens ka kb ψ i k z * tens ka' kb' ψ' k j (z⁻¹ * y)) = fun z =>
        (∏ v, fA ka ka' i.1.1 j.1.1 k.1.1 y.1 v (gInf v z.1)) * (∏ v, fA kb kb' i.1.2 j.1.2 k.1.2 y.2 v (gInf v z.2)) *
          (fun h => ψ i.2 k.2 h * ψ' k.2 j.2 (h⁻¹ * hFin y)) (hFin z) := by
      funext z
      have hz : hFin (z⁻¹ * y) = (hFin z)⁻¹ * hFin y := by simp [hFin]
      simp only [tens, entA, fA, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv, map_mul, map_inv, hz,
        Finset.prod_mul_distrib]
      ring
    rw [e]
    exact hC _ _ _ (fun v => fA_cts hka hka' _ _ _ _ v) (fun v => fA_cts hkb hkb' _ _ _ _ v)
      ((hψ i.2 k.2).1.mul ((hψ' k.2 j.2).1.comp (continuous_inv.mul continuous_const))) (hψ i.2 k.2).2.mul_right
  show ∑ k, ∫ z, tens ka kb ψ i k z * tens ka' kb' ψ' k j (z⁻¹ * y) ∂D.μ =
    entA (convK μa ka ka') i.1.1 j.1.1 y.1 * entA (convK μb kb kb') i.1.2 j.1.2 y.2 * mulF ν ψ ψ' i.2 j.2 (hFin y)
  rw [Finset.sum_congr rfl fun k _ => step k, entA_convK μa hka hka', entA_convK μb hkb hkb']
  unfold mulF
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]

end PMul

open PMul in

theorem tensMul : TensMul := fun _ _ _ _ _ _ D _ _ _ _ _ _ μa _ μb _ ν _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hC hka hkb hka'
    hkb' hψ hψ' => ⟨mulF_fin ν hψ hψ', mulM_tens D μa μb ν hC hka hkb hka' hkb' hψ hψ'⟩

end PositivityTheory.Rg.BcB.CG
