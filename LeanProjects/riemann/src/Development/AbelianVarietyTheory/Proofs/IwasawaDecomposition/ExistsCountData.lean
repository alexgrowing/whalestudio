import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRightTranslation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWeakIntegralOfStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCompleteDense
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CharFnLocallyConstant

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField Matrix
open scoped InnerProductSpace ComplexOrder Classical

namespace GlobalTheory.Mem.RowsBundle

section Infl

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem fibre_eq (q : Q) :
    ∃ t : I.Gf, {x | x ∈ I.Kset ∧ ρ.toFun x = q} = (fun y => t * y) ⁻¹' I.Kg g := by
  obtain ⟨t, ht, rfl⟩ := ρ.surj q
  have ht' : t⁻¹ ∈ I.Kset := (Ksub I).inv_mem ht
  refine ⟨t⁻¹, Set.ext fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine (ρ.ker _ ((Ksub I).mul_mem ht' h.1)).1 ?_
    rw [ρ.map_mul _ ht' _ h.1, ρ.map_inv ht, h.2, inv_mul_cancel]
  · have h1 : t⁻¹ * x ∈ I.Kset := h.1
    have hx : x ∈ I.Kset := ((Ksub I).mul_mem_cancel_left ht').1 h1
    have h2 := (ρ.ker _ h1).2 h
    rw [ρ.map_mul _ ht' _ hx, ρ.map_inv ht, inv_mul_eq_one] at h2
    exact ⟨hx, h2.symm⟩

theorem integral_inflate [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (F : Q → ℂ) :
    Integrable (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) μf ∧
      ∫ x, (if x ∈ I.Kset then F (ρ.toFun x) else 0) ∂μf = ((μf (I.Kg g)).toReal : ℂ) * ∑ q, F q := by
  have hU : IsOpen (I.Kg g) := I.topf_open g hg
  have hfin : μf (I.Kg g) ≠ ⊤ :=
    ((measure_mono fun x hx => hx.1).trans_lt (GlobalTheory.adelicStab_isCompact_isOpen I).1.measure_lt_top).ne
  have hm : ∀ q, MeasurableSet {x | x ∈ I.Kset ∧ ρ.toFun x = q} ∧
      μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) := fun q => by
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨(hU.preimage (by fun_prop)).measurableSet, measure_preimage_mul μf t _⟩
  have e : (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) =
      fun x => ∑ q, {x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q) x := by
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [if_pos hx, Finset.sum_eq_single (ρ.toFun x)]
      · rw [Set.indicator_of_mem]
        exact ⟨hx, rfl⟩
      · exact fun q _ hq => Set.indicator_of_notMem (fun h => hq h.2.symm) _
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun h => hx h.1) _).symm
  have hi : ∀ q, Integrable ({x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q)) μf := fun q =>
    (integrable_indicator_iff (hm q).1).2 (integrableOn_const ((hm q).2 ▸ hfin))
  rw [e]
  refine ⟨integrable_finset_sum _ fun q _ => hi q, ?_⟩
  rw [integral_finset_sum _ fun q _ => hi q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hm q).1, Measure.real, (hm q).2, Complex.real_smul]

theorem integrable_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q) :
    Integrable (ρ.lift μf a) μf := by
  letI := Fintype.ofFinite Q
  exact (integral_inflate ρ μf hg fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ)).1

theorem lift_biinv (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (x : I.Gf) (k : I.Gf) (hk : k ∈ I.Kg g)
    (k' : I.Gf) (hk' : k' ∈ I.Kg g) : ρ.lift μf a (k * x * k') = ρ.lift μf a x := by
  by_cases hx : x ∈ I.Kset
  · have h1 : k * x ∈ I.Kset := (Ksub I).mul_mem hk.1 hx
    rw [ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a ((Ksub I).mul_mem h1 hk'.1), ρ.map_mul _ h1 _ hk'.1,
      ρ.map_mul _ hk.1 _ hx, (ρ.ker _ hk.1).2 hk, (ρ.ker _ hk'.1).2 hk', one_mul, mul_one]
  · rw [ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a fun h => hx
      (((Ksub I).mul_mem_cancel_left hk.1).1 (((Ksub I).mul_mem_cancel_right hk'.1).1 h))]

theorem coeff_mul_eq_sum [Fintype Q] (a b : MonoidAlgebra ℂ Q) (s : Q) :
    (a * b).coeff s = ∑ q, a.coeff q * b.coeff (q⁻¹ * s) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp)]

theorem conv_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a b : MonoidAlgebra ℂ Q) :
    I.convF μf (ρ.lift μf a) (ρ.lift μf b) = ρ.lift μf (a * b) := by
  letI := Fintype.ofFinite Q
  funext x
  unfold AutInst.convF
  by_cases hx : x ∈ I.Kset
  · have e : (fun y => ρ.lift μf a y * ρ.lift μf b (y⁻¹ * x)) = fun y => if y ∈ I.Kset then
        (fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ) *
          (b.coeff (q⁻¹ * ρ.toFun x) / ((μf (I.Kg g)).toReal : ℂ))) (ρ.toFun y) else 0 := by
      funext y
      by_cases hy : y ∈ I.Kset
      · have hy' : y⁻¹ ∈ I.Kset := (Ksub I).inv_mem hy
        rw [if_pos hy, ρ.lift_of_mem μf a hy, ρ.lift_of_mem μf b ((Ksub I).mul_mem hy' hx), ρ.map_mul _ hy' _ hx,
          ρ.map_inv hy]
      · rw [if_neg hy, ρ.lift_of_notMem μf a hy, zero_mul]
    rw [e, (integral_inflate ρ μf hg fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ) *
      (b.coeff (q⁻¹ * ρ.toFun x) / ((μf (I.Kg g)).toReal : ℂ))).2, ρ.lift_of_mem μf _ hx, coeff_mul_eq_sum, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases h : ((μf (I.Kg g)).toReal : ℂ) = 0
    · simp [h]
    · field_simp
  · rw [ρ.lift_of_notMem μf _ hx]
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : y ∈ I.Kset
    · have : y⁻¹ * x ∉ I.Kset := fun h => hx (((Ksub I).mul_mem_cancel_left ((Ksub I).inv_mem hy)).1 h)
      simp only [ρ.lift_of_notMem μf b this, mul_zero, Pi.zero_apply]
    · simp only [ρ.lift_of_notMem μf a hy, zero_mul, Pi.zero_apply]

theorem isPosType_lift [Finite Q] (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (h1 : a * a = a) (h2 : IsSA a) :
    I.IsPosType (ρ.lift μf a) := by
  letI := Fintype.ofFinite Q
  intro m x c
  let q : Fin m → I.Gf ⧸ Ksub I := fun i => (x i : I.Gf ⧸ Ksub I)
  have hk : ∀ i, ((q i).out)⁻¹ * x i ∈ I.Kset := fun i => by
    show _ ∈ Ksub I
    rw [← QuotientGroup.eq]
    exact Quotient.out_eq _
  let b : Q → Fin m → ℂ := fun u i => c i * a.coeff (u⁻¹ * ρ.toFun (((q i).out)⁻¹ * x i))
  have key : ∀ i j, star (c i) * c j * ρ.lift μf a ((x i)⁻¹ * x j) =
      ∑ u, (if q i = q j then star (b u i) * b u j else 0) * (1 / ((μf (I.Kg g)).toReal : ℂ)) := by
    intro i j
    by_cases hij : q i = q j
    · have e1 : (x i)⁻¹ * x j = (((q i).out)⁻¹ * x i)⁻¹ * (((q j).out)⁻¹ * x j) := by
        rw [← hij]; group
      have hi' : (((q i).out)⁻¹ * x i)⁻¹ ∈ I.Kset := (Ksub I).inv_mem (hk i)
      rw [e1, ρ.lift_of_mem μf a ((Ksub I).mul_mem hi' (hk j)), ρ.map_mul _ hi' _ (hk j), ρ.map_inv (hk i)]
      simp only [if_pos hij, b]
      generalize ρ.toFun (((q i).out)⁻¹ * x i) = s
      generalize ρ.toFun (((q j).out)⁻¹ * x j) = t
      have e2 : a.coeff (s⁻¹ * t) = ∑ u, star (a.coeff (u⁻¹ * s)) * a.coeff (u⁻¹ * t) := by
        conv_lhs => rw [← h1, coeff_mul_eq_sum]
        refine Fintype.sum_equiv (Equiv.mulLeft s) _ _ fun u => ?_
        rw [← h2]
        simp [mul_assoc]
      rw [e2, Finset.sum_div, Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      simp only [star_mul']
      ring
    · have : (x i)⁻¹ * x j ∉ I.Kset := fun h => hij (QuotientGroup.eq.2 h)
      simp only [if_neg hij, ρ.lift_of_notMem μf a this, mul_zero, zero_mul, Finset.sum_const_zero]
  have e3 : ∑ i, ∑ j, star (c i) * c j * ρ.lift μf a ((x i)⁻¹ * x j) =
      ∑ u, (∑ i, ∑ j, if q i = q j then star (b u i) * b u j else 0) * (1 / ((μf (I.Kg g)).toReal : ℂ)) := by
    simp only [key, Finset.sum_mul]
    rw [Finset.sum_comm (γ := Q)]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [e3]
  refine Finset.sum_nonneg fun u _ => mul_nonneg (GlobalTheory.CharIdem.sum_fiber_nonneg q (b u)) ?_
  have : (1 / ((μf (I.Kg g)).toReal : ℂ)) = ((1 / (μf (I.Kg g)).toReal : ℝ) : ℂ) := by push_cast; rfl
  rw [this]
  exact Complex.zero_le_real.2 (by positivity)

theorem isAdmIdem_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (g₀ : ℕ)
    (a : MonoidAlgebra ℂ Q) (h1 : a * a = a) (h2 : IsSA a)
    (h3 : ∀ x ∈ I.Kset, a.coeff (ρ.toFun x) ≠ 0 → I.UnipMod g₀ x) : I.IsAdmIdem μf g g₀ (ρ.lift μf a) := by
  have hU : IsOpen (I.Kg g) := I.topf_open g hg
  have hone : (1 : I.Gf) ∈ I.Kg g := (KgSub I g).one_mem
  have hs : ∀ x, ρ.lift μf a x ≠ 0 → x ∈ I.Kset := fun x hx => by
    by_contra h
    exact hx (ρ.lift_of_notMem μf a h)
  refine ⟨?_, by rw [conv_lift ρ μf hg, h1], ρ.lift_inv μf a h2, isPosType_lift ρ μf a h1 h2, hs,
    fun x k hk k' hk' => lift_biinv ρ μf a x k hk k' hk', fun x hx => h3 x (hs x hx) fun h => hx ?_⟩
  · rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨(fun y => x⁻¹ * y) ⁻¹' I.Kg g, hU.preimage (by fun_prop), by simpa using hone, fun y hy => ?_⟩
    have e1 : y = 1 * x * (x⁻¹ * y) := by group
    rw [e1, lift_biinv ρ μf a x 1 hone _ hy]
  · rw [ρ.lift_of_mem μf a (hs x hx), h, zero_div]

end Infl

section Tens

variable {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]

theorem tensAlg_mul (a b : ∀ i, MonoidAlgebra ℂ (G i)) : tensAlg a * tensAlg b = tensAlg fun i => a i * b i := by
  letI := fun i => Fintype.ofFinite (G i)
  ext h
  rw [coeff_mul_eq_sum]
  simp only [tensAlg_coeff, coeff_mul_eq_sum, ← Finset.prod_mul_distrib]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rfl

theorem isSA_tensAlg (a : ∀ i, MonoidAlgebra ℂ (G i)) (h : ∀ i, IsSA (a i)) : IsSA (tensAlg a) := by
  intro q
  rw [tensAlg_coeff, tensAlg_coeff, star_prod]
  exact Finset.prod_congr rfl fun i _ => h i _

end Tens

theorem isDS_low_unitary {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (h : IsDS ε lam σ) :
    (∃ w, IsLowUnit ε lam σ w) ∧
      ∀ (x : Formalism.REAL.UJ ε) a b, ⟪σ (uMat x) a, σ (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ := by
  obtain ⟨-, -, hU, -, -, ⟨S, hS⟩, -⟩ := h
  constructor
  · obtain ⟨v, hv, h0, -⟩ := hS.2.2.2.1
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, ?_, Submodule.smul_mem _ _ ((le_sSup hS : S ≤ _) hv)⟩
    rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 h0)]
  · intro x a b
    exact (LinearIsometry.mk (σ (uMat x) : H →ₗ[ℂ] H) (hU.2.1 (uMat x) x.2)).inner_map_map a b

theorem exists_count_data (I : AutInst) (H : InfinitePlace I.F → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] (σ : ∀ v, Matrix (Fin I.n) (Fin I.n) ℂ → (H v →L[ℂ] H v))
    (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (e : I.Gf → ℂ)
    (hσ : ∀ v (x : Formalism.REAL.UJ (I.ε v)) a b, ⟪σ v (uMat x) a, σ v (uMat x) b⟫_ℂ = ⟪a, b⟫_ℂ)
    (he : Integrable e μf) :
    ∃ (fund : Set I.GA) (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (_ : CompleteSpace Hs)
      (σs : I.Ginf → (Hs →L[ℂ] Hs)) (tens : (∀ v, H v) → Hs) (R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund))
      (Re : I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsFundDom (I.muA μf) fund ∧ I.IsHilbTensor σ σs tens ∧
      I.IsRightReg μf fund R ∧ I.IsRConvF μf fund R e Re := by
  obtain ⟨fund, hfund⟩ := GlobalTheory.FundExists.exists_isFundDom I μf
  obtain ⟨R, hR, -⟩ := GlobalTheory.RightRegExists.exists_rightReg I μf fund hfund
  obtain ⟨Hs, i1, i2, i3, σs, tens, htens⟩ := GlobalTheory.HilbTensorExists.exists_isHilbTensor I H σ hσ
  obtain ⟨Re, hRe⟩ := (GlobalTheory.AutInst_exists_isRConvF_and_isRConv I μf fund hfund R hR).1 e he
  exact ⟨fund, Hs, i1, i2, i3, σs, tens, R, Re, hfund, htens, hR, hRe⟩

end GlobalTheory.Mem.RowsBundle
