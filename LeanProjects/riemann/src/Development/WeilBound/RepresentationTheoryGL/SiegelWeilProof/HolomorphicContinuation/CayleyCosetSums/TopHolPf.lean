import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.RcCongr
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.MapsToUpToSign
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.FactorL
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.HolParam
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.LocOpA

noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem lift_mR (φ : GR n → ℂ) (w : GR n) : lift φ (mR w) = φ w := by
  have h : IsUnit (mR w) ∧ InG (mR w) := ⟨⟨w.1, rfl⟩, w.2⟩
  unfold lift
  rw [dif_pos h]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp [mR]

theorem ιK_apply (k : KR n) : ιK n k = mR (k : GR n) := rfl

theorem mR_mul' (g h : GR n) : mR (g * h) = mR g * mR h := rfl

theorem tOp_resG {G : Type} [Group G] (ι : GR n →* G) [MeasurableSpace (KR n)] (μ : Measure (KR n)) (ρ : KR n → ℂ)
    (ψ : (Fin n → Fin n → ℝ) → ℂ) {a b : M2 n} (ha : InG a) (hb : InG b) (F : G → ℂ) (g : G) (y : GR n) :
    tOp μ (ιK n) ρ ψ a b (resG ι F g) (mR y) =
      ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F ((g * ι y) * ι ((k : GR n) * LocOpA.mkG a ha * LocOpA.nbEl t *
        LocOpA.mkG b hb)) * ψ t) ∂μ := by
  unfold tOp resG
  congr 1
  funext k
  congr 1
  congr 1
  funext t
  congr 1
  have e1 : mR y * ιK n k * a * nU (herm t) * b =
      mR (y * ((k : GR n) * LocOpA.mkG a ha * LocOpA.nbEl t * LocOpA.mkG b hb)) := by
    simp only [mR_mul', ιK_apply, LocOpA.mR_mkG, LocOpA.nbEl, Matrix.mul_assoc]
  rw [e1, lift_mR, map_mul]
  simp only [mul_assoc]

theorem hol_int {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {ι : GR n →* G} (hιc : Continuous ι)
    [MeasurableSpace (KR n)] [BorelSpace (KR n)] [CompactSpace (KR n)] (μ : Measure (KR n)) [IsFiniteMeasure μ]
    {a b : GR n} {ρ : KR n → ℂ} (hρ : Continuous ρ) {ψ : (Fin n → Fin n → ℝ) → ℂ} (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) {U : Set ℂ} (hU : IsOpen U) (E : ℂ → G → ℂ)
    (hEc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ univ)) (hEh : ∀ g, DifferentiableOn ℂ (fun z => E z g) U)
    (g : G) :
    DifferentiableOn ℂ (fun z => ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ,
      E z (g * ι ((k : GR n) * a * LocOpA.nbEl t * b)) * ψ t) ∂μ) U ∧
    ∀ z ∈ U, ∀ r : ℕ, iteratedDeriv r (fun z => ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ,
      E z (g * ι ((k : GR n) * a * LocOpA.nbEl t * b)) * ψ t) ∂μ) z =
      ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, iteratedDeriv r (fun w => E w (g * ι ((k : GR n) * a * LocOpA.nbEl t * b))) z *
        ψ t) ∂μ := by
  set C := tsupport ψ
  have hC : IsCompact C := hψs
  haveI : IsFiniteMeasure (volume.restrict C) := ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hCc : (volume.restrict C) Cᶜ = 0 := by
    rw [Measure.restrict_apply (isClosed_tsupport ψ).isOpen_compl.measurableSet, Set.compl_inter_self, measure_empty]
  have hnb := LocOpA.continuous_nbEl (n := n)
  have hj : ContinuousOn (fun y : (KR n × (Fin n → Fin n → ℝ)) × ℂ =>
      E y.2 (g * ι ((y.1.1 : GR n) * a * LocOpA.nbEl y.1.2 * b)) * ψ y.1.2) (univ ×ˢ U) := by
    refine ContinuousOn.mul ?_ (hψc.comp (continuous_snd.comp continuous_fst)).continuousOn
    refine hEc.comp (Continuous.continuousOn (continuous_snd.prodMk ((Vac.continuous_arg hιc hnb g).comp continuous_fst))) ?_
    intro y hy
    exact ⟨hy.2, trivial⟩
  have e1 : ∀ (k : KR n) (h : ℂ → G → ℂ) (z : ℂ), (∫ x in C, h z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) =
      ∫ x, h z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x := fun k h z =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]
  have hinner : ∀ k : KR n, ContinuousOn (fun y : (Fin n → Fin n → ℝ) × ℂ =>
      E y.2 (g * ι ((k : GR n) * a * LocOpA.nbEl y.1 * b)) * ψ y.1) (C ×ˢ U) := by
    intro k
    refine hj.comp (Continuous.continuousOn ((Continuous.prodMk_right k).prodMap continuous_id)) ?_
    intro y hy; exact ⟨trivial, hy.2⟩
  have hind : ∀ k : KR n, ∀ x ∈ C, DifferentiableOn ℂ (fun z => E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) U :=
    fun k x _ => (hEh _).mul_const _
  have hin : ∀ k : KR n, DifferentiableOn ℂ (fun z => ∫ x in C, E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) U :=
    fun k => (holParam (Fin n → Fin n → ℝ) (volume.restrict C) C hC hCc U _ hU (hinner k) (hind k)).1
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  have hcont : Continuous (fun y : KR n × U => ∫ x in C, E (y.2 : ℂ) (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) := by
    refine continuous_parametric_integral_of_continuous
      (f := fun (y : KR n × U) x => E (y.2 : ℂ) (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) ?_ hC
    have : Continuous (fun w : (KR n × U) × (Fin n → Fin n → ℝ) =>
        (((w.1.1, w.2), (w.1.2 : ℂ)) : (KR n × (Fin n → Fin n → ℝ)) × ℂ)) :=
      ((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    exact hj.comp_continuous this fun w => ⟨trivial, w.1.2.2⟩
  have hcon : ContinuousOn (fun y : KR n × ℂ => ρ y.1 *
      ∫ x in C, E y.2 (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) (univ ×ˢ U) := by
    refine (hρ.comp continuous_fst).continuousOn.mul ?_
    rw [continuousOn_iff_continuous_domRestrict]
    have : (univ ×ˢ U).domRestrict (fun y : KR n × ℂ => ∫ x in C, E y.2 (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) =
        (fun y : KR n × U => ∫ x in C, E (y.2 : ℂ) (g * ι ((y.1 : GR n) * a * LocOpA.nbEl x * b)) * ψ x) ∘
          (fun w : (univ ×ˢ U : Set (KR n × ℂ)) => ((w.1.1, ⟨w.1.2, w.2.2⟩) : KR n × U)) := by
      funext w; rfl
    rw [this]
    exact hcont.comp ((continuous_fst.comp continuous_subtype_val).prodMk
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _))
  have hP := holParam (KR n) μ univ isCompact_univ (by simp) U
    (fun k z => ρ k * ∫ x in C, E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) hU hcon
    (fun k _ => (hin k).const_mul _)
  have e2 : (fun z => ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, E z (g * ι ((k : GR n) * a * LocOpA.nbEl t * b)) * ψ t) ∂μ) =
      fun z => ∫ k, ρ k * (∫ x in C, E z (g * ι ((k : GR n) * a * LocOpA.nbEl x * b)) * ψ x) ∂μ := by
    funext z
    congr 1
    funext k
    rw [e1 k E z]
  rw [e2]
  refine ⟨hP.1, fun z hz r => ?_⟩
  rw [hP.2 z hz r]
  congr 1
  funext k
  rw [iteratedDeriv_const_mul_field]
  congr 1
  rw [(holParam (Fin n → Fin n → ℝ) (volume.restrict C) C hC hCc U _ hU (hinner k) (hind k)).2 z hz r]
  simp_rw [iteratedDeriv_mul_const_field]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem topHol : TopHol := by
  intro m n e _ _ G _ _ _ _ _ _ Pp Γ ι s₀ Ht f U d Ê t hD _ _ μ _ _ ρ ψ a b hρ hψc hψs ha hb g y
  haveI : CompactSpace (KR n) := kRCpt n
  have hfun : ∀ F : ℂ → G → ℂ, (fun z => tOp μ (ιK n) ρ ψ a b (resG ι (F z) g) (mR y)) = fun z =>
      ∫ k, ρ k * (∫ t : Fin n → Fin n → ℝ, F z ((g * ι y) * ι ((k : GR n) * LocOpA.mkG a ha * LocOpA.nbEl t *
        LocOpA.mkG b hb)) * ψ t) ∂μ := fun F => funext fun z => tOp_resG ι μ ρ ψ ha hb (F z) g y
  have H := hol_int hD.ιc μ (a := LocOpA.mkG a ha) (b := LocOpA.mkG b hb) hρ hψc hψs hD.hU Ê hD.cont hD.hol (g * ι y)
  refine ⟨?_, fun r => ?_⟩
  · rw [hfun Ê]
    exact H.1
  · rw [hfun Ê, H.2 s₀ hD.hs r, tOp_resG ι μ ρ ψ ha hb _ g y]

theorem JJ_mul_self : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, zero_add, add_zero, Matrix.mul_neg, Matrix.mul_one]
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_neg]
  simp

theorem JJ_inv : (JJ n)⁻¹ = -JJ n := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_neg, JJ_mul_self, neg_neg]

theorem JJ_conjTranspose : (JJ n)ᴴ = -JJ n := by
  unfold JJ
  rw [fromBlocks_conjTranspose, Matrix.fromBlocks_neg]
  simp

theorem sig_eq (X : M2 n) : sig X = JJ n * Xᴴ * JJ n := by
  unfold sig
  rw [JJ_inv]
  simp [Matrix.neg_mul]

theorem sig_conjTranspose (X : M2 n) : (sig X)ᴴ = JJ n * X * JJ n := by
  rw [sig_eq]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, JJ_conjTranspose, Matrix.neg_mul,
    Matrix.mul_neg, neg_neg, Matrix.mul_assoc]

theorem lie_half1 (Z : M2 n) (t : ℝ) :
    ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))ᴴ * JJ n + JJ n * ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))) = 0 := by
  have h := JJ_mul_self (n := n)
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, sig_conjTranspose, Complex.star_def,
    Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  rw [sig_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, h]
  rw [← Matrix.mul_assoc (JJ n) (JJ n), h]
  simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  module

theorem lie_half2 (Z : M2 n) (t : ℝ) :
    ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z)))ᴴ * JJ n +
      JJ n * ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))) = 0 := by
  have h := JJ_mul_self (n := n)
  have hI : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [star_div₀, star_one, star_mul', Complex.star_def, Complex.conj_I]
    simp [Complex.conj_ofNat]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, sig_conjTranspose, hI, Complex.star_def,
    Complex.conj_ofReal]
  rw [sig_eq]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, h]
  rw [← Matrix.mul_assoc (JJ n) (JJ n), h]
  simp only [Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, Matrix.one_mul]
  module

theorem inG_exp_of_lie {X : M2 n} (hX : Xᴴ * JJ n + JJ n * X = 0) : InG (NormedSpace.exp X) := by
  unfold InG
  have hJu : IsUnit (JJ n) := by
    refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    have := congrArg Matrix.det (JJ_mul_self (n := n))
    rw [Matrix.det_mul, Matrix.det_neg] at this
    refine isUnit_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero] at this
    simp at this
  have hXh : Xᴴ = JJ n * (-X) * (JJ n)⁻¹ := by
    have h1 : Xᴴ * JJ n = -(JJ n * X) := eq_neg_of_add_eq_zero_left hX
    calc Xᴴ = Xᴴ * JJ n * (JJ n)⁻¹ := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hJu), Matrix.mul_one]
      _ = JJ n * (-X) * (JJ n)⁻¹ := by rw [h1, Matrix.mul_neg, Matrix.neg_mul]
  rw [← Matrix.exp_conjTranspose, hXh, Matrix.exp_conj _ _ hJu, Matrix.exp_neg]
  have hE : IsUnit (NormedSpace.exp X) := Matrix.isUnit_exp X
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (JJ n)⁻¹ (JJ n),
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hJu), Matrix.one_mul, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hE), Matrix.mul_one]

theorem expLie (x Z : M2 n) (t : ℝ) (hx : InG x) :
    InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) ∧
      InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z)))) := by
  have hmul : ∀ {a b : M2 n}, InG a → InG b → InG (a * b) := fun {a b} ha hb => by
    unfold InG at *
    calc (a * b)ᴴ * JJ n * (a * b) = bᴴ * (aᴴ * JJ n * a) * b := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = JJ n := by rw [ha, hb]
  exact ⟨hmul hx (inG_exp_of_lie (lie_half1 Z t)), hmul hx (inG_exp_of_lie (lie_half2 Z t))⟩

theorem rcCongr : RcCongr := by
  intro n F F' Z x _ h h1 h2
  unfold rC
  have e1 : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z))))) =
      fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) := funext fun t => h _ (h1 t)
  have e2 : (fun t : ℝ => F (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))) =
      fun t : ℝ => F' (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z)))) := funext fun t => h _ (h2 t)
  rw [e1, e2]

end PositivityTheory.Rg.Sw.HSt
