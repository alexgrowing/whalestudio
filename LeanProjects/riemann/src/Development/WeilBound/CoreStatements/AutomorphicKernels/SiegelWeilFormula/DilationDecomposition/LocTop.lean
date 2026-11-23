import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocFamPf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocGaussPf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DBoundB
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocAlgPf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocNbar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpMMLaw

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

open PositivityTheory.Rg.Sw.Glob (aC ptZ jC gC actZ jF IsSiegel gZf)
open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem fP_smul_one {m n : ℕ} (c : ℂ) : fP (c • (1 : PX m n)) = fun u => c * fP 1 u := by
  funext u
  simp only [fP, evX, MvPolynomial.smul_eval, map_one]
  ring

theorem fP_one_zero {m n : ℕ} : fP (1 : PX m n) 0 = 1 := by
  simp [fP, evX, gs]

theorem fP_one_of {m n : ℕ} (x : Fin m → Fin n → ℂ) (hx : ∀ i j, x i j = 0) : fP (1 : PX m n) x = 1 := by
  have : x = 0 := funext fun i => funext fun j => hx i j
  rw [this]; exact fP_one_zero

theorem weight_factor_unipotent_one {n : ℕ} (p q : ℕ) (e : ℤ) (y : GR n) (b : Matrix (Fin n) (Fin n) ℂ) (hy : mR y = nU b) :
    F0 p q e y = 1 := by
  simp only [F0, f0, u1, u2, hy, nU, Matrix.toBlocks_fromBlocks₂₁, Matrix.toBlocks_fromBlocks₂₂, smul_zero, zero_add,
    neg_zero, Matrix.det_one, _root_.one_zpow, mul_one, Matrix.det_fromBlocks_zero₂₁]

theorem vac_law {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P)) (y : GR d.n) :
    L y (fP 1) = fun u => F0 p q e y *
      gZf (fun _ : Fin d.m => true) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (2 * Real.pi) (actZ y (Complex.I • 1)) u := by
  obtain ⟨pp, k, hpp, hk, rfl⟩ := PositivityTheory.Rg.Sw.AbsSt.iwa d.n y
  have hk' : InK (mR k) := hk
  obtain ⟨nb, ma, b, a, hb, ha, hnb, hma, hpe, hZ⟩ := up_decomp_closed pp hpp
  obtain ⟨c, -, hcf⟩ := R.locOp_mM hT hG hL
  have hsw1 : IsSw (fP (1 : PX d.m d.n)) := hFP d.m d.n 1
  have hk1 : L k (fP 1) = fun u => F0 p q e k * fP 1 u := by
    rw [hρ k 1 hk', hLD.kvac k hk', fP_smul_one]
  have hma21 : (mR ma).toBlocks₂₁ = 0 := by rw [hma, mLoc, Matrix.toBlocks_fromBlocks₂₁]
  have hnb21 : (mR nb).toBlocks₂₁ = 0 := by rw [hnb, nU, Matrix.toBlocks_fromBlocks₂₁]
  have hca : c a = F0 p q e ma := by
    have h1 := hLD.law 1 ma 1 hma21
    have h0 : fP (1 : PX d.m d.n) (Matrix.of (0 : Fin d.m → Fin d.n → ℂ) * a) = 1 := by
      have e0 : (Matrix.of (0 : Fin d.m → Fin d.n → ℂ) * a : Matrix (Fin d.m) (Fin d.n) ℂ) = 0 := by
        ext i j; simp [Matrix.mul_apply]
      rw [e0]; exact fP_one_zero
    rw [mul_one, hsL, hsL, hcf ma a ha hma _ hsw1, R.locOp_one hT hG hL _ hsw1] at h1
    beta_reduce at h1
    rw [fP_one_of _ (fun i j => by
      show ∑ k, (Matrix.of (0 : Fin d.m → Fin d.n → ℂ)) i k * a k j = 0
      simp), fP_one_zero] at h1
    simpa using h1
  have hF0 : F0 p q e (pp * k) = c a * F0 p q e k := by
    have m1 := ((PositivityTheory.Rg.Sw.AbsSt.mult d.n p q e).2 pp k hpp).1
    have m2 := ((PositivityTheory.Rg.Sw.AbsSt.mult d.n p q e).2 nb ma hnb21).1
    rw [m1, hpe, m2, weight_factor_unipotent_one p q e nb b hnb, one_mul, hca]
  have hZ' : actZ (pp * k) (Complex.I • 1) = b + Complex.I • (a * aᴴ) := by rw [actZ_mul_K pp k hk', hZ]
  have hswk : IsSw (L k (fP 1)) := (hL k _ hsw1).1
  have hswm : IsSw (L ma (L k (fP 1))) := (hL ma _ hswk).1
  rw [R.locOp_mul hT hG hL pp k _ hsw1, hpe, R.locOp_mul hT hG hL nb ma _ hswk, R.locOp_nU hT hG hL nb b hb hnb _ hswm,
    hcf ma a ha hma _ hswk, ← hpe, hF0, hZ', hk1]
  funext u
  rw [gzf_eval (R.sg w) b a hb u]
  ring_nf
  rfl

theorem cont_slice {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : A × B × C → ℂ) (s : Set (A × B × C)) (hf : ContinuousOn f s) (a : A) (t : Set (B × C))
    (ht : ∀ x ∈ t, (a, x.1, x.2) ∈ s) : ContinuousOn (fun x : B × C => f (a, x.1, x.2)) t :=
  hf.comp (by fun_prop) ht

theorem cont_slice2 {A B C : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]
    (f : A × B × C → ℂ) (s : Set (A × B × C)) (hf : ContinuousOn f s) (c : C) (t : Set (A × B))
    (ht : ∀ x ∈ t, (x.1, x.2, c) ∈ s) : ContinuousOn (fun x : A × B => f (x.1, x.2, c)) t :=
  hf.comp (by fun_prop) ht

def kerFT {m n : ℕ} (s : ℂ) (ξ v : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of ξ)ᴴ * Matrix.of v)).re : ℂ))

theorem kerFT_cont {m n : ℕ} (s : ℂ) (ξ : Fin m → Fin n → ℂ) : Continuous (kerFT s ξ) := by
  unfold kerFT
  fun_prop

theorem kerFT_norm {m n : ℕ} (s : ℂ) (ξ v : Fin m → Fin n → ℂ) : ‖kerFT s ξ v‖ ≤ 1 := by
  unfold kerFT
  rw [show (2 * Real.pi * Complex.I * ((s * Matrix.trace ((Matrix.of ξ)ᴴ * Matrix.of v)).re : ℂ)) =
    ((2 * Real.pi * (s * Matrix.trace ((Matrix.of ξ)ᴴ * Matrix.of v)).re : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem isAddHaarMeasure_vector_volume (n : ℕ) : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _

theorem isAddHaarMeasure_matrix_volume (m n : ℕ) : (volume : Measure (Fin m → Fin n → ℂ)).IsAddHaarMeasure := by
  haveI := isAddHaarMeasure_vector_volume n
  exact Measure.pi.isAddHaarMeasure _

theorem sw_cont_int {m n : ℕ} {f : (Fin m → Fin n → ℂ) → ℂ} (hf : IsSw f) : Continuous f ∧ Integrable f := by
  obtain ⟨φ, rfl⟩ := hf
  haveI := isAddHaarMeasure_matrix_volume m n
  exact ⟨φ.continuous, φ.integrable⟩

theorem gf_L {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (s : ℝ) :
    Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X y s = L (y * a s) (fP 1) := by
  rw [gf_real e p q _ X a ha y s, vac_law R hT hG hFP hL hLD hsL hρ (y * a s)]

theorem fam_sw {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L)
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (s : ℝ) :
    IsSw (fun v => fam d.m X s v) := by
  rw [← fam_eq_L_closed R hT hG hFP hL X a ha s]
  exact (hL (a s) (fP 1) (hFP _ _ 1)).1

theorem gf_L_fam {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (s : ℝ) :
    Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X y s = L y (fun v => fam d.m X s v) := by
  rw [gf_L R hT hG hFP hL hLD hsL hρ X a ha y s, R.locOp_mul hT hG hL y (a s) (fP 1) (hFP _ _ 1),
    fam_eq_L_closed R hT hG hFP hL X a ha s]

theorem der_nbar {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L) (hB : GfBound)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s))
    (nbb : GR d.n) (c : Matrix (Fin d.n) (Fin d.n) ℂ) (hc : cᴴ = c) (hnbb : mR nbb = nbLoc c) (r : ℕ) :
    (fun v => iteratedDeriv r (fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) (m := d.m) X nbb z v) 0) =
      L nbb (fP ((dil (2 * Real.pi) X ^ r) 1)) := by
  obtain ⟨C, s', κ, ε, hs', hκ, h4, -, hconj, -, -⟩ := R.locOp_nbar hT hA hG hL
  obtain ⟨hhol, hcont, hbd⟩ := hB d.m d.n e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (abs_tw R w)
  have h0s : (0 : ℂ) ∈ strip X := fun j => by simp [Real.pi_pos]
  obtain ⟨N, δ, Cb, hN, hδ, hNb⟩ := hbd nbb 0 h0s
  obtain ⟨ρs, hρs, hss⟩ := strip_ball X
  have hev : (fun z : ℂ => (nbb, z)) ⁻¹' N ∈ 𝓝 (0 : ℂ) :=
    (continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds hN
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.mem_nhds_iff.1 hev
  set rr := min ρ0 ρs with hrrdef
  have hrr : 0 < rr := lt_min hρ0 hρs
  have hsub : Metric.ball (0 : ℂ) rr ⊆ strip X := (Metric.ball_subset_ball (min_le_right _ _)).trans hss
  have hsubN : ∀ z ∈ Metric.ball (0 : ℂ) rr, (nbb, z) ∈ N := fun z hz =>
    hball (Metric.ball_subset_ball (min_le_left _ _) hz)
  set Φ : ℂ → (Fin d.m → Fin d.n → ℂ) → ℂ := fun z v => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb z v with hΦ
  have hΦd : ∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 rr) := fun v => (hhol nbb v).mono hsub
  have hΦc : ContinuousOn (fun zv : ℂ × (Fin d.m → Fin d.n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 rr ×ˢ Set.univ) :=
    cont_slice _ _ hcont nbb _ fun zv hzv => ⟨Set.mem_univ _, hsub hzv.1, Set.mem_univ _⟩
  have hΦb : ∀ z ∈ Metric.ball (0 : ℂ) rr, ∀ v, ‖Φ z v‖ ≤ Cb * Real.exp (-δ * sq v) := by
    intro z hz v
    have h := hNb (nbb, z) (hsubN z hz) (hsub hz) v
    simpa [sq, neg_mul] using h
  have hC : C ≠ 0 := by
    intro hC0
    have h := congrFun (h4 _ (hFP d.m d.n 1)) 0
    simp only [locFT, hC0, zero_mul, Pi.smul_apply, smul_eq_mul, fP_one_zero, mul_one] at h
    exact hκ h.symm
  set P : PX d.m d.n := (dil (2 * Real.pi) X ^ r) 1 with hP
  have hGsw : IsSw (L nbb (fP P)) := (hL nbb _ (hFP _ _ P)).1
  obtain ⟨hGc, hGi⟩ := sw_cont_int hGsw
  obtain ⟨ρ9, hρ9, -, hr9⟩ := hol_int_closed Φ rr Cb δ hrr hδ hΦd hΦc hΦb (kerFT s' 0) (kerFT_cont s' 0) (kerFT_norm s' 0)
  obtain ⟨-, hDc, C', hDb⟩ := hr9 r
  have hDi : Integrable (fun v => iteratedDeriv r (fun z => Φ z v) 0) := by
    refine Integrable.mono' ((gauss_int_closed δ hδ).const_mul C') hDc.aestronglyMeasurable (Filter.Eventually.of_forall fun v => ?_)
    exact hDb v
  have key : ∀ ξ : Fin d.m → Fin d.n → ℂ, ∫ v, kerFT s' ξ v * iteratedDeriv r (fun z => Φ z v) 0 =
      ∫ v, kerFT s' ξ v * L nbb (fP P) v := by
    intro ξ
    obtain ⟨ρ1, hρ1, hd1, hr1⟩ := hol_int_closed Φ rr Cb δ hrr hδ hΦd hΦc hΦb (kerFT s' ξ) (kerFT_cont s' ξ) (kerFT_norm s' ξ)
    obtain ⟨ρ2, hρ2, hd2, hr2⟩ := fam_int_hol_closed d.m X (kerFT s' ξ) (kerFT_cont s' ξ) (kerFT_norm s' ξ)
    set ch : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
      Matrix.trace (((((ε : ℤ) : ℂ) * R.ζ⁻¹ * R.ζ⁻¹) • c) * ((Matrix.of ξ)ᴴ * Matrix.of ξ))) with hch
    have hreal : ∀ s : ℝ, |s| < min ρ1 ρ2 → C * (∫ v, kerFT s' ξ v * Φ s v) = ch * (C * ∫ v, kerFT s' ξ v * fam d.m X s v) := by
      intro s _
      have e1 : ∀ v, Φ s v = L nbb (fun v => fam d.m X s v) v := fun v =>
        congrFun (gf_L_fam R hT hG hFP hL hLD hsL hρ X a ha nbb s) v
      simp only [e1]
      exact congrFun (hconj nbb c hc hnbb _ (fam_sw R hT hG hFP hL X a ha s)) ξ
    have hid := iteratedDeriv_eq_of_real_closed (f := fun z => C * ∫ v, kerFT s' ξ v * Φ z v)
      (g := fun z => ch * (C * ∫ v, kerFT s' ξ v * fam d.m X z v)) (ρ := min ρ1 ρ2) (lt_min hρ1 hρ2)
      ((hd1.mono (Metric.ball_subset_ball (min_le_left _ _))).const_mul C)
      (((hd2.mono (Metric.ball_subset_ball (min_le_right _ _))).const_mul C).const_mul ch) hreal r
    rw [iteratedDeriv_const_mul', iteratedDeriv_const_mul', iteratedDeriv_const_mul'] at hid
    beta_reduce at hid
    rw [(hr1 r).1, hr2 r] at hid
    simp only [fam_deriv_closed] at hid
    have h2 : C * ∫ v, kerFT s' ξ v * L nbb (fP P) v = ch * (C * ∫ v, kerFT s' ξ v * fP P v) :=
      congrFun (hconj nbb c hc hnbb _ (hFP _ _ P)) ξ
    exact mul_left_cancel₀ hC (hid.trans h2.symm)
  have hint : ∀ ξ : Fin d.m → Fin d.n → ℂ, ∀ g : (Fin d.m → Fin d.n → ℂ) → ℂ, Integrable g →
      Integrable (fun v => kerFT s' ξ v * g v) := fun ξ g hg =>
    MeasureTheory.Integrable.bdd_mul hg (kerFT_cont s' ξ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun v => kerFT_norm s' ξ v)
  have hfin := ft_uniq_closed s' hs' (fun v => iteratedDeriv r (fun z => Φ z v) 0 - L nbb (fP P) v) (hDc.sub hGc)
    (hDi.sub hGi) (fun ξ => by
      have h := key ξ
      rw [← sub_eq_zero, ← integral_sub (hint ξ _ hDi) (hint ξ _ hGi)] at h
      simpa [kerFT, mul_sub] using h)
  funext v
  exact sub_eq_zero.1 (congrFun hfin v)

theorem gf_der_big {d : SD σ} (R : RD d) {w : InfinitePlace F}
    {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hFP : FPSw) (hL : R.IsLocOp w L) (hB : GfBound)
    {sL : PX d.m d.n →ₗ[ℂ] (GR d.n → ℂ)} {ρ : GR d.n → PX d.m d.n →ₗ[ℂ] PX d.m d.n} {p q : ℕ} {e : ℤ}
    (hLD : LocData (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ)
    (hsL : ∀ P y, sL P y = L y (fP P) 0) (hρ : ∀ (k : GR d.n) P, InK (mR k) → L k (fP P) = fP (ρ k P))
    (X : Fin d.n → ℝ) (a : ℝ → GR d.n) (ha : ∀ s, IsDil X s (a s)) (y : GR d.n) (hy : ((mR y).toBlocks₂₂).det ≠ 0)
    (r : ℕ) (u : Fin d.m → Fin d.n → ℂ) :
    iteratedDeriv r (fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X y z u) 0 =
      L y (fP ((dil (2 * Real.pi) X ^ r) 1)) u := by
  obtain ⟨pp, nbb, c, hpp, hc, hnbb, rfl⟩ := dcell_closed y hy
  obtain ⟨nb', ma', b', a', hb', ha', hnb', hma', hpe', -⟩ := up_decomp_closed pp hpp
  obtain ⟨cm, -, hcf⟩ := R.locOp_mM hT hG hL
  obtain ⟨hhol, -, -⟩ := hB d.m d.n e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (abs_tw R w)
  obtain ⟨ρs, hρs, hss⟩ := strip_ball X
  set eb : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
    Matrix.trace (b' * ((Matrix.of u)ᴴ * Matrix.of u))) with heb
  set w' : Fin d.m → Fin d.n → ℂ := fun i j => (Matrix.of u * a') i j with hw'
  have hform : ∀ f, IsSw f → L (pp * nbb) f u = eb * (cm a' * L nbb f w') := by
    intro f hf
    have h1 : IsSw (L nbb f) := (hL nbb f hf).1
    have h2 : IsSw (L ma' (L nbb f)) := (hL ma' _ h1).1
    rw [R.locOp_mul hT hG hL pp nbb f hf, hpe', R.locOp_mul hT hG hL nb' ma' _ h1,
      R.locOp_nU hT hG hL nb' b' hb' hnb' _ h2, hcf ma' a' ha' hma' _ h1]
    rfl
  have hreal : ∀ s : ℝ, |s| < ρs → Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (pp * nbb) s u =
      eb * (cm a' * Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb s w') := by
    intro s _
    rw [gf_L_fam R hT hG hFP hL hLD hsL hρ X a ha (pp * nbb) s, gf_L_fam R hT hG hFP hL hLD hsL hρ X a ha nbb s]
    exact hform _ (fam_sw R hT hG hFP hL X a ha s)
  have hid := iteratedDeriv_eq_of_real_closed
    (f := fun z => Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X (pp * nbb) z u)
    (g := fun z => eb * (cm a' * Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X nbb z w')) (ρ := ρs) hρs
    ((hhol _ u).mono hss) ((((hhol nbb w').mono hss).const_mul _).const_mul _) hreal r
  rw [hid, iteratedDeriv_const_mul', iteratedDeriv_const_mul']
  beta_reduce
  have hdn := congrFun (der_nbar R hT hA hG hFP hL hB hLD hsL hρ X a ha nbb c hc hnbb r) w'
  beta_reduce at hdn
  rw [hdn, hform _ (hFP _ _ _)]

theorem locFamG_of (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hFP : FPSw) (hLI : LocInst) (hB : GfBound) : LocFamG := by
  intro F E _ _ _ _ _ σ d R w L hL X a ha
  obtain ⟨sL, ρ, p, q, e, -, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  obtain ⟨hhol, hcont, hbd⟩ := hB d.m d.n e p q _ X (abs_tw R w)
  refine ⟨Gf e p q (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) X, fun y t => gf_L R hT hG hFP hL hLD hsL hρ X a ha y t, hhol,
    fun u => ?_, fun q' hq' => ?_, fun y hy r u => gf_der_big R hT hA hG hFP hL hB hLD hsL hρ X a ha y hy r u⟩
  · exact cont_slice2 _ _ hcont u _ fun q' hq' => ⟨Set.mem_univ _, hq'.2, Set.mem_univ _⟩
  · obtain ⟨N, δ, C, hN, hδ, hNb⟩ := hbd q'.1 q'.2 hq'.2
    refine ⟨N, hN, C, δ, hδ, fun q'' hq'' hs u => ?_⟩
    have h := hNb q'' hq'' hs u
    simpa [sq, neg_mul] using h

theorem gfBound : GfBound := fun m n e p q t X ht =>
  PositivityTheory.Rg.Sw.Glob.dBoundPQ m n (fun _ => true) t (2 * Real.pi) e p q X (by positivity) ht

theorem locFamG_of' (hT : TAll) (hA : AuxiliaryPrimeFunction) (hG : GoodAwayEx) (hFP : FPSw) (hLI : LocInst) : LocFamG :=
  locFamG_of hT hA hG hFP hLI gfBound

end PositivityTheory.SiegelWeilFormula.Kdil

end
