import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftEisensteinLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResEtaOfIsWeilSch
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzExistsRealMajorantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableSchwartzRestrictionColumnsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationThetaIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilRepresentationFourierCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaFourierCoefficientWeylIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponentsStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RCellP

variable {D : D7} {n r t : ℕ}

theorem maj_mem {θ : InfFam D} {a b : ℕ} {φ : Mx D a b → ℂ} (hφ : φ ∈ schwartzA θ a b) :
    ∃ F ∈ schwartzA θ a b, ∀ x, (F x).im = 0 ∧ ‖φ x‖ ≤ (F x).re := by
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨F₀, hF₀⟩ := GlobalTheory.T.schwartz_exists_real_majorant _ f
    refine ⟨fun x => F₀ (fun τ i j => compAt θ τ x i j) * (fun u => ((‖g u‖ : ℝ) : ℂ)) (fun i j => finPart D (x i j)),
      Submodule.subset_span ⟨F₀, fun u => ((‖g u‖ : ℝ) : ℂ), ⟨?_, ?_⟩, rfl⟩, fun x => ?_⟩
    · exact hg.1.comp fun z => ((‖z‖ : ℝ) : ℂ)
    · exact hg.2.comp_left (g := fun z => ((‖z‖ : ℝ) : ℂ)) (by simp)
    · have h := hF₀ (fun τ i j => compAt θ τ x i j)
      constructor
      · simp [Complex.mul_im, h.1]
      · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, norm_mul]
        exact mul_le_mul_of_nonneg_right h.2 (norm_nonneg _)
  | zero => exact ⟨0, Submodule.zero_mem _, fun x => by simp⟩
  | add φ₁ φ₂ _ _ h₁ h₂ =>
    obtain ⟨F₁, m₁, e₁⟩ := h₁
    obtain ⟨F₂, m₂, e₂⟩ := h₂
    refine ⟨F₁ + F₂, Submodule.add_mem _ m₁ m₂, fun x => ⟨?_, ?_⟩⟩
    · simp [(e₁ x).1, (e₂ x).1]
    · simpa using (norm_add_le _ _).trans (add_le_add (e₁ x).2 (e₂ x).2)
  | smul c φ _ h =>
    obtain ⟨F, m, e⟩ := h
    refine ⟨((‖c‖ : ℝ) : ℂ) • F, Submodule.smul_mem _ _ m, fun x => ⟨?_, ?_⟩⟩
    · simp [(e x).1]
    · simpa [norm_smul] using mul_le_mul_of_nonneg_left (e x).2 (norm_nonneg c)

theorem exists_real_schwartz_majorant {θ : InfFam D} {a b : ℕ} (Φ : schwartzA θ a b) :
    ∃ F : schwartzA θ a b, ∀ x, (F.1 x).im = 0 ∧ ‖Φ.1 x‖ ≤ (F.1 x).re :=
  let ⟨F, m, e⟩ := maj_mem Φ.2
  ⟨⟨F, m⟩, e⟩

theorem c_jn_cont (hn : r + t = n) {a : ℕ} : Continuous (fun z : Mx D a r × Mx D a t => jn hn z.1 z.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun z : Mx D a r × Mx D a t => Matrix.fromCols z.1 z.2 i ((finSumFinEquiv.trans (finCongr hn)).symm j)
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = c
  rcases c with c | c
  · exact continuous_fst.matrix_elem i c
  · exact continuous_snd.matrix_elem i c

theorem inner_product_mul_eq_pairing (V : HSp D) (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) (x : Mx D V.rank r) (v : Mx D V.rank t) (y : Mx D r t) :
    ip V (mm x y) v = pr b₀ y (yv V b₀ (x, v)) := by
  have h1 : (b₀.1.map (incA D) : Mx D r r) * rat b₀.1⁻¹ = 1 := by
    show b₀.1.map (incA D) * b₀.1⁻¹.map (incA D) = 1
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (Ne.isUnit hb)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  simp only [ip, pr, yv, mm, adj_mul]
  rw [← Matrix.mul_assoc (b₀.1.map (incA D)), h1, Matrix.one_mul, Matrix.mul_assoc]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (u : AF D.host.F) : conj (ψ u) = ψ (-u) := by
  have h1 : ψ u * conj (ψ u) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hψ.2.1 u]
    simp
  have h2 : ψ u * ψ (-u) = 1 := by
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have h0 : ψ u ≠ 0 := fun h => by simp [h] at h1
  exact mul_left_cancel₀ h0 (h1.trans h2.symm)

theorem character_quadratic_form_identity (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (b₀ : HermE D r) (b : hermA D t)
    (z : Mx D V.rank r × Mx D V.rank t) :
    pch ψ b.1 (ip V z.2 z.2) * conj (ψ (halfTr (Matrix.trace (mm b.1 (pr b₀ (yv V b₀ z) (yv V b₀ z)))))) = pch ψ b.1 (qv V b₀ z) := by
  rw [conj_psi hψ]
  simp only [pch, qv, mm]
  rw [← AddChar.map_add_eq_mul, Matrix.mul_sub, Matrix.trace_sub]
  congr 1
  simp only [halfTr, trA, map_sub]
  ring

theorem integrable_schwartz_slice {θ : InfFam D} (hθ : IsInfFam θ) {a : ℕ} (hn : r + t = n) (μt : Measure (Mx D a t)) [μt.IsAddHaarMeasure]
    (Φ : schwartzA θ a n) (x : Mx D a r) : Integrable (fun v => Φ.1 (jn hn x v)) μt := GlobalTheory.T.integrable_schwartz_restriction_columns hθ hn μt Φ x

theorem fub {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {μ : Measure Y} {ν : Measure X} [SFinite μ] [SFinite ν]
    {P : X → ℂ} {e : Y → X → ℂ} {O : Y → ℂ} (hP : Integrable P ν) (hO : Integrable O μ)
    (he : AEStronglyMeasurable (fun q : Y × X => e q.1 q.2) (μ.prod ν)) (hn : ∀ y z, ‖e y z‖ = 1)
    (hem : ∀ y, AEStronglyMeasurable (e y) ν) :
    (∀ y, Integrable (fun z => P z * e y z) ν) ∧
    ∫ y, (∫ z, P z * e y z ∂ν) * O y ∂μ = ∫ z, P z * ∫ y, e y z * O y ∂μ ∂ν := by
  have hIPe : ∀ y, Integrable (fun z => P z * e y z) ν := fun y =>
    hP.mono (hP.aestronglyMeasurable.mul (hem y)) (ae_of_all _ fun z => by simp [hn])
  refine ⟨hIPe, ?_⟩
  have hbase := Integrable.mul_prod hO hP
  have hIF : Integrable (Function.uncurry fun (y : Y) z => P z * e y z * O y) (μ.prod ν) := by
    refine hbase.mono ?_ (ae_of_all _ fun q => ?_)
    · exact (hP.aestronglyMeasurable.comp_snd.mul he).mul hO.aestronglyMeasurable.comp_fst
    · simp [Function.uncurry, hn, mul_comm]
  calc ∫ y, (∫ z, P z * e y z ∂ν) * O y ∂μ = ∫ y, ∫ z, P z * e y z * O y ∂ν ∂μ := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        beta_reduce
        rw [integral_mul_const]
    _ = ∫ z, ∫ y, P z * e y z * O y ∂μ ∂ν := integral_integral_swap hIF
    _ = _ := by
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        beta_reduce
        simp only [mul_assoc]
        rw [integral_const_mul]

theorem integrable_fib (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D}
    (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕)
    (b₀ : HermE D r) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib)
    (Φ : schwartzA θ V.rank n) {w : G D t} (hw : IsW w) :
    Integrable (fun z => Φ.1 (jn hn z.1 z.2)) (fib.prod μt) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -⟩ := lattice_Mx D V.rank t
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank t) := ⟨rfl⟩
  haveI := hfib.fin
  haveI := hμt.choose_spec.1
  obtain ⟨F, hF⟩ := exists_real_schwartz_majorant Φ
  have hPa := hP D n r t hn M V ψ hψ χ hχ hη θ hθ μ hμ ω hω μr μt hμr hμt
  have hm : ∀ x, ∫ v, F.1 (jn hn x v) ∂μt = (ω (M.emb w) F).1 (jn hn x 0) := by
    intro x
    rw [(hPa F).2.2 w hw x 0]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    have : ip V (0 : Mx D V.rank t) v = 0 := by
      simp [ip, mm, adj]
    simp [this]
  have hφ := (hPa (ω (M.emb w) F)).2.1
  have hint := (hfib.int _ hφ).1
  have hcF : Continuous fun z : Mx D V.rank r × Mx D V.rank t => F.1 (jn hn z.1 z.2) :=
    (GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ F).comp (c_jn_cont hn)
  have hcΦ : Continuous fun z : Mx D V.rank r × Mx D V.rank t => Φ.1 (jn hn z.1 z.2) :=
    (GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ Φ).comp (c_jn_cont hn)
  have hIF : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => F.1 (jn hn z.1 z.2)) (fib.prod μt) := by
    refine (integrable_prod_iff hcF.aestronglyMeasurable).2 ⟨ae_of_all _ fun x => integrable_schwartz_slice hθ hn μt F x, ?_⟩
    refine (hint.re).congr (ae_of_all _ fun x => ?_)
    have e1 : ∀ v, ‖F.1 (jn hn x v)‖ = (F.1 (jn hn x v)).re := by
      intro v
      have h := hF (jn hn x v)
      have h0 : 0 ≤ (F.1 (jn hn x v)).re := (norm_nonneg _).trans h.2
      rw [← Complex.re_add_im (F.1 (jn hn x v)), h.1]
      simp [abs_of_nonneg h0]
    simp only [e1]
    show (RCLike.re ((ω (M.emb w) F).1 (jn hn x 0))) = _
    rw [← hm x]
    exact (integral_re (integrable_schwartz_slice hθ hn μt F x)).symm
  exact hIF.mono hcΦ.aestronglyMeasurable (ae_of_all _ fun z =>
    (hF _).2.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _)))

theorem core (hP : PartFT) {hn : r + t = n} (M : Maps D hn) (m : Meas D r t) (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsCharAF D.host.F ψ) {χ : (AE D)ˣ →* Circle} (hχ : IsHeckeChar D χ) (hη : ResEta D χ V.rank) {θ : InfFam D}
    (hθ : IsInfFam θ) {μ : Measure (Mx D V.rank n)} (hμ : ∃ 𝓕, IsCovolOne (ratMx D V.rank n) μ 𝓕)
    {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    {μr : Measure (Mx D V.rank r)} (hμr : ∃ 𝓕, IsCovolOne (ratMx D V.rank r) μr 𝓕)
    {μt : Measure (Mx D V.rank t)} (hμt : ∃ 𝓕, IsCovolOne (ratMx D V.rank t) μt 𝓕)
    (b₀ : HermE D r) (hb : b₀.1.det ≠ 0) {fib : Measure (Mx D V.rank r)} (hfib : IsFib ψ θ V b₀ μr m.lz fib)
    {Ω : G D t → Mx D r t → ℂ} (hΩ : IsTh ψ χ θ b₀ m.μ Ω)
    (Φ : schwartzA θ V.rank n) {nb : hermA D t → G D t} (hnb : IsNMap nb) {w : G D t} (hw : IsW w) (b : hermA D t)
    (hI : Integrable (fun z => Φ.1 (jn hn z.1 z.2)) (fib.prod μt)) :
    Rsec M m ψ b₀ (fun g => (ω g Φ).1 0) 1 Ω (w * nb b) =
        ∫ z, Φ.1 (jn hn z.1 z.2) * conj (Ω 1 (yv V b₀ z)) * pch ψ b.1 (qv V b₀ z) ∂(fib.prod μt) := by
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D V.rank r
  obtain ⟨j1, j2, j3, j4, -⟩ := lattice_Mx D V.rank t
  obtain ⟨k1, k2, k3, k4, -⟩ := lattice_Mx D r t
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  haveI : BorelSpace (Mx D V.rank t) := ⟨rfl⟩
  haveI : BorelSpace (Mx D r t) := ⟨rfl⟩
  haveI := hfib.fin
  haveI := hμt.choose_spec.1
  haveI := m.hμ.1
  obtain ⟨hc1, hc2, hc3, hc4, hn1, hn2⟩ := GlobalTheory.T.continuous_theta_kernel_components (t := t) hψ V b₀ b
  have hcΦ : Continuous fun z : Mx D V.rank r × Mx D V.rank t => Φ.1 (jn hn z.1 z.2) :=
    (GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ Φ).comp (c_jn_cont hn)
  have hcP : Continuous fun z : Mx D V.rank r × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2) * Φ.1 (jn hn z.1 z.2) := hc1.mul hcΦ
  have hIP : Integrable (fun z : Mx D V.rank r × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2) * Φ.1 (jn hn z.1 z.2)) (fib.prod μt) :=
    hI.mono hcP.aestronglyMeasurable (ae_of_all _ fun z => by simp [hn1])
  have hcΩ : Continuous (Ω (w * nb b)) := hΩ.cont.comp (continuous_const.prodMk continuous_id)
  have hIΩ : Integrable (fun y => conj (Ω (w * nb b) y)) m.μ :=
    (GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ m.μ ⟨_, hΩ.mem (w * nb b)⟩).mono
      (Complex.continuous_conj.comp hcΩ).aestronglyMeasurable (ae_of_all _ fun y => by simp)
  obtain ⟨hIPe, hsw⟩ := fub (μ := m.μ) (ν := fib.prod μt) (e := fun y z => ψ (trA (Matrix.trace (pr b₀ y (yv V b₀ z))))) hIP hIΩ
    hc3.aestronglyMeasurable (fun y z => hn2 _)
    (fun y => (hc3.comp (Continuous.prodMk_right y)).aestronglyMeasurable)
  have hW : ∀ y, Wz M m ψ b₀ (fun g => (ω g Φ).1 0) (M.sh y * M.emb (w * nb b) * 1) =
      ∫ z, pch ψ b.1 (ip V z.2 z.2) * Φ.1 (jn hn z.1 z.2) * ψ (trA (Matrix.trace (pr b₀ y (yv V b₀ z)))) ∂(fib.prod μt) := by
    intro y
    rw [GlobalTheory.T.weil_representation_theta_integral hP M m V hψ hχ hη hθ hμ hω hμr hμt b₀ hfib Φ, integral_prod _ (hIPe y)]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    beta_reduce
    rw [GlobalTheory.T.weil_representation_fourier_coefficient hP M V hψ hχ hη hθ hμ hω hμr hμt Φ hnb hw b y x]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    beta_reduce
    rw [inner_product_mul_eq_pairing V b₀ hb x v y]
  unfold Rsec
  simp only [hW]
  rw [hsw]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  beta_reduce
  rw [GlobalTheory.T.theta_fourier_coefficient_weyl_integral hψ hχ hΩ hnb hw b (yv V b₀ z), map_mul, ← character_quadratic_form_identity V hψ b₀ b z]
  ring

theorem rcell : WMaj → PartFT → RCell := by
  intro _ hP D n t B W d hn ψ χ θ μB μW ωB ωW hS M m b₀ hb μr μt hμr hμt fib hfib Ω hΩ Φ nb hnb w hw
  obtain ⟨𝓕, h𝓕⟩ := hS.hμB
  have hn0 : 0 < n := by
    have := hS.pos
    have := hS.lt
    omega
  have hη : ResEta D χ B.rank := GlobalTheory.RegSch.JointCont.resEta_of_isWeilSch hn0 hS.hψ hS.hθ h𝓕 hS.hB
  have hI := integrable_fib hP M m B hS.hψ hS.hχ hη hS.hθ ⟨𝓕, h𝓕⟩ hS.hB hμr hμt b₀ hfib Φ hw
  exact ⟨hI, fun b => core hP M m B hS.hψ hS.hχ hη hS.hθ ⟨𝓕, h𝓕⟩ hS.hB hμr hμt b₀ hb hfib hΩ Φ hnb hw b hI⟩

end GlobalTheory.CompanionTheory.RCellP

end
