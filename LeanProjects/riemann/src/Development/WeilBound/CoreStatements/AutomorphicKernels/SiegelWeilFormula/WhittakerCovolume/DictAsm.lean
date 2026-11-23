import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.WhitAtCOneIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GramZeroLeft
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.SectionLinearFinsetSum

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

set_option linter.unusedSectionVars false

theorem asm_incl (e : E) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) e = HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) e := rfl

theorem asm_cA (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = HeckeCharacterZeroLocus.SiegelWeilU.sigR (AF F) σ z := rfl

theorem asm_half : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
  refine invOf_eq_right_inv ?_
  rw [show (2 : AF F) = algebraMap F (AF F) 2 from (map_ofNat _ 2).symm, ← map_mul]
  norm_num

theorem asm_scalar_mul {n : ℕ} (η : E) (M : Matrix (Fin n) (Fin n) (AE F E)) :
    incM F (Matrix.scalar (Fin n) η) * M = (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η) • M := by
  ext i j
  simp only [incM, Matrix.mul_apply, Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply, apply_ite,
    map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Matrix.smul_apply, smul_eq_mul]
  rfl

theorem asm_gramR (d : SD σ) (η : E) (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (Jd d η) Y =
      (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η) • (d.gram (toMx Y) (toMx Y))ᵀ := by
  ext c a
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.gramR, HeckeCharacterZeroLocus.SiegelWeilU.hR, HeckeCharacterZeroLocus.SiegelWeilU.hform, HeckeCharacterZeroLocus.SiegelWeilU.JR, Jd,
    Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, SD.gram, Matrix.mul_apply, toMx,
    Matrix.of_apply, incM, map_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [asm_incl, asm_cA]
  ring

theorem asm_phase_cell {d : SD σ} {R : RD d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : Rel d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b)
    (Y : Fin d.n → Fin d.m → AF F ⊗[F] E) :
    -(⅟(2 : AF F) * d.tt (β.1 * d.gram (toMx Y) (toMx Y))) =
      PositivityTheory.PfSWUS.Loc.trPair (AF F) ((hOf β).1) (HeckeCharacterZeroLocus.SiegelWeilU.gramR (AF F) σ (Jd d η) Y) := by
  rw [PositivityTheory.PfSWUS.Loc.trPair, asm_gramR, hr.hof β, SD.tt, asm_half, Matrix.neg_mul, asm_scalar_mul,
    Matrix.smul_mul, Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg, mul_neg, neg_neg]
  congr 1
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem asm_phase_whit {d : SD σ} {R : RD d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hr : Rel d R x t u T η T₀ hOf θ fr g) (β : nA σ d.Y d.b) :
    -d.tt (T.1.1 * β.1) =
      -PositivityTheory.PfSWUS.Loc.trPair (AF F) ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) ((hOf β).1) := by
  rw [neg_inj, PositivityTheory.PfSWUS.Loc.trPair, hr.hof β, hr.rat, SD.tt, asm_scalar_mul, Matrix.mul_neg, Matrix.mul_smul,
    Matrix.trace_neg, Matrix.trace_smul, smul_eq_mul, map_neg]
  have h2 : ∑ a, ∑ c, ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F))) a c * ((hOf β).1 : Mx F E d.n d.n) c a =
      algebraMap (AF F) (AE F E) (-2) * (HeckeCharacterZeroLocus.SiegelWeilU.inclR (F := F) (AF F) η *
        (incM F T₀ * ((hOf β).1 : Mx F E d.n d.n)ᵀ).trace) := by
    simp only [Td, Matrix.map_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_neg,
      map_ofNat, Matrix.trace, Matrix.diag, Matrix.mul_apply, incM, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [asm_incl]
    ring
  rw [h2, ← Algebra.smul_def (-2 : AF F) _, LinearMap.map_smul, smul_eq_mul, ← mul_assoc]
  have h5 : algebraMap F (AF F) (1 / 2) * (-2 : AF F) = -1 := by
    rw [show (-2 : AF F) = algebraMap F (AF F) (-2) by rw [map_neg, map_ofNat], ← map_mul]
    norm_num
  rw [h5]
  ring

theorem asm_cpow_split {C ν : ℝ} (hC : 0 < C) (hν : 0 < ν) (w : ℂ) :
    ((C * ν⁻¹ : ℝ) : ℂ) ^ w = (C : ℂ) ^ w * (ν : ℂ) ^ (-w) := by
  rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hC.le (inv_nonneg.2 hν.le), Complex.ofReal_inv,
    Complex.inv_cpow _ _ (by rw [Complex.arg_ofReal_of_nonneg hν.le]; exact Real.pi_pos.ne), Complex.cpow_neg]

theorem asm_c_ne (d : SD σ) (t : GL (Fin d.n) (AE F E)) :
    (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
  have hpos : 0 < (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) := by
    have h : absE F E (Matrix.GeneralLinearGroup.det t) * absE F E (Matrix.GeneralLinearGroup.det t)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have h0 : absE F E (Matrix.GeneralLinearGroup.det t) ≠ 0 := left_ne_zero_of_mul_eq_one h
    exact_mod_cast pos_iff_ne_zero.2 h0
  exact mul_ne_zero (Circle.coe_ne_zero _) (Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hpos _).ne')

theorem asm_meanC_smul {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (μH : Measure (HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J))
    (𝓕 : Set (HeckeCharacterZeroLocus.SiegelWeilU.HA (AF F) σ J)) (c : ℂ) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ)
    (S : Set (Fin n → Fin M → E)) :
    HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ M J (fun Y => c * Φ Y) S) =
      c * HeckeCharacterZeroLocus.SiegelWeilU.meanC μH 𝓕 (HeckeCharacterZeroLocus.SiegelWeilU.thetaS F E σ M J Φ S) := by
  simp only [HeckeCharacterZeroLocus.SiegelWeilU.meanC, HeckeCharacterZeroLocus.SiegelWeilU.thetaS, tsum_mul_left, integral_const_mul, Complex.real_smul]
  ring

theorem dictAsmX : DictAsmX := by
  intro hCell hRel hH hM hTh hT hA F E _ _ _ _ _ σ d R Φ hΦ P gf hpg x hx nb lam 𝓖 hcd ε w hw T hTnd
  obtain ⟨t, u, hxtu⟩ := hx
  obtain ⟨η, T₀, hOf, θ, fr, g, l, εs, Φg, Φf, Φv, μ, ν, hr, hΦg, hani, hεs, hcm, hherm, hTT, hdet, hchr, hpl, hfr,
    hpure, hprod, hsdW, hsdH⟩ := hRel hT hA F E σ d R Φ hΦ P gf hpg x t u hxtu T hTnd
  obtain ⟨lv, L₁, L₂, C, hC, hlv, hco, hstd, hht⟩ := hH F E σ d R x t u T η T₀ hOf θ fr g hr nb lam 𝓖 hcd ε w hw
  obtain ⟨hMβ, hMZ⟩ := hM F E σ d R x t u T η T₀ hOf θ fr g hr
  obtain ⟨hembβ, hpresβ⟩ := hMβ nb lam 𝓖 hcd ν hsdH
  obtain ⟨νc, hνc⟩ := (hA F E σ d).1
  obtain ⟨hembZ, hpresZ⟩ := hMZ μ νc hsdW hνc
  obtain ⟨μH, 𝓕, hμH, h𝓕, horb⟩ := hTh F E σ d η hr.ne hr.herm
  set c : ℂ := (d.χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      (((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ) with hc
  have hc0 : c ≠ 0 := asm_c_ne d t
  have hTx : ∀ Y, d.T (d.om x Φ) (toMx Y) = c * Φg Y := by
    intro Y
    rw [hΦg Y]
    exact (hT.2.1 F E σ d Φ hΦ.1).2.1 x t u hxtu (toMx Y)
  have hint : ∀ z : ℂ, ∀ β : nA σ d.Y d.b,
      flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) * d.B.ψ (-d.tt (T.1.1 * β.1)) =
        c * (C : ℂ) ^ (z - s0 d.m d.n) * Gen.whI (AF F) σ (Jd d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
          ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β) := by
    intro z β
    obtain ⟨hνpos, ha⟩ := hht β
    have hcell := hCell hT F E σ d νc hνc ε w hw Φ hΦ.1 (nb β) x β.1 (hcd.1 β)
    have hZ : ∫ Z, d.B.ψ (-(⅟(2 : AF F) * d.tt (β.1 * d.gram Z Z))) * d.T (d.om x Φ) Z ∂νc =
        c * PositivityTheory.PfSWUS.Loc.jtR (AF F) σ (Jd d η) d.B.ψ μ Φg (hOf β) := by
      rw [← hpresZ.integral_comp hembZ]
      simp only [PositivityTheory.PfSWUS.Loc.jtR, hTx, asm_phase_cell hr β]
      rw [← integral_const_mul]
      congr 1
      funext Y
      ring
    have hs : s0 d.m d.n = ((d.m : ℂ) - d.n) / 2 := rfl
    simp only [flat]
    rw [hcell, hZ, ha, asm_phase_whit hr β, asm_cpow_split hC hνpos]
    simp only [Gen.whI, hs]
    ring
  refine ⟨2, Jd d η, Td η T₀, d.bs, d.B.ψ, θ, l, εs, fr, g, lv, L₁, L₂, Φg, Φf, Φv, μ, ν, c, C,
    ⟨hcm, hherm, hTT, hdet, hchr, hpl, hfr, hlv, hco, hstd, hpure, hprod, hsdW, hsdH⟩, hani, hεs, hC,
    ⟨0, fun z _ => ⟨fun hI => ?_, ?_⟩⟩, μH, 𝓕, hμH, h𝓕, ?_⟩
  · have hk : c * (C : ℂ) ^ (z - s0 d.m d.n) ≠ 0 :=
      mul_ne_zero hc0 (Complex.cpow_ne_zero_iff.2 (Or.inl (Complex.ofReal_ne_zero.2 hC.ne')))
    have h1 : Integrable (fun β => flat d.a (d.sec0 Φ) (s0 d.m d.n) z (w * nb β * x) *
        d.B.ψ (-d.tt (T.1.1 * β.1))) lam :=
      hI.mul_bdd (lin_psi_meas d T.1.1).aestronglyMeasurable
        (Eventually.of_forall fun β => (GlobalTheory.StdCharFromIsStd.norm_psi d.ok.good.std _).le)
    have h2 := h1.const_mul (c * (C : ℂ) ^ (z - s0 d.m d.n))⁻¹
    have hcomp : Integrable (fun β => Gen.whI (AF F) σ (Jd d η) d.B.ψ μ Φg (Gen.nuA θ g lv L₁ L₂)
        ((Td η T₀).map (HeckeCharacterZeroLocus.SiegelWeilU.inclR (AF F))) z (hOf β)) lam := by
      refine h2.congr (Eventually.of_forall fun β => ?_)
      simp only [hint z β]
      exact inv_mul_cancel_left₀ hk _
    exact (hpresβ.integrable_comp_emb hembβ).1 hcomp
  · simp_rw [hint z]
    rw [integral_const_mul, hpresβ.integral_comp hembβ]
  · rw [horb T T₀ hr.rat (d.om x Φ) (om_mem_sch d x hΦ.1)]
    have : (fun Y => d.T (d.om x Φ) (toMx Y)) = fun Y => c * Φg Y := funext hTx
    rw [this, asm_meanC_smul]

end PositivityTheory.SiegelWeilFormula.KWhit

end
