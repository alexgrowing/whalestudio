import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelEisensteinDoubled
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeCartanInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesDoubledSpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingDarbouxPairSettingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxSymplecticDoubledHermitianStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingPolarizedDataIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicOfDefinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicFundamentalDomainHaarSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnisotropicUnitaryIntegralConverges
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FundamentalDomainLineDerivativeIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

noncomputable section

namespace GlobalTheory.DblDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem aniso_of_min_eq_zero {r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (h : min r s = 0) :
    ∀ x, form σ X.J x x = 0 → x = 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have e := (hX.sig w).1
  refine GlobalTheory.DefiniteAniso.anisotropic_of_definite hB.cm (B := B) ?_
  rcases Nat.min_eq_zero_iff.1 h with rfl | rfl
  · rw [zero_add] at e; subst e; exact Or.inr hX
  · rw [add_zero] at e; subst e; exact Or.inl hX

theorem vol_ne (hK : KP) {M : Model σ X W} {r s : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hM : M.IsGood B.ψ)
    (han : ∀ x, form σ X.J x x = 0 → x = 0) : (M.μ M.dom).toReal ≠ 0 := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hB.cm
  obtain ⟨C, hC, hcov⟩ := LiftContDef.cocompact_of_aniso hK.siegelSetUnitary hB.cm X.J (one_ne_zero : (1 : E) ≠ 0)
    (by rw [one_smul]; exact GlobalTheory.UnitaryVol.isHermND_map hσ hX) han
  obtain ⟨hTG, h2, h3, h4⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ n X.J
  haveI : BorelSpace (UA σ X.J) := ⟨rfl⟩
  haveI := hM.haar
  haveI := GlobalTheory.UnitaryVol.countable_ratU σ X.J
  have h5 := (GlobalTheory.ThK.DefCovol.of_compact_cover (ratU σ X.J) C hC hcov M.μ M.dom hM.dom).1
  haveI : SMulInvariantMeasure (ratU σ X.J) (UA σ X.J) M.μ :=
    ⟨fun c s _ => measure_preimage_mul M.μ (c : UA σ X.J) s⟩
  haveI : MeasurableConstSMul (ratU σ X.J) (UA σ X.J) := ⟨fun c => measurable_const_mul (c : UA σ X.J)⟩
  have h6 : M.μ M.dom ≠ 0 := hM.dom.measure_ne_zero (NeZero.ne _)
  exact ENNReal.toReal_ne_zero.2 ⟨h6, h5.ne⟩

end GlobalTheory.DblDatum

theorem GlobalTheory.DblDatum.datum : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (Xs : Spc F E n) (W : Spc F E d) (M : Model σ Xs W) (χX χW : Chr F E) (om : Rep σ Xs W) (r s' r₁ s₁ : ℕ),
    IsPair B M χX χW om r s' r₁ s₁ → min r s' = 0 → 1 ≤ n → 1 ≤ d →
    ∀ Φ₂' ∈ PolData B M, ∀ Ψ' ∈ PolData B M,
    ∀ W₂ : Spc F E (d + d), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∃ (K : Subgroup (UA σ W₂.J)) (φ₀ Ψ : UA σ W₂.J → ℂ) (κ : ℂ),
      IsStab B K ∧ IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K ∧
      φ₀ ∈ degPSOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K χX (((n : ℂ) - (d : ℂ)) / 2) ∧
      (∀ s : ℂ, (d : ℝ) / 2 < s.re →
        GlobalTheory.AutomorphicL2Unitary.LeftInv ((siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) ⊓ ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) ∧
        ∀ g, GlobalTheory.Eis.CosetConv (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) g) ∧
      (∀ g, GlobalTheory.Cont.HolValueAt (fun s => GlobalTheory.Eis.cosetSum (siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype) (ratU σ W₂.J) (flatOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K φ₀ (((n : ℂ) - (d : ℂ)) / 2) s) g) (((n : ℂ) - (d : ℂ)) / 2) (Ψ g)) ∧
      κ ≠ 0 ∧ ∀ h h', GlobalTheory.ThKLiftCusp.kern M om Ψ' Φ₂' h h' = κ * (Ψ (i (h, h')) * (((χX (Matrix.GeneralLinearGroup.det h'.1))⁻¹ : Circle) : ℂ)) := by
  intro hK F E _ _ _ _ _ σ B n d X W M χX χW om r s r₁ s₁ hP hmin hn hd Φ₂ h₂ Φ₁ h₁ W₂ hJ hL hθ i hi
  have hB := hP.base
  have hψ := GlobalTheory.StdCharFromIsStd.isCharAF hB.std
  have han := GlobalTheory.DblDatum.aniso_of_min_eq_zero hB hP.herm hmin
  obtain ⟨co, hco, hdiag, hanti⟩ := GlobalTheory.T.darboux_coordinates_doubled_space F E σ d n X.J W.J W₂.J hJ M.co hP.good.rat
  obtain ⟨om₂, hom₂⟩ := GlobalTheory.T.doubling_darboux_pair_setting hK.base F E σ B n d X W M χX χW om r s r₁ s₁ hP W₂ hJ co hco
  obtain ⟨K, hKs, hKi⟩ := GlobalTheory.T.self_dual_lattice_cartan_involution F E σ hB.cm hB.unram B d W hP.skew.skew hP.skew.lat hP.skew.dual hP.skew.cartan
    W₂ hJ hL hθ
  obtain ⟨Φ, hΦ, hf, c, hc, hth⟩ := GlobalTheory.T.doubling_polarized_data_integral F E σ B n d X W M χX χW om r s r₁ s₁ hP Φ₁ h₁ Φ₂ h₂ W₂ hJ hL hθ i hi co hco
    hdiag hanti om₂ hom₂ K hKs
  have hmem := GlobalTheory.T.darboux_symplectic_doubled_hermitian F E σ hB.cm B hψ d n W hP.skew.skew W₂ hJ X hP.herm.herm co hco hdiag hanti χX hP.hX hP.resX
    om₂ hom₂ K hKs hKi Φ hΦ hf
  obtain ⟨-, hconv, hhol⟩ := hK.siegelWeilAnisotropicHermitian F E σ hB.cm hB.unram B hψ d n hd hn W hP.skew.skew
    hP.skew.lat hP.skew.dual hP.skew.cartan W₂ hJ hL hθ X hP.herm.herm han co hco hdiag hanti χX hP.hX hP.resX om₂ hom₂
    K hKs hKi Φ hΦ hf M.μ M.dom hP.good.haar hP.good.dom
  have hv : ((M.μ M.dom).toReal : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (GlobalTheory.DblDatum.vol_ne hK hB hP.herm hP.good han)
  have ht : (if d < n then 1 else 2 : ℂ) ≠ 0 := by split_ifs <;> norm_num
  refine ⟨K, _, _, c * ((M.μ M.dom).toReal : ℂ) / (if d < n then 1 else 2 : ℂ), hKs, hKi, hmem, hconv, hhol,
    div_ne_zero (mul_ne_zero hc hv) ht, fun h h' => ?_⟩
  generalize (if d < n then 1 else 2 : ℂ) = t at ht
  simp only [GlobalTheory.ThKLiftCusp.kern, hth, setAverage_eq, integral_const_mul, integral_mul_const, Complex.real_smul,
    Complex.ofReal_inv, Measure.real, GlobalTheory.ThK.DblKer.chiInv]
  field_simp

end
