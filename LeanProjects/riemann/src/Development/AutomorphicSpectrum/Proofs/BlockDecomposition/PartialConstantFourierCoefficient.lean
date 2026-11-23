import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianIntegralBlockFubini
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousPartialFourierMeanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodicPartialFourierMeanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqConstOfFourierCoefficientsZeroStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientUnipotentMeanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierCoefficientConjugationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDiagonalNormalFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankDirectSumHermitianLtStatement
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PcFc

variable {D : D7} {n ρ p : ℕ}

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : AF D.host.F) : conj (ψ t) = ψ (-t) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ.2.1 t)]

theorem chn_eq (ψ : AddChar (AF D.host.F) ℂ) (β : HermE D n) (b : hermA D n) :
    chn ψ β b = ψ (-GlobalTheory.CompanionTheory.FourierN.pr β.1 b.1) := rfl

theorem chn_cont {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : Continuous (chn ψ β) :=
  hψ.1.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_pr β.1).neg.comp continuous_subtype_val)

theorem chn_per {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (β : HermE D n) : IsPer (chn ψ β) := fun γ hγ x => by
  rw [chn_eq, chn_eq, show (γ + x).1 = γ.1 + x.1 from rfl, GlobalTheory.CompanionTheory.FourierN.pr_add_right, neg_add, AddChar.map_add_eq_mul,
    GlobalTheory.CompanionTheory.FourierN.ker_of_rat hψ γ hγ, one_mul]

theorem trace_bl_mul {R : Type} [CommRing R] (hn : ρ + p = n) (a z : Matrix (Fin ρ) (Fin ρ) R) (d y : Matrix (Fin p) (Fin p) R)
    (x : Matrix (Fin ρ) (Fin p) R) (c : Matrix (Fin p) (Fin ρ) R) :
    Matrix.trace (bl hn a 0 0 d * bl hn z x c y) = Matrix.trace (a * z) + Matrix.trace (d * y) := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  have h : ∀ M : Matrix (Fin ρ ⊕ Fin p) (Fin ρ ⊕ Fin p) R,
      Matrix.trace (M.submatrix (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm) = Matrix.trace M :=
    fun M => Equiv.sum_comp (finSumFinEquiv.trans (finCongr hn)).symm (fun j => M j j)
  rw [h]
  simp [Matrix.trace, Fintype.sum_sum_type]

theorem map_dsum (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) :
    (dsum hn b₀ β').1.map (incA D) = bl hn (b₀.1.map (incA D)) 0 0 (β'.1.map (incA D)) := by
  refine Matrix.ext fun i j => ?_
  simp only [dsum, bl, Matrix.map_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i' | i' <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j' | j' <;> simp

theorem pr_split (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p) (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    GlobalTheory.CompanionTheory.FourierN.pr (dsum hn b₀ β').1 (bT hn z x y).1 = GlobalTheory.CompanionTheory.FourierN.pr b₀.1 z.1 + GlobalTheory.CompanionTheory.FourierN.pr β'.1 y.1 := by
  simp only [GlobalTheory.CompanionTheory.FourierN.pr, ← GlobalTheory.CompanionTheory.FourierN.halfTr_add]
  congr 1
  rw [map_dsum]
  exact trace_bl_mul hn _ _ _ _ _ _

theorem chn_split {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (hn : ρ + p = n) (b₀ : HermE D ρ) (β' : HermE D p)
    (z : hermA D ρ) (x : Mx D ρ p) (y : hermA D p) :
    chn ψ (dsum hn b₀ β') (bT hn z x y) = conj (chz ψ b₀ z) * chn ψ β' y := by
  rw [chn_eq, pr_split, neg_add, AddChar.map_add_eq_mul, chn_eq]
  congr 1
  exact (conj_psi hψ _).symm

theorem coef_pm (hn : ρ + p = n) (m : Meas D ρ p) {lam : Measure (hermA D n)} {𝓖 : Set (hermA D n)} (h : IsCovolOneH lam 𝓖)
    {lp : Measure (hermA D p)} {𝓖p : Set (hermA D p)} (hp : IsCovolOneH lp 𝓖p) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ)
    (b₀ : HermE D ρ) (β' : HermE D p) (Φ : hermA D n → ℂ) (hc : Continuous Φ) (hper : IsPer Φ) :
    ∫ b in 𝓖, Φ b * chn ψ (dsum hn b₀ β') b ∂lam = ∫ y in 𝓖p, pm hn m ψ b₀ Φ y * chn ψ β' y ∂lp := by
  have hd := GlobalTheory.T.hermitian_integral_block_fubini hn m h hp (fun b => Φ b * chn ψ (dsum hn b₀ β') b) (hc.mul (chn_cont hψ _))
    (fun γ hγ x => by
      show Φ (γ + x) * chn ψ (dsum hn b₀ β') (γ + x) = _
      rw [hper γ hγ x, chn_per hψ _ γ hγ x])
  rw [hd]
  refine integral_congr_ae (.of_forall fun y => ?_)
  show ∫ x in m.𝓕, ∫ z in m.𝓖, Φ (bT hn z x y) * chn ψ (dsum hn b₀ β') (bT hn z x y) ∂m.lz ∂m.μ = pm hn m ψ b₀ Φ y * chn ψ β' y
  simp only [chn_split hψ, ← mul_assoc]
  simp only [integral_mul_const, pm]

end GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

theorem per_nb {D : D7} {n : ℕ} {F : G D n → ℂ} (hinv : LeftInv (GF D n) F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    IsPer (fun b => F (nb b * g)) := fun γ hγ x => by
  show F (nb (γ + x) * g) = F (nb x * g)
  rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
  exact hinv _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _

theorem cont_nb {D : D7} {n : ℕ} {F : G D n → ℂ} (hF : Continuous F) {nb : hermA D n → G D n} (hnb : IsNMap nb) (g : G D n) :
    Continuous (fun b => F (nb b * g)) :=
  hF.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)

def zH (D : D7) (p : ℕ) : HermE D p := ⟨0, by
  rw [Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]⟩

theorem chn_zero {D : D7} {p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (y : hermA D p) : chn ψ (zH D p) y = 1 := by
  have h := GlobalTheory.CompanionTheory.FourierN.pr_zero_left (D := D) (n := p) y.1
  simp only [GlobalTheory.CompanionTheory.FourierN.pr] at h
  simp only [chn, zH, h, neg_zero, AddChar.map_zero_eq_one]

theorem pcFc : PcFc := by
  intro D n ρ p hn M m ψ hψ F hF hinv
  obtain ⟨lp, 𝓖p, hp⟩ := GlobalTheory.CompanionTheory.HermVol.exists_isCovolOneH D p
  refine ⟨?_, ?_⟩
  · intro h nb lam 𝓖 hC β hr g
    obtain ⟨a, b₀, β', hd, he⟩ := GlobalTheory.T.hermitian_block_diagonal_normal_form hn β hr
    obtain ⟨q, hq⟩ := GlobalTheory.T.fourier_coefficient_conjugation hψ F hF hinv hC a β
    have h1 := hq (q⁻¹ * g)
    rw [mul_inv_cancel_left] at h1
    rw [h1, he]
    have h2 := coef_pm hn m hC.2 hp hψ b₀ β' _ (cont_nb hF hC.1 (q⁻¹ * g)) (per_nb hinv hC.1 (q⁻¹ * g))
    refine h2.trans ?_
    refine setIntegral_eq_zero_of_forall_eq_zero fun y _ => ?_
    rw [← GlobalTheory.T.partial_coefficient_unipotent_mean M m ψ b₀ F hC.1, h b₀ hd, zero_mul]
  · intro hR b₀ hb β hβ nb lam 𝓖 hC g
    have hc := cont_nb hF hC.1 g
    have hpr := per_nb hinv hC.1 g
    have key := GlobalTheory.T.eq_const_of_fourier_coefficients_zero hp hψ (pm hn m ψ b₀ (fun b => F (nb b * g))) (GlobalTheory.T.continuous_partial_fourier_mean hn m hψ b₀ _ hc hpr)
      (GlobalTheory.T.periodic_partial_fourier_mean hn m ψ b₀ _ hpr)
      (fun a ha => by
        rw [← coef_pm hn m hC.2 hp hψ b₀ a _ hc hpr]
        exact hR nb lam 𝓖 hC _ (GlobalTheory.T.rank_direct_sum_hermitian_lt hn b₀ hb a ha) g)
    have e0 : β = dsum hn b₀ (zH D p) := Subtype.ext hβ
    have e1 : fc ψ lam 𝓖 nb F β g = ∫ y in 𝓖p, pm hn m ψ b₀ (fun b => F (nb b * g)) y * chn ψ (zH D p) y ∂lp := by
      rw [e0]
      exact coef_pm hn m hC.2 hp hψ b₀ _ _ hc hpr
    have e2 : pc M m ψ b₀ F g = pm hn m ψ b₀ (fun b => F (nb b * g)) 0 := by
      have := GlobalTheory.T.partial_coefficient_unipotent_mean M m ψ b₀ F hC.1 g 0
      have hz : bT hn (0 : hermA D ρ) 0 (0 : hermA D p) = 0 := by
        apply Subtype.ext
        show (bl hn (0 : Mx D ρ ρ) 0 (adj (0 : Mx D ρ p)) 0 : Mx D n n) = 0
        rw [adj_zero, bl, Matrix.fromBlocks_zero]
        rfl
      rw [hz, GlobalTheory.CompanionTheory.FourierN.nb_zero hC.1, one_mul] at this
      exact this
    rw [e1, e2]
    simp only [chn_zero, mul_one]
    rw [show (fun y => pm hn m ψ b₀ (fun b => F (nb b * g)) y) = fun _ => pm hn m ψ b₀ (fun b => F (nb b * g)) 0 from funext key]
    rw [setIntegral_const, measureReal_def, hp.2.2]
    simp

theorem target : MapsExist → PositivityTheory.PfSWUS.FourierZero → PcFc := fun _ _ => pcFc

end GlobalTheory.CompanionTheory.PcFc
