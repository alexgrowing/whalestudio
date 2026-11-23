import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunctionStatement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.IoPTprodInjectiveRangeEqValSpace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem exists_of_mem_coefLatFn {D : D7} {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (φ : GLR D n → ℂ)
    (hφ : φ ∈ coefLatFn D.what₂.embLL (labLL D) (intLL D) lam M) :
    ∃ F : VV D.what₂.LL lam, F ∈ nabAtr (labLL D) lam M ∧ φ = coefFn D.what₂.embLL lam (F : Pol D.what₂.LL D.what₂.Tau n) := by
  induction hφ using Submodule.span_induction with
  | mem φ hφ => exact hφ
  | zero => exact ⟨0, zero_mem _, funext fun y => by simp [coefFn]⟩
  | add φ ψ _ _ h1 h2 =>
    obtain ⟨F1, m1, rfl⟩ := h1
    obtain ⟨F2, m2, rfl⟩ := h2
    exact ⟨F1 + F2, add_mem m1 m2, funext fun y => by simp [coefFn, mul_add]⟩
  | smul a φ _ h1 =>
    obtain ⟨F1, m1, rfl⟩ := h1
    obtain ⟨t, ht⟩ := a.2
    refine ⟨t • F1, Submodule.smul_mem _ _ m1, funext fun y => ?_⟩
    have e1 : ((t • F1 : VV D.what₂.LL lam) : Pol D.what₂.LL D.what₂.Tau n) =
        MvPolynomial.C (t : D.what₂.LL) * (F1 : Pol D.what₂.LL D.what₂.Tau n) := by
      rw [← MvPolynomial.smul_eq_C_mul]
      rfl
    have e2 : D.what₂.embLL (t : D.what₂.LL) = (a : ℂ) := by
      rw [← ht]
      rfl
    show (a : ℂ) * coefFn _ _ (F1 : Pol D.what₂.LL D.what₂.Tau n) y = _
    rw [e1, coefFn, coefFn, map_mul, MvPolynomial.eval₂Hom_C, e2]
    ring

theorem _root_.UpperTheory.KN.scaled_fock_form_coefficients_integral :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ), IsLow X j u →
      ∀ gramR c0R c0L, Bridge.FamTie X.R.B X.R.pl (X.R.Sb : Set (Pl D.host.E)) X.R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L →
      ∀ κ : ℂ, κ ≠ 0 → (∀ F : VV D.what₂.LL (lamV D j), harmFn (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS (X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F)) = κ • coefFn D.what₂.embLL (lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank)) →
      ∀ (h : Bridge.Gf (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank), P ∈ (baseOf Z c w j).coefLat D.what₂.embLL (labLL D) (intLL D) h ↔
        ∃ F : VV D.what₂.LL (lamV D j), F ∈ nabAtr (labLL D) (lamV D j) (Bridge.hLat (Vc D j) h) ∧ P = κ⁻¹ • X.R.ioP j (PiTensorProduct.tprod ℂ u) (c0L j F) := by
  intro D X X0 Y S YS Z c w j H ι hι u hu gramR c0R c0L _ κ hκ hF h P
  have hB := Z.good.base (c.twI w) j (c.sd w)
  have hBo := GlobalTheory.BigOn.Exp.TwConj.baseOf_of_realPin X.char.lev Z.good Z.pin (c.twI w) j (c.sd w)
  have hval : ∀ v, X.R.ioP j (PiTensorProduct.tprod ℂ u) v ∈
      harm (Wc D j).rank (baseOf Z c w j).w (baseOf Z c w j).F.BS := fun v => by
    have h1 := LinearMap.mem_range_self (X.R.ioP j (PiTensorProduct.tprod ℂ u)) v
    rw [(UpperTheory.KN.ioP_tprod_injective_and_range_eq_valSpace D X X0 Y S YS Z c w j H ι hι u hu).2] at h1
    exact h1
  have hM : (baseOf Z c w j).latAt h = Bridge.hLat (Vc D j) h :=
    GlobalTheory.LatAtHLat.latAt_eq_hLat _ _ _ _ (GlobalTheory.LatFull.baseFrame_one_eq _ _ _ (Z.good.latS _ j _)) _
  have hlam : (baseOf Z c w j).w.lam = lamV D j := hBo.lam
  unfold Base.coefLat
  rw [mem_harmLat, hlam, hM]
  constructor
  · rintro ⟨hPh, hPF⟩
    obtain ⟨F, hF0, hFe⟩ := exists_of_mem_coefLatFn _ _ _ hPF
    refine ⟨F, hF0, ?_⟩
    have hm : ∀ τ, (baseOf Z c w j).w.p τ + (baseOf Z c w j).w.q τ ≤ (Wc D j).rank := fun τ => by
      have h1 := hB.sig τ
      have h2 := Formalism.BasicNotions.sig_sum _ hB.sigOK (Formalism.BasicNotions.TH.tauE D τ)
      rw [← h1] at h2
      exact h2.le
    have hinj := GlobalTheory.T.harmonic_polynomial_eq_zero_of_function _ _ _ _ (baseOf Z c w j).F.BS hB.wt hm
    exact (eq_inv_smul_iff₀ hκ).2
      (IsScaleAt.ioP_eq (Rl := X.R) (B := baseOf Z c w j) (c0 := c0L j) hF hinj hPh (hval _) hFe).symm
  · rintro ⟨F, hF0, rfl⟩
    refine ⟨Submodule.smul_mem _ _ (hval _), ?_⟩
    rw [map_smul, hF F, inv_smul_smul₀ hκ]
    exact Submodule.subset_span ⟨F, hF0, rfl⟩
