import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.OmSch
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.StepNM

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

namespace RD

variable {d : SD σ} (R : RD d) {w : InfinitePlace F}
  {L : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}

theorem _root_.PositivityTheory.SiegelWeilFormula.SD.T_lin (d : SD σ) (a : ℂ) (Φ Φ' : d.Fn) : d.T (a • Φ + Φ') = a • d.T Φ + d.T Φ' := by
  funext X
  have h : ∀ p : (d.κ → AF F) × (d.κ → AF F), schr d.B.ψ p (a • Φ + Φ') = a • schr d.B.ψ p Φ + schr d.B.ψ p Φ' :=
    fun p => by
      funext x
      simp only [schr, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
  simp only [SD.T, Darboux.rho, h, map_add, map_smul, Pi.add_apply, Pi.smul_apply]

theorem isSw_lin {m n : ℕ} {f g : (Fin m → Fin n → ℂ) → ℂ} (a : ℂ) (hf : IsSw f) (hg : IsSw g) : IsSw (a • f + g) := by
  obtain ⟨φ, hφ⟩ := hf
  obtain ⟨φ', hφ'⟩ := hg
  exact ⟨a • φ + φ', by funext u; simp [← hφ, ← hφ']⟩

theorem tens_cancel {Ψ : d.MF} (hΨ : d.IsAwayW w Ψ) (h0 : Ψ ≠ 0) {g g' : d.LF}
    (h : R.tens w g Ψ = R.tens w g' Ψ) : g = g' := by
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, Ψ X₀ ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (funext hc)
  funext u
  obtain ⟨Z, hZ1, hZ2, hZ3⟩ := R.loc_surj w X₀ u
  have := congrFun h (X₀ + Z)
  simp only [RD.tens, hZ3, hΨ X₀ Z hZ1 hZ2] at this
  exact mul_right_cancel₀ hX₀ this

theorem exists_adm (hT : TAll) {Ψ : d.MF} (hΨ : R.GoodAway w Ψ) {f : d.LF} (hf : IsSw f) :
    ∃ Φ ∈ d.sch, d.T Φ = R.tens w f Ψ := (hT.1 F E σ d).2.1 _ (hΨ.2.2 f hf)

theorem locOp_unique (hT : TAll) (hG : GoodAwayEx) {L' : GR d.n → ((Fin d.m → Fin d.n → ℂ) → ℂ) → (Fin d.m → Fin d.n → ℂ) → ℂ}
    (hL : R.IsLocOp w L) (hL' : R.IsLocOp w L') : ∀ y f, IsSw f → L y f = L' y f := by
  intro y f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  exact R.tens_cancel hΨ.1 hΨ.2.1 (((hL y f hf).2 Ψ hΨ.1 Φ hΦ hT').symm.trans ((hL' y f hf).2 Ψ hΨ.1 Φ hΦ hT'))

theorem locOp_one (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) : ∀ f, IsSw f → L 1 f = f := by
  intro f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e := (hL 1 f hf).2 Ψ hΨ.1 Φ hΦ hT'
  rw [map_one, map_one, Module.End.one_apply, hT'] at e
  exact (R.tens_cancel hΨ.1 hΨ.2.1 e).symm

theorem locOp_mul (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∀ y y' f, IsSw f → L (y * y') f = L y (L y' f) := by
  intro y y' f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y' f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := (hL y (L y' f) (hL y' f hf).1).2 Ψ hΨ.1 _ (d.om_sch _ Φ hΦ) e1
  have e3 := (hL (y * y') f hf).2 Ψ hΨ.1 Φ hΦ hT'
  rw [map_mul, map_mul, Module.End.mul_apply] at e3
  exact R.tens_cancel hΨ.1 hΨ.2.1 (e3.symm.trans e2)

theorem locOp_lin (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∀ y (a : ℂ) f g, IsSw f → IsSw g → L y (a • f + g) = a • L y f + L y g := by
  intro y a f g hf hg
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φf, hΦf, hTf⟩ := R.exists_adm hT hΨ hf
  obtain ⟨Φg, hΦg, hTg⟩ := R.exists_adm hT hΨ hg
  have hΦ : a • Φf + Φg ∈ d.sch := d.sch.add_mem (d.sch.smul_mem a hΦf) hΦg
  have hTΦ : d.T (a • Φf + Φg) = R.tens w (a • f + g) Ψ := by
    rw [d.T_lin, hTf, hTg]
    funext X
    simp only [RD.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e := (hL y (a • f + g) (isSw_lin a hf hg)).2 Ψ hΨ.1 _ hΦ hTΦ
  have ef := (hL y f hf).2 Ψ hΨ.1 Φf hΦf hTf
  have eg := (hL y g hg).2 Ψ hΨ.1 Φg hΦg hTg
  rw [map_add, map_smul, d.T_lin, ef, eg] at e
  apply R.tens_cancel hΨ.1 hΨ.2.1
  rw [← e]
  funext X
  simp only [RD.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem locOp_nU (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∀ (y : GR d.n) (b : Matrix (Fin d.n) (Fin d.n) ℂ), bᴴ = b → mR y = nU b → ∀ f, IsSw f →
      L y f = fun u => Complex.exp (2 * Real.pi * Complex.I * ((R.sg w : ℤ) : ℂ) *
        Matrix.trace (b * ((Matrix.of u)ᴴ * Matrix.of u))) * f u := by
  intro y b hb hy f hf
  obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
  obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
  have e1 := (hL y f hf).2 Ψ hΨ.1 Φ hΦ hT'
  have e2 := ((R.stepN w hT y b hb hy).2 Ψ hΨ.1).2 f hf Φ hΦ hT'
  exact R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2)

theorem locOp_mM (hT : TAll) (hG : GoodAwayEx) (hL : R.IsLocOp w L) :
    ∃ c : Matrix (Fin d.n) (Fin d.n) ℂ → ℂ, (∀ a, IsUnit a.det → c a ≠ 0) ∧
      ∀ (y : GR d.n) (a : Matrix (Fin d.n) (Fin d.n) ℂ), IsUnit a.det → mR y = mLoc a → ∀ f, IsSw f →
        L y f = fun u => c a * f (Matrix.of u * a) := by
  classical
  have hinj : ∀ y y' : GR d.n, mR y = mR y' → y = y' := fun y y' h => Subtype.ext (Units.ext h)
  refine ⟨fun a => if h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a then
    (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose else 1, fun a ha => ?_, fun y a ha hy f hf => ?_⟩
  · by_cases h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a
    · dsimp only
      rw [dif_pos h]
      exact (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose_spec.1
    · dsimp only
      rw [dif_neg h]
      exact one_ne_zero
  · have h : IsUnit a.det ∧ ∃ y : GR d.n, mR y = mLoc a := ⟨ha, y, hy⟩
    have hy0 : h.2.choose = y := hinj _ _ (h.2.choose_spec.trans hy.symm)
    simp only [dif_pos h]
    have hs := (R.stepM w hT h.2.choose a h.1 h.2.choose_spec).choose_spec.2
    rw [← hy0]
    obtain ⟨Ψ, hΨ⟩ := hG F E σ d R w
    obtain ⟨Φ, hΦ, hT'⟩ := R.exists_adm hT hΨ hf
    have e1 := (hL h.2.choose f hf).2 Ψ hΨ.1 Φ hΦ hT'
    have e2 := (hs.2 Ψ hΨ.1).2 f hf Φ hΦ hT'
    exact R.tens_cancel hΨ.1 hΨ.2.1 (e1.symm.trans e2)

end RD

end PositivityTheory.SiegelWeilFormula

end
