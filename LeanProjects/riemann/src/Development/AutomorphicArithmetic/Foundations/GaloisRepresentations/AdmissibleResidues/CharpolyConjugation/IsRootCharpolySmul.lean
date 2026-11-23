import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlfrob
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlres
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unliso
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Unlwd

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep UpperTheory.V.Af UpperTheory.GalN.V

private theorem isRoot_charpoly_smul' {k : Type} [Field k] {n : ℕ} (c : k) (hc : c ≠ 0)
    (M : Matrix (Fin n) (Fin n) k) (x : k) :
    (c • M).charpoly.IsRoot (c * x) ↔ M.charpoly.IsRoot x := by
  have h : Matrix.scalar (Fin n) (c * x) - c • M = c • (Matrix.scalar (Fin n) x - M) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hij, mul_sub]
  rw [Polynomial.IsRoot.def, Polynomial.IsRoot.def, Matrix.eval_charpoly, Matrix.eval_charpoly, h,
    Matrix.det_smul]
  simp [hc]

private theorem finite_char_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (μ : G F Ω →* (Qbar l)ˣ) (hμ : Continuous μ)
    {w : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) : (μ '' (Ine (F := F) A : Set (G F Ω))).Finite := by
  obtain ⟨ι⟩ : Nonempty (Qbar l ≃+* ℂ) := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
  let m : G F Ω →* GL (Fin 1) (Qbar l) := UpperTheory.V.Af.tw 1 μ
  have hval : ∀ s, (m s : Matrix (Fin 1) (Fin 1) (Qbar l)) = (μ s : Qbar l) • (1 : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
    intro s
    simpa [m] using UpperTheory.V.Af.tw_val (1 : G F Ω →* GL (Fin 1) (Qbar l)) μ s
  have hc : Continuous fun g => (m g : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
    simp only [hval]
    exact (Units.continuous_val.comp hμ).smul continuous_const
  have h0 : (wdOf h hl ι m).mono0 :=
    WD.mono0_of_lpDim_eq_one (by rw [lpDim_wdOf]; simp)
  have hfin := (weilDeligneParam_monodromy_eq_zero_iff hl ι hc).1 h0
  refine (hfin.image Matrix.GeneralLinearGroup.det).subset ?_
  rintro _ ⟨s, hs, rfl⟩
  refine ⟨m s, ⟨s, hs, rfl⟩, ?_⟩
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.val_det_apply, hval]

theorem UpperTheory.GalN.V.L.wtw :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (r : G F Ω →* GL (Fin n) (Qbar l)) (μ : G F Ω →* (Qbar l)ˣ), Continuous μ → Unlinked r → Unlinked (UpperTheory.V.Af.tw r μ) := by
  intro F Ω _ _ _ _ _ l _ n r μ hμ hU w hl A hA hfin
  have hμf := finite_char_ine μ hμ hl hA
  have hr : (r '' (Ine (F := F) A : Set (G F Ω))).Finite := by
    refine (Set.Finite.image2
      (fun (c : (Qbar l)ˣ) (x : GL (Fin n) (Qbar l)) => Matrix.GeneralLinearGroup.scalar (Fin n) c⁻¹ * x)
      hμf hfin).subset ?_
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨μ s, ⟨s, hs, rfl⟩, UpperTheory.V.Af.tw r μ s, ⟨s, hs, rfl⟩, ?_⟩
    apply Units.ext
    have e := UpperTheory.V.Af.tw_val r μ s
    simp only [Units.val_mul, e]
    simp [Matrix.GeneralLinearGroup.scalar, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul, smul_smul]
  obtain ⟨s, j, hj, hs, hn⟩ := hU w hl A hA hr
  refine ⟨s, j, hj, hs, ?_⟩
  intro α β hα hβ k hk e
  set c : Qbar l := (μ s : Qbar l) with hcdef
  have hc : c ≠ 0 := Units.ne_zero _
  rw [UpperTheory.V.Af.tw_val] at hα hβ
  have back : ∀ x : Qbar l, (c • (r s : Matrix (Fin n) (Fin n) (Qbar l))).charpoly.IsRoot x →
      (r s : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot (c⁻¹ * x) := by
    intro x hx
    refine (isRoot_charpoly_smul' c hc _ _).1 ?_
    rwa [mul_inv_cancel_left₀ hc]
  refine hn _ _ (back _ hα) (back _ hβ) k hk ?_
  rw [mul_pow, mul_left_comm, mul_pow, e, mul_pow]
