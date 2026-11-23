import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PExpFin
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.SquareIntegrableCovers.SetLIntegralLeOfCover
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOfIsAutFormTotallyComplex
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraFiniteFormsGLSingleCharSpanMem

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.PExpFin

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

def tl (r : ℕ) (s : ℝ) : Module.End ℂ (GA E N → ℂ) where
  toFun f g := f (aT E N r s * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tl_pow (r : ℕ) (s : ℝ) (i : ℕ) (f : GA E N → ℂ) : (tl r s ^ i) f = fun g => f (aT E N r (s * i) * g) := by
  induction i generalizing f with
  | zero =>
    funext g
    simp [aT_zero]
  | succ i ih =>
    funext g
    rw [pow_succ, Module.End.mul_apply, ih]
    show f (aT E N r s * (aT E N r (s * i) * g)) = f (aT E N r (s * ((i + 1 : ℕ) : ℝ)) * g)
    rw [← mul_assoc, ← aT_add, show s + s * (i : ℝ) = s * ((i + 1 : ℕ) : ℝ) by push_cast; ring]

theorem kl_iff (r : ℕ) (s : ℝ) (p : ℂ[X]) (F : GA E N → ℂ) : Kl r s p F ↔ aeval (tl r s) p F = 0 := by
  have e : aeval (tl (N := N) r s) p F = fun g => ∑ j ∈ Finset.range (p.natDegree + 1), p.coeff j * F (aT E N r (s * j) * g) := by
    rw [aeval_eq_sum_range, LinearMap.sum_apply]
    funext g
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.smul_apply, tl_pow]
    rfl
  rw [e]
  constructor
  · intro h
    funext g
    exact h g
  · intro h g
    exact congrFun h g

theorem kl_mul {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s p F) : Kl r s (p * q) F := by
  rw [kl_iff] at h ⊢
  rw [mul_comm, aeval_mul, Module.End.mul_apply, h, map_zero]

theorem kl_mul' {r : ℕ} {s : ℝ} {p q : ℂ[X]} {F : GA E N → ℂ} (h : Kl r s q F) : Kl r s (p * q) F := by
  rw [mul_comm]
  exact kl_mul h

theorem ctn_eq_ct (r : ℕ) :
    letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
    ∃ μ : Measure (BlockIx N r → Ad E), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (ratN E N r) (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) μ ∧
      ∀ f : Sm E N, An.ctn r f.1 = PositivityTheory.Affgl.CT.ct μ (GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r) f.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, hint⟩ := JDict.exists_normed E N r
  refine ⟨μ, hμ, hD, fun f => funext fun g => ?_⟩
  show An.ctn r f.1 g = ∫ x in GroundTheory.Automorphic.AutomorphicForm.unipFundamentalDomain E N r, f.1 (unip x * g) ∂μ
  rw [hint]
  simp only [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm, GlobalTheory.CompanionTheory.CuspBridge.unipGL_eq_unip]

theorem ctn_add (r : ℕ) {φ ψ : Sm E N} (hφ : IsAutForm φ) (hψ : IsAutForm ψ) :
    An.ctn r (φ + ψ).1 = An.ctn r φ.1 + An.ctn r ψ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  have : BorelSpace (BlockIx N r → Ad E) := ⟨rfl⟩
  obtain ⟨μ, hμ, hD, e⟩ := ctn_eq_ct (E := E) (N := N) r
  have := hμ
  rw [e, e, e]
  exact ct_add μ _ hD hφ hψ

theorem ctn_smul (r : ℕ) (c : ℂ) (φ : Sm E N) : An.ctn r (c • φ).1 = c • An.ctn r φ.1 := by
  letI : MeasurableSpace (BlockIx N r → Ad E) := borel _
  obtain ⟨μ, -, -, e⟩ := ctn_eq_ct (E := E) (N := N) r
  rw [e, e]
  exact ct_smul μ _ c φ

def Good (β : ℕ → ℝ) (φ : Sm E N) : Prop :=
  IsAutForm φ ∧ ∀ r, 0 < r → r < N → ∃ p : ℂ[X], p.Monic ∧ Kl r 1 p (An.ctn r φ.1) ∧ ∀ z, p.IsRoot z → ‖z‖ ≤ Real.exp (β r)

theorem good_bound {β : ℕ → ℝ} {φ : Sm E N} (h : Good β φ) :
    ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro r hr hrN c hc
  obtain ⟨p, -, hk, hroot⟩ := h.2 r hr hrN
  obtain ⟨F₀, hCT, F, hFspan, hF0, hFe⟩ := hc
  obtain ⟨-, -, -, hD⟩ := dict_holds E N
  obtain ⟨c₁, -, e₁⟩ := (hD φ h.1 r hr hrN).2 F₀ hCT
  have hk₀ : Kl r 1 p F₀ := by
    have : F₀ = c₁ • An.ctn r φ.1 := by
      funext g
      rw [e₁]
      rfl
    rw [this]
    exact (klSub r 1 p).smul_mem c₁ hk
  have hroot' := kl_eigen (kl_span hk₀ hFspan) hF0 hFe
  have h1 := hroot (Complex.exp (c * ((1 : ℝ) : ℂ))) hroot'
  rw [Complex.norm_exp] at h1
  have h2 := Real.exp_le_exp.1 h1
  simpa using h2

theorem good_of (β : ℕ → ℝ) {φ : Sm E N} (hφ : IsAutForm φ)
    (hexp : ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) : Good β φ := by
  refine ⟨hφ, fun r hr hrN => ?_⟩
  obtain ⟨hA, -, -, hCT⟩ := dict_holds E N
  have hct := (hCT φ hφ r hr hrN).1
  have hfin := finTr_holds E N φ hφ r hr hrN _ hct
  have hadd : ∀ s t, aT E N r (s + t) = aT E N r s * aT E N r t := fun s t => aT_add r s t
  have hcont : ∀ g, Continuous fun t => An.ctn r φ.1 (aT E N r t * g) := by
    intro g
    have e : (fun t => An.ctn r φ.1 (aT E N r t * g)) = fun t => An.ctn r φ.1 (An.aR E N r t * g) :=
      funext fun t => by rw [hA]
    rw [e]
    exact JSqIntGlue.continuous_ctn_comp (GlobalTheory.CompanionTheory.ContAutForm.continuous_of_isAutForm_totallyComplex E N φ hφ) r
      ((JSqIntGlue.continuous_aR r).mul continuous_const)
  obtain ⟨p, hp, hpk, hroots⟩ := killPoly_holds (GA E N) (aT E N r) (An.ctn r φ.1) hadd hcont hfin
  refine ⟨p, hp, fun g => ?_, fun z hz => ?_⟩
  · have := hpk g
    simpa only [one_mul] using this
  · obtain ⟨c, rfl, F, hF, hF0, hFe⟩ := hroots z hz
    have hc : c ∈ Exp r φ.1 := ⟨_, hct, F, hF, hF0, hFe⟩
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.2 (hexp r hr hrN c hc)

theorem good_add {β : ℕ → ℝ} {φ ψ : Sm E N} (hφ : Good β φ) (hψ : Good β ψ) : Good β (φ + ψ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_add hφ.1 hψ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  obtain ⟨q, hq, hqk, hqr⟩ := hψ.2 r hr hrN
  refine ⟨p * q, hp.mul hq, ?_, fun z hz => ?_⟩
  · rw [ctn_add r hφ.1 hψ.1]
    exact (klSub r 1 (p * q)).add_mem (kl_mul hpk) (kl_mul' hqk)
  · rcases (Polynomial.root_mul.1 hz) with h | h
    · exact hpr z h
    · exact hqr z h

theorem good_smul {β : ℕ → ℝ} {φ : Sm E N} (hφ : Good β φ) (c : ℂ) : Good β (c • φ) := by
  refine ⟨GlobalTheory.CompanionTheory.AffglAssembly.isAutForm_smul c hφ.1, fun r hr hrN => ?_⟩
  obtain ⟨p, hp, hpk, hpr⟩ := hφ.2 r hr hrN
  refine ⟨p, hp, ?_, hpr⟩
  rw [ctn_smul]
  exact (klSub r 1 p).smul_mem c hpk

theorem good_zero (β : ℕ → ℝ) : Good β (0 : Sm E N) := by
  refine ⟨GlobalTheory.HCF.FormsSub.isAutForm_zero, fun r hr hrN => ⟨1, monic_one, ?_, fun z hz => ?_⟩⟩
  · have e : An.ctn r (0 : Sm E N).1 = (0 : ℂ) • An.ctn r (0 : Sm E N).1 := by
      rw [← ctn_smul, zero_smul]
    rw [e]
    exact (klSub r 1 1).smul_mem 0 (by
      intro g
      simp [An.ctn, GroundTheory.Automorphic.AutomorphicForm.constantTerm])
  · exact absurd hz (by simp [Polynomial.IsRoot])

theorem exp_span (S : Set (Sm E N)) (β : ℕ → ℝ) (haut : ∀ φ ∈ S, IsAutForm φ)
    (hexp : ∀ φ ∈ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r) :
    ∀ φ ∈ Submodule.span ℂ S, ∀ r, 0 < r → r < N → ∀ c ∈ Exp r φ.1, c.re ≤ β r := by
  intro φ hφ
  refine good_bound ?_
  induction hφ using Submodule.span_induction with
  | mem x hx => exact good_of β (haut x hx) (hexp x hx)
  | zero => exact good_zero β
  | add x y _ _ hx hy => exact good_add hx hy
  | smul c x _ hx => exact good_smul hx c

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockExponential

end
