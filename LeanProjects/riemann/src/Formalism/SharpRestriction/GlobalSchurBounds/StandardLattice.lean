import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataLevelD
import Formalism.LocalRingCardinality.DataTies
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset
open scoped ENNReal

section SW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def OnH (P : Measure (HA (AF F) σ J) → Set (HA (AF F) σ J) → Prop) : Prop :=
  (∃ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure) ∧
  ∀ μ : Measure (HA (AF F) σ J), μ.IsHaarMeasure →
    (∃ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ) ∧
    ∀ 𝓕, IsFundamentalDomain (HFinIn (AF F) σ J) 𝓕 μ → P μ 𝓕

def thSum {n : ℕ} (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (S : Set (Fin n → Fin M → E))
    (h : HA (AF F) σ J) : ℂ :=
  ∑' X : S, Φ (h⁻¹ • ratTup (F := F) (AF F) (X : Fin n → Fin M → E))

def OnSD (ψ : AddChar (AF F) ℂ) (n : ℕ) (Yi : Type) [AddCommGroup Yi] [TopologicalSpace Yi]
    [MeasurableSpace Yi] (Yv : HeightOneSpectrum (𝓞 F) → Type) [∀ v, AddCommGroup (Yv v)]
    [∀ v, TopologicalSpace (Yv v)] [∀ v, MeasurableSpace (Yv v)]
    (χi : Yi → Yi → ℂ) (χv : ∀ v, Yv v → Yv v → ℂ)
    (Q : Measure (Fin n → Fin M → Ainf F ⊗[F] E) → Measure Yi →
      (∀ v, Measure (Fin n → Fin M → Fv F v ⊗[F] E)) → (∀ v, Measure (Yv v)) → Prop) : Prop :=
  let Si := fun μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E) =>
    SelfDual μi (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y))
  let Sv := fun μv : ∀ v, Measure (Fin n → Fin M → Fv F v ⊗[F] E) =>
    ∀ v, SelfDual (μv v) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))
  (∃ μi, Si μi) ∧ (∃ νi : Measure Yi, SelfDual νi χi) ∧ (∃ μv, Sv μv) ∧
    (∃ νv : ∀ v, Measure (Yv v), ∀ v, SelfDual (νv v) (χv v)) ∧
  ∀ μi νi μv νv, Si μi → SelfDual νi χi → Sv μv → (∀ v, SelfDual (νv v) (χv v)) → Q μi νi μv νv

def SW1a1 : Prop := OnH F E σ M J fun μ 𝓕 => μ 𝓕 < ⊤

def SW1a2 : Prop :=
  3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ)
    (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin 1 → Fin M → Af F ⊗[F] E) → ℂ),
    IsSB Φf → Measurable Φi → RapidDecay b Φi → IsProdInfFin Φ Φi Φf →
    OnH F E σ M J fun μ 𝓕 =>
      ∫⁻ h in 𝓕, ∑' x : (Fin 1 → Fin M → E),
        ‖Φ (h⁻¹ • ratTup (F := F) (AF F) x)‖ₑ ∂μ < ⊤

def SW1b1 : Prop :=
  3 ≤ M → ∀ (β : F) (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin 1 → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φi → RapidDecay b Φi → IsPureFin b Φf Φv → IsProdInfFin Φ Φi Φf →
    AllSome (IsCharAF F) fun ψ =>
    OnH F E σ M J fun μ 𝓕 =>
    OnSD F E σ M J ψ 1 (Ainf F) (Fv F) (fun s t => psiInf F ψ (s * t)) (fun v s t => psiV F ψ v (s * t))
      fun μi νi μv νv =>
      ∃ (Fi : Ainf F → ℂ) (Fl : ∀ v, Fv F v → ℂ),
        IsContDensity μi (fun X => qR (Ainf F) σ J (X 0)) id νi Φi Fi ∧
        (∀ v, IsContDensity (μv v) (fun X => qR (Fv F v) σ J (X 0)) id (νv v) (Φv v) (Fl v)) ∧
        Multipliable (fun v => Fl v (algebraMap F (Fv F v) β)) ∧
        meanC μ 𝓕 (thSum F E σ M J Φ {x | x 0 ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β}) =
          Fi (algebraMap F (Ainf F) β) * ∏' v, Fl v (algebraMap F (Fv F v) β)

def SW1b2 : Prop :=
  3 ≤ M → ∀ (β : F), β ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Φf : (Fin 1 → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
    Measurable Φi → IsPureFin b Φf Φv → (∀ v Y, 0 ≤ (Φv v Y).re ∧ (Φv v Y).im = 0) →
    (∀ X, Φ X = Φi (projInf X) * ENNReal.ofReal (Φf (projFin X)).re) →
    AllSome (IsCharAF F) fun ψ =>
    OnH F E σ M J fun μ 𝓕 =>
    OnSD F E σ M J ψ 1 (Ainf F) (Fv F) (fun s t => psiInf F ψ (s * t)) (fun v s t => psiV F ψ v (s * t))
      fun μi νi μv νv =>
      (∃ fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi {c | ∀ w, c w ≠ 0} fi) ∧
      (∃ fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
        ∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v) {c | c ≠ 0}
          (fv v)) ∧
      ∀ (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E))
        (fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
        IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi {c | ∀ w, c w ≠ 0} fi →
        (∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v) {c | c ≠ 0}
          (fv v)) →
        Multipliable (fun v => ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))) ∧
        meanL μ 𝓕 (fun h => ∑' x : {x : Fin 1 → Fin M → E | x 0 ≠ 0 ∧
            hE σ J (x 0) (x 0) = algebraMap F E β},
          Φ (h⁻¹ • ratTup (F := F) (AF F) (x : Fin 1 → Fin M → E))) =
        (∫⁻ X, Φi X ∂(fi (algebraMap F (Ainf F) β))) *
          ∏' v, ∫⁻ X, ENNReal.ofReal (Φv v X).re ∂(fv v (algebraMap F (Fv F v) β))

def SW1c1 : Prop :=
  ∀ (n : ℕ), n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c),
    T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin n → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φi → RapidDecay b Φi → IsPureFin b Φf Φv → IsProdInfFin Φ Φi Φf →
    AllSome (IsCharAF F) fun ψ =>
    OnH F E σ M J fun μ 𝓕 =>
    OnSD F E σ M J ψ n (HermR (Ainf F) σ n) (fun v => HermR (Fv F v) σ n)
      (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ n S S'))
      (fun v S S' => psiV F ψ v (pairHerm (Fv F v) σ n S S'))
      fun μi νi μv νv =>
      ∃ (gi : HermR (Ainf F) σ n → ℂ) (gv : ∀ v, HermR (Fv F v) σ n → ℂ),
        IsContDensityOn μi (gramR (Ainf F) σ J) Subtype.val νi
          {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} Φi gi ∧
        (∀ v, IsContDensityOn (μv v) (gramR (Fv F v) σ J) Subtype.val (νv v)
          {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} (Φv v) (gv v)) ∧
        Multipliable (fun v => gv v (hermOf (Fv F v) σ T hT)) ∧
        meanC μ 𝓕 (thSum F E σ M J Φ {X | gramE σ J X = T}) =
          gi (hermOf (Ainf F) σ T hT) * ∏' v, gv v (hermOf (Fv F v) σ T hT)

def SW1c2 : Prop :=
  ∀ (p : ℕ), 2 * p + 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E)
    (Φ : (Fin p → Fin M → AF F ⊗[F] E) → ℂ) (Φi : (Fin p → Fin M → Ainf F ⊗[F] E) → ℂ)
    (Φf : (Fin p → Fin M → Af F ⊗[F] E) → ℂ)
    (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin p → Fin M → Fv F v ⊗[F] E) → ℂ),
    Continuous Φi → RapidDecay b Φi → IsPureFin b Φf Φv → IsProdInfFin Φ Φi Φf →
    AllSome (IsCharAF F) fun ψ =>
    OnH F E σ M J fun μ 𝓕 =>
    OnSD F E σ M J ψ p (HermR (Ainf F) σ p) (fun v => HermR (Fv F v) σ p)
      (fun S S' => psiInf F ψ (pairHerm (Ainf F) σ p S S'))
      (fun v S S' => psiV F ψ v (pairHerm (Fv F v) σ p S S'))
      fun μi νi μv νv =>
      (∃ fi : HermR (Ainf F) σ p → Measure (Fin p → Fin M → Ainf F ⊗[F] E),
        IsFibreFamily μi (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} νi Set.univ fi) ∧
      (∃ fv : ∀ v, HermR (Fv F v) σ p → Measure (Fin p → Fin M → Fv F v ⊗[F] E),
        ∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
          {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fv v)) ∧
      ∀ (fi : HermR (Ainf F) σ p → Measure (Fin p → Fin M → Ainf F ⊗[F] E))
        (fv : ∀ v, HermR (Fv F v) σ p → Measure (Fin p → Fin M → Fv F v ⊗[F] E)),
        IsFibreFamily μi (gramR (Ainf F) σ J) Subtype.val
          {X | LinearIndependent (Ainf F ⊗[F] E) X} νi Set.univ fi →
        (∀ v, IsFibreFamily (μv v) (gramR (Fv F v) σ J) Subtype.val
          {X | LinearIndependent (Fv F v ⊗[F] E) X} (νv v) Set.univ (fv v)) →
        Multipliable (fun v => ∫ X, Φv v X ∂(fv v 0)) ∧
        meanC μ 𝓕 (thSum F E σ M J Φ {X | LinearIndependent E X ∧ gramE σ J X = 0}) =
          (∫ X, Φi X ∂(fi 0)) * ∏' v, ∫ X, Φv v X ∂(fv v 0)

def IsDxDq (ψ : AddChar (AF F) ℂ) (β : F) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) : Prop :=
  ν {y | qR (AF F) σ J (y 0) ≠ algebraMap F (AF F) β} = 0 ∧
  OnSD F E σ M J ψ 1 (Ainf F) (Fv F) (fun s t => psiInf F ψ (s * t))
    (fun v s t => psiV F ψ v (s * t)) fun μi νi μv νv =>
    (∃ fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E),
      IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi {c | ∀ w, c w ≠ 0} fi) ∧
    (∃ fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E),
      ∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v) {c | c ≠ 0}
        (fv v)) ∧
    ∀ (fi : Ainf F → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E))
      (fv : ∀ v, Fv F v → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)),
      IsFibreFamily μi (fun X => qR (Ainf F) σ J (X 0)) id Set.univ νi {c | ∀ w, c w ≠ 0} fi →
      (∀ v, IsFibreFamily (μv v) (fun X => qR (Fv F v) σ J (X 0)) id Set.univ (νv v)
        {c | c ≠ 0} (fv v)) →
      ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ)
        (Φi : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ) (Φf : (Fin 1 → Fin M → Af F ⊗[F] E) → ℂ)
        (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin M → Fv F v ⊗[F] E) → ℂ),
        Continuous Φi → HasCompactSupport Φi → IsPureFin b Φf Φv → IsProdInfFin Φ Φi Φf →
        Integrable Φ ν ∧
        Multipliable (fun v => ∫ X, Φv v X ∂(fv v (algebraMap F (Fv F v) β))) ∧
        ∫ y, Φ y ∂ν = (∫ X, Φi X ∂(fi (algebraMap F (Ainf F) β))) *
          ∏' v, ∫ X, Φv v X ∂(fv v (algebraMap F (Fv F v) β))

def Carries (x : Fin 1 → Fin M → E) (μ : Measure (HA (AF F) σ J))
    (μ' : Measure (Hstab (AF F) σ J x)) (ν : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) : Prop :=
  ∀ f : HA (AF F) σ J → ℝ≥0∞, Measurable f →
    ∀ s : (Fin 1 → Fin M → AF F ⊗[F] E) → HA (AF F) σ J,
      (∀ y, (∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) →
        s y • ratTup (F := F) (AF F) x = y) →
      ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ h', f (s y * (h' : HA (AF F) σ J)) ∂μ' ∂ν

def SW1c3 : Prop :=
  3 ≤ M → ∀ (x : Fin 1 → Fin M → E) (β : F), β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    (∀ y : Fin 1 → Fin M → AF F ⊗[F] E, qR (AF F) σ J (y 0) = algebraMap F (AF F) β →
      ∃ g : HA (AF F) σ J, g • ratTup (F := F) (AF F) x = y) →
    AllSome (IsCharAF F) fun ψ =>
    OnH F E σ M J fun μ 𝓕 =>
    AllSome (IsDxDq F E σ M J ψ β) fun ν =>
    AllSome (fun μ' : Measure (Hstab (AF F) σ J x) =>
      μ'.IsHaarMeasure ∧ Carries F E σ M J x μ μ' ν) fun μ' =>
    AllSome (fun 𝓕' : Set (Hstab (AF F) σ J x) =>
      IsFundamentalDomain (HstabFin (AF F) σ J x) 𝓕' μ') fun 𝓕' => μ' 𝓕' = μ 𝓕

end SW

def Conclusion1 (_D : D7) : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ J →
      SW1a1 F E σ M J ∧ SW1a2 F E σ M J ∧ SW1b1 F E σ M J ∧ SW1b2 F E σ M J ∧
      SW1c1 F E σ M J ∧ SW1c2 F E σ M J ∧ SW1c3 F E σ M J

section Vol

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain
open scoped TensorProduct

def intAf (F : Type) [Field F] [NumberField F] : Set (Af F) :=
  {a | ∀ v : HeightOneSpectrum (𝓞 F), evalV F v a ∈ v.adicCompletionIntegers F}

def latHat (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Set (Fin M → E)) : AddSubgroup (Fin M → Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ intAf F, ∃ x ∈ L, y = fun i => a ⊗ₜ[F] x i}

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

def finMat (h : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E) :=
  ((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map
    (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E))

def infMat (θ : Ainf F ⊗[F] E →+* ℂ) (h : HA (AF F) σ J) : Matrix (Fin M) (Fin M) ℂ :=
  (((HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)).map
    (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E))).map θ

def IsInfEmb (τ : E →+* ℂ) (θ : Ainf F ⊗[F] E →+* ℂ) : Prop :=
  (∀ x : E, θ ((1 : Ainf F) ⊗ₜ[F] x) = τ x) ∧ Continuous fun a : Ainf F => θ (a ⊗ₜ[F] (1 : E))

end Vol

def embOf (D : D7) (ρ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb (D.eTau ρ).1

def L0c (D : D7) : letI := D.host.cmStar; ∀ W : HSpace D.host.E, Set (Fin W.rank → D.host.E) :=
  letI := D.host.cmStar
  fun W => {x | ∑ i, x i • W.frame i ∈ W.L0}

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory in

def IsVolMeas (D : D7) : letI := D.host.cmStar; ∀ (W : HSpace D.host.E) (_P _Q : ℕ),
    Measure (HA (AF D.host.F) D.sp.cm.sig W.gram) → Prop :=
  letI := D.host.cmStar
  fun W P Q μ =>
  μ.IsHaarMeasure ∧
  AllSome (fun θ : D.what₂.Tau → (TensorProduct D.host.F (Ainf D.host.F) D.host.E →+* ℂ) =>
    ∀ ρ, IsInfEmb (embOf D ρ) (θ ρ)) fun θ =>
  AllSome (fun A : D.what₂.Tau → Matrix (Fin P ⊕ Fin Q) (Fin W.rank) ℂ =>
    ∀ ρ, (A ρ).conjTranspose * Formalism.UG.Jpq P Q * A ρ = W.gram.map (embOf D ρ)) fun A =>
  ∀ B : D.what₂.Tau → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) →
    μ {h | (∀ y, y ∈ latHat D.host.F D.host.E (L0c D W) ↔
          (finMat D.sp.cm.sig W.gram h).mulVec y ∈ latHat D.host.F D.host.E (L0c D W)) ∧
        ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat D.sp.cm.sig W.gram (θ ρ) h} =
      ∏ ρ, D.cd.cd P Q (B ρ)

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory in

def VolTie (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) →
    AllSome (IsVolMeas D W P Q) fun μ =>
    AllSome (fun 𝓕 => IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ) fun 𝓕 =>
      μ 𝓕 = ENNReal.ofReal (D.vol W)

def Conclusion2 (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 3 ≤ W.rank →
    ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) →
    ∃ x : W.V, W.hT x x = (if s then 1 else -1) ∧
      ∃ (W' : HSpace D.host.E) (ι : W'.V →ₗ[D.host.E] W.V),
        HSpace.IsIsomEmb W' W ι ∧ LinearMap.range ι = LinearMap.ker (W.hT x) ∧ W'.SigOK ∧
        (∀ τ, W'.sig τ = (if s then (P - 1, Q) else (P, Q - 1))) ∧
        D.vol W / D.vol W' = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E W.rank

def VolumeEqMass₂ (D : D7) : Prop :=
  letI := D.host.cmStar
  (∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → D.vol W = massI D W.rank) ∧
  (∀ (W : HSpace D.host.E) (P Q : ℕ), W.SigOK → (∀ τ, W.sig τ = (P, Q)) → 2 ≤ P →
    D.vol W = massI D (P + Q))

def SiegelMassRatioCM : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ M : ℕ, 3 ≤ M →
    Formalism.HermitianLatticesTheory.mass (stdForm K M) (stdLat K M) / Formalism.HermitianLatticesTheory.mass (stdForm K (M - 1)) (stdLat K (M - 1)) =
      Formalism.HermitianLatticesTheory.massRatioRightSide K M

def SiegelMassRatioModels : Prop := Formalism.HermitianLatticesTheory.SiegelMassRatio

def MassRatio₂ (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ M : ℕ, 3 ≤ M → massI D M / massI D (M - 1) = Formalism.HermitianLatticesTheory.massRatioRightSide D.host.E M

def LogLValueZetaBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K], Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ M : ℕ, 2 ≤ M →
    |Real.log (Formalism.HermitianLatticesTheory.lValEta K M)| ≤ (Formalism.HermitianLatticesTheory.fDeg K : ℝ) * Real.log (zetaR M)

def gram_det_kernel_dual_lattice (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ M : ℕ, 2 ≤ M → |Real.log (Formalism.HermitianLatticesTheory.lValEta D.host.E M)| ≤ (D.R.f : ℝ) * Real.log (zetaR M)

theorem mass_ratio_of_general (D : D7) (h : SiegelMassRatioCM) : MassRatio₂ D := by
  let _ := D.host.cmStar
  intro M hM
  exact h D.host.E D.sp.cm.cmUnram M hM

theorem prod_gap_eq_facProd (n : ℕ) :
    (∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))) = facProd n := by
  cases n with
  | zero => simp [facProd]
  | succ m =>
    have h1 := Matrix.det_vandermonde (fun i : Fin (m + 1) => ((i : ℕ) : ℝ))
    have h2 := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
    have h3 : (∏ a : Fin (m + 1), ∏ b ∈ univ.filter (fun b : Fin (m + 1) => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)))
        = ∏ i : Fin (m + 1), ∏ j ∈ Ioi i, (((j : ℕ) : ℝ) - ((i : ℕ) : ℝ)) := by
      refine Finset.prod_congr rfl fun a _ => Finset.prod_congr ?_ fun _ _ => rfl
      ext b; simp
    rw [h3, ← h1, h2, facProd, ← Nat.prod_range_succ_factorial]
    push_cast
    rfl

theorem dimV_eq_fdegHC {n : ℕ} (lam : Fin n → ℝ) (h : StrictAnti lam) :
    dimV lam = Formalism.QuantumDeterminants.fdegHC lam := by
  unfold dimV Formalism.QuantumDeterminants.fdegHC vand
  rw [prod_gap_eq_facProd]
  congr 1
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b hb => ?_
  have hab : a < b := (Finset.mem_filter.1 hb).2
  rw [abs_of_pos (sub_pos.2 (h hab))]

section DS

open Formalism.MainNotions.S MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

def wtF {n : ℕ} (lam : Fin n → ℝ) (X km : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∏ i : Fin (n - 1),
    (leadMinor (km⁻¹ * NormedSpace.exp X * km) (i.val + 1) (by omega)).re ^
      (-(lam ⟨i.val, by omega⟩ - lam ⟨i.val + 1, by omega⟩ + 1))

def rank1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (x : H) : H →L[ℂ] H :=
  (innerSL ℂ x).smulRight x

def SmallPrimeLengthBound (_D : D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∀ E : H →L[ℂ] H, IsOrthProjOnto E (lowKSub ε lam σ) →
      ∀ w : H, IsHighestUnit ε lam σ w →
      ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
        120 * (n : ℝ) * ((min (nPlus ε) (nMinus ε) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
      ∀ X : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.inP ε X →
        (E ∘L σ (NormedSpace.exp X) ∘L E =
          ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℂ) •
            ∫ kk : Formalism.REAL.KG ε, ((wtF lam X (Formalism.REAL.toMK kk) : ℝ) : ℂ) • rank1 (σ (Formalism.REAL.toMK kk) w)
              ∂(Formalism.REAL.muK ε)) ∧
        (E ∘L σ (NormedSpace.exp X) ∘L E).IsPositive

def NonvanishingBesselPeriod (_D : D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      ∃ d : ℝ, IsFdeg (Formalism.REAL.muG ε) σ d

def FamilyMassLastLine (_D : D7) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ →
      IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) (lowKSub ε lam σ) ∧
        ((Module.finrank ℂ (lowKSub ε lam σ) : ℕ) : ℝ) = dTau ε lam

def RepresentationDimensionGeneral (D : D7) (C3 : ℝ) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    let p : ℝ := (Finset.univ.filter (fun a => ε a = true)).card
    let q : ℝ := (Finset.univ.filter (fun a => ε a = false)).card
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h0 →
    Real.exp (-(N : ℝ)) ≤ ep0 → ep0 < 1 / 2 →
    C3 * min p q * (p * q) ^ 3 * N * Real.log N / ep0 ^ 2 ≤ h0 →
    IsDS ε lam σ → w ≠ 0 →
    (1 - ep0) * Formalism.QuantumDeterminants.fdegHC lam ≤ fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ∧
    fdegOf ((D.s.cdScale N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
      4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) * (C3 * p * q * N * lamAbs lam) ^ (p * q)

def DsigEx (D : D7) : Prop :=
  ∀ τ : D.what₂.Tau, ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ → (H →L[ℂ] H)),
    IsDS (epsSH D.R) (lamSH D.R (D.hc τ)) σ ∧
    IsFdeg ((D.s.cdScale _ (epsSH D.R) : ENNReal) • Formalism.REAL.muG (epsSH D.R)) σ (D.dsig τ)

end DS

def pY (D : D7) : ℕ := D.R.sigY0.1

def qY (D : D7) : ℕ := D.R.sigY0.2

def gap3 (D : D7) (C ep0 : ℝ) : ℝ :=
  C * (min (pY D) (qY D) : ℕ) * ((pY D : ℝ) * (qY D : ℝ)) ^ 3 * (D.R.r : ℝ) *
    Real.log (D.R.r : ℝ) / ep0 ^ 2

def PointsLemma (D : D7) (C : ℝ) : Prop :=
  ∀ ep0 : ℝ, Real.exp (-(D.R.r : ℝ)) ≤ ep0 → ep0 < 1 / 2 → ∀ ρ : D.what₂.Tau,
    GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D C ep0) →
    (1 - ep0) * dimV (rowLam D ρ) ≤ D.dsig ρ ∧
    D.dsig ρ ≤ 4 * dTau (rowSgn D) (rowLam D ρ) *
      (C * (pY D : ℝ) * (qY D : ℝ) * (D.R.r : ℝ) * lamAbs (rowLam D ρ)) ^ (pY D * qY D)

def Conclusion4a (D : D7) : Prop :=
  ∀ i : Fin 2, 3 ≤ D.host.g i →
    (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) / 2 ≤ idxColLoc (D.host.g i) D.R.k ∧
    idxColLoc (D.host.g i) D.R.k ≤ (D.host.g i : ℝ) ^ (D.R.k * (D.R.k + 1) / 2) ∧
    (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2) / 2 ≤
      idxRowLoc (D.host.g i) D.R.k D.R.m ∧
    idxRowLoc (D.host.g i) D.R.k D.R.m ≤ (D.host.g i : ℝ) ^ ((D.R.r ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) / 2)

def Conclusion4b (D : D7) : Prop :=
  D.R.r = D.R.k + 1 + 2 * D.R.rS ∧
  2 * (dimN D.R.k D.R.m : ℤ) = (D.R.r : ℤ) ^ 2 - ((D.R.k : ℤ) + 1) ^ 2 - 2 * (D.R.rS : ℤ) ∧
  ((D.R.r : ℤ) ^ 2 + 3 * D.R.k + 1 + 2 * D.R.rS) - (D.R.k : ℤ) * (D.R.k + 1) =
    (D.R.m : ℤ) * (2 * D.R.k + D.R.m - 1)

def PrimeSumLogBound (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ g : ℕ, g.Prime → ∀ A : (D.sp.X 0).V ≃ₗ[D.host.E] (D.sp.X 0).V,
    (∀ x y, (D.sp.X 0).hT (A x) (A y) = (D.sp.X 0).hT x y) → A ^ g = 1 → A ≠ 1 →
      g - 1 ≤ 2 * D.R.f * D.R.k

def GBig (D : D7) : Prop := ∃ i : Fin 2, 2 * D.R.f * D.R.k < D.host.g i - 1

def SplitsF (D : D7) (p : ℕ) : Prop :=
  Nat.card {v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F) // (p : 𝓞 D.host.F) ∈ v.asIdeal} = D.R.f ∧
  ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), (p : 𝓞 D.host.F) ∈ v.asIdeal →
    Nat.card (𝓞 D.host.F ⧸ v.asIdeal) = p

def adm17 (D : D7) (Lv : LevelData D) : Prop :=
  letI := D.host.cmStar
  GBig D → ∀ u : D.what₂.Word, (Lv u).ProG → ∀ c : (D.mem u).C.cls 0,
    Formalism.UG.ratPts D.sp.cm.sig D.sp.gram0 (IsDedekindDomain.FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊓
      (Lv u).U.map (MulAut.conj ((Lv u).y c : GL (Fin D.R.k) _)).toMonoidHom = ⊥

def Conclusion4p (D : D7) (Lv : LevelData D) : Prop :=
  letI := D.host.cmStar
  ∀ u : D.what₂.Word, (Lv u).ProG

def SmallOrderPrimeLogSumBound (D : D7) (_Lv : LevelData D) : Prop :=
  GBig D → ∀ u : D.what₂.Word, (D.mem u).C.StabZero

def LevelIndexAtPlace (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (v : (D.mem u).A.vT) (φ : Fin D.R.k → (D.mem u).A.Fv v), φ ≠ 0 →
    Nat.card (GL (Fin D.R.k) ((D.mem u).A.Fv v)) =
      Nat.card {A : GL (Fin D.R.k) ((D.mem u).A.Fv v) //
        Matrix.vecMul φ (A : Matrix (Fin D.R.k) (Fin D.R.k) ((D.mem u).A.Fv v)) = φ} *
      ((D.mem u).A.T ^ D.R.k - 1)

def ClassNumberFormula₂ (D : D7) (_Lv : LevelData D) : Prop :=
  GBig D → (∀ i, SplitsF D (D.host.g i)) → ∀ u : D.what₂.Word, SplitsF D (D.mem u).A.T →
    (Nat.card ((D.mem u).C.cls 0) : ℝ) =
      massI D D.R.k * idxPi D (D.host.g 0) (D.host.g 1) * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

def Mu0Tie (D : D7) (u : D.what₂.Word) : Prop :=
  (D.mem u).C.StabZero →
    ((haveI := (D.mem u).A.Mu0_fd; Module.finrank ℂ (D.mem u).A.Mu0 : ℕ) : ℝ) =
      (Nat.card ((D.mem u).C.cls 0) : ℝ) * ∏ ρ, dimV (uColR D u ρ)

def Conclusion4f (D : D7) (_Lv : LevelData D) : Prop :=
  GBig D → (∀ i, SplitsF D (D.host.g i)) → ∀ u : D.what₂.Word, SplitsF D (D.mem u).A.T → Mu0Tie D u →
    ((haveI := (D.mem u).A.Mu0_fd; Module.finrank ℂ (D.mem u).A.Mu0 : ℕ) : ℝ) =
      duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f

theorem level_rank_of_trivial_stabilisers (D : D7) (Lv : LevelData D) (hd : SmallOrderPrimeLogSumBound D Lv) (hn : ClassNumberFormula₂ D Lv) : Conclusion4f D Lv := by
  intro hg hs u hT hM
  rw [hM (hd hg u), hn hg hs u hT]
  unfold duStarU duStarP
  ring

def OrthonormalLatticeRankK (D : D7) : Prop :=
  letI := D.host.cmStar
  ∃ L : Submodule (𝓞 D.host.E) (D.sp.X 0).V, Formalism.HermitianLatticesTheory.IsOrthoLattice (D.sp.X 0).hT L D.R.k

def DstarLow (D : D7) : Prop :=
  (2 / 3 : ℝ) ^ D.R.f * massI D D.R.r * idxSig D (D.host.g 0) (D.host.g 1) *
    ∏ ρ, dimV (rowLam D ρ) ≤ DstarD D

def DstarLowerFromGap (D : D7) (C3 : ℝ) : Prop :=
  (∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D C3 (1 / 3))) → DstarLow D

def uN (D : D7) (u : D.what₂.Word) (ρ : D.what₂.Tau) (i : ℕ) : ℝ :=
  if h : i < D.R.k then (((D.hcW u ρ).u ⟨i, h⟩ : ℚ) : ℝ) else 0

def vN (D : D7) (ρ : D.what₂.Tau) (i : ℕ) : ℝ :=
  if h : i < D.R.k - 1 then (((D.hc ρ).v ⟨i, h⟩ : ℚ) : ℝ) else 0

def bN (D : D7) (ρ : D.what₂.Tau) (j : ℕ) : ℝ :=
  if h : j < D.R.m then (((D.hc ρ).b ⟨j, h⟩ : ℚ) : ℝ) else 0

def IsTop (D : D7) (ρ : D.what₂.Tau) : Prop := (D.eTau ρ).1 ∈ D.host.topPlaces

def GapA (D : D7) (sc : Scale) (C0 : ℝ) : Prop :=
  ∀ ρ j, j + 1 < D.R.m →
    (D.R.r : ℝ) ^ 19 * (D.R.f : ℝ) ^ 5 * sc.L / C0 ≤ bN D ρ (j + 1) - bN D ρ j

def DataB (D : D7) (sc : Scale) (C0 : ℝ) (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ) : Prop :=
  Real.pi ≤ D.host.v ∧ Real.log D.host.v ≤ sc.L ∧
  (D.R.f : ℝ) ≤ sc.x ^ C0 ∧ (D.R.m : ℝ) ^ 2 * sc.L ≤ D.R.k ∧ (D.R.k : ℝ) ≤ sc.x ^ C0 ∧
  (∀ i : Fin 2, ((D.R.k : ℝ) * sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧ Real.log (D.host.g i : ℝ) ≤ C0 * sc.L) ∧
  1 ≤ Δ ∧
  (∀ ρ i, i < D.R.k - 1 → 0 ≤ vN D ρ i ∧ vN D ρ i ≤ (D.R.k : ℝ) * (4 * Δ)) ∧
  (∀ ρ i, i + 1 < D.R.k - 1 → vN D ρ i - vN D ρ (i + 1) = 4 * Δ) ∧
  (∀ u ρ l, 1 ≤ l → l ≤ D.R.k - 2 →
    uN D u ρ l = vN D ρ (l - 1) - 1 / 2 ∨ uN D u ρ l = vN D ρ (l - 1) - 1 / 2 - Δ) ∧
  (∀ u ρ, IsTop D ρ → uN D u ρ 0 ≤ 2 * sc.a ∧ -sc.a ≤ uN D u ρ (D.R.k - 1)) ∧
  (∀ u ρ, ¬ IsTop D ρ →
    (D.R.k : ℝ) * (4 * Δ) ≤ uN D u ρ 0 - vN D ρ 0 ∧ uN D u ρ 0 - vN D ρ 0 ≤ 2 * D.R.k * (4 * Δ) ∧
    uN D u ρ (D.R.k - 1) = vN D ρ (D.R.k - 2) - 1 / 2) ∧
  (∀ ρ j, j < D.R.m → 0 < w j ρ ∧ bN D ρ j < w j ρ ∧ |w j ρ - bN D ρ j| ≤ bN D ρ j / sc.x) ∧
  (∀ ρ j, j + 1 < D.R.m → w j ρ < bN D ρ (j + 1)) ∧
  (∀ ρ, (D.R.k : ℝ) * (4 * Δ) ≤ bN D ρ 0 / sc.x ∧ w (D.R.m - 1) ρ ≤ 2 * sc.b) ∧
  GapA D sc C0

def PartFourSectionBData (D : D7) (sc : Scale) (C3 C0 : ℝ) : Prop :=
  ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w →
    (∀ i : Fin 2, 2 * D.R.f * D.R.k < D.host.g i - 1) ∧
    (∀ ρ, GapAtLeast (rowSgn D) (rowLam D ρ) (gap3 D C3 (1 / 3))) ∧
    (∀ u : D.what₂.Word, (D.mem u).C.StabZero) ∧ DstarLow D

def lowB (D : D7) (sc : Scale) (C : ℝ) (w : ℕ → D.what₂.Tau → ℝ) : ℝ :=
  (∑ j ∈ range D.R.m, (1 / (D.R.f : ℝ)) * ∑ ρ, Real.log (w j ρ * D.host.v / Real.pi)) +
    (D.R.m : ℝ) * (∑ i : Fin 2, Real.log (D.host.g i : ℝ)) -
    C * (sc.L + (D.R.m : ℝ) ^ 2 * sc.L / D.R.k)

def Conclusion5 (D : D7) (sc : Scale) (C0 C : ℝ) : Prop :=
  ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w → ∀ u : D.what₂.Word,
    lowB D sc C w ≤ logXuD D u ∧ logXuD D u ≤ C * D.R.m * sc.L

def TorusPairsWithVariant (D : D7) (sc : Scale) (C0 C : ℝ) : Prop :=
  ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w → ∀ Γ : ℝ, 1 ≤ Γ → ∀ u : D.what₂.Word,
    Real.exp (logXuD D u) * Γ ^ (-(2 : ℝ) / (D.R.f * D.R.k)) ≤ ((D.mem u).A.T : ℝ) →
    ((D.mem u).A.T : ℝ) ≤
      Real.exp (logXuD D u) * Γ ^ (-(2 : ℝ) / (D.R.f * D.R.k)) * (1 + 1 / ((D.R.f : ℝ) * D.R.k)) →
    |Real.log (duStarU D u * (((D.mem u).A.T : ℝ) ^ D.R.k - 1) ^ D.R.f / (DstarD D * Γ ^ (-(2 : ℝ))))| ≤ C ∧
    Real.log ((D.mem u).A.T : ℝ) ≤ C * D.R.m * sc.L ∧
    lowB D sc C w - 2 * Real.log Γ / ((D.R.f : ℝ) * D.R.k) ≤ Real.log ((D.mem u).A.T : ℝ)

def VandermondeVariationBound (D : D7) (sc : Scale) (C0 C : ℝ) : Prop :=
  ∀ (Δ : ℝ) (w : ℕ → D.what₂.Tau → ℝ), DataB D sc C0 Δ w →
    (∀ (u u' : D.what₂.Word) (ρ : D.what₂.Tau),
      |Real.log (vand (uColR D u ρ)) - Real.log (vand (uColR D u' ρ))| ≤
        C * D.R.k * Real.log D.R.k) ∧
    ∀ u u' : D.what₂.Word, |logXuD D u - logXuD D u'| ≤ C * Real.log D.R.k

def IntegralityFromMetric (D : D7) : Prop := Conclusion1 D

def MassVolumeBoundsAll : Prop := SiegelMassRatioCM ∧ SiegelMassRatioModels ∧ LogLValueZetaBound

def VolumeMass (D : D7) : Prop := Conclusion2 D ∧ VolumeEqMass₂ D ∧ MassRatio₂ D ∧ gram_det_kernel_dual_lattice D

def AbsoluteConstantSecondPart (D : D7) : Prop := Conclusion1 D → MassVolumeBoundsAll

def HodgeTateFromSandwich (D : D7) : Prop := Conclusion1 D → VolTie D → VolumeMass D

def Adm3 (D : D7) : Prop := SmallPrimeLengthBound D ∧ NonvanishingBesselPeriod D ∧ FamilyMassLastLine D

def TheoremThreeCompactDual (D : D7) (C3 : ℝ) : Prop := Adm3 D → cdScaleTie D → RepresentationDimensionGeneral D C3

def TowerRallisLemma (D : D7) (C3 : ℝ) : Prop := RepresentationDimensionGeneral D C3 → FamilyMassLastLine D → DsigEx D → PointsLemma D C3

def StandardLatticeProperties (D : D7) (Lv : LevelData D) (C3 : ℝ) : Prop :=
  Conclusion4a D ∧ Conclusion4b D ∧ PrimeSumLogBound D ∧ Conclusion4p D Lv ∧ SmallOrderPrimeLogSumBound D Lv ∧ LevelIndexAtPlace D ∧ ClassNumberFormula₂ D Lv ∧ Conclusion4f D Lv ∧
  OrthonormalLatticeRankK D ∧ DstarLowerFromGap D C3

def ThetaChernBoundOfLastLine (D : D7) (Lv : LevelData D) (C3 : ℝ) : Prop :=
  VolumeMass D → PointsLemma D C3 → adm17 D Lv → StandardLatticeProperties D Lv C3

def PartFourSectionBStatement (D : D7) (Lv : LevelData D) (sc : Scale) (C3 C0 : ℝ) : Prop :=
  StandardLatticeProperties D Lv C3 → PartFourSectionBData D sc C3 C0

def Conclusion5₂ (D : D7) (sc : Scale) (C0 C : ℝ) : Prop := Conclusion5 D sc C0 C ∧ TorusPairsWithVariant D sc C0 C ∧ VandermondeVariationBound D sc C0 C

def GGFromIrreducibility (D : D7) (sc : Scale) (C3 C0 C : ℝ) : Prop :=
  VolumeMass D → PointsLemma D C3 → Conclusion4a D → Conclusion4b D → PartFourSectionBData D sc C3 C0 → Conclusion5₂ D sc C0 C

def admitted (D : D7) (Lv : LevelData D) : Prop := Adm3 D ∧ adm17 D Lv

def TiesP (D : D7) : Prop := VolTie D ∧ cdScaleTie D ∧ DsigEx D

def Conclusion₂ (D : D7) (Lv : LevelData D) (sc : Scale) (C3 C0 C : ℝ) : Prop :=
  Conclusion1 D ∧ MassVolumeBoundsAll ∧ VolumeMass D ∧ RepresentationDimensionGeneral D C3 ∧ PointsLemma D C3 ∧ StandardLatticeProperties D Lv C3 ∧ PartFourSectionBData D sc C3 C0 ∧ Conclusion5₂ D sc C0 C

def Stmt (D : D7) (Lv : LevelData D) (sc : Scale) (C3 C0 C : ℝ) : Prop :=
  admitted D Lv → TiesP D → Conclusion₂ D Lv sc C3 C0 C

theorem stmt_of_items (D : D7) (Lv : LevelData D) (sc : Scale) (C3 C0 C : ℝ)
    (h1 : IntegralityFromMetric D) (h2a : AbsoluteConstantSecondPart D) (h2 : HodgeTateFromSandwich D) (h3a : TheoremThreeCompactDual D C3) (h3 : TowerRallisLemma D C3)
    (h4 : ThetaChernBoundOfLastLine D Lv C3) (h4B : PartFourSectionBStatement D Lv sc C3 C0) (h5 : GGFromIrreducibility D sc C3 C0 C) :
    Stmt D Lv sc C3 C0 C := by
  rintro ⟨hA3, h17⟩ ⟨hV, hc, hd⟩
  have p2 := h2 h1 hV
  have p3a := h3a hA3 hc
  have p3 := h3 p3a hA3.2.2 hd
  have p4 := h4 p2 p3 h17
  have p4B := h4B p4
  exact ⟨h1, h2a h1, p2, p3a, p3, p4, p4B, h5 p2 p3 p4.1 p4.2.1 p4B⟩

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyPartOne : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i)
def FamilyMassVolumeBounds : Prop := ∀ x (i : Fm.Ix x), VolumeMass (Fm.D x i)
def FamilyTheoremThreeGeneral (C3 : ℝ) : Prop := ∀ x (i : Fm.Ix x), RepresentationDimensionGeneral (Fm.D x i) C3
def FamilyTheoremThree (C3 : ℝ) : Prop := ∀ x (i : Fm.Ix x), PointsLemma (Fm.D x i) C3
def FamilyPartFour (C3 : ℝ) : Prop :=
  ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), StandardLatticeProperties (Fm.D x i) (Fm.ex x hx i).lev C3

def FamilyPartFourSectionB (C3 : ℝ) : Prop :=
  ∀ C0 : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, PartFourSectionBData (Fm.D x i) (Fm.L x i).sc C3 C0

def PartFiveFamilyBounds : Prop :=
  ∀ C0 : ℝ, ∃ C x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ i : Fm.Ix x, Conclusion5₂ (Fm.D x i) (Fm.L x i).sc C0 C

def VolTieF : Prop := ∀ x (i : Fm.Ix x), VolTie (Fm.D x i)
def DsigExF : Prop := ∀ x (i : Fm.Ix x), DsigEx (Fm.D x i)
def FamilyTheoremThreeAdmitted : Prop := ∀ x (i : Fm.Ix x), Adm3 (Fm.D x i)
def FamilyLevelConditionAdmitted : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), adm17 (Fm.D x i) (Fm.ex x hx i).lev

def PeriodFamilyStatement : Prop := FamilyPartOne Fm
def FamilyMassTheoremAll : Prop := FamilyPartOne Fm → MassVolumeBoundsAll
def DeterminantValueFamily : Prop := FamilyPartOne Fm → VolTieF Fm → FamilyMassVolumeBounds Fm
def FamilyTheoremThreeAll (C3 : ℝ) : Prop := FamilyTheoremThreeAdmitted Fm → FamilyTheoremThreeGeneral Fm C3
def FlatLineDegreeFamilyStatement (C3 : ℝ) : Prop := FamilyTheoremThreeGeneral Fm C3 → FamilyTheoremThreeAdmitted Fm → DsigExF Fm → FamilyTheoremThree Fm C3
def LiftNormFamilyStatement (C3 : ℝ) : Prop := FamilyMassVolumeBounds Fm → FamilyTheoremThree Fm C3 → FamilyLevelConditionAdmitted Fm → FamilyPartFour Fm C3
def FamilySectionBStatement (C3 : ℝ) : Prop := FamilyPartFour Fm C3 → FamilyPartFourSectionB Fm C3
def DegreeBoundFamilyStatement (C3 : ℝ) : Prop := FamilyMassVolumeBounds Fm → FamilyTheoremThree Fm C3 → FamilyPartFour Fm C3 → FamilyPartFourSectionB Fm C3 → PartFiveFamilyBounds Fm

def AdmF : Prop := FamilyTheoremThreeAdmitted Fm ∧ FamilyLevelConditionAdmitted Fm
def TiesF : Prop := VolTieF Fm ∧ DsigExF Fm
def ConclusionOnFamily (C3 : ℝ) : Prop :=
  FamilyPartOne Fm ∧ MassVolumeBoundsAll ∧ FamilyMassVolumeBounds Fm ∧ FamilyTheoremThreeGeneral Fm C3 ∧ FamilyTheoremThree Fm C3 ∧ FamilyPartFour Fm C3 ∧ FamilyPartFourSectionB Fm C3 ∧ PartFiveFamilyBounds Fm
def KudlaFamilyStatement (C3 : ℝ) : Prop := AdmF Fm → TiesF Fm → ConclusionOnFamily Fm C3

theorem stmtF_of_items (C3 : ℝ) (h1 : PeriodFamilyStatement Fm) (h2a : FamilyMassTheoremAll Fm) (h2 : DeterminantValueFamily Fm)
    (h3a : FamilyTheoremThreeAll Fm C3) (h3 : FlatLineDegreeFamilyStatement Fm C3) (h4 : LiftNormFamilyStatement Fm C3) (h4B : FamilySectionBStatement Fm C3)
    (h5 : DegreeBoundFamilyStatement Fm C3) : KudlaFamilyStatement Fm C3 := by
  rintro ⟨hA3, h17⟩ ⟨hV, hd⟩
  have p2 := h2 h1 hV
  have p3a := h3a hA3
  have p3 := h3 p3a hA3 hd
  have p4 := h4 p2 p3 h17
  have p4B := h4B p4
  exact ⟨h1, h2a h1, p2, p3a, p3, p4, p4B, h5 p2 p3 p4 p4B⟩

end Fam

def FactDuStar (D : D7) : Prop := ∀ u, ((D.mem u).A.duStar : ℝ) = duStarU D u

def FactDstar (D : D7) : Prop := D.what₂.Dstar = DstarD D

theorem factDuStar_fam {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    FactDuStar (Fm.D x i) := (Fm.ex x hx i).duStar_def

theorem factDstar_fam {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    FactDstar (Fm.D x i) := (Fm.ex x hx i).Dstar_def

end Formalism.MainNotions.StandardLattice
