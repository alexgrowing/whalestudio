import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert

noncomputable section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical

namespace UpperTheory.ConvolutionTheory.GM

section Defs

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

def cf (w : Pl K) (x : AdelicGLn.FiniteAdelicGL K n) : GL (Fin n) (w.adicCompletion K) := finAt w (finEmb K n x)

def Free (w : Pl K) (r : AdelicGLn.FiniteAdelicGL K n → ℂ) : Prop := ∀ y x, r (AdelicGLn.localEmbedding w y * x) = r x

def mono (wd : List (Option (Ix K n))) : MvPolynomial (Option (Ix K n)) ℂ := (wd.map X).prod

def atPl (w : Pl K) (p : MvPolynomial (Fin n) ℂ) : MvPolynomial (Pl K × Fin n) ℂ := rename (fun i => (w, i)) p

variable {F : Type} [Field F] [NumberField F] [Algebra F K]

def Sup {q : Pl F} (w₀ : PlacesOver K q) (ν : Fin n → ℤ) (j : ℕ) (Y : ℝ) (f : normOneGL K n → ℂ) : Prop :=
  ∀ g : normOneGL K n, f g ≠ 0 → heightOff q (g : AdelicGLn.AdelicGL K n) ≤ Y ∧
    finAt w₀.1 (g : AdelicGLn.AdelicGL K n) ∈ iwCoset w₀.1 (fun i => (j : ℤ) * ν i) ∧
    ∀ w : PlacesOver K q, w ≠ w₀ → finAt w.1 (g : AdelicGLn.AdelicGL K n) ∈ GLnLocal.iwahori (w.1.adicCompletion K) n

end Defs

def ConvSpec : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (β γ : TI K n),
    (∀ g, conv ν β γ g = ∫ x, β x * γ (x⁻¹ * g) ∂ν) ∧
      ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure], Oinf μ ν (conv ν β γ) = Oinf μ ν β ∘L Oinf μ ν γ

def WordHt : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (ν : Measure (archGroup K n)) [ν.IsHaarMeasure] (a₀ : TI K n), SmoothT a₀ →
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ (wd : List (Option (Ix K n))) (g : archGroup K n), word ν a₀ wd g ≠ 0 →
      AutomorphicForm.height (infEmb K n g) ≤ Y ^ (wd.length + 1)

def SphEx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ w : Pl K, (∀ p : MvPolynomial (Fin n) ℂ, ∃ h, IsSph w p h) ∧
    IsSph w (1 : MvPolynomial (Fin n) ℂ) ((GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1) ∧
    ∀ (p : MvPolynomial (Fin n) ℂ) h, IsSph w p h → IsLocallyConstant h ∧ HasCompactSupport h ∧
      ∀ k ∈ GLnLocal.integralGL (w.adicCompletion K) n, ∀ x, h (k * x) = h x ∧ h (x * k) = h x

def SphAct : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (𝔞 : Amp μ) (ev), 𝔞.IsEv ev → ∀ w ∉ 𝔞.S,
    ∀ (p : MvPolynomial (Fin n) ℂ) h, IsSph w p h → ∀ u ∈ fixL μ w (GLnLocal.integralGL (w.adicCompletion K) n),
      sphOp μ w h u = ev (map C (atPl w p)) u

def StepFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
    (w : Pl K) (J : Subgroup (GL (Fin n) (w.adicCompletion K))), IsOpen (J : Set (GL (Fin n) (w.adicCompletion K))) →
    ∀ (h : GL (Fin n) (w.adicCompletion K) → ℂ), HasCompactSupport h → (∀ k ∈ J, ∀ x, h (x * k) = h x) →
    ∀ (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w r → ∀ e₀ e₁ : TF K n,
      (∀ x, e₀ x = r x * (J : Set _).indicator 1 (cf w x)) → (∀ x, e₁ x = r x * h (cf w x)) →
      (∀ u, Ofin μ m e₀ u ∈ fixL μ w J) ∧
        Ofin μ m e₁ = (∑ᶠ c : GL (Fin n) (w.adicCompletion K) ⧸ J, h c.out • rhoL μ w c.out) ∘L Ofin μ m e₀

def HeckeFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
    (𝔞 : Amp μ) (ev), 𝔞.IsEv ev → ∀ T : Finset (Pl K), (∀ w ∈ T, w ∉ 𝔞.S) →
    ∀ (p : Pl K → MvPolynomial (Fin n) ℂ) (h : ∀ w : Pl K, GL (Fin n) (w.adicCompletion K) → ℂ), (∀ w ∈ T, IsSph w (p w) (h w)) →
    ∀ (r : AdelicGLn.FiniteAdelicGL K n → ℂ), (∀ w ∈ T, Free w r) → ∀ e₀ e₁ : TF K n,
      (∀ x, e₀ x = r x * ∏ w ∈ T, (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x)) →
      (∀ x, e₁ x = r x * ∏ w ∈ T, h w (cf w x)) → Ofin μ m e₁ = ev (map C (∏ w ∈ T, atPl w (p w))) ∘L Ofin μ m e₀

def UiwMul : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (w : Pl K) (ν ν' : Fin n → ℤ), Antitone ν → Antitone ν' →
    Uiw μ w (ν + ν') = Uiw μ w ν ∘L Uiw μ w ν'

def UiwFin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (m : Measure (AdelicGLn.FiniteAdelicGL K n)) [m.IsHaarMeasure]
    (w : Pl K) (ν : Fin n → ℤ), Antitone ν → ∀ (j : ℕ) (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w r → ∀ e₀ e₁ : TF K n,
      (∀ x, e₀ x = r x * (iwCoset w 0).indicator 1 (cf w x)) →
      (∀ x, e₁ x = r x * (iwCoset w fun i => (j : ℤ) * ν i).indicator 1 (cf w x)) → Ofin μ m e₁ = (Uiw μ w ν ^ j) ∘L Ofin μ m e₀

def RepOne : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (n : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (𝔞 : Amp μ) (ev), 𝔞.IsEv ev → ∀ w₀ ∈ 𝔞.S, ∀ ν : Fin n → ℤ, Antitone ν →
    ∀ T : Finset (Pl K), (∀ w ∈ T, w ∉ 𝔞.S) →
    ∀ (p : Pl K → MvPolynomial (Fin n) ℂ) (h : ∀ w : Pl K, GL (Fin n) (w.adicCompletion K) → ℂ), (∀ w ∈ T, IsSph w (p w) (h w)) →
    ∀ (r : AdelicGLn.FiniteAdelicGL K n → ℂ), Free w₀ r → (∀ w ∈ T, Free w r) →
      (∀ u ∈ 𝔞.U, cf w₀ u ∈ GLnLocal.iwahori (w₀.adicCompletion K) n ∧ ∀ x, r (u * x) = r x) →
    ∀ (j : ℕ) (wd : List (Option (Ix K n))) (e₀ e₁ : TF K n),
      (∀ x, e₀ x = r x * (iwCoset w₀ 0).indicator 1 (cf w₀ x) *
        ∏ w ∈ T, (GLnLocal.integralGL (w.adicCompletion K) n : Set _).indicator 1 (cf w x)) →
      (∀ x, e₁ x = r x * (iwCoset w₀ fun i => (j : ℤ) * ν i).indicator 1 (cf w₀ x) * ∏ w ∈ T, h w (cf w x)) →
      RR μ (tens (word 𝔞.ν 𝔞.a₀ (none :: wd)) e₁) =
        𝔞.A ∘L (ev (C (mono wd) * map C (∏ w ∈ T, atPl w (p w))) ∘L Uiw μ w₀ ν ^ j) ∘L RR μ (tens 𝔞.a₀ e₀)

def AvgE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), 0 < n → ∀ (S : Finset (Pl F)) (β : TI E n)
    (φ : ∀ v : Pl F, GL (Fin n) (CompletionsOver E v) → ℂ), (∀ v ∈ S, IsLocallyConstant (φ v) ∧ HasCompactSupport (φ v)) →
    (∀ v ∉ S, φ v = (unitSet E n v).indicator 1) →
    ∃ e : TF E n, IsLocallyConstant e ∧ (∀ x, e x = ∏ᶠ v, φ v (mapGL n (atFin v) (finEmb E n x))) ∧
      ∀ x, tens β e x = avg (tensE (onInf β) φ) x

def AvgF : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n → ∀ (S : Finset (Pl F)) (β : TI F n)
    (f : ∀ v : Pl F, GL (Fin n) (v.adicCompletion F) → ℂ), (∀ v ∈ S, IsLocallyConstant (f v) ∧ HasCompactSupport (f v)) →
    (∀ v ∉ S, f v = (GLnLocal.integralGL (v.adicCompletion F) n : Set _).indicator 1) →
    ∃ e : TF F n, IsLocallyConstant e ∧ (∀ x, e x = ∏ᶠ v, f v (cf v x)) ∧ ∀ x, tens β e x = avg (tensF (onInf β) f) x

def TensHt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ), 0 < n → ∀ q : Pl F, ∃ c : ℕ, ∀ Yf : ℝ, 1 ≤ Yf → ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∀ (β : TI E n) (e : TF E n) (Y : ℝ), 1 ≤ Y →
    (∀ g, β g ≠ 0 → AutomorphicForm.height (infEmb E n g) ≤ Y) →
    (∀ x, e x ≠ 0 → heightOff q (finEmb E n x) ≤ Yf ∧
      ∀ w : PlacesOver E q, Valued.v (cf w.1 x : Matrix (Fin n) (Fin n) (w.1.adicCompletion E)).det = 1) →
    ∀ g : normOneGL E n, tens β e g ≠ 0 → heightOff q (g : AdelicGLn.AdelicGL E n) ≤ C₁ * Y ^ c ∧ e (finPart E n g) ≠ 0

def HtTot : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (q : Pl F) (w₀ : PlacesOver E q) (ν : Fin n → ℤ), ∃ Q : ℝ, 1 ≤ Q ∧
    ∀ (j : ℕ) (Y : ℝ) (f : normOneGL E n → ℂ), Sup w₀ ν j Y f → ∀ g, f g ≠ 0 →
      AutomorphicForm.height (g : AdelicGLn.AdelicGL E n) ≤ Y * Q ^ j

def TwLin : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), 0 < n → ∀ (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (θ : Twist μ) (ι : Type) (s : Finset ι) (c : ι → ℂ) (f : ι → TG K n) (Z : ℝ),
    (∀ i ∈ s, ∀ x, Z < qht x → twK θ (f i) x = 0) →
    Rop μ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i • Rop μ (f i) ∧ (∀ x, Z < qht x → twK θ (∑ i ∈ s, c i • f i) x = 0) ∧
      twInt θ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * twInt θ (f i)

def SideE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ → ∀ (q : Pl F) (w₀ : PlacesOver E q), Split E q →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (aE : TI E n), AmpFn μ νE aE → ∀ (L : Loc σ n q w₀) (ν : Fin n → ℤ),
      ∃ 𝔢 : Side θ (Module.finrank F E), IsSideE L νE aE ν 𝔢

def SideF : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL F n)) [μ.IsHaarMeasure] (q : Pl F) (w₀ : PlacesOver E q)
      (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (aF : TI F n), AmpFn μ νF aF → ∀ (L : Loc σ n q w₀) (ν : Fin n → ℤ),
      ∃ 𝔣 : Side (Twist.id μ) (Module.finrank F E), IsSideF L νF aF ν 𝔣

open Classical in

def LocAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (κ : Finset (Pl E)), (∀ w ∈ κ, Unr E (w.under (𝓞 F))) → ∀ t₀ : Pl E → Multiset ℂ, (∀ w ∈ κ, (t₀ w).card = n ∧ 0 ∉ t₀ w) → ∀ D : ℕ,
    ∃ γ : Pl E → MvPolynomial (Fin n) ℂ, (∀ w ∈ κ, eval (fun i : Fin n => (t₀ w).esymm (i + 1)) (γ w) ≠ 0) ∧
      ∀ p : Pl E → MvPolynomial (Fin n) ℂ, (∀ w ∈ κ, (p w).totalDegree ≤ D) → ∀ v : Pl F, Unr E v →
        ∀ (h : ∀ w : Pl E, GL (Fin n) (w.adicCompletion E) → ℂ) (f : GL (Fin n) (v.adicCompletion F) → ℂ),
          (∀ w ∈ κ, IsSph w (γ w * p w) (h w)) →
          (∀ w ∉ κ, h w = (GLnLocal.integralGL (w.adicCompletion E) n : Set _).indicator 1) →
          IsSph v (∏ w ∈ κ.filter fun w => w.under (𝓞 F) = v, aeval (powE (resDeg F w)) (γ w * p w)) f →
          MatchAt σ v 1 (prodFn fun w : PlacesOver E v => h w.1) f

def TermEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsTotallyComplex F] [IsTotallyComplex E] (σ : E ≃ₐ[F] E),
    (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL E n)) [μE.IsHaarMeasure] (μF : Measure (normOneGL F n)) [μF.IsHaarMeasure] (θ : Twist μE)
      (q : Pl F) (w₀ : PlacesOver E q) (q₀ : PlacesOver F q), Split E q →
    ∀ (νE : Measure (archGroup E n)) [νE.IsHaarMeasure] (νF : Measure (archGroup F n)) [νF.IsHaarMeasure] (aE : TI E n) (aF : TI F n)
      (ci : ℝ), 0 < ci → ArchPair σ νE νF aE aF ci →
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ (L : Loc σ n q w₀) (ν : Fin n → ℤ), Good ν →
      ∀ (𝔢 : Side θ (Module.finrank F E)) (𝔣 : Side (Twist.id μF) (Module.finrank F E)), IsSideE L νE aE ν 𝔢 → IsSideF L νF aF ν 𝔣 →
      ∃ Y₀ : ℝ, 1 ≤ Y₀ ∧ ∀ (κ : Finset (Pl E)), (∀ w ∈ κ, w ∉ 𝔢.S) → ∀ t₀ : Pl E → Multiset ℂ, (∀ w ∈ κ, (t₀ w).card = n ∧ 0 ∉ t₀ w) →
      ∀ D : ℕ, ∃ γ : MvPolynomial (Pl E × Fin n) ℂ, (∀ x ∈ γ.vars, x.1 ∈ κ) ∧ eval (hval t₀) γ ≠ 0 ∧
        ∀ β : Pl E × Fin n →₀ ℕ, (∀ x ∈ β.support, x.1 ∈ κ) → β.degree ≤ D → ∃ Y₁ : ℝ, 1 ≤ Y₁ ∧
          ∀ evE evF, 𝔢.toAmp.IsEv evE → 𝔣.toAmp.IsEv evF → ∀ (j : ℕ) (wd : List (Option (Ix E n))), ∃ (fE : TG E n) (fF : TG F n),
            Rop μE fE = 𝔢.toAmp.A ∘L (evE (map C γ * monomial β (mono wd)) ∘L 𝔢.Uq 0 ^ j) ∘L Rop μE 𝔢.g ∧
            Rop μF fF = 𝔣.toAmp.A ∘L (evF (bcPR F (map C γ * monomial β (mono wd))) ∘L 𝔣.Uq 0 ^ j) ∘L Rop μF 𝔣.g ∧
            Sup w₀ ν j (Y₁ * Y₀ ^ wd.length) fE ∧ Sup q₀ ν j (Y₁ * Y₀ ^ wd.length) fF ∧
            GMatch σ μE μF (κ₀ * ∏ v ∈ L.S, L.c v) fE fF

end UpperTheory.ConvolutionTheory.GM
