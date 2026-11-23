import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.VecClose

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate

namespace PositivityTheory.Rg.BcB.E2

open PositivityTheory.Rg.BcB.E1

def Gelf : Prop := ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (R : B →⋆ₐ[ℂ] (K →L[ℂ] K)),
  ∃ (S : Type) (_ : TopologicalSpace S) (_ : CompactSpace S) (_ : T2Space S) (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K))
    (e : B →⋆ₐ[ℂ] C(S, ℂ)), (∀ f, ‖π f‖ = ‖f‖) ∧ ∀ b, π (e b) = R b

def Point : Prop := ∀ (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (S : Type) [TopologicalSpace S]
  [CompactSpace S] (e : B →⋆ₐ[ℂ] C(S, ℂ)) (p : B →⋆ₐ[ℂ] ℂ), (∀ b, ‖p b‖ ≤ ‖e b‖) → ∃ s, ∀ b, e b s = p b

def SpecMeas : Prop := ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (S : Type)
  [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S] (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K))
  (v : K), ∃ ν : Measure S, IsFiniteMeasure ν ∧ ν.Regular ∧ ∀ f : C(S, ℂ), ∫ s, f s ∂ν = inner ℂ v (π f v)

def SpecIso : Prop := ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (S : Type)
  [TopologicalSpace S] [CompactSpace S] [T2Space S] [MeasurableSpace S] [BorelSpace S] (π : C(S, ℂ) →⋆ₐ[ℂ] (K →L[ℂ] K))
  (v : K) (ν : Measure S) [IsFiniteMeasure ν] [ν.Regular], (∀ f : C(S, ℂ), ∫ s, f s ∂ν = inner ℂ v (π f v)) →
  ∃ V : Lp ℂ 2 ν →L[ℂ] K, (∀ h, ‖V h‖ = ‖h‖) ∧
    ∀ (f : C(S, ℂ)) (h h' : Lp ℂ 2 ν), ((h' : S → ℂ) =ᵐ[ν] fun s => f s * h s) → V h' = π f (V h)

structure IsSpec {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] {B : Type} [CommRing B]
    [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (R : B →⋆ₐ[ℂ] (K →L[ℂ] K)) {S : Type} [MeasurableSpace S] (ν : Measure S)
    (χ : S → (B →⋆ₐ[ℂ] ℂ)) (V : Lp ℂ 2 ν →L[ℂ] K) : Prop where
  ne : ν ≠ 0
  meas : ∀ b, Measurable fun s => χ s b
  bdd : ∀ b s, ‖χ s b‖ ≤ ‖R b‖
  iso : ∀ h, ‖V h‖ = ‖h‖
  mul : ∀ b (h h' : Lp ℂ 2 ν), ((h' : S → ℂ) =ᵐ[ν] fun s => χ s b * h s) → V h' = R b (V h)

def Spec : Prop := ∀ (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B] (R : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (p : B →⋆ₐ[ℂ] ℂ)
  (C₀ : Finset B) (ε : ℝ), (∀ b, ‖p b‖ ≤ ‖R b‖) → 0 < ε →
  ∃ (S : Type) (_ : MeasurableSpace S) (ν : Measure S) (_ : IsFiniteMeasure ν) (χ : S → (B →⋆ₐ[ℂ] ℂ))
    (V : Lp ℂ 2 ν →L[ℂ] K), IsSpec R ν χ V ∧ ∀ᵐ s ∂ν, ∀ c ∈ C₀, ‖χ s c - p c‖ ≤ ε

def JointRep : Prop := ∀ (S : Type) [MeasurableSpace S] (ν : Measure S) [TopologicalSpace.SeparableSpace (Lp ℂ 2 ν)]
  [MeasurableSpace (Lp ℂ 2 ν)] [BorelSpace (Lp ℂ 2 ν)],
  ∃ Ψ : Lp ℂ 2 ν → S → ℂ, Measurable (Function.uncurry Ψ) ∧ ∀ h, Ψ h =ᵐ[ν] h

def IsRep {Y S : Type} [MeasurableSpace Y] [MeasurableSpace S] {ν : Measure S} (F : Y → Lp ℂ 2 ν) (f : Y → S → ℂ) : Prop :=
  Measurable (Function.uncurry f) ∧ ∀ y, f y =ᵐ[ν] F y

def Tonelli : Prop := ∀ (Y S : Type) [MeasurableSpace Y] [MeasurableSpace S] (m : Measure Y) [SFinite m] (ν : Measure S)
  [IsFiniteMeasure ν] (F : Y → Lp ℂ 2 ν) (f : Y → S → ℂ) (W : Y → ℝ≥0∞), IsRep F f → Measurable W →
  ∫⁻ y, W y * ‖F y‖ₑ ^ 2 ∂m ≠ ⊤ → ∀ᵐ s ∂ν, ∫⁻ y, W y * ‖f y s‖ₑ ^ 2 ∂m < ⊤

def WeakAE : Prop := ∀ (Y S ι : Type) [MeasurableSpace Y] [MeasurableSpace S] [Fintype ι] (m : Measure Y) [SFinite m]
  (ν : Measure S) [IsFiniteMeasure ν] (F : ι → Y → Lp ℂ 2 ν) (f : ι → Y → S → ℂ) (c : ι → Y → ℂ) (q : S → ℂ),
  (∀ j, IsRep (F j) (f j)) → (∀ j, AEStronglyMeasurable (c j) m) → (∀ j, ∫⁻ y, ‖c j y‖ₑ * ‖F j y‖ₑ ∂m ≠ ⊤) →
  MemLp q 2 ν → (∀ h : Lp ℂ 2 ν, ∑ j, ∫ y, c j y * inner ℂ (F j y) h ∂m = ∫ s, q s * h s ∂ν) →
  ∀ᵐ s ∂ν, ∑ j, ∫ y, c j y * conj (f j y s) ∂m = q s

def WeakEq (X : Ctx) {ι S : Type} [Fintype ι] [MeasurableSpace S] {ν : Measure S} (F : ι → X.G → Lp ℂ 2 ν)
    (Φ : Matrix ι ι (X.G → ℂ)) (σ : S → ℂ) : Prop :=
  ∀ x i (h : Lp ℂ 2 ν), ∑ j, ∫ y, Φ i j y * inner ℂ (F j (x * y)) h ∂X.μ = ∫ s, σ s * conj (F i x s) * h s ∂ν

def EigAE : Prop := ∀ (X : Ctx) (ι S : Type) [Fintype ι] [MeasurableSpace S] (ν : Measure S) [IsFiniteMeasure ν]
  (F : ι → X.G → Lp ℂ 2 ν) (f : ι → X.G → S → ℂ) (Φ : Matrix ι ι (X.G → ℂ)) (σ : S → ℂ) (A : ℝ),
  (∀ j, Continuous (F j)) → (∀ j, IsRep (F j) (f j)) → (∀ i j, Tst (Φ i j)) → Measurable σ → (∀ s, ‖σ s‖ ≤ A) →
  WeakEq X F Φ σ → ∀ᵐ s ∂ν, ∀ i, ∀ᵐ x ∂X.μ, ∑ j, ∫ y, Φ i j y * conj (f j (x * y) s) ∂X.μ = σ s * conj (f i x s)

def LocInt : Prop := ∀ (X : Ctx) (S : Type) [MeasurableSpace S] (ν : Measure S) [IsFiniteMeasure ν]
  (F : X.G → Lp ℂ 2 ν) (f : X.G → S → ℂ), Continuous F → IsRep F f → ∀ᵐ s ∂ν, LocallyIntegrable (fun x => f x s) X.μ

def NonZero : Prop := ∀ (X : Ctx) (S : Type) [MeasurableSpace S] (ν : Measure S) [IsFiniteMeasure ν]
  (F : X.G → Lp ℂ 2 ν) (f : X.G → S → ℂ), Continuous F → IsRep F f → (∀ᵐ s ∂ν, ∀ᵐ x ∂X.μ, f x s = 0) → F = 0

def ConvCont : Prop := ∀ (X : Ctx) (φ u : X.G → ℂ), Tst φ → LocallyIntegrable u X.μ →
  Continuous fun x => ∫ y, φ y * u (x * y) ∂X.μ

def Smooth : Prop := ∀ (X : Ctx) (ι κ : Type) [Fintype ι] (u : ι → X.G → ℂ) (Φ : κ → Matrix ι ι (X.G → ℂ)) (lam : κ → ℂ)
  (c₀ : κ), (∀ i, LocallyIntegrable (u i) X.μ) → (∀ i, ∀ γ ∈ X.Γ, ∀ x, u i (γ * x) = u i x) → (∀ c i j, Tst (Φ c i j)) →
  lam c₀ ≠ 0 → (∀ c i, ∀ᵐ x ∂X.μ, ∑ j, ∫ y, Φ c i j y * u j (x * y) ∂X.μ = lam c * u i x) →
  ∃ f : ι → X.G → ℂ, (∀ i, Continuous (f i) ∧ f i =ᵐ[X.μ] u i ∧ ∀ γ ∈ X.Γ, ∀ x, f i (γ * x) = f i x) ∧
    ∀ c i x, ∑ j, ∫ y, Φ c i j y * f j (x * y) ∂X.μ = lam c * f i x

structure EigData (X : Ctx) {ι κ S : Type} [Fintype ι] [MeasurableSpace S] (ν : Measure S) (F : ι → X.G → Lp ℂ 2 ν)
    (W : X.G → ℝ≥0∞) (Φ : κ → Matrix ι ι (X.G → ℂ)) (σ : κ → S → ℂ) (g : ℕ → ι → X.G → ℂ) : Prop where
  cont : ∀ i, Continuous (F i)
  inv : ∀ i, ∀ γ ∈ X.Γ, ∀ x, F i (γ * x) = F i x
  ne : F ≠ 0
  wt : ∀ i, ∫⁻ x, W x * ‖F i x‖ₑ ^ 2 ∂X.ν ≠ ⊤
  eig : ∀ c, WeakEq X F (Φ c) (σ c)
  gint : ∀ n i, AEStronglyMeasurable (g n i) X.ν ∧ ∫⁻ x, ‖g n i x‖ₑ * ‖F i x‖ₑ ∂X.ν ≠ ⊤
  orth : ∀ n (h : Lp ℂ 2 ν), ∑ i, ∫ x, g n i x * inner ℂ (F i x) h ∂X.ν = 0

structure Realised (X : Ctx) {ι κ : Type} [Fintype ι] (W : X.G → ℝ≥0∞) (Φ : κ → Matrix ι ι (X.G → ℂ)) (lam : κ → ℂ)
    (g : ℕ → ι → X.G → ℂ) (f : ι → X.G → ℂ) : Prop where
  cont : ∀ i, Continuous (f i)
  ne : f ≠ 0
  inv : ∀ i, ∀ γ ∈ X.Γ, ∀ x, f i (γ * x) = f i x
  wt : ∀ i, ∫⁻ x, W x * ‖f i x‖ₑ ^ 2 ∂X.ν < ⊤
  eig : ∀ c i x, ∑ j, ∫ y, Φ c i j y * f j (x * y) ∂X.μ = lam c * f i x
  orth : ∀ n, ∑ i, ∫ x, g n i x * f i x ∂X.ν = 0

def Desint : Prop := ∀ (X : Ctx) (ι κ S : Type) [Fintype ι] [Countable κ] [MeasurableSpace S] (ν : Measure S)
  [IsFiniteMeasure ν] [TopologicalSpace.SeparableSpace (Lp ℂ 2 ν)] (F : ι → X.G → Lp ℂ 2 ν) (W : X.G → ℝ≥0∞)
  (Φ : κ → Matrix ι ι (X.G → ℂ)) (σ : κ → S → ℂ) (g : ℕ → ι → X.G → ℂ) (c₀ : κ) (P : S → Prop),
  EigData X ν F W Φ σ g → Measurable W → (∀ c i j, Tst (Φ c i j)) → (∀ c, Measurable (σ c) ∧ ∃ A : ℝ, ∀ s, ‖σ c s‖ ≤ A) →
  (∀ᵐ s ∂ν, σ c₀ s ≠ 0) → (∀ᵐ s ∂ν, P s) → ∃ s, P s ∧ ∃ f, Realised X W Φ (fun c => σ c s) g f

def AeEq : Prop := ∀ (X : Ctx) (u u' : X.G → ℂ), Continuous u → Continuous u' → (∀ γ ∈ X.Γ, ∀ x, u (γ * x) = u x) →
  (∀ γ ∈ X.Γ, ∀ x, u' (γ * x) = u' x) → u =ᵐ[X.ν] u' → u = u'

def Unfold : Prop := ∀ (X : Ctx) (φ u : X.G → ℂ), Tst φ → Continuous u → (∀ γ ∈ X.Γ, ∀ x, u (γ * x) = u x) →
  (∀ x, ∫ y, ker X.Γ φ x y * u y ∂X.ν = ∫ y, φ y * u (x * y) ∂X.μ) ∧ Continuous fun x => ∫ y, φ y * u (x * y) ∂X.μ

structure IsRows (X : Ctx) {ι : Type} [Fintype ι] (T : X.Hs ι →L[ℂ] X.Hs ι) (k : ι → X.G → X.Hs ι) : Prop where
  cont : ∀ i, Continuous (k i)
  inv : ∀ i, ∀ γ ∈ X.Γ, ∀ x, k i (γ * x) = k i x
  rep : ∀ u i, (T u i : X.G → ℂ) =ᵐ[X.ν] fun x => inner ℂ (k i x) u
  norm : ∃ (C : ℝ≥0∞) (Ω : Set X.G), C ≠ ⊤ ∧ IsCompact Ω ∧ ∀ i x, ‖k i x‖ₑ ^ 2 ≤ C * cnt X.Γ Ω x

def RowsEx : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)) (T : X.Hs ι →L[ℂ] X.Hs ι),
  (∀ i j, Tst (Φ i j)) → X.IsOp Φ T → ∃ k, IsRows X T k

def RowsEig : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (Φ : Matrix ι ι (X.G → ℂ)) (T T₁ : X.Hs ι →L[ℂ] X.Hs ι)
  (k : ι → X.G → X.Hs ι) (u u' : X.Hs ι), (∀ i j, Tst (Φ i j)) → X.IsOp Φ T → IsRows X T₁ k → T (T₁ u) = T₁ u' →
  ∀ x i, ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ = inner ℂ (k i x) u'

def HsSep : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι], TopologicalSpace.SeparableSpace (X.Hs ι)

def FData : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] (J : K →L[ℂ] X.Hs ι) (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
  (R : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (a₀ : B) (Φ : B → Matrix ι ι (X.G → ℂ)) (g : ℕ → X.Hs ι) (W : X.G → ℝ≥0∞)
  (S : Type) [MeasurableSpace S] (ν : Measure S) [IsFiniteMeasure ν] (χ : S → (B →⋆ₐ[ℂ] ℂ)) (V : Lp ℂ 2 ν →L[ℂ] K),
  (∀ v, ‖J v‖ = ‖v‖) → (∀ b i j, Tst (Φ b i j)) → (∀ b, ∃ T, X.IsOp (Φ b) T ∧ ∀ v, T (J v) = J (R (b * a₀) v)) →
  IsSpec R ν χ V → (∀ᵐ s ∂ν, χ s a₀ ≠ 0) → Measurable W → (∀ x, W x ≠ 0 ∧ W x ≠ ⊤) →
  (∀ Ω, IsCompact Ω → ∫⁻ x, W x * cnt X.Γ Ω x ∂X.ν ≠ ⊤) → (∀ n v, inner ℂ (J v) (g n) = 0) →
  (∀ n i, ∫⁻ x, (W x)⁻¹ * ‖(g n i : X.G → ℂ) x‖ₑ ^ 2 ∂X.ν ≠ ⊤) →
  ∃ F : ι → X.G → Lp ℂ 2 ν, EigData X ν F W Φ (fun b s => χ s (b * a₀)) fun n i x => conj ((g n i : X.G → ℂ) x)

def OneStep : Prop := ∀ (X : Ctx) (ι : Type) [Fintype ι] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  [CompleteSpace K] (J : K →L[ℂ] X.Hs ι) (B : Type) [CommRing B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]
  (R : B →⋆ₐ[ℂ] (K →L[ℂ] K)) (p : B →⋆ₐ[ℂ] ℂ) (a₀ : B) (C : Set B) (Φ : B → Matrix ι ι (X.G → ℂ)) (g : ℕ → X.Hs ι)
  (W : X.G → ℝ≥0∞), (∀ v, ‖J v‖ = ‖v‖) → (∀ b, ‖p b‖ ≤ ‖R b‖) → p a₀ ≠ 0 → C.Countable → (1 : B) ∈ C →
  (∀ b i j, Tst (Φ b i j)) → (∀ b, ∃ T, X.IsOp (Φ b) T ∧ ∀ v, T (J v) = J (R (b * a₀) v)) →
  Measurable W → (∀ x, W x ≠ 0 ∧ W x ≠ ⊤) → (∀ Ω, IsCompact Ω → ∫⁻ x, W x * cnt X.Γ Ω x ∂X.ν ≠ ⊤) →
  (∀ n v, inner ℂ (J v) (g n) = 0) → (∀ n i, ∫⁻ x, (W x)⁻¹ * ‖(g n i : X.G → ℂ) x‖ₑ ^ 2 ∂X.ν ≠ ⊤) →
  ∀ (C₀ : Finset B) (ε : ℝ), 0 < ε → ∃ (s : B →⋆ₐ[ℂ] ℂ) (f : ι → X.G → ℂ), (∀ c ∈ C₀, ‖s c - p c‖ ≤ ε) ∧ s a₀ ≠ 0 ∧
    (∀ b, ‖s b‖ ≤ ‖R b‖) ∧
    Realised X W (fun c : C => Φ c) (fun c => s (c * a₀)) (fun n i x => conj ((g n i : X.G → ℂ) x)) f

theorem oneStep_of (h1 : Spec) (h2 : FData) (h3 : Desint) (h4 : HsSep) : OneStep := by
  classical
  intro X ι _ K _ _ _ J B _ _ _ _ R p a₀ C Φ g W hJ hp ha hC h1C hΦ hT hW hW' hWc hg hg' C₀ ε hε
  have hpos : 0 < ‖p a₀‖ := norm_pos_iff.2 ha
  obtain ⟨S, _, ν, _, χ, V, hS, hae⟩ := h1 K B R p (insert a₀ C₀) (min ε (‖p a₀‖ / 2)) hp (lt_min hε (half_pos hpos))
  have hne : ∀ᵐ s ∂ν, χ s a₀ ≠ 0 := hae.mono fun s hs e => by
    have := (hs a₀ (Finset.mem_insert_self _ _)).trans (min_le_right _ _)
    rw [e, zero_sub, norm_neg] at this
    linarith
  obtain ⟨F, hF⟩ := h2 X ι K J B R a₀ Φ g W S ν χ V hJ hΦ hT hS hne hW hW' hWc hg hg'
  have := h4 X ι
  have : SecondCountableTopology (X.Hs ι) := UniformSpace.secondCountable_of_separable _
  have : SecondCountableTopology (Lp ℂ 2 ν) :=
    (AddMonoidHomClass.isometry_of_norm (J.comp V) fun h => (hJ _).trans (hS.iso h)).isEmbedding.secondCountableTopology
  have := hC.to_subtype
  obtain ⟨s, hs, f, hf⟩ := h3 X ι C S ν F W (fun c : C => Φ c) (fun c s => χ s (c * a₀)) _ ⟨1, h1C⟩ _
    ⟨hF.cont, hF.inv, hF.ne, hF.wt, fun c => hF.eig c, hF.gint, hF.orth⟩ hW (fun c => hΦ c)
    (fun c => ⟨hS.meas _, _, hS.bdd _⟩) (by simpa using hne) (hae.and hne)
  exact ⟨χ s, f, fun c hc => (hs.1 c (Finset.mem_insert_of_mem hc)).trans (min_le_left _ _), hs.2, fun b => hS.bdd b s, hf⟩

end PositivityTheory.Rg.BcB.E2

end
