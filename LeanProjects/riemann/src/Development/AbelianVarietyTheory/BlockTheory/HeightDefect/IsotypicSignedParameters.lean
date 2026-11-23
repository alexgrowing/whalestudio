import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.IsAutFunDef
import Formalism.LocalRingCardinality.DataTies

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters

structure SignedPar (n : ℕ) where
  lam : Fin n → ℝ
  sgn : Fin n → Bool
  hc : Formalism.QuantumDeterminants.IsHCParam lam

namespace SignedPar

variable {n : ℕ} (P : SignedPar n)

def p : ℕ := (Finset.univ.filter fun a => P.sgn a = true).card

def q : ℕ := (Finset.univ.filter fun a => P.sgn a = false).card

def IsOfSig (p q : ℕ) : Prop := P.p = p ∧ P.q = q

def entries : Multiset (ℝ × Bool) := Finset.univ.val.map fun a => (P.lam a, P.sgn a)

def low : Fin n → ℝ := Formalism.QuantumDeterminants.lowK P.sgn P.lam

def size : ℝ := ⨆ ab : Fin n × Fin n, |P.lam ab.1 - P.lam ab.2|

def dimV : ℝ :=
  (∏ a : Fin n, ∏ b ∈ Finset.univ.filter (fun b : Fin n => a < b), (P.lam a - P.lam b)) /
    ∏ i ∈ Finset.range n, ((i.factorial : ℕ) : ℝ)

def GapGe (h : ℝ) : Prop := ∀ a b : Fin n, P.sgn a ≠ P.sgn b → h ≤ |P.lam a - P.lam b|

def dual : SignedPar n where
  lam a := -P.lam a.rev
  sgn a := P.sgn a.rev
  hc := by
    refine ⟨fun a b hab => neg_lt_neg (P.hc.1 (Fin.rev_lt_rev.2 hab)), fun a => ?_⟩
    obtain ⟨m, hm⟩ := P.hc.2 a.rev
    refine ⟨-m - (n - 1), ?_⟩
    push_cast
    linarith

def twist (c : ℤ) : SignedPar n where
  lam a := P.lam a + c
  sgn := P.sgn
  hc := by
    refine ⟨fun a b hab => by simpa using P.hc.1 hab, fun a => ?_⟩
    obtain ⟨m, hm⟩ := P.hc.2 a
    refine ⟨m + c, ?_⟩
    push_cast
    linarith

end SignedPar

def signedParameterU11 : SignedPar 2 where
  lam := ![1 / 2, -1 / 2]
  sgn := ![true, false]
  hc := by
    refine ⟨?_, fun a => ?_⟩
    · intro a b hab
      fin_cases a <;> fin_cases b <;> simp at hab ⊢
      norm_num
    · fin_cases a
      · exact ⟨0, by norm_num⟩
      · exact ⟨-1, by norm_num⟩

theorem signedParameter_one_one_isOfSig : signedParameterU11.IsOfSig 1 1 := by
  constructor <;> decide

theorem signedParameter_one_one_dimV_eq_one : signedParameterU11.dimV = 1 := by
  have h0 : (Finset.univ.filter fun b : Fin 2 => (0 : Fin 2) < b) = {1} := by decide
  have h1 : (Finset.univ.filter fun b : Fin 2 => (1 : Fin 2) < b) = ∅ := by decide
  simp only [SignedPar.dimV, Fin.prod_univ_two, h0, h1, Finset.prod_range_succ]
  simp [signedParameterU11]
  norm_num

section Chains

variable {R : Ranks} (c : HCParam R)

def block (e : ℚ) (s : ℕ) : Multiset ℝ := (Multiset.range s).map fun i : ℕ => -(e : ℝ) + ((s : ℝ) - 1) / 2 - (i : ℝ)

def sigShift (n : ℕ) : ℝ := if Even n then -(1 / 2) else 0

def sigmaEntries (s : Fin R.m → Bool) : Multiset (ℝ × Bool) :=
  (Finset.univ.val.map fun i : Fin (R.k - 1) => (((c.v i : ℚ) : ℝ), true)) +
    Finset.univ.val.map fun i : Fin R.m => (-((c.b i : ℚ) : ℝ), s i)

def IsParD (j : ℕ) {n : ℕ} (P : SignedPar n) : Prop :=
  j ≤ R.m ∧ P.entries =
    (sigmaEntries c (fun i => decide ((i.val - j) % 2 = 0)) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin R.m => i.val < j), (block (c.e i) R.t).map fun x => (x, true)).map
      fun x => (x.1 + sigShift (R.rankY j), x.2)

def IsParHol (i : Fin R.m) {n : ℕ} (P : SignedPar n) : Prop :=
  P.entries = sigmaEntries c fun l => decide (l ≤ i)

def IsParV (i : Fin R.m) {n : ℕ} (P : SignedPar n) : Prop :=
  P.entries = (sigmaEntries c (fun _ => true) + (block (c.e i) R.t).map fun x => (x, true)).map
    fun x => (x.1 + sigShift R.nV, x.2)

def IsParPi (j : ℕ) {n : ℕ} (P : SignedPar n) : Prop :=
  j ≤ R.m ∧ P.entries =
    (Finset.univ.val.map fun i : Fin R.k => (((c.u i : ℚ) : ℝ), true)) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin R.m => i.val < j), (block (c.e i) (R.t + 1)).map fun x => (x, true)

end Chains

def IsFrame {n N : ℕ} (ε : Fin n → Bool) (G : Matrix (Fin N) (Fin N) ℂ) (A : Matrix (Fin n) (Fin N) ℂ)
    (B : Matrix (Fin N) (Fin n) ℂ) : Prop :=
  Aᴴ * Formalism.REAL.Jm ε * A = G ∧ A * B = 1 ∧ B * A = 1

def isotypic {n : ℕ} (u : Fin n → ℝ) {M : Type*} [AddCommGroup M] [Module ℂ M]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) M) : Submodule ℂ M :=
  sSup {S | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (T : H →ₗ[ℂ] M), IsHCTypeU n u π ∧
      (∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (x : H), T (π (k : Matrix (Fin n) (Fin n) ℂ) x) = ρ k (T x)) ∧
      S = LinearMap.range T}

section Adelic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def gramAt (V : HSp D) (τ : D.what₂.Tau) : Matrix (Fin V.rank) (Fin V.rank) ℂ := V.gram.map (tauE D τ)

def AtPlace (V : HSp D) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (h : GA D V) : Prop :=
  ∃ θ, IsInfFam θ ∧ IsAtTau θ V τ g h

def isotypicAt (V : HSp D) (τ : D.what₂.Tau) {n : ℕ} (u : Fin n → ℝ) : Submodule ℂ (GA D V → ℂ) :=
  sSup {S | ∃ (s : Bool) (A : Matrix (Fin n) (Fin V.rank) ℂ) (B : Matrix (Fin V.rank) (Fin n) ℂ)
    (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (T : H →ₗ[ℂ] (GA D V → ℂ)),
      IsFrame (fun _ => s) (gramAt V τ) A B ∧ IsHCTypeU n u π ∧
      (∀ k ∈ Matrix.unitaryGroup (Fin n) ℂ,
        AllSome (AtPlace V τ (B * k * A)) fun h => ∀ x : H, T (π k x) = rTr V h (T x)) ∧
      S = LinearMap.range T}

def isotypicInf (V : HSp D) {n : ℕ} (u : D.what₂.Tau → Fin n → ℝ) : Submodule ℂ (GA D V → ℂ) :=
  ⨅ τ, isotypicAt V τ (u τ)

def IsFormOfType (V : HSp D) {n : ℕ} (u : D.what₂.Tau → Fin n → ℝ) (φ : GA D V → ℂ) : Prop :=
  IsAutFunDef V φ ∧ φ ∈ isotypicInf V u

end Adelic

def IsCompactDual {n : ℕ} (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε)) : Prop :=
  ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n) (ν : Measure (UpqT P Q)) (νc : Measure (UpqT (P + Q) 0)) (c : ENNReal),
    (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false) ∧
    ν.IsHaarMeasure ∧ νc.IsHaarMeasure ∧ IsProbabilityMeasure νc ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
    OmegaDensity ν c ∧ OmegaDensity νc c ∧
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      μ A = ν {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)}

section Rep

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def HasFdeg {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  Nontrivial H ∧ ∃ μ : Measure (Formalism.REAL.UJ ε), IsCompactDual ε μ ∧ IsFdeg μ σ d

def IsDSPar {n : ℕ} (P : SignedPar n) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  IsDS P.sgn P.lam σ

def IsLowType {n : ℕ} (P : SignedPar n) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) : Prop :=
  IsKTypeOf P.sgn σ P.low S

def IsDSOn {n N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (P : SignedPar n)
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ A B, IsFrame P.sgn G A B ∧ IsDSPar P fun k => σ (B * k * A)

def HasFdegOn {N : ℕ} (G : Matrix (Fin N) (Fin N) ℂ) (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (d : ℝ) : Prop :=
  ∃ (ε : Fin N → Bool) (A B : Matrix (Fin N) (Fin N) ℂ), IsFrame ε G A B ∧ HasFdeg ε (fun k => σ (B * k * A)) d

def IsDSAt {D : D7} (V : HSp D) (τ : D.what₂.Tau) {n : ℕ} (P : SignedPar n)
    (σ : (letI := D.host.cmStar; Matrix (Fin V.rank) (Fin V.rank) ℂ) → (H →L[ℂ] H)) : Prop :=
  IsDSOn (gramAt V τ) P σ

end Rep

def IsFdegPar {n : ℕ} (P : SignedPar n) (d : ℝ) : Prop :=
  (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDSPar P σ) ∧
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDSPar P σ → HasFdeg P.sgn σ d

theorem IsFdegPar.pos {n : ℕ} {P : SignedPar n} {d : ℝ} (h : IsFdegPar P d) : 0 < d := by
  obtain ⟨⟨H, _, _, σ, hσ⟩, h2⟩ := h
  obtain ⟨_, μ, _, hd⟩ := h2 H σ hσ
  exact hd.1

def GapHyp (C : ℝ) {N : ℕ} (P : SignedPar N) (ep : ℝ) : Prop :=
  Real.exp (-(N : ℝ)) ≤ ep ∧ ep < 1 / 2 ∧
    P.GapGe (C * ((min P.p P.q : ℕ) : ℝ) * ((P.p : ℝ) * P.q) ^ 3 * N * Real.log N / ep ^ 2)

def ForDS {N : ℕ} (P : SignedPar N) (Q : ℝ → ℕ → Prop) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H))
    (d : ℝ) (S : Submodule ℂ H), IsDSPar P σ → HasFdeg P.sgn σ d → IsLowType P σ S → Q d (Module.finrank ℂ S)

def FdegTwoSided (C : ℝ) : Prop :=
  ∀ (N : ℕ) (P : SignedPar N) (ep : ℝ), GapHyp C P ep → ForDS P fun d dτ =>
    (1 - ep) * P.dimV ≤ d ∧ d ≤ 4 * (dτ : ℝ) * (C * P.p * P.q * N * P.size) ^ (P.p * P.q)

def DimBounds : Prop :=
  ∀ (N : ℕ) (P : SignedPar N), (1 ≤ P.dimV ∧ P.dimV ≤ (1 + P.size) ^ (N ^ 2)) ∧
    ForDS P fun _ dτ => 1 ≤ dτ ∧ (dτ : ℝ) ≤ (1 + P.size) ^ (N ^ 2)

def FdegLog (C : ℝ) : Prop :=
  ∀ (N : ℕ) (P : SignedPar N) (ep : ℝ), GapHyp C P ep → ForDS P fun d _ =>
    -1 ≤ Real.log d ∧ Real.log d ≤ C * (N : ℝ) ^ 2 * Real.log (C * N * (1 + P.size))

def SizeHyp (sc : Scale) {N : ℕ} (P : SignedPar N) : Prop :=
  (N : ℝ) ≤ sc.x ^ 6 ∧ P.size ≤ sc.x ^ 6 * sc.b

def FdegPoly (C : ℝ) : Prop :=
  ∃ (B : ℕ) (x0 : ℝ), ∀ sc : Scale, x0 ≤ sc.x →
    ∀ (N : ℕ) (P : SignedPar N) (ep : ℝ), GapHyp C P ep → SizeHyp sc P → ForDS P fun d _ =>
      |Real.log d| ≤ sc.x ^ B * sc.L ∧
      ∀ (N' : ℕ) (P' : SignedPar N') (ep' : ℝ), GapHyp C P' ep' → SizeHyp sc P' → ForDS P' fun d' _ =>
        |Real.log (d / d')| ≤ sc.x ^ B * sc.L

def FormalDegreeBounds : Prop :=
  ∃ C : ℝ, 0 < C ∧ FdegTwoSided C ∧ DimBounds ∧ FdegLog C ∧ FdegPoly C

def HarishChandraDegree : Prop := ∀ (N : ℕ) (P : SignedPar N), IsFdegPar P P.dimV

section Signatures

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def latAt (v : HeightOneSpectrum (𝓞 F)) {M : ℕ} (L : Set (Fin M → E)) :
    AddSubgroup (Fin M → v.adicCompletion F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ a ∈ v.adicCompletionIntegers F, ∃ x ∈ L, y = fun i => a ⊗ₜ[F] x i}

def LocIsom (hc : CMData F E) (v : HeightOneSpectrum (𝓞 F)) {M M' : ℕ} (G : Matrix (Fin M) (Fin M) E)
    (G' : Matrix (Fin M') (Fin M') E) (L : Set (Fin M → E)) (L' : Set (Fin M' → E)) : Prop :=
  ∃ (A : Matrix (Fin M') (Fin M) (v.adicCompletion F ⊗[F] E)) (B : Matrix (Fin M) (Fin M') (v.adicCompletion F ⊗[F] E)),
    A * B = 1 ∧ B * A = 1 ∧
    Formalism.UG.cT (Algebra.TensorProduct.map (AlgHom.id F (v.adicCompletion F)) hc.sig).toRingHom A *
              G'.map (fun x => (1 : v.adicCompletion F) ⊗ₜ[F] x) * A = G.map (fun x => (1 : v.adicCompletion F) ⊗ₜ[F] x) ∧
    ∀ y, y ∈ latAt v L ↔ A.mulVec y ∈ latAt v L'

def coordLat (W : HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

def HermSignatures (hc : CMData F E) : Prop :=
  (∀ (M : ℕ) (sg : (E →+* ℂ) → ℕ × ℕ), 1 ≤ M → (∀ τ, (sg τ).1 + (sg τ).2 = M) →
    (∀ τ, sg (ComplexEmbedding.conjugate τ) = sg τ) → Even (∑ w : InfinitePlace E, (sg w.embedding).2) →
      ∃ W : HSpace E, W.rank = M ∧ W.SigOK ∧ W.sig = sg) ∧
  (∀ M p q : ℕ, 1 ≤ M → p + q = M → ∃ W : HSpace E, W.rank = M ∧ W.SigOK ∧ ∀ τ, W.sig τ = (p, q)) ∧
  (∀ W W' : HSpace E, W.SigOK → W'.SigOK → W.sig = W'.sig →
    ∃ ι : W.V ≃ₗ[E] W'.V, HSpace.IsIsomEmb W W' (ι : W.V →ₗ[E] W'.V)) ∧
  ∀ W W' : HSpace E, W.rank = W'.rank → ∀ v : HeightOneSpectrum (𝓞 F),
    LocIsom hc v W.gram W'.gram (coordLat W) (coordLat W')

def IsSkewSelfDual {M : ℕ} (S : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  Sᴴ = -S ∧ S.det ≠ 0 ∧ Submodule.IsLattice E L ∧
    ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ S.mulVec x ∈ (1 : Submodule (𝓞 E) E)

def SkewSig (δ : E) {M : ℕ} (S : Matrix (Fin M) (Fin M) E) (p q : ℕ) : Prop :=
  ∀ τ : E →+* ℂ, Formalism.UG.HasSignature ((δ⁻¹ • S).map τ) p q

def SkewSignatures (hc : CMData F E) (δ : E) : Prop :=
  ∀ M : ℕ, Even M →
    (∀ p q : ℕ, p + q = M → ∃ (S : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)),
      IsSkewSelfDual S L ∧ SkewSig δ S p q) ∧
    ∀ (S S' : Matrix (Fin M) (Fin M) E) (L L' : Submodule (𝓞 E) (Fin M → E)),
      IsSkewSelfDual S L → IsSkewSelfDual S' L' →
        (∀ p q : ℕ, SkewSig δ S p q → SkewSig δ S' p q →
          ∃ g : GL (Fin M) E, (g : Matrix (Fin M) (Fin M) E)ᴴ * S' * (g : Matrix (Fin M) (Fin M) E) = S) ∧
        ∀ v : HeightOneSpectrum (𝓞 F), LocIsom hc v S S' (L : Set (Fin M → E)) (L' : Set (Fin M → E))

end Signatures

def IsWittIndex {M : ℕ} (G : Matrix (Fin M) (Fin M) ℂ) (r : ℕ) : Prop :=
  IsGreatest {s | ∃ W : Submodule ℂ (Fin M → ℂ), Module.finrank ℂ W = s ∧
    ∀ x ∈ W, ∀ y ∈ W, star x ⬝ᵥ G.mulVec y = 0} r

def WittIndexReal : Prop :=
  ∀ (M p q : ℕ) (G : Matrix (Fin M) (Fin M) ℂ), Formalism.UG.HasSignature G p q → IsWittIndex G (min p q)

def Signatures : Prop :=
  (∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E), Even (Module.finrank ℚ F) → (∀ x : E, IsOfFinOrder x → x = 1 ∨ x = -1) →
    ∀ (d : ℕ) (δ : E), 0 < d → δ ^ 2 = -(d : E) → star δ = -δ →
      HermSignatures hc ∧ SkewSignatures hc δ) ∧
  WittIndexReal

end GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters
