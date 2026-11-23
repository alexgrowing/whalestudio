import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm

noncomputable section

namespace GlobalTheory.Core.Rk.NSing

open scoped TensorProduct ENNReal NNReal ComplexConjugate Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Cont

section Abstract

def ProdLaw {ι VA Vi : Type} {Vv : ι → Type} [MeasurableSpace VA] [MeasurableSpace Vi] [∀ v, MeasurableSpace (Vv v)]
    (pi : VA → Vi) (pv : ∀ v, VA → Vv v) (L : ∀ v, Set (Vv v)) (μ : Measure VA) (μi : Measure Vi)
    (μv : ∀ v, Measure (Vv v)) : Prop :=
  Measurable pi ∧ (∀ v, Measurable (pv v)) ∧ (∀ v, MeasurableSet (L v)) ∧ (∀ᶠ v in cofinite, μv v (L v) = 1) ∧
  (∀ x, ∀ᶠ v in cofinite, pv v x ∈ L v) ∧
  ∀ S : Finset ι, (∀ v ∉ S, μv v (L v) = 1) → ∀ (fi : Vi → ℝ≥0∞) (fv : ∀ v, Vv v → ℝ≥0∞), Measurable fi →
    (∀ v, Measurable (fv v)) →
    ∫⁻ x in {x | ∀ v ∉ S, pv v x ∈ L v}, fi (pi x) * ∏ v ∈ S, fv v (pv v x) ∂μ = (∫⁻ y, fi y ∂μi) * ∏ v ∈ S, ∫⁻ y, fv v y ∂μv v

def RegOn {X : Type} [TopologicalSpace X] (U : Set X) (M : ℂ → X → ℂ) : Prop :=
  ∃ (Mc : ℂ → X → ℂ) (σ₀ : ℝ), (∀ s : ℂ, σ₀ < s.re → ∀ x ∈ U, Mc s x = M s x) ∧
    ∀ s₁ : ℂ, ∃ (k : ℕ) (r : ℝ) (H : ℂ → X → ℂ), 0 < r ∧
      (∀ s ∈ Metric.ball s₁ r, s ≠ s₁ → ∀ x ∈ U, H s x = (s - s₁) ^ k * Mc s x) ∧
      (∀ x ∈ U, DifferentiableOn ℂ (H · x) (Metric.ball s₁ r)) ∧
      ContinuousOn (fun p : ℂ × X => H p.1 p.2) (Metric.ball s₁ r ×ˢ U)

def DeltaAt {X : Type} [TopologicalSpace X] [MeasurableSpace X] (x₀ : X) (s₀ : ℂ) (M : ℂ → X → ℂ) (V : X → ℂ) : Prop :=
  ∀ U ∈ 𝓝 x₀, ∃ (ρ : Measure X) (K : Set X), IsProbabilityMeasure ρ ∧ IsCompact K ∧ K ⊆ U ∧ ρ Kᶜ = 0 ∧
    HolValueAt (fun s => ∫ x, M s x ∂ρ) s₀ (∫ x, V x ∂ρ)

end Abstract

section Ring

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def pairM {n : ℕ} (S T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) : R :=
  algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (∑ a, ∑ b, S a b * T b a)

def starM (σ : E →ₐ[F] E) {m n : ℕ} (g : Matrix (Fin m) (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin m) (R ⊗[F] E) :=
  (g.map (sigR R σ))ᵀ

variable [TopologicalSpace R] (χ : R → ℂ) (σ : E →ₐ[F] E)

def fou {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin n → Fin M → R ⊗[F] E))
    (Φ : (Fin n → Fin M → R ⊗[F] E) → ℂ) : HermR R σ n → ℂ :=
  fun S => ∫ X, Φ X * χ (pairM R S.1 (gramR R σ J X)) ∂μ

def wh {n : ℕ} (ν : Measure (HermR R σ n)) (G : HermR R σ n → ℂ) (lam : HermR R σ n → ℝ) (z : ℂ) (T : HermR R σ n) : ℂ :=
  ∫ S, G S * (lam S : ℂ) ^ z * conj (χ (pairM R S.1 T.1)) ∂ν

def ndeg (n : ℕ) : Set (HermR R σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det}

end Ring

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n d : ℕ}

def hermInf (S : HermR (AF F) σ n) : HermR (Ainf F) σ n :=
  ⟨Matrix.of fun a c => Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (S.1 a c), fun a c => by
    rw [Matrix.of_apply, Matrix.of_apply, ← S.2 a c]
    generalize S.1 c a = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [sigR]
    | add x y hx hy => simp only [map_add, hx, hy]⟩

def hermV (v : HeightOneSpectrum (𝓞 F)) (S : HermR (AF F) σ n) : HermR (Fv F v) σ n :=
  ⟨Matrix.of fun a c => GlobalTheory.GaugeEx.prV v (S.1 a c), fun a c => by
    rw [Matrix.of_apply, Matrix.of_apply, ← S.2 a c]
    generalize S.1 c a = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [sigR, GlobalTheory.GaugeEx.prV]
    | add x y hx hy => simp only [map_add, hx, hy]⟩

def latH (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) : Set (HermR (Fv F v) σ n) :=
  {S | ∀ a c, S.1 a c ∈ GlobalTheory.GaugeEx.intV b v}

def hermQ (n : ℕ) : AddSubgroup (HermR (AF F) σ n) :=
  (AddSubgroup.closure (Set.range fun T : Matrix (Fin n) (Fin n) E => T.map (inclR (F := F) (AF F)))).addSubgroupOf _

def tupQ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n M : ℕ) :
    AddSubgroup (Fin n → Fin M → AF F ⊗[F] E) :=
  AddSubgroup.closure (Set.range (ratTup (F := F) (E := E) (AF F) (M := M) (n := n)))

def CovOne {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (Γ : AddSubgroup V) (μ : Measure V) : Prop :=
  μ.IsAddHaarMeasure ∧ ∃ 𝓕, IsAddFundamentalDomain Γ 𝓕 μ ∧ μ 𝓕 = 1

def LocInv (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] (σ : E →ₐ[F] E) (lam : HermR R σ n → ℝ) : Prop :=
  ∃ N ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) (R ⊗[F] E)), ∀ m ∈ N, ∀ S S' : HermR R σ n,
    S'.1 = m * S.1 * starM R σ m → lam S' = lam S

def IsIdxHgt (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : HermR (Fv F v) σ n → ℝ) : Prop :=
  ∀ μ : Measure (Fin n → Fv F v ⊗[F] E), μ.IsAddHaarMeasure → μ {y | ∀ i, y i ∈ GlobalTheory.GaugeEx.intV b v} = 1 →
    ∀ S, lam S = μ.real {y | (∀ i, y i ∈ GlobalTheory.GaugeEx.intV b v) ∧ ∀ i, (S.1 *ᵥ y) i ∈ GlobalTheory.GaugeEx.intV b v}

structure IsHgt (b : Module.Basis (Fin d) F E) (ν : Measure (HermR (AF F) σ n)) (lam : HermR (AF F) σ n → ℝ)
    (li : HermR (Ainf F) σ n → ℝ) (lv : ∀ v, HermR (Fv F v) σ n → ℝ) (x₀ : ℝ) : Prop where

  prod : ∀ S, lam S = li (hermInf σ S) * ∏ᶠ v, lv v (hermV σ v S)

  inf : Continuous li ∧ ∀ S, 0 < li S

  fin : ∀ v, Continuous (lv v) ∧ ∀ S, 0 < lv v S

  poly : ∃ (C : ℝ) (N : ℕ), ∀ S, li S ≤ C * (1 + sizeTup b S.1) ^ N ∧ (li S)⁻¹ ≤ C * (1 + sizeTup b S.1) ^ N

  inv : ∀ v, LocInv (Fv F v) σ (lv v)

  unr : ∀ᶠ v in cofinite, IsIdxHgt σ b v (lv v)

  int : ∀ x : ℝ, x₀ < x → Integrable (fun S => lam S ^ x) ν

def IsGlue (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a c, σ (T c a) = T a c) (T' : HermR (Ainf F) σ n)
    (T'' : HermR (AF F) σ n) : Prop :=
  hermInf σ T'' = T' ∧ ∀ v, hermV σ v T'' = hermOf (Fv F v) σ T hT

structure IsBump (b : Module.Basis (Fin d) F E) (χ : Ainf F → ℂ) (ν : Measure (HermR (Ainf F) σ n))
    (β : HermR (Ainf F) σ n → ℝ) : Prop where

  cont : Continuous β

  nonneg : ∀ S, 0 ≤ β S

  cpt : HasCompactSupport β

  mass : ∫ S, β S ∂ν = 1

  dec : ∀ N : ℕ, Integrable (fun S : HermR (Ainf F) σ n =>
    ‖∫ T, (β T : ℂ) * conj (χ (pairM (Ainf F) S.1 T.1)) ∂ν‖ * (1 + sizeTup b S.1) ^ N) ν

end Adelic

section Residue

def IsResRing (K : Type) [CommRing K] (τ : K →+* K) (q : ℕ) (ε : ℂ) : Prop :=
  (∀ x, τ (τ x) = x) ∧ Nat.card K = q ^ 2 ∧ IsUnit (2 : K) ∧
    ((IsField K ∧ (∃ x, τ x ≠ x) ∧ ε = -1) ∨
      ∃ (k : Type) (_ : Field k) (e : K ≃+* k × k), (∀ x, e (τ x) = (e x).swap) ∧ ε = 1)

def IsHermK {K : Type} [CommRing K] (τ : K →+* K) {n : ℕ} (S : Matrix (Fin n) (Fin n) K) : Prop := (S.map τ)ᵀ = S

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ}

structure ResData (b : Module.Basis (Fin d) F E) (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (O : Subring (Fv F v ⊗[F] E)) (ϖ : Fv F v) (K : Type) [CommRing K] (τ : K →+* K) (red : O →+* K)
    (ψ₀ : AddChar K ℂ) : Prop where

  carrier : (O : Set (Fv F v ⊗[F] E)) = GlobalTheory.GaugeEx.intV b v

  stab : ∀ x : O, ∃ h : sigR (Fv F v) σ x.1 ∈ O, red ⟨_, h⟩ = τ (red x)

  unif : Valued.v ϖ = WithZero.exp (-1 : ℤ)

  two : Valued.v (2 : Fv F v) = 1

  base : ∀ t : Fv F v, algebraMap (Fv F v) (Fv F v ⊗[F] E) t ∈ O ↔ t ∈ v.adicCompletionIntegers F

  surj : Function.Surjective red

  ker : ∀ x : O, red x = 0 ↔ ∃ y ∈ O, x.1 = ϖ • y

  res : IsResRing K τ (Ideal.absNorm v.asIdeal) (GlobalTheory.LFun.etaU E v : ℂˣ)

  unram : GlobalTheory.LFun.etaFam E 1 v = {GlobalTheory.LFun.etaU E v ^ 1}

  cond : ∀ y : Fv F v, (∀ t ∈ v.adicCompletionIntegers F, psiV F ψ v (y * t) = 1) ↔ y ∈ v.adicCompletionIntegers F

  perf : ∀ y : Fv F v ⊗[F] E, (∀ x ∈ O, Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (y * x) ∈ v.adicCompletionIntegers F) ↔ y ∈ O

  chr : ∀ x : O, ψ₀ (red x) =
    psiV F ψ v (ϖ⁻¹ * (algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) x.1))

  nontriv : ∃ x, τ x = x ∧ ψ₀ x ≠ 1

end Residue

section Datum

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.MixModel
open GlobalTheory.Core.Rk.SWLaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def toTup {m n : ℕ} (x : Mx D m n) : Fin n → Fin m → AF D.host.F ⊗[D.host.F] D.host.E := fun a i => x i a

def ofTup {m n : ℕ} (X : Fin n → Fin m → AF D.host.F ⊗[D.host.F] D.host.E) : Mx D m n := Matrix.of fun i a => X a i

def IsSkH {n : ℕ} (e : HermR (AF D.host.F) D.sp.cm.sig n ≃+ skewA D n) : Prop :=
  Continuous e ∧ Continuous e.symm ∧ ∀ S, ((e S).1 : Mx D n n) = incA D (-D.host.xi0⁻¹) • (S.1 : Mx D n n)

def lamA (A : HSp D) (a : GL (Fin A.rank) (AE D)) (w g : GA D (dblSp A))
    (e : HermR (AF D.host.F) D.sp.cm.sig A.rank ≃+ skewA D A.rank) (S : HermR (AF D.host.F) D.sp.cm.sig A.rank) : ℝ :=
  hgt A a (w * (dblDec A).nC (e S) * g)

def lamV (A : HSp D) (w g : GA D (dblSp A)) (e : HermR (AF D.host.F) D.sp.cm.sig A.rank ≃+ skewA D A.rank)
    (v : HeightOneSpectrum (𝓞 D.host.F)) (S : HermR (AF D.host.F) D.sp.cm.sig A.rank) : ℝ :=
  hgtFin D.sp.cm.sig (dblSp A).gram (frameLat A) v (proj D.sp.cm.sig (dblSp A).gram v (w * (dblDec A).nC (e S) * g))

def lamI (A : HSp D) (a : GL (Fin A.rank) (AE D)) (w g : GA D (dblSp A))
    (e : HermR (AF D.host.F) D.sp.cm.sig A.rank ≃+ skewA D A.rank) (S : HermR (AF D.host.F) D.sp.cm.sig A.rank) : ℝ :=
  lamA A a w g e S / ∏ᶠ v, lamV A w g e v S

end Datum

end GlobalTheory.Core.Rk.NSing

end
